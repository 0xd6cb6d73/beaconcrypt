import BeaconcryptCore.Computational.PqxdhBeaconPhase2Routed
import BeaconcryptCore.Computational.PqxdhPhase2JointIdentity
import BeaconcryptCore.Computational.PqxdhGeneratedBeaconState
import BeaconcryptCore.Computational.PqxdhProtocolSelector
import BeaconcryptCore.Computational.PqxdhProtocolQueryBounds

/-!
The private Phase2 auxiliary compiler retains the reached CTX cache and local callback state. Original optional codec, conversion, local-key and DH callbacks are fixed before fresh generation. Initial64 and ongoing/raw callbacks use the same fixed source and the existing shared-cache native handler. Generated static DH forwards only its original identity index and peer bytes through the joint source service; the seed stays in the later borrowed interpreter.

The generated private-conversion representation uses the explicit native conversion contract from JointIdentity; its model-total conversion is not a proof that an arbitrary optional native conversion succeeds. Other conversion failures remain actual optional callback results. Functional HKDF/AEAD, the total ROM hash interface, local callback implementation, and physical erasure remain explicit contracts. No reached scheduler, freshness or cryptographic distribution claim is introduced. Storage and restoration are outside scope.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SourceAux
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhBeaconPhase2Routed (AuxQuery AuxSpec)
open PqxdhGeneratedBeaconState (IdentityHandle)
open PqxdhPhase2JointIdentity (Converted)
open PqxdhPrivateKemSource PqxdhKemIndCca PqxdhJointKdfGame
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhRootTableInitialization (rootArray)

/-- Only actual local source operations, with no generated secret or private-root capability. -/
inductive LocalQuery (I D K X Response : Type) where
  | decode : Bytes → LocalQuery I D K X Response
  | ciphertext : Response → LocalQuery I D K X Response
  | ephemeral : Response → LocalQuery I D K X Response
  | serverIdentity : Response → LocalQuery I D K X Response
  | publicConversion : Word32 → LocalQuery I D K X Response
  | privateConversion : I → LocalQuery I D K X Response
  | dhPair : D → Word32 → LocalQuery I D K X Response
  | dhIdentity : X → Word32 → LocalQuery I D K X Response
  | assignedId : Response → LocalQuery I D K X Response
  | localDecapsulation : Ciphertext → K → LocalQuery I D K X Response
  | application : Response → LocalQuery I D K X Response

abbrev LocalSpec (I D K X Response : Type) : OracleSpec (LocalQuery I D K X Response)
  | .decode _ => Option Response
  | .ciphertext _ => Option Ciphertext
  | .ephemeral _ | .serverIdentity _ | .publicConversion _ => Option Word32
  | .privateConversion _ => Option X
  | .dhPair _ _ | .dhIdentity _ _ | .localDecapsulation _ _ => Option Word32
  | .assignedId _ => Std.U64
  | .application _ => Option Bytes

abbrev Spec (I D K X Response : Type) := AuxSpec (IdentityHandle I) D K (X ⊕ Converted) Response
abbrev SharedState := RawCtxSharedPrimitive.SharedState

variable {ι I D K X Response A : Type} {baseSpec : OracleSpec ι}

/-- Original local state changes preserve the same reached common CTX cache. -/
def localRun (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (LocalSpec I D K X Response).Domain) (state : SharedState A) :
    ProbComp ((LocalSpec I D K X Response).Range query × SharedState A) :=
  (fun result => (result.1, (result.2, state.2))) <$> (localImpl query).run state.1

/-- One actual source native callback; no independent private/public cache is allocated. -/
noncomputable def rawRun (source : FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (state : SharedState A) :=
  (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run state

/-- The executable auxiliary compiler contains neither an identity seed nor the selected KEM secret. -/
noncomputable def sourceAux (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (Spec I D K X Response) (StateT (SharedState A) (OracleComp (SelectorSpec baseSpec)))
  | .decode raw => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.decode raw) state)
  | .ciphertext response => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.ciphertext response) state)
  | .ephemeral response => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.ephemeral response) state)
  | .serverIdentity response => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.serverIdentity response) state)
  | .publicConversion value => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.publicConversion value) state)
  | .privateConversion (.existing identity) =>
      StateT.mk fun state => (fun result => (Option.map Sum.inl result.1, result.2)) <$>
        PqxdhProtocolSelector.coins (localRun localImpl (.privateConversion identity) state)
  | .privateConversion (.generated index publicIdentity) => pure (some (.inr ⟨index, publicIdentity⟩))
  | .dhPair pair peer => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.dhPair pair peer) state)
  | .dhIdentity (.inl identity) peer => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.dhIdentity identity peer) state)
  | .dhIdentity (.inr handle) peer => StateT.mk fun state => (fun reply => (Option.map rootArray reply, state)) <$>
      PqxdhPhase2JointIdentity.selectorDh handle (PqxdhPhase2InputBytes.word peer)
  | .assignedId response => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.assignedId response) state)
  | .localDecapsulation ciphertext key => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.localDecapsulation ciphertext key) state)
  | .initial request => pure (RawCtxSourceHkdf.initialResponse source.crypto request)
  | .application response => StateT.mk fun state => PqxdhProtocolSelector.coins (localRun localImpl (.application response) state)
  | .raw query => StateT.mk fun state => PqxdhProtocolSelector.coins (rawRun source query state)

/-- Ordinary interpretation keeps both private states; only this later interpreter owns the identity pool. -/
noncomputable def borrowedAux
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (Spec I D K X Response)
      (StateT (SharedState A × BareState count) (OracleComp (MlKemCCAOracleSpec baseSpec))) :=
  ((borrowedSelector attachedVerify primitives count).mapStateTBase (sourceAux source localImpl)).flattenStateT

/-- Direct source execution retains all local effects and the complete joint service history. -/
noncomputable def directAux
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) :
    QueryImpl (Spec I D K X Response) (StateT (SharedState A × BareState count) ProbComp)
  | .decode raw => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.decode raw) state.1
  | .ciphertext response => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.ciphertext response) state.1
  | .ephemeral response => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.ephemeral response) state.1
  | .serverIdentity response => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.serverIdentity response) state.1
  | .publicConversion value => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.publicConversion value) state.1
  | .privateConversion (.existing identity) => StateT.mk fun state =>
      (fun r => (Option.map Sum.inl r.1, (r.2, state.2))) <$> localRun localImpl (.privateConversion identity) state.1
  | .privateConversion (.generated index publicIdentity) => pure (some (.inr ⟨index, publicIdentity⟩))
  | .dhPair pair peer => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.dhPair pair peer) state.1
  | .dhIdentity (.inl identity) peer => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.dhIdentity identity peer) state.1
  | .dhIdentity (.inr handle) peer => StateT.mk fun state =>
      (fun r => (Option.map rootArray r.1, (state.1, r.2))) <$>
        (simulateQ (bareImpl attachedVerify primitives count)
          (PqxdhPhase2JointIdentity.staticDh handle (PqxdhPhase2InputBytes.word peer))).run state.2
  | .assignedId response => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.assignedId response) state.1
  | .localDecapsulation ciphertext key => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.localDecapsulation ciphertext key) state.1
  | .initial request => pure (RawCtxSourceHkdf.initialResponse source.crypto request)
  | .application response => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> localRun localImpl (.application response) state.1
  | .raw query => StateT.mk fun state => (fun r => (r.1, (r.2, state.2))) <$> rawRun source query state.1

/-- Internal local coins preserve the full identity pool and use the original ordinary uniform channel. -/
theorem borrowed_coins {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (work : ProbComp Result) (state : BareState count) :
    (simulateQ (borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count)
      (PqxdhProtocolSelector.coins work)).run state =
      ccaCoins ((fun result => (result, state)) <$> work) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      change (do
        let reply ← (liftM ((MlKemCCAOracleSpec baseSpec).query (.inl (.inl query))) : OracleComp (MlKemCCAOracleSpec baseSpec) _)
        (simulateQ (borrowedSelector attachedVerify primitives count)
          (PqxdhProtocolSelector.coins (next reply))).run state) = _
      simp only [ih, ccaCoins, simulateQ_map, simulateQ_bind, simulateQ_spec_query, map_bind]
      rfl

/-- Each original optional callback and both complete private poststates survive ordinary interpretation. -/
theorem borrowed_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (Spec I D K X Response).Domain) (state : SharedState A × BareState count) :
    (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl query).run state =
      ccaCoins ((directAux attachedVerify primitives count source localImpl query).run state) := by
  cases query with
  | privateConversion identity =>
      cases identity <;>
        simp only [borrowedAux, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, sourceAux,
          StateT.run_mk, directAux, simulateQ_map, StateT.run_map, borrowed_coins,
          simulateQ_pure, StateT.run_pure, map_pure, ccaCoins, simulateQ_map, Functor.map_map]
  | dhIdentity identity peer =>
      cases identity with
      | inl prior =>
          simp only [borrowedAux, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, sourceAux,
            StateT.run_mk, directAux, borrowed_coins, ccaCoins, simulateQ_map, Functor.map_map]
      | inr handle =>
          simp only [borrowedAux, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, sourceAux,
            StateT.run_mk, directAux, simulateQ_map, StateT.run_map,
            PqxdhPhase2JointIdentity.selectorDh, PqxdhPhase2JointIdentity.borrowed_source,
            ccaCoins, simulateQ_map, Functor.map_map]
  | initial request => rfl
  | _ =>
      simp only [borrowedAux, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, sourceAux,
        StateT.run_mk, directAux, borrowed_coins, ccaCoins, simulateQ_map, Functor.map_map]

/-- The same arbitrary adaptive client preserves its result, local state, common cache and joint identity history. -/
theorem borrowed_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec I D K X Response) Result) (state : SharedState A × BareState count) :
    (simulateQ (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl) client).run state =
      ccaCoins ((simulateQ (directAux attachedVerify primitives count source localImpl) client).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, borrowed_step]
      simp only [ccaCoins, simulateQ_bind, ih]

/-- Flattening the existing selector interpreter is merely an exact reassociation of the complete two-state result. -/
theorem source_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec I D K X Response) Result)
    (state : SharedState A) (identities : BareState count) :
    (simulateQ (borrowedSelector (baseSpec := baseSpec) attachedVerify primitives count)
      ((simulateQ (sourceAux source localImpl) client).run state)).run identities =
      ccaCoins ((fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (directAux attachedVerify primitives count source localImpl) client).run (state, identities)) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  change (fun result => ((result.1, result.2.1), result.2.2)) <$>
    (simulateQ (borrowedAux attachedVerify primitives count source localImpl) client).run (state, identities) = _
  rw [borrowed_complete]
  simp only [ccaCoins, simulateQ_map]

/-- Actual ordinary local evaluation recovers the original source auxiliary program without any target-key success or agreement premise. -/
theorem evaluated_complete {Result KemSK : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (client : OracleComp (Spec I D K X Response) Result)
    (state : SharedState A × BareState count) :
    evalKem baseImpl kem secret
      ((simulateQ (borrowedAux attachedVerify primitives count source localImpl) client).run state) =
      (simulateQ (directAux attachedVerify primitives count source localImpl) client).run state := by
  rw [borrowed_complete, evalKem_coins]

/-- Legal fixed-source initial64 uses the actual request and leaves both complete private states unchanged. -/
theorem initial_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (request : ratchet.SymmetricRatchetKdfRequest) (state : SharedState A × BareState count) :
    (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl (.initial request)).run state =
      pure (RawCtxSourceHkdf.initialResponse source.crypto request, state) := by
  rfl

/-- The raw callback uses the existing native shared-cache interpreter at the actual reached state. -/
theorem raw_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : RawCtxSourceOpen.NativeSpec.Domain) (state : SharedState A × BareState count) :
    (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl (.raw query)).run state =
      ccaCoins ((fun result => (result.1, (result.2, state.2))) <$>
        (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run state.1) := by
  exact borrowed_step attachedVerify primitives count source localImpl (.raw query) state

/-- A represented generated identity returns the actual optional source DH, with the original nested optional history and untouched shared primitive state. -/
theorem generated_dh_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64)
    (wiring : SourceWiring source.crypto primitives secretOfSeed)
    (handle : Converted) (peer : Word32) (seed : IdentitySeed) (state : SharedState A × BareState count)
    (represented : PqxdhPhase2JointIdentity.Represents primitives state.2 handle seed) :
    (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl (.dhIdentity (.inr handle) peer)).run state =
      let reply := sourceDhReply source.crypto (secretOfSeed seed).toList (PqxdhPhase2InputBytes.word peer)
      pure (Option.map rootArray reply,
        (state.1, PqxdhPhase2JointIdentity.afterDh handle (PqxdhPhase2InputBytes.word peer) (some reply) state.2)) := by
  rw [borrowed_step]
  simp only [directAux, StateT.run_mk, PqxdhPhase2JointIdentity.staticDh_source attachedVerify
    source.crypto primitives secretOfSeed wiring count handle (PqxdhPhase2InputBytes.word peer) state.2 seed represented,
    map_pure, ccaCoins, simulateQ_pure]

/-- The original source service records missing indices and rejected DH replies without changing the reached primitive state. -/
theorem generated_dh_complete
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (handle : Converted) (peer : Word32) (state : SharedState A × BareState count) :
    (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl (.dhIdentity (.inr handle) peer)).run state =
      let reply := state.2.2.seeds[handle.index]?.map (fun seed => primitives.staticDh seed (PqxdhPhase2InputBytes.word peer))
      pure (Option.map rootArray reply.join,
        (state.1, PqxdhPhase2JointIdentity.afterDh handle (PqxdhPhase2InputBytes.word peer) reply state.2)) := by
  rw [borrowed_step]
  simp only [directAux, StateT.run_mk, PqxdhPhase2JointIdentity.staticDh_complete,
    map_pure, ccaCoins, simulateQ_pure]

/-- Generated conversion retains only public provenance and changes no source state. Native optional conversion still requires its explicit reached representation equation. -/
theorem generated_conversion
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (index : Nat) (publicIdentity : PublicIdentity) (state : SharedState A) :
    (sourceAux (baseSpec := baseSpec) source localImpl (.privateConversion (.generated index publicIdentity))).run state =
      pure (some (.inr (⟨index, publicIdentity⟩ : Converted)), state) := by
  rfl

open PqxdhPrivateKemQueryBounds PqxdhJointPhase1AcceptanceComposition PqxdhJointPhase1Reports

def serviceBill (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] :
    (Spec I D K X Response).Domain → Nat
  | .dhIdentity (.inr handle) peer =>
      if predicate (.inl (PqxdhPhase2JointIdentity.request handle (PqxdhPhase2InputBytes.word peer))) then 1 else 0
  | _ => 0

/-- Every possible callback has its exact source-service bill; actual local coins remain on the separately counted internal channel. -/
theorem source_class_bound
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (query : (Spec I D K X Response).Domain) (state : SharedState A) :
    ((sourceAux (baseSpec := baseSpec) source localImpl query).run state).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) predicate) (serviceBill predicate query) := by
  have excluded {Result : Type} (work : ProbComp Result) :=
    PqxdhProtocolSelector.coins_excluded (baseSpec := baseSpec) (SelectorSource (baseSpec := baseSpec) predicate)
      (fun _ => by simp [SelectorSource]) work
  cases query with
  | privateConversion identity =>
      cases identity <;> simp only [sourceAux, StateT.run_mk, StateT.run_pure, serviceBill,
        isQueryBoundP_map_iff]
      · exact excluded _
      · trivial
  | dhIdentity identity peer =>
      cases identity with
      | inl prior => exact excluded _
      | inr handle =>
          simpa only [sourceAux, StateT.run_mk, isQueryBoundP_map_iff, serviceBill] using
            PqxdhPhase2JointIdentity.selectorDh_class_bound (baseSpec := baseSpec)
              handle (PqxdhPhase2InputBytes.word peer) predicate
  | initial request => trivial
  | _ => exact excluded _

/-- This compiler cannot request a signature; the complete later identity transcript is still retained. -/
theorem source_no_sign
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (Spec I D K X Response).Domain) (state : SharedState A) :
    ((sourceAux (baseSpec := baseSpec) source localImpl query).run state).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) IsSigning) 0 := by
  have bound := source_class_bound (baseSpec := baseSpec) source localImpl IsSigning query state
  have cost : serviceBill IsSigning query = 0 := by
    cases query <;> try rfl
    case dhIdentity identity peer =>
      cases identity <;> simp [serviceBill, IsSigning, PqxdhPhase2JointIdentity.request,
        PqxdhDynamicIdentityRouting.dynamicClass, PqxdhJointIdentityFamily.IsClass]
  simpa only [cost] using bound

/-- No auxiliary callback allocates a joint identity. -/
theorem source_no_create
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (Spec I D K X Response).Domain) (state : SharedState A) :
    ((sourceAux (baseSpec := baseSpec) source localImpl query).run state).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) (IsSourceClass (SourceClass PqxdhDynamicIdentityPool.IsCreate))) 0 := by
  have bound := source_class_bound (baseSpec := baseSpec) source localImpl
    (IsSourceClass (SourceClass PqxdhDynamicIdentityPool.IsCreate)) query state
  have cost : serviceBill (IsSourceClass (SourceClass PqxdhDynamicIdentityPool.IsCreate)) query = 0 := by
    cases query <;> try rfl
    case dhIdentity identity peer =>
      cases identity <;> simp [serviceBill, IsSourceClass, sourceQuery, SourceClass,
        PqxdhDynamicIdentityPool.IsCreate, PqxdhPhase2JointIdentity.request]
  simpa only [cost] using bound

/-- The actual shared native callback pays at most one 64-byte hash sampling, with deterministic source HKDF and AEAD still real local computation. -/
theorem raw_uniform (source : FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (state : SharedState A) :
    (rawRun source query state).IsTotalQueryBound 64 := by
  have bound := RawCtxSharedPrimitive.native_uniform_step source.crypto (RawCtxSourceHkdf.kdfImpl source) 0
    (RawCtxSourceHkdf.kdf_uniform source) query state
  apply bound.mono
  split <;> (try split) <;> omega

/-- The direct source bill includes all local callback coins and the original shared hash, with no charge inferred from distribution equality. -/
theorem direct_uniform_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (Spec I D K X Response).Domain) (state : SharedState A × BareState count) :
    ((directAux attachedVerify primitives count source localImpl query).run state).IsTotalQueryBound (max qLocal 64) := by
  have localBudget (query : (LocalSpec I D K X Response).Domain) (before : SharedState A) :
      (localRun localImpl query before).IsTotalQueryBound (max qLocal 64) := by
    simpa only [localRun, IsTotalQueryBound, isQueryBound_map_iff] using
      (localBound query before.1).mono (Nat.le_max_left qLocal 64)
  cases query with
  | privateConversion identity =>
      cases identity <;> simp only [directAux, StateT.run_mk, StateT.run_pure,
        IsTotalQueryBound, isQueryBound_map_iff]
      · exact localBudget _ _
      · trivial
  | dhIdentity identity peer =>
      cases identity with
      | inl prior =>
          simpa only [directAux, StateT.run_mk, IsTotalQueryBound, isQueryBound_map_iff] using localBudget (.dhIdentity prior peer) state.1
      | inr handle =>
          simp only [directAux, StateT.run_mk, PqxdhPhase2JointIdentity.staticDh_complete, map_pure]
          trivial
  | initial request => trivial
  | raw request =>
      simpa only [directAux, StateT.run_mk, IsTotalQueryBound, isQueryBound_map_iff] using
        (raw_uniform source request state.1).mono (Nat.le_max_right qLocal 64)
  | _ =>
      simp only [directAux, StateT.run_mk, IsTotalQueryBound, isQueryBound_map_iff]
      exact localBudget _ _

/-- The ordinary auxiliary interface has only actual uniform calls: static DH is interpreted privately, and retained prior keys do not cause a selected-key decapsulation request. -/
theorem borrowed_classes
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (Spec I D K X Response).Domain) (state : SharedState A × BareState count) :
    let work := (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl query).run state
    work.IsQueryBoundP IsMlKemUniformQuery (max qLocal 64) ∧
      work.IsQueryBoundP IsMlKemBaseQuery 0 ∧ work.IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0 := by
  dsimp only
  rw [borrowed_step]
  refine ⟨PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
    (direct_uniform_bound attachedVerify primitives count source localImpl qLocal localBound query state), ?_, ?_⟩
  · exact PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ (fun _ => by simp [IsMlKemBaseQuery])
  · exact PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ (fun _ => by simp [IsMlKemLogicalDecapsulationQuery])

set_option backward.isDefEq.respectTransparency false in
/-- Source syntax charges the actual local coins and every generated static-DH request before any private interpretation. -/
theorem source_total_bound
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (Spec I D K X Response).Domain) (state : SharedState A) :
    ((sourceAux (baseSpec := baseSpec) source localImpl query).run state).IsTotalQueryBound (max qLocal 64) := by
  have localBudget (query : (LocalSpec I D K X Response).Domain) (before : SharedState A) :
      (PqxdhProtocolSelector.coins (baseSpec := baseSpec) (localRun localImpl query before)).IsTotalQueryBound (max qLocal 64) := by
    apply PqxdhProtocolQueryBounds.coins_total
    simpa only [localRun, IsTotalQueryBound, isQueryBound_map_iff] using
      (localBound query before.1).mono (Nat.le_max_left qLocal 64)
  cases query with
  | privateConversion identity =>
      cases identity <;> simp only [sourceAux, StateT.run_mk, StateT.run_pure,
        IsTotalQueryBound, isQueryBound_map_iff]
      · exact localBudget _ _
      · trivial
  | dhIdentity identity peer =>
      cases identity with
      | inl prior => exact localBudget _ _
      | inr handle =>
          change (do
            let reply ← (liftM ((SelectorSpec baseSpec).query
              (.inl (.inl (PqxdhPhase2JointIdentity.request handle (PqxdhPhase2InputBytes.word peer))))) :
              OracleComp (SelectorSpec baseSpec) (Option (Option DhOutput)))
            pure (Option.map rootArray reply.join, state)).IsTotalQueryBound (max qLocal 64)
          exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, fun _ => by trivial⟩
  | initial request => trivial
  | raw request =>
      exact PqxdhProtocolQueryBounds.coins_total _ _
        ((raw_uniform source request state).mono (Nat.le_max_right qLocal 64))
  | _ => exact localBudget _ _

/-- An arbitrary adaptive auxiliary program performs no signing or identity creation, including every rejected callback and subsequent continuation. -/
theorem source_restrictions {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec I D K X Response) Result) (state : SharedState A) :
    let work := (simulateQ (sourceAux (baseSpec := baseSpec) source localImpl) client).run state
    work.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) IsSigning) 0 ∧
      work.IsQueryBoundP (SelectorSource (baseSpec := baseSpec)
        (IsSourceClass (SourceClass PqxdhDynamicIdentityPool.IsCreate))) 0 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact ⟨by trivial, by trivial⟩
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      constructor
      · exact isQueryBoundP_bind (source_no_sign source localImpl query state)
          (fun result _ => (ih result.1 result.2).1)
      · exact isQueryBoundP_bind (source_no_create source localImpl query state)
          (fun result _ => (ih result.1 result.2).2)

end BeaconcryptCore.Computational.PqxdhPhase2SourceAux

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.evaluated_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.evaluated_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.initial_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.initial_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.raw_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.raw_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.generated_dh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.generated_dh_source

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.generated_dh_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.generated_dh_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.generated_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.generated_conversion

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_no_sign' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_no_sign

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_no_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_no_create

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.raw_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.raw_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.direct_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.direct_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.borrowed_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_total_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_total_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_restrictions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SourceAux.source_restrictions

import BeaconcryptCore.Computational.PqxdhLivePhase2Aux
import BeaconcryptCore.Computational.PqxdhPhase2SharedBounds

/-!
Actual native KEM handles are represented by the selected creation slot or an explicitly different creation slot. This prevents other-key auxiliary decapsulation from acquiring the selected slot through arbitrary public-key aliases. It is an indexed representation of the same complete source owner, not a claim that any two key byte strings are unequal.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot
open PqxdhKemIndCca PqxdhLiveKemRouting
open PqxdhLivePhase2Aux (Identity LocalSpec SharedState)
variable {KemSK I D A Response : Type}

abbrev OtherHandle (selected : Nat) := { handle : Handle // handle.2 ≠ selected }

def encode (selected : Nat) (handle : Handle) : Option (OtherHandle selected) :=
  if same : handle.2 = selected then none else some ⟨handle, same⟩

def decode (selected : Nat) (target : MlKem768PublicKey) : Option (OtherHandle selected) → Handle
  | none => (target, selected)
  | some handle => handle.val

/-- An actual retained selected handle recovers its public bytes from its unique creation index; other-index bytes need not be distinct. -/
theorem decode_encode (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (handle : Handle) (known : Known pool handle) :
    decode selected target (encode selected handle) = handle := by
  by_cases same : handle.2 = selected
  · simpa only [encode, dite_eq_left same, decode] using
      Prod.ext (PqxdhLiveKemOwnership.selected_public pool selected target secret present handle known same).symm same.symm
  · simp only [encode, dite_eq_right same, decode]

/-- Reversible representation retains every private prekey, identity, binding, cache-independent owner field and attempt counter. -/
theorem owner_inverse (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat)
    (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (owner : RawCtxBeaconLifecycle.State I D Handle) (valid : PqxdhLiveKemOwnership.Owner pool owner) :
    PqxdhBeaconPhase1Publication.mapState id (decode selected target)
      (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner) = owner := by
  cases owner with
  | mk beacon attempts =>
    cases beacon with
    | mk identity keyId serverIdentity phase =>
      cases phase <;> simp only [PqxdhLiveKemOwnership.Owner, PqxdhPhase2KemProvenance.Phase] at valid
      all_goals simp only [PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase, id_eq]
      all_goals rw [decode_encode pool selected target secret present _ valid]

/-- The complete native program commutes with this selected/other-index representation, preserving every optional reply and complete auxiliary poststate. -/
theorem native_encoded_run {X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D Handle X Response) (StateT A m))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State I D Handle) (valid : PqxdhLiveKemOwnership.Owner pool owner) (auxiliary : A) :
    (fun result => ((result.1.1, PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2), result.2)) <$>
      (simulateQ (handler ∘ₛ PqxdhPhase2KemHandles.native (decode selected target))
        (PqxdhBeaconPhase2Publication.nativeOwner read raw
          (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner))).run auxiliary =
      (simulateQ handler (PqxdhBeaconPhase2Publication.nativeOwner read raw owner)).run auxiliary := by
  rw [PqxdhPhase2KemHandles.native_owner_run, owner_inverse pool selected target secret present owner valid]


variable {ι : Type} {baseSpec : OracleSpec ι}
open PqxdhPrivateKemSource PqxdhJointIdentity PqxdhJointKdfGame
open PqxdhBeaconPhase2Preparation (Word32 Ciphertext)
open PqxdhPhase2JointIdentity (Converted)
open PqxdhRootTableInitialization (rootArray)

abbrev AuxSpec (selected : Nat) (D Response : Type) :=
  PqxdhBeaconPhase2Routed.AuxSpec Identity D (OtherHandle selected) Converted Response

/-- Both original local/cache and joint-identity states stay private. KEM attempt instrumentation is accumulated separately by the complete native dispatcher. -/
abbrev AuxState (A : Type) := SharedState A × PqxdhDynamicIdentityPool.SourceState

def localCca (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (LocalSpec D Response).Domain) : StateT (AuxState A) (OracleComp (MlKemCCAOracleSpec baseSpec)) ((LocalSpec D Response).Range query) :=
  fun state => ccaCoins ((fun result => (result.1, ((result.2, state.1.2), state.2))) <$> (callbacks query).run state.1.1)

/-- A typed other-index operation never forwards to the selected CCA oracle. Missing local slots and missing local payloads retain their optional rejection. -/
def otherDecapsulation (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (handle : OtherHandle selected) (ciphertext : MlKem768Ciphertext) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret) :=
  match keys handle.val.2 with
  | none => pure none
  | some pair => match pair.2 with
      | none => pure none
      | some secret => ccaAmbient (kem.decaps secret ciphertext)

/-- Concrete optional auxiliary operations require no selected-secret or candidate argument. Original local/private state, correlated joint DH, real fixed initial HKDF and shared raw cache are retained. Arbitrary input histories and byte aliases are not excluded. -/
noncomputable def auxiliary (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp)) :
    QueryImpl (AuxSpec selected D Response) (StateT (AuxState A) (OracleComp (MlKemCCAOracleSpec baseSpec)))
  | .decode raw => localCca callbacks (.decode raw)
  | .ciphertext response => localCca callbacks (.ciphertext response)
  | .ephemeral response => localCca callbacks (.ephemeral response)
  | .serverIdentity response => localCca callbacks (.serverIdentity response)
  | .publicConversion value => localCca callbacks (.publicConversion value)
  | .privateConversion identity => pure (some ⟨identity.1, identity.2⟩)
  | .dhPair pair value => localCca callbacks (.dhPair pair value)
  | .dhIdentity converted peer => fun state => ccaCoins
      ((fun result => (Option.map rootArray result.1.join, (state.1, result.2))) <$>
        (PqxdhDynamicIdentityPool.lazyImpl primitives
          (PqxdhPhase2JointIdentity.request converted (PqxdhPhase2InputBytes.word peer))).run state.2)
  | .assignedId response => localCca callbacks (.assignedId response)
  | .localDecapsulation ciphertext handle => fun state =>
      (fun reply => (Option.map rootArray reply, state)) <$>
        otherDecapsulation kem selected keys handle (PqxdhPhase2InputBytes.ciphertext ciphertext)
  | .initial request => pure (RawCtxSourceHkdf.initialResponse source.crypto request)
  | .application response => localCca callbacks (.application response)
  | .raw query => fun state => ccaCoins
      ((fun result => (result.1, (result.2, state.2))) <$>
        (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run state.1)

/-- Typed other-index dispatch is exactly the existing indexed router at a provably different slot. No public-key or secret-byte inequality is needed. -/
theorem other_pre (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (handle : OtherHandle selected) (ciphertext : MlKem768Ciphertext) :
    otherDecapsulation kem selected keys handle ciphertext = pre kem selected keys handle.val ciphertext := by
  simp only [otherDecapsulation, pre, handle.property, ite_false]
  rfl


/-- Challenge blocking does not change an other-index callback: its complete original primitive program remains on the ambient channel. -/
theorem other_post_pre (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (selected : Nat) (keys : PrivateKeys KemSK) (handle : OtherHandle selected) (ciphertext : MlKem768Ciphertext) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge (otherDecapsulation kem selected keys handle ciphertext) =
      evalKem baseImpl kem secret (otherDecapsulation kem selected keys handle ciphertext) := by
  cases found : keys handle.val.2 with
  | none => simp only [otherDecapsulation, found]; rfl
  | some pair =>
    cases payload : pair.2 with
    | none => simp only [otherDecapsulation, found, payload]; rfl
    | some localSecret =>
      simp only [otherDecapsulation, found, payload]
      rw [PqxdhDynamicKemPost.ambient, evalKem_ambient]

/-- Actual source other-key decapsulation is simulated at its exact indexed key, even when its public or shared-secret bytes alias the selected key. -/
theorem other_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret)) (challenge : MlKem768Ciphertext)
    (handle : OtherHandle selected) (ciphertext : MlKem768Ciphertext) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
      (otherDecapsulation kem selected (redact selected pool) handle ciphertext) =
        Prod.fst <$> (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate handle.val.2 ciphertext)).run pool := by
  rw [other_post_pre, other_pre, PqxdhLiveKemRouting.pre_source baseImpl kem pool selected target secret present]


/-- Every other-key primitive operation retains its ordinary resource allowance; the compiler introduces no extra ambient request. -/
theorem other_queries (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (keys : PrivateKeys KemSK) (handle : OtherHandle selected) (ciphertext : MlKem768Ciphertext)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] (cost : Nat)
    (bounded : ∀ secret, (kem.decaps secret ciphertext).IsQueryBoundP (fun query => predicate (.inl query)) cost) :
    (otherDecapsulation kem selected keys handle ciphertext).IsQueryBoundP predicate cost := by
  cases found : keys handle.val.2 with
  | none => simp only [otherDecapsulation, found]; trivial
  | some pair =>
    cases payload : pair.2 with
    | none => simp only [otherDecapsulation, found, payload]; trivial
    | some localSecret =>
      simpa only [otherDecapsulation, found, payload] using
        PqxdhPrivateRootQueryBounds.ccaAmbient_bound _ predicate cost (bounded localSecret)

/-- The source-derived other-index type prevents every auxiliary selected-key CCA query, including equal-byte aliases and rejected local handles. -/
theorem auxiliary_no_selected (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (AuxSpec selected D Response).Domain) (state : AuxState A) :
    ((auxiliary primitives kem selected keys source callbacks query).run state).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0 := by
  have coins {Result : Type} (work : ProbComp Result) :=
    PqxdhPrivateRootQueryBounds.ccaCoins_excluded (baseSpec := baseSpec) work IsMlKemLogicalDecapsulationQuery
      (fun _ => by simp [IsMlKemLogicalDecapsulationQuery])
  cases query with
  | localDecapsulation ciphertext handle =>
    change ((fun reply => (Option.map rootArray reply, state)) <$>
      otherDecapsulation kem selected keys handle (PqxdhPhase2InputBytes.ciphertext ciphertext)).IsQueryBoundP _ 0
    rw [isQueryBoundP_map_iff]
    apply other_queries
    intro secret
    simpa [IsQueryBoundP, IsMlKemLogicalDecapsulationQuery] using isQueryBoundP_false (kem.decaps secret (PqxdhPhase2InputBytes.ciphertext ciphertext)) 0
  | privateConversion identity => trivial
  | initial request => trivial
  | _ => exact coins _


structure DecapsulationEvent (Shared : Type) where
  index : Nat
  ciphertext : MlKem768Ciphertext
  reply : Option Shared

def slot (selected : Nat) : Option (OtherHandle selected) → Nat
  | none => selected
  | some handle => handle.val.2

/-- Every attempted native decapsulation is recorded after its actual optional reply, including rejection and any later abort before root evaluation. -/
def observe {Shared : Type} (selected : Nat)
    (query : (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared).Domain)
    (reply : (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared).Range query)
    (history : List (DecapsulationEvent Shared)) : List (DecapsulationEvent Shared) :=
  match query with
  | .inl (.decapsulate ciphertext handle) =>
      history ++ [⟨slot selected handle, PqxdhPhase2InputBytes.ciphertext ciphertext, reply⟩]
  | _ => history

/-- Only mathematical source reconstruction materializes challenge markers into source-private observation replies. -/
def observations {Shared : Type} (materialize : Shared → MlKemSharedSecret)
    (history : List (DecapsulationEvent Shared)) : List (PqxdhLiveKemBirth.Observation KemSK) :=
  history.map (fun event => ⟨.decapsulate event.index event.ciphertext, event.reply.map materialize⟩)

/-- The complete native interpreter gets an additional private ordered attempt log, without changing callback arguments or returning the log to the source continuation. -/
def logged {Shared : Type} {m : Type → Type} [Monad m] (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared)
      (StateT A m)) :
    QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared)
      (StateT (A × List (DecapsulationEvent Shared)) m) := fun query state => do
  let result ← (handler query).run state.1
  pure (result.1, (result.2, observe selected query result.1 state.2))

/-- Forgetting only the added decapsulation instrumentation gives the exact complete original execution, retaining every optional callback result and all existing auxiliary state. -/
theorem logged_erase {Shared Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) (StateT A m))
    (client : OracleComp (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) Result)
    (auxiliary : A) (history : List (DecapsulationEvent Shared)) :
    (fun result => (result.1, result.2.1)) <$> (simulateQ (logged selected handler) client).run (auxiliary, history) =
      (simulateQ handler client).run auxiliary := by
  induction client using OracleComp.inductionOn generalizing auxiliary history with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [logged, StateT.run, map_bind, pure_bind, bind_assoc]
    congr 1
    exact funext fun result => ih result.1 result.2 (observe selected query result.1 history)


/-- Attempt instrumentation adds no underlying query in any resource class, for the full adaptive native continuation. -/
theorem logged_queries {Shared Result κ : Type} {spec : OracleSpec κ} (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) (StateT A (OracleComp spec)))
    (client : OracleComp (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) Result)
    (auxiliary : A) (history : List (DecapsulationEvent Shared))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((simulateQ (logged selected handler) client).run (auxiliary, history)).IsQueryBoundP predicate bound ↔
      ((simulateQ handler client).run auxiliary).IsQueryBoundP predicate bound := by
  rw [← logged_erase selected handler client auxiliary history, isQueryBoundP_map_iff]

/-- Source reconstruction appends the actual indexed optional reply in precisely the original pool-history order. -/
theorem observations_step {Shared : Type} (materialize : Shared → MlKemSharedSecret) (selected : Nat)
    (ciphertext : Ciphertext) (handle : Option (OtherHandle selected)) (reply : Option Shared)
    (history : List (DecapsulationEvent Shared)) :
    observations (KemSK := KemSK) materialize
      (observe (D := D) (Response := Response) selected (.inl (.decapsulate ciphertext handle)) reply history) =
      observations materialize history ++ [⟨.decapsulate (slot selected handle) (PqxdhPhase2InputBytes.ciphertext ciphertext), reply.map materialize⟩] := by
  simp only [observe, observations, List.map_append, List.map_cons, List.map_nil]

open PqxdhPhase2DecapsulationRouting (Shared)

/-- Actual opaque-shared owner execution with concrete live auxiliary services and complete private attempt instrumentation. Selected challenge bytes are never an executable argument. -/
noncomputable def privateOwner (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected)))
    (state : AuxState A × List (DecapsulationEvent Shared)) :=
  (simulateQ (logged selected (PqxdhBeaconPhase2Routed.handles source challenge
      (auxiliary primitives kem selected keys source callbacks)))
    (PqxdhBeaconPhase2Shared.owner read raw owner)).run state

/-- The retained log does not change the native private-root execution, original optional plaintext, full final owner, auxiliary state or shared cache. -/
theorem privateOwner_erase (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected)))
    (state : AuxState A × List (DecapsulationEvent Shared)) :
    (fun result => (result.1, result.2.1)) <$>
      privateOwner primitives kem selected keys source callbacks challenge read raw owner state =
      (simulateQ (PqxdhBeaconPhase2Routed.handles source challenge
        (auxiliary primitives kem selected keys source callbacks))
        (PqxdhBeaconPhase2Shared.owner read raw owner)).run state.1 :=
  logged_erase selected _ _ state.1 state.2


def mapEvent {Shared T : Type} (interpret : Shared → T) (event : DecapsulationEvent Shared) : DecapsulationEvent T :=
  ⟨event.index, event.ciphertext, event.reply.map interpret⟩

/-- The source comparison may interpret a private marker while preserving each attempt's original index, ciphertext, order and optional rejection. -/
def observeWith {Shared T : Type} (interpret : Shared → T) (selected : Nat)
    (query : (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared).Domain)
    (reply : (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared).Range query)
    (history : List (DecapsulationEvent T)) : List (DecapsulationEvent T) :=
  match query with
  | .inl (.decapsulate ciphertext handle) =>
      history ++ [⟨slot selected handle, PqxdhPhase2InputBytes.ciphertext ciphertext, reply.map interpret⟩]
  | _ => history

def loggedWith {Shared T : Type} {m : Type → Type} [Monad m] (interpret : Shared → T) (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) (StateT A m)) :
    QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared)
      (StateT (A × List (DecapsulationEvent T)) m) := fun query state => do
  let result ← (handler query).run state.1
  pure (result.1, (result.2, observeWith interpret selected query result.1 state.2))

/-- Interpreting the private attempt log commutes with one actual callback observation, including every optional failure. -/
theorem observe_map {Shared T : Type} (interpret : Shared → T) (selected : Nat)
    (query : (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared).Domain)
    (reply : (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared).Range query)
    (history : List (DecapsulationEvent Shared)) :
    (observe selected query reply history).map (mapEvent interpret) =
      observeWith interpret selected query reply (history.map (mapEvent interpret)) := by
  rcases query with preparation | tail
  · cases preparation <;> simp only [observe, observeWith, List.map_append, List.map_cons, List.map_nil, mapEvent]
  · rfl

/-- Materializing a private log is an exact full-state transformation of the complete adaptive execution. No log or shared secret is inserted into a source callback reply. -/
theorem logged_map {Shared T Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → T) (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) (StateT A m))
    (client : OracleComp (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) Result)
    (auxiliary : A) (history : List (DecapsulationEvent Shared)) :
    (fun result => (result.1, (result.2.1, result.2.2.map (mapEvent interpret)))) <$>
      (simulateQ (logged selected handler) client).run (auxiliary, history) =
        (simulateQ (loggedWith interpret selected handler) client).run (auxiliary, history.map (mapEvent interpret)) := by
  induction client using OracleComp.inductionOn generalizing auxiliary history with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [logged, loggedWith, StateT.run, map_bind, pure_bind, bind_assoc]
    congr 1
    exact funext fun result => (ih result.1 result.2 (observe selected query result.1 history)).trans
      (congrArg (fun history => (simulateQ (loggedWith interpret selected handler) (next result.1)).run (result.2, history))
        (observe_map interpret selected query result.1 history))


def nativeObserve (selected : Nat)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response).Domain)
    (reply : (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response).Range query)
    (history : List (DecapsulationEvent Word32)) : List (DecapsulationEvent Word32) :=
  match query with
  | .inl (.decapsulate ciphertext handle) =>
      history ++ [⟨slot selected handle, PqxdhPhase2InputBytes.ciphertext ciphertext, reply⟩]
  | _ => history

def nativeLogged {m : Type → Type} [Monad m] (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response) (StateT A m)) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response)
      (StateT (A × List (DecapsulationEvent Word32)) m) := fun query state => do
  let result ← (handler query).run state.1
  pure (result.1, (result.2, nativeObserve selected query result.1 state.2))

set_option backward.isDefEq.respectTransparency false in
/-- The exact original optional decapsulation correspondence also preserves the complete ordered private attempt log. -/
theorem logged_decapsulation {Shared : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32) (selected : Nat)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response) (StateT A m))
    (handles : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) (StateT A m))
    (calls : PqxdhBeaconPhase2Shared.FullCalls interpret native handles)
    (ciphertext : Ciphertext) (handle : Option (OtherHandle selected)) :
    nativeLogged selected native (.inl (.decapsulate ciphertext handle)) =
      Option.map interpret <$> loggedWith interpret selected handles (.inl (.decapsulate ciphertext handle)) := by
  funext state
  simp only [nativeLogged, nativeObserve]
  rw [calls.preparation.decapsulate ciphertext handle]
  change _ = (Option.map interpret <$> loggedWith interpret selected handles (.inl (.decapsulate ciphertext handle))).run state
  rw [StateT.run_map, StateT.run_map]
  simp only [loggedWith, StateT.run, observeWith, bind_map_left, map_bind, map_pure]
  rfl


private def unchanged {X : Type} {m : Type → Type} [Monad m] (callback : StateT A m X) :
    StateT (A × List (DecapsulationEvent Word32)) m X := fun state => do
  let result ← callback.run state.1
  pure (result.1, (result.2, state.2))

/-- Every original native callback correspondence extends to the complete ordered attempt instrumentation. Its decapsulation reply is interpreted once, without changing any continuation or private auxiliary effect. -/
theorem logged_full_calls {Shared : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32) (selected : Nat)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response) (StateT A m))
    (handles : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) (StateT A m))
    (calls : PqxdhBeaconPhase2Shared.FullCalls interpret native handles) :
    PqxdhBeaconPhase2Shared.FullCalls interpret (nativeLogged selected native) (loggedWith interpret selected handles) := by
  constructor
  · constructor
    · intro raw; exact congrArg unchanged (calls.preparation.decode raw)
    · intro response; exact congrArg unchanged (calls.preparation.ciphertext response)
    · intro response; exact congrArg unchanged (calls.preparation.ephemeral response)
    · intro response; exact congrArg unchanged (calls.preparation.serverIdentity response)
    · intro value; exact congrArg unchanged (calls.preparation.publicConversion value)
    · intro identity; exact congrArg unchanged (calls.preparation.privateConversion identity)
    · exact logged_decapsulation interpret selected native handles calls
    · intro pair value; exact congrArg unchanged (calls.preparation.dhPair pair value)
    · intro identity value; exact congrArg unchanged (calls.preparation.dhIdentity identity value)
    · intro response; exact congrArg unchanged (calls.preparation.assignedId response)
    · intro secrets; exact congrArg unchanged (calls.preparation.eraseShared secrets)
  · constructor
    · intro secrets input built; exact congrArg unchanged (calls.tail.root secrets input built)
    · intro request; exact congrArg unchanged (calls.tail.initial request)
    · intro response; exact congrArg unchanged (calls.tail.application response)
    · intro query; exact congrArg unchanged (calls.tail.raw query)


/-- Complete native source execution and opaque-shared execution retain the same interpreted attempt log and every original owner/auxiliary field. This includes aborting after decapsulation and before root processing. -/
theorem owner_logged_realization {Shared : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (interpret : Shared → Word32) (selected : Nat)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response) (StateT A m))
    (handles : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) (StateT A m))
    (calls : PqxdhBeaconPhase2Shared.FullCalls interpret native handles)
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected)))
    (auxiliary : A) (history : List (DecapsulationEvent Shared)) :
    (simulateQ (nativeLogged selected native) (PqxdhBeaconPhase2Publication.nativeOwner read raw owner)).run
      (auxiliary, history.map (mapEvent interpret)) =
        (fun result => (result.1, (result.2.1, result.2.2.map (mapEvent interpret)))) <$>
          (simulateQ (logged selected handles) (PqxdhBeaconPhase2Shared.owner read raw owner)).run (auxiliary, history) := by
  rw [PqxdhBeaconPhase2Shared.owner_realization interpret _ _ (logged_full_calls interpret selected native handles calls)]
  exact (logged_map interpret selected handles _ auxiliary history).symm

/-- Interpreting the original primitive effects commutes with logging their actual replies; the entire private auxiliary and ordered log states remain present. -/
theorem logged_interpret {Shared κ ξ : Type} {spec : OracleSpec κ} {base : OracleSpec ξ}
    (interpreter : QueryImpl spec (OracleComp base)) (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared)
      (StateT A (OracleComp spec))) :
    interpreter.mapStateTBase (logged selected handler) = logged selected (interpreter.mapStateTBase handler) := by
  funext query state
  simp only [QueryImpl.mapStateTBase, logged, StateT.run, simulateQ_bind, simulateQ_pure]
  rfl

/-- Primitive interpretation preserves the whole adaptive private-marker transcript before mathematical materialization. -/
theorem logged_program_interpret {Shared Result κ ξ : Type} {spec : OracleSpec κ} {base : OracleSpec ξ}
    (interpreter : QueryImpl spec (OracleComp base)) (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared)
      (StateT A (OracleComp spec)))
    (client : OracleComp (PqxdhBeaconPhase2Shared.FullSpec Identity D (Option (OtherHandle selected)) Converted Response Shared) Result)
    (state : A × List (DecapsulationEvent Shared)) :
    simulateQ interpreter ((simulateQ (logged selected handler) client).run state) =
      (simulateQ (logged selected (interpreter.mapStateTBase handler)) client).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, logged_interpret]


/-- The concrete live auxiliary services and private challenge-root interpreter realize the entire native owner together with its ordered optional decapsulation log. Only the source comparison supplies the selected secret and materializes the private log. -/
theorem privateOwner_actual (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (keys : PrivateKeys KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected)))
    (state : AuxState A × List (DecapsulationEvent Shared)) :
    (simulateQ (nativeLogged selected (PqxdhBeaconPhase2Routed.native source kem secret challenge
      (auxiliary primitives kem selected keys source callbacks)))
      (PqxdhBeaconPhase2Publication.nativeOwner read raw owner)).run
        (state.1, state.2.map (mapEvent (fun shared => rootArray (PqxdhPhase2DecapsulationRouting.materialize supplied shared)))) =
      (fun result => (result.1, (result.2.1, result.2.2.map
        (mapEvent (fun shared => rootArray (PqxdhPhase2DecapsulationRouting.materialize supplied shared)))))) <$>
        simulateQ (PqxdhChallengeSecretRouting.actualImpl source kem secret challenge)
          (privateOwner primitives kem selected keys source callbacks challenge read raw owner state) := by
  unfold privateOwner
  rw [logged_program_interpret]
  exact owner_logged_realization _ selected _ _
    (PqxdhBeaconPhase2Routed.full_calls source kem secret challenge supplied agreement
      (auxiliary primitives kem selected keys source callbacks)) read raw owner state.1 state.2


/-- Source reconstruction retains the original private key table and appends exactly the native optional decapsulation replies to its existing history. -/
def restorePool (pool : PqxdhLiveKemBirth.Pool KemSK) (history : List (DecapsulationEvent Word32)) :
    PqxdhLiveKemBirth.Pool KemSK :=
  { pool with transcript := pool.transcript ++ observations PqxdhPhase2InputBytes.word history }

/-- The complete original local/cache and identity state are paired with the reconstructed original KEM state. This mathematical map is not an executable reveal. -/
def restore (pool : PqxdhLiveKemBirth.Pool KemSK) (state : AuxState A × List (DecapsulationEvent Word32)) :
    SharedState A × PqxdhLiveKemBirth.State KemSK :=
  (state.1.1, (state.1.2, restorePool pool state.2))

set_option backward.isDefEq.respectTransparency false in
/-- Original pool decapsulation changes only the ordered observation history, for both present and missing indices and every optional primitive reply. -/
theorem pool_decapsulation (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) :
    (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate index ciphertext)).run pool =
      (fun reply => (reply, PqxdhLiveKemBirth.record (.decapsulate index ciphertext) reply pool)) <$>
        (Prod.fst <$> (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate index ciphertext)).run pool) := by
  cases found : pool.keys[index]? <;>
    simp only [PqxdhLiveKemBirth.poolImpl, StateT.run, found, bind_pure_comp, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Each native byte-array reply reconstructs precisely one original pool observation, without losing rejection or the existing history prefix. -/
theorem restorePool_append (pool : PqxdhLiveKemBirth.Pool KemSK) (history : List (DecapsulationEvent Word32))
    (index : Nat) (ciphertext : MlKem768Ciphertext) (reply : Option MlKemSharedSecret) :
    restorePool pool (history ++ [⟨index, ciphertext, reply.map rootArray⟩]) =
      PqxdhLiveKemBirth.record (.decapsulate index ciphertext) reply (restorePool pool history) := by
  cases reply <;> simp only [restorePool, observations, List.map_append, List.map_cons, List.map_nil,
    Option.map_some, Option.map_none, PqxdhPhase2InputBytes.word_rootArray,
    PqxdhLiveKemBirth.record, List.append_assoc]

/-- The ordinary native comparison evaluates primitive effects while retaining the private native attempt log. This is not the executable reduction interface. -/
noncomputable def evaluatedNative (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (secret : KemSK)
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) :=
  nativeLogged selected ((PqxdhInitializerSecrecy.kemAmbientImpl baseImpl).mapStateTBase
    (PqxdhBeaconPhase2Routed.native source kem secret challenge
      (auxiliary primitives kem selected (redact selected pool) source callbacks)))

set_option backward.isDefEq.respectTransparency false in
/-- Selected native decapsulation preserves its original key lookup and complete source history, including unsuccessful primitive replies. -/
theorem selected_source_step (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (ciphertext : Ciphertext)
    (state : AuxState A × List (DecapsulationEvent Word32)) :
    (fun result => (result.1, restore pool result.2)) <$>
      (evaluatedNative baseImpl primitives kem pool selected secret source callbacks challenge
        (.inl (.decapsulate ciphertext none))).run state =
      (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks
        (.localDecapsulation ciphertext (target, selected))).run (restore pool state) := by
  simp only [evaluatedNative, nativeLogged, nativeObserve, QueryImpl.mapStateTBase,
    PqxdhBeaconPhase2Routed.native, StateT.run, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
    StateT.lift, StateT.mk, bind_pure_comp, simulateQ_map, Functor.map_map,
    PqxdhLivePhase2Aux.direct, PqxdhLiveKemBirth.poolImpl, restore, restorePool, present]
  congr 1
  funext reply
  exact congrArg (fun pool => (reply.map rootArray, state.1.1, state.1.2, pool))
    (restorePool_append pool state.2 selected (PqxdhPhase2InputBytes.ciphertext ciphertext) reply)

set_option backward.isDefEq.respectTransparency false in
/-- Other-index decapsulation retains the complete actual indexed pool result, even for missing indices, rejected ciphertexts and equal-byte aliases. -/
theorem other_source_step (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (ciphertext : Ciphertext) (handle : OtherHandle selected)
    (state : AuxState A × List (DecapsulationEvent Word32)) :
    (fun result => (result.1, restore pool result.2)) <$>
      (evaluatedNative baseImpl primitives kem pool selected secret source callbacks challenge
        (.inl (.decapsulate ciphertext (some handle)))).run state =
      (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks
        (.localDecapsulation ciphertext handle.val)).run (restore pool state) := by
  simp only [evaluatedNative, nativeLogged, nativeObserve, QueryImpl.mapStateTBase,
    PqxdhBeaconPhase2Routed.native, PqxdhBeaconPhase2Routed.nativeAux, auxiliary,
    StateT.run, StateT.mk, bind_pure_comp, simulateQ_map, Functor.map_map]
  change (fun reply => (reply.map rootArray, restore pool
    (state.1, state.2 ++ [⟨handle.val.2, PqxdhPhase2InputBytes.ciphertext ciphertext, reply.map rootArray⟩]))) <$>
      PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge
        (otherDecapsulation kem selected (redact selected (restorePool pool state.2)) handle
          (PqxdhPhase2InputBytes.ciphertext ciphertext)) = _
  rw [other_source baseImpl kem (restorePool pool state.2) selected target secret present challenge handle]
  change _ = (fun result : Option MlKemSharedSecret × PqxdhLiveKemBirth.Pool KemSK =>
    (result.1.map rootArray, state.1.1, state.1.2, result.2)) <$>
      (PqxdhLiveKemBirth.poolImpl baseImpl kem
        (.decapsulate handle.val.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))).run (restorePool pool state.2)
  conv_rhs => rw [pool_decapsulation]
  simp only [Functor.map_map]
  congr 1
  funext result
  exact congrArg (fun pool => (result.1.map rootArray, state.1.1, state.1.2, pool))
    (restorePool_append pool state.2 handle.val.2 (PqxdhPhase2InputBytes.ciphertext ciphertext) result.1)

/-- Complete ordinary source coin programs are preserved through the blocked CCA interpreter, including all private callback effects. -/
theorem evaluated_coins {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (challenge : MlKem768Ciphertext) (work : ProbComp Result) :
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (PqxdhChallengeSecretRouting.publicImpl kem secret challenge) (ccaCoins work)) = work :=
  PqxdhDynamicKemJointRouter.post_coins baseImpl kem secret challenge work

set_option backward.isDefEq.respectTransparency false in
/-- Every original callback commutes with complete source-state restoration. No private pool observation is discarded or recorded twice. -/
theorem native_source_step (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response).Domain)
    (state : AuxState A × List (DecapsulationEvent Word32)) :
    (fun result => (result.1, restore pool result.2)) <$>
      (evaluatedNative baseImpl primitives kem pool selected secret source callbacks challenge query).run state =
      ((PqxdhLivePhase2Aux.dispatch source (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks) ∘ₛ
        PqxdhPhase2KemHandles.native (decode selected target)) query).run (restore pool state) := by
  rcases query with preparation | tail
  · cases preparation
    case decapsulate ciphertext handle =>
      cases handle with
      | none =>
        simpa only [QueryImpl.compose, PqxdhPhase2KemHandles.native, PqxdhPhase2KemHandles.preparation,
          simulateQ_spec_query, PqxdhLivePhase2Aux.dispatch, decode] using
          selected_source_step baseImpl primitives kem pool selected target secret present source callbacks challenge ciphertext state
      | some handle =>
        simpa only [QueryImpl.compose, PqxdhPhase2KemHandles.native, PqxdhPhase2KemHandles.preparation,
          simulateQ_spec_query, PqxdhLivePhase2Aux.dispatch, decode] using
          other_source_step baseImpl primitives kem pool selected target secret present source callbacks challenge ciphertext handle state
    all_goals simp only [QueryImpl.compose, PqxdhPhase2KemHandles.native, PqxdhPhase2KemHandles.preparation,
      simulateQ_spec_query, PqxdhLivePhase2Aux.dispatch, evaluatedNative, nativeLogged, nativeObserve,
      QueryImpl.mapStateTBase, PqxdhBeaconPhase2Routed.native, PqxdhBeaconPhase2Routed.nativeAux,
      auxiliary, localCca, StateT.run, StateT.mk, bind_pure_comp, evaluated_coins, Functor.map_map,
      PqxdhLivePhase2Aux.direct, PqxdhLivePhase2Aux.directLocal, restore]
    case dhIdentity identity peer => rfl
    all_goals rfl
  · rcases tail with rawQuery | tail
    · simp only [QueryImpl.compose, PqxdhPhase2KemHandles.native, simulateQ_spec_query,
        PqxdhLivePhase2Aux.dispatch, evaluatedNative, nativeLogged, nativeObserve,
        QueryImpl.mapStateTBase, PqxdhBeaconPhase2Routed.native, PqxdhBeaconPhase2Routed.nativeAux,
        auxiliary, StateT.run, StateT.mk, bind_pure_comp, evaluated_coins, Functor.map_map,
        PqxdhLivePhase2Aux.direct, restore]
    · cases tail <;> simp only [QueryImpl.compose, PqxdhPhase2KemHandles.native, simulateQ_spec_query,
        PqxdhLivePhase2Aux.dispatch, evaluatedNative, nativeLogged, nativeObserve,
        QueryImpl.mapStateTBase, PqxdhBeaconPhase2Routed.native, PqxdhBeaconPhase2Routed.nativeAux,
        auxiliary, localCca, StateT.run, StateT.mk, bind_pure_comp, evaluated_coins, Functor.map_map,
        PqxdhLivePhase2Aux.direct, PqxdhLivePhase2Aux.directLocal, restore]
      all_goals rfl

/-- The entire adaptive native continuation retains the same optional result and complete restored local, identity, KEM and observation states. -/
theorem native_source_program {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response) Result)
    (state : AuxState A × List (DecapsulationEvent Word32)) :
    (fun result => (result.1, restore pool result.2)) <$>
      (simulateQ (evaluatedNative baseImpl primitives kem pool selected secret source callbacks challenge) client).run state =
      (simulateQ (PqxdhLivePhase2Aux.dispatch source (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks) ∘ₛ
        PqxdhPhase2KemHandles.native (decode selected target)) client).run (restore pool state) := by
  exact map_run_simulateQ_eq_of_query_map_eq _ _ (restore pool)
    (native_source_step baseImpl primitives kem pool selected target secret present source callbacks challenge) client state

/-- The actual owned native Phase2 execution is recovered with every original owner and source-state field, including the existing private KEM transcript. -/
theorem native_source_owner (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D Handle) (valid : PqxdhLiveKemOwnership.Owner pool owner)
    (state : AuxState A × List (DecapsulationEvent Word32)) :
    (fun result => ((result.1.1, PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2),
      restore pool result.2)) <$>
      (simulateQ (evaluatedNative baseImpl primitives kem pool selected secret source callbacks challenge)
        (PqxdhBeaconPhase2Publication.nativeOwner read raw
          (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner))).run state =
      (simulateQ (PqxdhLivePhase2Aux.dispatch source (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks))
        (PqxdhBeaconPhase2Publication.nativeOwner read raw owner)).run (restore pool state) := by
  rw [← native_encoded_run (PqxdhLivePhase2Aux.dispatch source
    (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks)) pool selected target secret present read raw owner valid]
  rw [← native_source_program baseImpl primitives kem pool selected target secret present source callbacks challenge]
  simp only [Functor.map_map]

/-- Mathematical primitive evaluation commutes with native attempt instrumentation, retaining the actual ordered optional replies. -/
theorem nativeLogged_interpret {κ ξ : Type} {spec : OracleSpec κ} {base : OracleSpec ξ}
    (interpreter : QueryImpl spec (OracleComp base)) (selected : Nat)
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Identity D (Option (OtherHandle selected)) Converted Response)
      (StateT A (OracleComp spec))) :
    interpreter.mapStateTBase (nativeLogged selected handler) = nativeLogged selected (interpreter.mapStateTBase handler) := by
  funext query state
  simp only [QueryImpl.mapStateTBase, nativeLogged, StateT.run, simulateQ_bind, simulateQ_pure]
  rfl

/-- Source comparison materializes only private marker observations, restoring the complete original key pool and joint/local state. -/
def restorePrivate (pool : PqxdhLiveKemBirth.Pool KemSK) (supplied : MlKemSharedSecret)
    (state : AuxState A × List (DecapsulationEvent Shared)) : SharedState A × PqxdhLiveKemBirth.State KemSK :=
  restore pool (state.1, state.2.map
    (mapEvent (fun shared => rootArray (PqxdhPhase2DecapsulationRouting.materialize supplied shared))))

/-- Actual original native Phase2, with its indexed private pool and complete observation history, equals the concrete opaque challenge-root execution. The actual callback order, rejected attempts, root input and full owner publication are retained. -/
theorem privateOwner_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D Handle) (valid : PqxdhLiveKemOwnership.Owner pool owner)
    (state : AuxState A) :
    (fun result => ((result.1.1, PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2),
      restorePrivate pool supplied result.2)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (PqxdhChallengeSecretRouting.actualImpl source kem secret challenge)
          (privateOwner primitives kem selected (redact selected pool) source callbacks challenge read raw
            (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner) (state, []))) =
      (simulateQ (PqxdhLivePhase2Aux.dispatch source (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks))
        (PqxdhBeaconPhase2Publication.nativeOwner read raw owner)).run (state.1, (state.2, pool)) := by
  have realized := congrArg (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl))
    (privateOwner_actual primitives kem selected (redact selected pool) source callbacks secret challenge supplied agreement
      read raw (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner) (state, []))
  rw [simulateQ_map, QueryImpl.simulateQ_mapStateTBase_run, nativeLogged_interpret] at realized
  have restored := native_source_owner baseImpl primitives kem pool selected target secret present source callbacks challenge
    read raw owner valid (state, [])
  simp only [List.map_nil] at realized
  simp only [evaluatedNative] at restored
  rw [realized] at restored
  simpa only [Functor.map_map, restorePrivate, restore, restorePool, observations, List.map_nil,
    List.append_nil] using restored

/-- The original native owner under the actual indexed identity/KEM service interpreter is recovered, including every private pool observation and all later callback state. -/
theorem privateOwner_live (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D Handle) (valid : PqxdhLiveKemOwnership.Owner pool owner)
    (state : AuxState A) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((simulateQ (PqxdhLivePhase2Aux.dispatch source (PqxdhLivePhase2Aux.aux source callbacks))
        (PqxdhBeaconPhase2Publication.nativeOwner read raw owner)).run state.1)).run (state.2, pool) =
    (fun result => (((result.1.1, PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2),
      (restorePrivate pool supplied result.2).1), (restorePrivate pool supplied result.2).2)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (PqxdhChallengeSecretRouting.actualImpl source kem secret challenge)
          (privateOwner primitives kem selected (redact selected pool) source callbacks challenge read raw
            (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner) (state, []))) := by
  rw [PqxdhLivePhase2Aux.owner_source, ← privateOwner_source baseImpl primitives kem pool selected target secret
    present source callbacks challenge supplied agreement read raw owner valid state]
  simp only [Functor.map_map]

/-- The real-source comparison consumes ordinary functional recipient correctness on actual generated/encapsulated support; its challenge agreement is not an extra protocol assumption. -/
theorem privateOwner_supported (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (generated : (target, secret) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (encapsulated : (challenge, supplied) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps target)))
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D Handle) (valid : PqxdhLiveKemOwnership.Owner pool owner)
    (state : AuxState A) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((simulateQ (PqxdhLivePhase2Aux.dispatch source (PqxdhLivePhase2Aux.aux source callbacks))
        (PqxdhBeaconPhase2Publication.nativeOwner read raw owner)).run state.1)).run (state.2, pool) =
    (fun result => (((result.1.1, PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2),
      (restorePrivate pool supplied result.2).1), (restorePrivate pool supplied result.2).2)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (PqxdhChallengeSecretRouting.actualImpl source kem secret challenge)
          (privateOwner primitives kem selected (redact selected pool) source callbacks challenge read raw
            (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner) (state, []))) :=
  privateOwner_live baseImpl primitives kem pool selected target secret present source callbacks challenge supplied
    (PqxdhChallengeSecretRouting.honest_decapsulation_program baseImpl kem functional correct generated encapsulated)
    read raw owner valid state

end BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.decode_encode' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.decode_encode
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.owner_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.owner_inverse
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_encoded_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_encoded_run
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_pre
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_post_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_post_pre
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_queries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.auxiliary_no_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.auxiliary_no_selected
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.observations_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.observations_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.observe_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.observe_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_decapsulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_decapsulation
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_full_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_full_calls
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.owner_logged_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.owner_logged_realization
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_program_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.logged_program_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_actual
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.pool_decapsulation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.pool_decapsulation
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.restorePool_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.restorePool_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.selected_source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.selected_source_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.other_source_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.evaluated_coins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.evaluated_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_source_step
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_source_program
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_source_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.native_source_owner
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.nativeLogged_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.nativeLogged_interpret
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_live
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot.privateOwner_supported

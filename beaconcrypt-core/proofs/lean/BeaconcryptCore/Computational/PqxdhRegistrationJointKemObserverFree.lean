import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawOpaque
import BeaconcryptCore.Computational.PqxdhRegistrationR1Audit

/-!
# The observer-free opaque KEM-ideal branch (item 2, stage S0a)

This module removes every write-only analysis observer from the post-challenge phase of the opaque raw-ordinal branch `PqxdhRegistrationJointKemRawOpaque.opaqueBranch` (theorem T6), by program equalities that charge no advantage. The observers are:

- the restricted Extract-family history and the native ghost (session and adversary table touches, seal contexts, acceptance snapshot), both erased by `PqxdhServerAuthNative.eraseObservers`;
- the whole KEM pool/router transcript (`PqxdhDynamicKemRouter.State.history`, queries and replies), including the prefix's stopped-router history carried into the post-challenge phase;
- the whole identity-pool transcript (`PqxdhDynamicIdentityPool.SourceState.transcript`), which contains the identity-routing and signing requests and replies.

Each observer is written but never read. `eraseImpl` and `eraseOptionImpl` turn a stateful handler into the handler that erases the observers of its input state and of every poststate; `run_erase` and `run_eraseOption` show that, for a handler that never reads its observers (`NeverRead`, `NeverReadOption`), the erased run is exactly the projection of the original run. The never-read facts are proved for every handler of the post-challenge phase: the native command backend of the actual source (Server accept, Server build, public HMAC, BLAKE2b, kernel reveal, the Beacon tail and the open pool requests), the private interpreter of the opaque resumption (the Server's root, consumption and bookkeeping), the dynamic KEM router and the identity pool.

The main theorem `opaqueBranch_free` states that `opaqueBranch` equals `freeBranch`, the same game in which every post-challenge handler is erased: the same key generation, prefix, challenger encapsulation, uniform draw, stopped router, CCA evaluation, stop status and decision. The decision reads only the stop status and the source's Boolean result (`decision_erase`), so the equality holds as programs of type `ProbComp Bool`. In `freeBranch` no observer holds any value, in particular none of the KEM candidate; the router's reply to a decapsulation of the challenge ciphertext under the selected key is no longer recorded anywhere, which is what stage S0b needs to remove that router request by an equality.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree

/-! ### Erasing write-only observers of a stateful handler -/

section Generic

variable {ι : Type} {spec : OracleSpec ι} {σ : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The handler that erases the observers of its input state and of every poststate. -/
def eraseImpl (erase : σ → σ) (impl : QueryImpl spec (StateT σ m)) : QueryImpl spec (StateT σ m) :=
  fun query => StateT.mk fun state => Prod.map id erase <$> (impl query).run (erase state)

/-- A handler never reads the observers removed by `erase`: after erasure, its step from a state and from the erased state agree. -/
def NeverRead (erase : σ → σ) (impl : QueryImpl spec (StateT σ m)) : Prop :=
  ∀ query state, Prod.map id erase <$> (impl query).run state =
    Prod.map id erase <$> (impl query).run (erase state)

/-- The erased run of a handler that never reads its observers is the projection of its original run. -/
theorem run_erase (erase : σ → σ) (idem : ∀ state, erase (erase state) = erase state)
    (impl : QueryImpl spec (StateT σ m)) (never : NeverRead erase impl) {α : Type}
    (oa : OracleComp spec α) (state : σ) :
    Prod.map id erase <$> (simulateQ impl oa).run state =
      (simulateQ (eraseImpl erase impl) oa).run (erase state) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq impl (eraseImpl erase impl) erase
    (fun query state => by
      change _ = Prod.map id erase <$> (impl query).run (erase (erase state))
      rw [idem]
      exact never query state) oa state

/-- The erasing handler of an optional stateful handler. -/
def eraseOptionImpl (erase : σ → σ) (impl : QueryImpl spec (OptionT (StateT σ m))) :
    QueryImpl spec (OptionT (StateT σ m)) :=
  fun query => OptionT.mk (StateT.mk fun state => Prod.map id erase <$> ((impl query).run).run (erase state))

/-- An optional stateful handler never reads the observers removed by `erase`. -/
def NeverReadOption (erase : σ → σ) (impl : QueryImpl spec (OptionT (StateT σ m))) : Prop :=
  ∀ query state, Prod.map id erase <$> ((impl query).run).run state =
    Prod.map id erase <$> ((impl query).run).run (erase state)

/-- The erased run of an optional handler that never reads its observers is the projection of its original run, including the stop status. -/
theorem run_eraseOption (erase : σ → σ) (idem : ∀ state, erase (erase state) = erase state)
    (impl : QueryImpl spec (OptionT (StateT σ m))) (never : NeverReadOption erase impl) {α : Type}
    (oa : OracleComp spec α) (state : σ) :
    Prod.map id erase <$> ((simulateQ impl oa).run).run state =
      ((simulateQ (eraseOptionImpl erase impl) oa).run).run (erase state) := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        map_bind]
      let rest : Option (spec.Range query) × σ → m (Option α × σ) := fun result =>
        (result.1.elim (pure none) fun value => (simulateQ (eraseOptionImpl erase impl) (next value)).run).run
          result.2
      have left : ∀ result : Option (spec.Range query) × σ,
          Prod.map id erase <$> (result.1.elim (pure none) fun value =>
            (simulateQ impl (next value)).run).run result.2 = rest (Prod.map id erase result) := by
        rintro ⟨_ | value, after⟩
        · simp [rest]
        · simpa [rest] using ih value after
      have right : ((eraseOptionImpl erase impl query).run).run (erase state) =
          Prod.map id erase <$> ((impl query).run).run state := by
        change Prod.map id erase <$> ((impl query).run).run (erase (erase state)) = _
        rw [idem]
        exact (never query state).symm
      rw [right, bind_map_left]
      exact bind_congr left

end Generic

/-! ### The KEM router and identity-pool transcripts -/

section Router

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- Erase the KEM pool/router transcript (queries and replies). -/
def eraseRouter (state : PqxdhDynamicKemRouter.State KemSK) : PqxdhDynamicKemRouter.State KemSK :=
  { state with history := [] }

/-- Erase the identity-pool transcript (identity-routing and signing requests and replies). -/
def eraseIdentity (state : PqxdhDynamicIdentityPool.SourceState) : PqxdhDynamicIdentityPool.SourceState :=
  { state with transcript := [] }

/-- Erase both transcripts of the joint identity/KEM source state. -/
def eraseJoint (state : PqxdhDynamicKemJointSource.State KemSK) : PqxdhDynamicKemJointSource.State KemSK :=
  (eraseIdentity state.1, eraseRouter state.2)

@[simp]
theorem eraseRouter_idem (state : PqxdhDynamicKemRouter.State KemSK) :
    eraseRouter (eraseRouter state) = eraseRouter state := rfl

@[simp]
theorem eraseIdentity_idem (state : PqxdhDynamicIdentityPool.SourceState) :
    eraseIdentity (eraseIdentity state) = eraseIdentity state := rfl

theorem eraseJoint_idem (state : PqxdhDynamicKemJointSource.State KemSK) :
    eraseJoint (eraseJoint state) = eraseJoint state := rfl

theorem lookup_erase (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (state : PqxdhDynamicKemRouter.State KemSK) :
    PqxdhDynamicKemRouter.lookup reservation (eraseRouter state) = PqxdhDynamicKemRouter.lookup reservation state :=
  rfl

/-- The dynamic KEM router never reads its transcript, for every decapsulation callback. -/
theorem router_neverRead
    (decapsulation : PqxdhDynamicKemRouter.Reservation KemSK → Nat → PqxdhKemIndCca.MlKem768Ciphertext →
      OracleComp (PqxdhKemIndCca.MlKemCCAOracleSpec baseSpec) (Option PqxdhKemIndCca.MlKemSharedSecret))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK) :
    NeverReadOption eraseRouter (PqxdhDynamicKemRouter.router decapsulation selected reservation) := by
  intro query state
  rcases query with _ | ⟨index, ciphertext⟩ | index
  · simp only [PqxdhDynamicKemRouter.router, OptionT.run_mk, StateT.run]
    cases reserved : reservation state.created <;>
      simp [eraseRouter, PqxdhDynamicKemRouter.record, reserved]
  · simp only [PqxdhDynamicKemRouter.router, OptionT.run_mk, StateT.run, lookup_erase]
    simp [eraseRouter, PqxdhDynamicKemRouter.record, Functor.map_map]
  · simp only [PqxdhDynamicKemRouter.router, OptionT.run_mk, StateT.run, lookup_erase]
    cases found : PqxdhDynamicKemRouter.lookup reservation state index with
    | none => simp [eraseRouter, PqxdhDynamicKemRouter.record]
    | some pair =>
        by_cases same : index = selected <;> simp [same, eraseRouter, PqxdhDynamicKemRouter.record]

/-- The lazy identity pool never reads its transcript. -/
theorem identity_neverRead (primitives : PqxdhJointIdentity.Primitives) :
    NeverRead eraseIdentity (PqxdhDynamicIdentityPool.lazyImpl primitives) := by
  intro query state
  rcases query with coin | (_ | ⟨identity, request⟩ | identity)
  all_goals simp [PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
    eraseIdentity, PqxdhDynamicIdentityPool.record, StateT.run, Prod.map, Functor.map_map]

/-- The post-challenge joint router never reads either transcript. -/
theorem post_neverRead (primitives : PqxdhJointIdentity.Primitives)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (reservation : PqxdhDynamicKemRouter.Reservation KemSK) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    NeverReadOption eraseJoint
      (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge candidate) := by
  intro query state
  rcases query with joint | (coin | pool)
  · have identity := congrArg (fun work => (fun result => (some result.1, (result.2, eraseRouter state.2))) <$>
      PqxdhPrivateKemSource.ccaCoins (baseSpec := baseSpec) work) (identity_neverRead primitives joint state.1)
    simp only [PqxdhPrivateKemSource.ccaCoins, simulateQ_map, Functor.map_map] at identity
    simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run,
      PqxdhPrivateKemSource.ccaCoins, Functor.map_map]
    exact identity
  · simp [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, eraseJoint, StateT.run,
      Functor.map_map]
  · have routed := congrArg (fun work => (fun result => (result.1, (eraseIdentity state.1, result.2))) <$> work)
      (router_neverRead (PqxdhDynamicKemRouter.postDecapsulation kem selected challenge candidate) selected
        reservation pool state.2)
    simp only [Functor.map_map] at routed
    simp only [PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine, PqxdhDynamicKemRouter.post,
      OptionT.run_mk, StateT.run, Functor.map_map]
    exact routed

end Router

/-! ### The native analysis observers -/

section Native

open PqxdhServerAuthExperiment PqxdhServerAuthNative

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A native computation never reads the family history or the ghost. -/
def Oblivious {α : Type} (work : NativeGame KemSK α) : Prop :=
  ∀ state, Prod.map id eraseObservers <$> work.run state =
    Prod.map id eraseObservers <$> work.run (eraseObservers state)

@[simp]
theorem eraseObservers_idem (state : NativeState KemSK) :
    eraseObservers (eraseObservers state) = eraseObservers state := rfl

theorem oblivious_pure {α : Type} (value : α) : Oblivious (pure value : NativeGame KemSK α) := by
  intro state
  simp

theorem oblivious_bind {α β : Type} {work : NativeGame KemSK α} {next : α → NativeGame KemSK β}
    (first : Oblivious work) (rest : ∀ value, Oblivious (next value)) : Oblivious (work >>= next) := by
  intro state
  have key : ∀ start : NativeState KemSK,
      (work.run start >>= fun result => Prod.map id eraseObservers <$> (next result.1).run result.2) =
        (Prod.map id eraseObservers <$> work.run start) >>= fun result =>
          Prod.map id eraseObservers <$> (next result.1).run result.2 := by
    intro start
    rw [bind_map_left]
    exact bind_congr fun result => rest result.1 result.2
  simp only [StateT.run_bind, map_bind]
  rw [key state, key (eraseObservers state), first state]

theorem oblivious_coins {α : Type} (work : ProbComp α) : Oblivious (nativeCoins (KemSK := KemSK) work) := by
  intro state
  simp [nativeCoins, StateT.run, Functor.map_map]

theorem oblivious_touch (touch : Touch) : Oblivious (nativeTouch (KemSK := KemSK) touch) := by
  intro state
  simp only [nativeTouch, localState, StateT.run, map_pure]
  rfl

theorem oblivious_consume (rid : beaconcrypt_core.pqxdh.RegistrationId) :
    Oblivious (nativeConsume (KemSK := KemSK) rid) := by
  intro state
  simp only [nativeConsume, localState, StateT.run, map_pure]
  rfl

theorem oblivious_set (value : GameState KemSK) : Oblivious (nativeSet value) := by
  intro state
  simp only [nativeSet, localState, StateT.run, map_pure]
  rfl

theorem oblivious_publish (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned) :
    Oblivious (nativeModify (KemSK := KemSK) fun current =>
      { current with pending := Function.update current.pending index (some token) }) := by
  intro state
  simp only [nativeModify, localState, StateT.run, map_pure]
  rfl

theorem oblivious_reveal (keyId : Std.U64) :
    Oblivious (localState (KemSK := KemSK) fun state => (revealKernel keyId state, state)) := by
  intro state
  simp only [localState, StateT.run, map_pure]
  rfl

theorem oblivious_romRootBytes (hmac : PqxdhSecretInputKdf.HmacSha512)
    (message : PqxdhJointDhExtractFamily.Message) (bytes : Pqxdh.Bytes) :
    Oblivious (romRootBytes (A := GameState KemSK) hmac message bytes) := by
  intro state
  simp only [romRootBytes, StateT.run, Functor.map_map]
  rfl

theorem oblivious_sourceRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    Oblivious (sourceRoot (KemSK := KemSK) hmac input) := by
  intro state
  simp only [sourceRoot, StateT.run, Functor.map_map]
  rfl

theorem oblivious_ctx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    Oblivious (nativeCtx (KemSK := KemSK) work) := by
  intro state
  change Prod.map id eraseObservers <$> nativeCtx work state =
    Prod.map id eraseObservers <$> nativeCtx work (eraseObservers state)
  rw [ctx_observation, ctx_observation]
  rfl

theorem oblivious_hash (bytes : Pqxdh.Bytes) : Oblivious (nativeHash (KemSK := KemSK) bytes) := by
  intro state
  simp only [nativeHash, StateT.run, Functor.map_map]
  rfl

theorem oblivious_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) : Oblivious (nativeBuild setup codec checks session payload) :=
  fun state => PqxdhRegistrationR1Audit.build_audit setup codec checks session payload state

theorem oblivious_hmac (setup : Setup baseSpec KemSK) (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    Oblivious (PqxdhRegistrationJointPublicShared.hmac setup key message) := by
  intro state
  rw [PqxdhRegistrationJointPublicShared.hmac_source setup (List.Vector.replicate 32 0) (List.Vector.replicate 32 0)]
  exact PqxdhRegistrationR1Audit.hmac_audit setup _ _ key message state

theorem oblivious_tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) :
    Oblivious (sourceBeaconTail setup codec query) := by
  rcases query with query | (input | request | response)
  · exact oblivious_ctx _
  · exact oblivious_sourceRoot _ _
  · exact oblivious_ctx _
  · exact oblivious_ctx _

theorem oblivious_loggedRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32)
    (original : beaconcrypt_core.pqxdh.PendingServerRegistration) :
    Oblivious (loggedRoot (KemSK := KemSK) hmac index input original) :=
  oblivious_bind (oblivious_romRootBytes _ _ _) fun _ =>
    oblivious_bind (oblivious_touch _) fun _ => oblivious_pure _

theorem oblivious_client (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    Oblivious (nativeClient (KemSK := KemSK) hmac index control binding input) := by
  unfold nativeClient
  split
  · exact oblivious_pure _
  · exact oblivious_pure _
  · exact oblivious_pure _
  · exact oblivious_bind (oblivious_loggedRoot _ _ _ _) fun _ =>
      oblivious_bind (oblivious_consume _) fun _ => oblivious_pure _

/-- The Server accept tail reads its snapshot of the game state only through fields other than the ghost. -/
theorem tail_oblivious (setup : Setup baseSpec KemSK) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) (state : NativeState KemSK) :
    Prod.map id eraseObservers <$>
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected).run state =
      Prod.map id eraseObservers <$>
        (PqxdhRegistrationJointServerAccept.tail setup publicIdentity { before with ghost := Ghost.empty }
          collected).run (eraseObservers state) := by
  rcases collected with ⟨_ | input, consumed⟩
  · simp only [PqxdhRegistrationJointServerAccept.tail, nativeSet, StateT.run]
    rfl
  · have rest : Oblivious (do
        let returned ← nativeClient (KemSK := KemSK) setup.hmac before.sessions before.server.control
          ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ input
        match returned with
        | .ok (some token) => do
            nativeModify fun current => { current with pending := Function.update current.pending before.sessions (some token) }
            pure (some before.sessions)
        | _ => pure none) :=
      oblivious_bind (oblivious_client _ _ _ _ _) fun returned => by
        split
        · exact oblivious_bind (oblivious_publish _ _) fun _ => oblivious_pure _
        · exact oblivious_pure _
    simp only [PqxdhRegistrationJointServerAccept.tail, nativeSet, StateT.run]
    exact rest _

end Native

/-! ### The native handlers of the post-challenge phase -/

section Handlers

open PqxdhServerAuthExperiment PqxdhServerAuthNative

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

theorem lift_native_erase {α : Type} (work : NativeGame KemSK α) (state : NativeState KemSK) :
    Prod.map id eraseObservers <$> (PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK)
        (PqxdhRegistrationJointOpenBackend.native (KemSK := KemSK) work)).run state =
      simulateQ (PqxdhRegistrationJointKemEncapsulation.forward (KemSK := KemSK))
        (PqxdhLiveKemBirth.coins (KemSK := KemSK) (Prod.map id eraseObservers <$> work.run state)) := by
  simp only [PqxdhRegistrationJointKemEncapsulation.lift, PqxdhRegistrationJointOpenBackend.native,
    PqxdhLiveKemBirth.coins, simulateQ_map, StateT.run]

theorem lift_native_neverRead {α : Type} {work : NativeGame KemSK α} (obl : Oblivious work)
    (state : NativeState KemSK) :
    Prod.map id eraseObservers <$> (PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK)
        (PqxdhRegistrationJointOpenBackend.native (KemSK := KemSK) work)).run state =
      Prod.map id eraseObservers <$> (PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK)
        (PqxdhRegistrationJointOpenBackend.native (KemSK := KemSK) work)).run (eraseObservers state) := by
  rw [lift_native_erase, lift_native_erase, obl state]

/-- The Server's raw accept with its encapsulation exposed never reads the analysis observers. -/
theorem accept_neverRead (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (raw : Pqxdh.Bytes)
    (state : NativeState KemSK) :
    Prod.map id eraseObservers <$>
        (PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run state =
      Prod.map id eraseObservers <$>
        (PqxdhRegistrationJointKemEncapsulation.accept setup codec checks identityIndex publicIdentity raw).run
          (eraseObservers state) := by
  have getStep : ∀ start : NativeState KemSK,
      (PqxdhRegistrationJointKemEncapsulation.lift (KemSK := KemSK)
        (PqxdhRegistrationJointOpenBackend.native (KemSK := KemSK) nativeGet)).run start = pure (start.2, start) := by
    intro start
    simp [PqxdhRegistrationJointKemEncapsulation.lift, PqxdhRegistrationJointOpenBackend.native, nativeGet,
      localState, PqxdhLiveKemBirth.coins, StateT.run]
  have prepareStep : ∀ start : NativeState KemSK,
      (PqxdhRegistrationJointKemEncapsulation.prepare setup codec checks identityIndex raw).run start =
        (fun result => (result, start)) <$>
          (simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
            (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run start.2.server.consumed :=
    fun _ => rfl
  unfold PqxdhRegistrationJointKemEncapsulation.accept
  simp only [StateT.run_bind, getStep, pure_bind, prepareStep, bind_map_left, map_bind]
  refine bind_congr fun collected => ?_
  rw [lift_native_erase, lift_native_erase, tail_oblivious]
  rfl

/-- The native command backend of the actual source, with only the raw-accept encapsulation exposed, never reads the analysis observers. -/
theorem impl_neverRead (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity) :
    NeverRead eraseObservers
      (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity) := by
  intro query state
  rcases query with (service | tail) | shared
  · simp [PqxdhRegistrationJointKemEncapsulation.impl, PqxdhRegistrationJointOpenBackend.impl,
      PqxdhRegistrationJointOpenBackend.pool, PqxdhRegistrationJointKemEncapsulation.lift, StateT.run,
      Functor.map_map]
  · exact lift_native_neverRead (oblivious_tail setup codec tail) state
  · cases shared with
    | accept raw => exact accept_neverRead setup codec checks identityIndex publicIdentity raw state
    | build session payload => exact lift_native_neverRead (oblivious_build setup codec checks session payload) state
    | hmac key message => exact lift_native_neverRead (oblivious_hmac setup key message) state
    | hash bytes => exact lift_native_neverRead (oblivious_hash bytes) state
    | reveal keyId => exact lift_native_neverRead (oblivious_reveal keyId) state

/-- The private native tail of the opaque resumption (root, consumption and bookkeeping) never reads the analysis observers. -/
theorem oblivious_opaqueTail (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) :
    Oblivious (PqxdhRegistrationJointKemOpaqueTail.impl hmac index candidate query) := by
  rcases query with (input | aux) | mutation
  · exact oblivious_bind (oblivious_romRootBytes _ _ _) fun _ =>
      oblivious_bind (oblivious_touch _) fun _ => oblivious_pure _
  · cases aux with
    | eraseShared => exact oblivious_pure _
    | eraseInput => exact oblivious_pure _
    | consume rid => exact oblivious_consume rid
  · cases mutation with
    | install value => exact oblivious_set value
    | publish slot token => exact oblivious_publish slot token

/-- The private interpreter of the opaque resumption never reads the analysis observers. -/
theorem resume_neverRead (setup : Setup baseSpec KemSK) (index : Nat) (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    NeverRead eraseObservers (PqxdhRegistrationJointKemOpaqueResume.liftImpl (Reader := Reader)
      PqxdhRegistrationJointKemOpaqueResume.clientNative setup index candidate
      PqxdhRegistrationJointKemOpaqueResume.forwardClient) := by
  intro query state
  rcases query with prefixQuery | tailQuery
  · simp [PqxdhRegistrationJointKemOpaqueResume.liftImpl, PqxdhRegistrationJointKemOpaqueResume.forwardClient,
      StateT.run, Functor.map_map]
  · exact lift_native_neverRead (oblivious_opaqueTail setup.hmac index candidate tailQuery) state

end Handlers

/-! ### The observer-free post-challenge phase and branch -/

section Assembly

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState eraseObservers)
open PqxdhRegistrationJointKemEncapsulation (actual commands)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointKemResume (ResultState)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (tagged hide)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemOpaqueResume (liftImpl clientNative forwardClient)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext toContext sourcePreOpaque opaqueResume opaquePost opaqueBranch)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- Erase the native analysis observers of a source outcome. -/
def eraseOutcome : Outcome KemSK R → Outcome KemSK R :=
  Prod.map id eraseObservers

/-- The observer-free opaque resumption: the opaque resumption of `KemRawOpaque.opaqueResume` and the rest of the tagged client, with both native interpreters erased. -/
noncomputable def freeResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK R) := do
  let answer ← (simulateQ (eraseImpl eraseObservers (liftImpl clientNative setup native.2.sessions candidate forwardClient))
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge native.2 consumed)).run (eraseObservers native)
  hide setup ((simulateQ (eraseImpl eraseObservers
      (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity))
    ((simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec)
      (tagged observe raw next answer.1)).run owners)).run answer.2)

/-- The opaque resumption with its native observers erased is the observer-free resumption. -/
theorem resume_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (native : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X)
    (ciphertext : MlKem768Ciphertext) (candidate : MlKemSharedSecret) :
    eraseOutcome <$> opaqueResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed
        native owners next ciphertext candidate =
      freeResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed native owners
        next ciphertext candidate := by
  have commandsFree : ∀ answer : Option Nat × NativeState KemSK,
      eraseOutcome <$> hide setup (commands setup codec checks identityIndex publicIdentity
        (tagged observe raw next answer.1) owners answer.2) =
      hide setup ((simulateQ (eraseImpl eraseObservers
          (PqxdhRegistrationJointKemEncapsulation.impl setup codec checks identityIndex publicIdentity))
        ((simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec)
          (tagged observe raw next answer.1)).run owners)).run (eraseObservers answer.2)) := by
    intro answer
    simp only [hide, eraseOutcome, ← simulateQ_map, commands]
    rw [run_erase eraseObservers eraseObservers_idem _ (impl_neverRead setup codec checks identityIndex publicIdentity)]
  simp only [opaqueResume, freeResume, map_bind, commandsFree]
  rw [← run_erase eraseObservers eraseObservers_idem _ (resume_neverRead setup native.2.sessions candidate),
    bind_map_left]
  rfl

/-- Erase both transcripts of the router state and the native observers of the outcome of a result. -/
def eraseResult {count : Nat} (result : ResultState KemSK A Bool count) : ResultState KemSK A Bool count :=
  (result.1, result.2.map (Prod.map (Option.map eraseOutcome) eraseJoint))

/-- The decision reads only the stop status and the source's Boolean result, so it ignores every erased observer. -/
theorem decision_erase {count : Nat} (result : ResultState KemSK A Bool count) :
    PqxdhRegistrationJointKemGame.decision (eraseResult result) = PqxdhRegistrationJointKemGame.decision result := by
  rcases result with ⟨context, _ | ⟨_ | outcome, state⟩⟩ <;> rfl

/-- One erased post-challenge router layer: the projection of the router run, with the outcome erased by `f`, is the erased router's run on the erased state. -/
theorem router_layer {α β : Type}
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))))
    (never : NeverReadOption eraseJoint router) (f : α → β) (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    Prod.map (Option.map f) eraseJoint <$> ((simulateQ router work).run).run state =
      ((simulateQ (eraseOptionImpl eraseJoint router) (f <$> work)).run).run (eraseJoint state) := by
  rw [← run_eraseOption eraseJoint eraseJoint_idem router never (f <$> work) state]
  simp only [simulateQ_map, OptionT.run_map, StateT.run_map, Functor.map_map]
  rfl

/-- The observer-free postchallenge step: `KemRawOpaque.opaquePost` with the erased joint router and the observer-free resumption, started from the erased router state. -/
noncomputable def freePost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (ResultState KemSK A Bool count) := do
  match transcript.context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners next)) state _ =>
    if value.keys.pqKey = transcript.publicKey then
      let reached ← (((simulateQ (eraseOptionImpl eraseJoint
          (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected transcript.publicKey others)
            transcript.ciphertext candidate))
        (simulateQ (actual setup) (freeResume setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (decideTag decision) raw value ephemeral consumed native owners next
          transcript.ciphertext candidate))).run).run (eraseJoint state))
      pure (toContext setup codec checks decision transcript.context, some reached)
    else pure (toContext setup codec checks decision transcript.context, none)
  | _ => pure (toContext setup codec checks decision transcript.context, none)

/-- The opaque postchallenge step with every observer erased is the observer-free postchallenge step. -/
theorem post_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1))
    (transcript : MlKemChallengeTranscript (OpaqueContext Reader KemSK A X count)) (candidate : MlKemSharedSecret) :
    eraseResult <$> opaquePost setup codec checks decision count selected transcript candidate =
      freePost setup codec checks decision count selected transcript candidate := by
  obtain ⟨publicKey, ciphertext, context⟩ := transcript
  cases context with
  | failed state => simp [opaquePost, freePost, eraseResult]
  | ready created others cut state runtime =>
    cases cut with
    | none => simp [opaquePost, freePost, eraseResult]
    | some cut =>
      cases cut with
      | complete outcome => simp [opaquePost, freePost, eraseResult]
      | pending raw value ephemeral consumed native owners next =>
        by_cases active : value.keys.pqKey = publicKey
        · simp only [opaquePost, freePost, active, ↓reduceIte, map_bind, map_pure]
          rw [← resume_free, simulateQ_map,
            ← router_layer _ (post_neverRead setup.joint setup.kem selected.val _ ciphertext candidate),
            bind_map_left]
          rfl
        · simp [opaquePost, freePost, active, eraseResult]

set_option backward.isDefEq.respectTransparency false in
/-- CCA evaluation commutes with a pure map of the result. -/
theorem evaluate_map {α β : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (f : α → β) (client : OracleComp (MlKemCCAOracleSpec baseSpec) α) :
    PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge (f <$> client) =
      f <$> PqxdhDynamicKemPost.evaluate baseImpl kem secret challenge client := by
  unfold PqxdhDynamicKemPost.evaluate
  rw [simulateQ_map, simulateQ_map]

/-- The observer-free opaque branch: `KemRawOpaque.opaqueBranch` with the observer-free postchallenge step. The key generation, prefix, challenger encapsulation, uniform draw, CCA evaluation and decision are unchanged. -/
noncomputable def freeBranch (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) : ProbComp Bool := do
  let chosen ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let context ← sourcePreOpaque (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count
    selected index chosen
  let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1)
  let uniform ← $ᵗ MlKemSharedSecret
  PqxdhRegistrationJointKemGame.decision <$> PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2
    encapsulated.1 (freePost setup codec checks decision count selected ⟨chosen.1, encapsulated.1, context⟩
      (if real then encapsulated.2 else uniform))

/-- Stage S0a. The opaque raw-ordinal branch (theorem T6) equals the observer-free branch, as programs and for both values of the branch bit: the family history, the native ghost, the KEM pool/router transcript and the identity-pool transcript of the post-challenge phase are written but never read, and the decision reads only the stop status and the source's Boolean result. This charges no advantage. -/
theorem opaqueBranch_free (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (runtime : A)
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (real : Bool) :
    opaqueBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real =
      freeBranch (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        real := by
  unfold opaqueBranch freeBranch
  refine bind_congr fun chosen => bind_congr fun context => bind_congr fun encapsulated =>
    bind_congr fun uniform => ?_
  rw [← post_free, evaluate_map, Functor.map_map]
  congr 1
  funext result
  exact (decision_erase result).symm

end Assembly

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.run_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.run_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.run_eraseOption' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.run_eraseOption

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseRouter_idem' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseRouter_idem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseIdentity_idem' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseIdentity_idem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseJoint_idem' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseJoint_idem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.lookup_erase' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.lookup_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.router_neverRead' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.router_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.identity_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.identity_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.post_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.post_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseObservers_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.eraseObservers_idem

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_touch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_touch

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_consume

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_set

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_publish

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_reveal

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_romRootBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_romRootBytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_sourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_sourceRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_ctx

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_build

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_hmac

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_loggedRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_loggedRoot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.tail_oblivious' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.tail_oblivious

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.lift_native_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.lift_native_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.lift_native_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.lift_native_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.accept_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.accept_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.impl_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.impl_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_opaqueTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.oblivious_opaqueTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.resume_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.resume_neverRead

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.resume_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.resume_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.decision_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.decision_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.router_layer' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.router_layer

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.post_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.post_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.evaluate_map' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.evaluate_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.opaqueBranch_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemObserverFree.opaqueBranch_free

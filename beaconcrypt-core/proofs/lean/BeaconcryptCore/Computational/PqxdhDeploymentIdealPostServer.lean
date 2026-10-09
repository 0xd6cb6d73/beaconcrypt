-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostRequests

/-!
# Item 2's per-request steps against the middle execution: the real Server requests (CE-11b, unit U6, third part)

This module proves `PqxdhDeploymentIdealPostSteps.StepAt` for the two real Server requests with native work: a raw accept other than the selected one, and a build that is not the marked session's build with a pending token. On item 2's side both run the skeleton's native layer at the factored value type (`PqxdhRegistrationJointKemEntryFactor.factoredServices`), whose table reads item 2's table layers answer from the public table cache; on the middle side they run item 2's annotated source on the full native state.

- `SplitT`: a native program and a skeleton program at the factored value type split when, from any native state, any marks and any slot state, the skeleton program from the game state without observers through the table layers (`PqxdhDeploymentIdealPostSim.tableLayer`) from the native table cache is the native run with the observers and the family history dropped, the marks and the slot state kept. It is closed under `pure` and bind (`splitT_pure`, `splitT_bind`) and holds for the game-state updates (`splitT_set`, `splitT_modify`, `splitT_consume`), the logged root against a direct table read (`splitT_loggedRoot`, through `tableRead_run`), the Server's core acceptance (`splitT_client`) and the accept tail (`splitT_tail`). Item 2's own splitting (`PqxdhRegistrationJointKemPostSkeleton.SplitN`) is stated at the native value type with the candidate's table; this is its counterpart for the post-challenge layers.
- The exposed encapsulation interface: `service_enc` and `service_encProgram` (the actual encapsulator and the post-challenge router under the CCA evaluation, the table state kept, through `fwdOption_liftComp`) and `lowerE_enc` (a program whose run by the actual encapsulator creates no KEM key, reveals no KEM secret and does not decapsulate the selected challenge ciphertext runs through item 2's erased service layers as under the actual private services).
- `step_accept`: the skeleton's raw accept (`upperLayer_accept`) is its exposed prefix and its tail; the prefix runs as item 2's annotated source prefix (`prefix_chain`, from item 2's `PqxdhRegistrationJointKemEncapsulation.prefix_program`, `PqxdhRegistrationJointOpenBackend.prefix_program` and `PqxdhRegistrationJointServerPrefix.prefix_source`, with the bounds of `PqxdhRegistrationJointOpenCosts.prefix_bound`), the tail splits, and together they are the middle's annotated source accept (`sourceMid_accept`, `source_accept_run`).
- `step_build`: at a session that the marks do not designate, the response tail is the source's own (`buildService_real`), so the skeleton's build is the native build (`build_real`); a build that is not hidden in the middle meets this condition (`skelMarks_real`), and the middle answers it with the native build (`sourceMid_build`).

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec SkelState NGame Marks fwd fwdOption coinLift clean)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostSim (SlotState ServiceState tableLayer serviceLayer upperLayer eraseService)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostItem (cleanSkel cleanUpper)
open PqxdhDeploymentIdealPostSteps (encodeMid upperE lowerE StepAt)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhServerAuthNative (NativeGame NativeState)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### Splitting native programs at the factored value type -/

section Split

/-- A native program and a skeleton program at the factored value type split: from any native state, any marks and any slot state, the skeleton program from the game state without observers, through item 2's table layers from the native table cache, is the native run with the observers and the family history dropped, the marks and the slot state kept. -/
def SplitT {α : Type} (work : NativeGame KemSK α) (free : NGame KemSK Output α) : Prop :=
  ∀ (native : NativeState KemSK) (marks : Marks Output) (slots : SlotState),
    (simulateQ tableLayer (free.run (clean native.2, marks))).run (native.1.cache, slots) =
      (fun result => ((result.1, (clean result.2.2, marks)), (result.2.1.cache, slots))) <$> work.run native

/-- Returning a value splits: both programs return it and leave their states unchanged. -/
theorem splitT_pure {α : Type} (value : α) : SplitT (KemSK := KemSK) (pure value) (pure value) := by
  intro native marks slots
  simp only [StateT.run_pure, simulateQ_pure, map_pure]

/-- Splitting is closed under bind: a split first program followed by split continuations splits. -/
theorem splitT_bind {α β : Type} {work : NativeGame KemSK α} {free : NGame KemSK Output α}
    {next : α → NativeGame KemSK β} {nextFree : α → NGame KemSK Output β}
    (first : SplitT work free) (rest : ∀ value, SplitT (next value) (nextFree value)) :
    SplitT (work >>= next) (free >>= nextFree) := by
  intro native marks slots
  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, first native marks slots, bind_map_left, StateT.run_bind,
    map_bind]
  exact bind_congr fun result => rest result.1 result.2 marks slots

/-- Setting the native game state splits against setting the skeleton's game state to its image without observers. -/
theorem splitT_set (value value' : GameState KemSK) (cleaned : value' = clean value) :
    SplitT (PqxdhServerAuthNative.nativeSet value) (PqxdhRegistrationJointKemPostSkeleton.setGame value') := by
  intro native marks slots
  change (simulateQ tableLayer (pure ((), (value', marks)))).run (native.1.cache, slots) =
    _ <$> (pure ((), (native.1, value)) : ProbComp _)
  rw [simulateQ_pure, StateT.run_pure, map_pure, cleaned]

/-- Modifying the native game state splits against a skeleton modification that commutes with dropping the observers. -/
theorem splitT_modify (change change' : GameState KemSK → GameState KemSK)
    (cleaned : ∀ game, change' (clean game) = clean (change game)) :
    SplitT (PqxdhServerAuthNative.nativeModify change) (PqxdhRegistrationJointKemPostSkeleton.modifyGame change') := by
  intro native marks slots
  change (simulateQ tableLayer (pure ((), (change' (clean native.2), marks)))).run (native.1.cache, slots) =
    _ <$> (pure ((), (native.1, change native.2)) : ProbComp _)
  rw [simulateQ_pure, StateT.run_pure, map_pure, cleaned]

/-- Consuming a registration id splits: both programs append the same id to the Server's consumed list. -/
theorem splitT_consume (rid : pqxdh.RegistrationId) :
    SplitT (PqxdhServerAuthNative.nativeConsume (KemSK := KemSK) rid)
      (PqxdhRegistrationJointKemPostSkeleton.consumeGame rid) := by
  intro native marks slots
  change (simulateQ tableLayer (pure ((), ({ clean native.2 with server := { (clean native.2).server with
      consumed := (clean native.2).server.consumed ++ [PqxdhRefinement.absBytes rid.bytes] } }, marks)))).run (native.1.cache, slots) =
    _ <$> (pure ((), (native.1, { native.2 with server := { native.2.server with
      consumed := native.2.server.consumed ++ [PqxdhRefinement.absBytes rid.bytes] } })) : ProbComp _)
  rw [simulateQ_pure, StateT.run_pure, map_pure]
  rfl

/-- A direct table read of the skeleton runs through item 2's table layers on the public cache. -/
theorem tableRead_run (point : Pqxdh.Bytes) (state : SkelState KemSK Output)
    (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    (simulateQ tableLayer ((PqxdhRegistrationJointKemPostSkeleton.tableRead (KemSK := KemSK) point).run state)).run tables =
      (fun result => ((result.1, state), (result.2, tables.2))) <$>
        (PqxdhSecretInputKdf.HmacOracle.randomOracle point).run tables.1 := by
  change (simulateQ tableLayer ((fun reply => (reply, state)) <$>
    ((SkelSpec Output).query (.inr (.inr point)) : OracleComp (SkelSpec Output) _))).run tables = _
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, PqxdhDeploymentIdealPostSteps.tableLayer_direct,
    Functor.map_map]

/-- The Server's logged root (the random-oracle root of the root key input, with its session touch recorded) splits against the skeleton's table read of the root key input, expanded; the split drops the recorded touch. -/
theorem splitT_loggedRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32)
    (original : pqxdh.PendingServerRegistration) :
    SplitT (KemSK := KemSK) (PqxdhServerAuthNative.loggedRoot hmac index input original)
      (PqxdhSecretInputKdf.expandRoot hmac <$>
        PqxdhRegistrationJointKemPostSkeleton.tableRead (PqxdhRefinement.absBytes original.root_key_input.bytes)) := by
  intro native marks slots
  rw [StateT.run_map, simulateQ_map, StateT.run_map, tableRead_run, Functor.map_map]
  simp only [PqxdhServerAuthNative.loggedRoot, PqxdhServerAuthNative.romRoot, StateT.run_bind]
  change _ = _ <$> ((fun result => (PqxdhSecretInputKdf.expandRoot hmac result.1, _)) <$>
    (PqxdhSecretInputKdf.HmacOracle.randomOracle (PqxdhRefinement.absBytes original.root_key_input.bytes)).run
      native.1.cache >>= _)
  simp only [bind_map_left, map_bind]
  rw [map_eq_bind_pure_comp]
  exact bind_congr fun _ => rfl

/-- The Server's core acceptance and root of a raw accept split. -/
theorem splitT_client (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    SplitT (KemSK := KemSK) (PqxdhServerAuthNative.nativeClient hmac index control binding input)
      (PqxdhRegistrationJointKemPostSkeleton.clientStep hmac control binding input) := by
  unfold PqxdhServerAuthNative.nativeClient PqxdhRegistrationJointKemPostSkeleton.clientStep
  cases PqxdhServerRelatedRootInput.accept control binding input with
  | ok result =>
      cases result with
      | Err error => exact splitT_pure _
      | Ok pair =>
          exact splitT_bind (splitT_loggedRoot hmac index input _) fun root =>
            splitT_bind (splitT_consume _) fun _ => splitT_pure _
  | fail error => exact splitT_pure _
  | div => exact splitT_pure _

/-- The Server's accept tail splits, the native tail capturing the native game state and the skeleton's the game state without observers. -/
theorem splitT_tail (setup : Setup baseSpec KemSK) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    SplitT (PqxdhRegistrationJointServerAccept.tail setup publicIdentity before collected)
      (PqxdhRegistrationJointKemPostSkeleton.acceptTail setup publicIdentity (clean before) collected) := by
  unfold PqxdhRegistrationJointServerAccept.tail PqxdhRegistrationJointKemPostSkeleton.acceptTail
  refine splitT_bind (splitT_set _ _ rfl) fun _ => ?_
  rcases collected with ⟨_ | input, consumed⟩
  · exact splitT_pure none
  · refine splitT_bind (splitT_client setup.hmac _ _ _ input) fun returned => ?_
    cases returned with
    | ok value =>
        cases value with
        | none => exact splitT_pure none
        | some token =>
            exact splitT_bind (splitT_modify _ _ fun _ => rfl) fun _ => splitT_pure _
    | fail error => exact splitT_pure none
    | div => exact splitT_pure none

end Split

/-! ### Requests of the exposed encapsulation interface through the service layers -/

section Lift
variable {ιA ιB ιT : Type} {A : OracleSpec ιA} {B : OracleSpec ιB} {T : OracleSpec ιT} {J : Type}

/-- Forwarding the table oracles through an optional stateful layer passes a lifted program through the layer. -/
theorem fwdOption_liftComp (layer : QueryImpl A (OptionT (StateT J (OracleComp B)))) {α : Type}
    (work : OracleComp A α) (state : J) :
    ((simulateQ (fwdOption (T := T) layer) (OracleComp.liftComp work (A + T))).run).run state =
      OracleComp.liftComp (((simulateQ layer work).run).run state) (B + T) := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (fwdOption (T := T) layer)
    (fun query => fwdOption (T := T) layer (.inl query)) (fun _ => rfl)]
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind,
        OracleComp.liftComp_bind]
      refine bind_congr fun result => ?_
      rcases result with ⟨_ | reply, after⟩
      · simp
      · exact ih reply after

end Lift

section Service
variable (setup : Setup baseSpec KemSK) {count : ℕ} (selected : Fin (count + 1))
  (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
  (challenge : MlKem768Ciphertext)
open PqxdhDeploymentIdealPostRequests (postRouter)

/-- A request of the exposed encapsulation interface passes through the actual encapsulator to the post-challenge router, whose KEM requests the CCA evaluation answers; the table state is kept. -/
theorem service_enc (query : (Enc KemSK).Domain) (state : ServiceState KemSK) :
    ((serviceLayer setup selected chosen others challenge (.inl query)).run).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 challenge
          (((simulateQ (postRouter setup selected chosen others challenge)
            (PqxdhRegistrationJointKemEncapsulation.actual setup query)).run).run state.1) := by
  simp only [serviceLayer, PqxdhDeploymentIdealPostSim.optionLower, OptionT.run_mk, StateT.run_mk,
    QueryImpl.apply_compose, PqxdhRegistrationJointKemPostSkeleton.fwd_inl]
  rw [fwdOption_liftComp, QueryImpl.simulateQ_compose, PqxdhDeploymentIdealPostItem.fwd_liftComp,
    ← PqxdhRegistrationJointKemPostSkeleton.evaluate_layer, PqxdhDeploymentIdealPostItem.tableLayer_lift,
    Functor.map_map]
  rfl

/-- A program of the exposed encapsulation interface sent by the skeleton passes through the service layers as its run by the actual encapsulator and the post-challenge router under the CCA evaluation; the table state is kept. -/
theorem service_encProgram {α : Type} (work : OracleComp (Enc KemSK) α) (state : ServiceState KemSK) :
    ((simulateQ (serviceLayer setup selected chosen others challenge)
        (simulateQ (PqxdhRegistrationJointKemPostSkeleton.encLift (V := Output)) work)).run).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        PqxdhDynamicKemPost.evaluate setup.baseImpl setup.kem chosen.2 challenge
          (((simulateQ (postRouter setup selected chosen others challenge)
            (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) work)).run).run state.1) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, PqxdhDynamicKemPost.evaluate, OptionT.run_pure, StateT.run_pure]
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
      have up : simulateQ (serviceLayer setup selected chosen others challenge)
          (PqxdhRegistrationJointKemPostSkeleton.encLift (V := Output) query) =
          serviceLayer setup selected chosen others challenge (.inl query) := simulateQ_spec_query _ _
      rw [up, service_enc, bind_map_left]
      simp only [PqxdhRegistrationJointKemPostSkeleton.evaluate_layer] at ih ⊢
      rw [simulateQ_bind, map_bind]
      refine bind_congr fun result => ?_
      rcases result with ⟨_ | reply, after⟩
      · simp only [Option.elim_none, StateT.run_pure, simulateQ_pure, map_pure]
      · exact ih reply (after, state.2)

end Service

section Lowered
variable (setup : Setup baseSpec KemSK) {count : ℕ} (t : Target count) (p : Params KemSK count)
open PqxdhDeploymentIdealPostRequests (challengeDecaps)

/-- A program of the exposed encapsulation interface sent by the skeleton, whose run by the actual encapsulator has no KEM creation, no KEM reveal and no decapsulation of the selected challenge ciphertext, runs through item 2's erased service layers from the erased router state of a prefix pool as its run under the actual private services after the actual encapsulator, without stopping, with the erased router state of the final pool and the table state kept. -/
theorem lowerE_enc {α : Type} (work : OracleComp (Enc KemSK) α)
    (noCreate : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) work).IsQueryBoundP
      (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0)
    (noReveal : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) work).IsQueryBoundP
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .other) 0)
    (fresh : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) work).IsQueryBoundP
      (fun query => challengeDecaps (KemSK := KemSK) t.kem.val p.challenge query = true) 0)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    ((simulateQ (lowerE setup t p) (simulateQ (PqxdhRegistrationJointKemPostSkeleton.encLift (V := Output)) work)).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables) =
      (fun result => (some result.1, (PqxdhRegistrationJointKemObserverFree.eraseJoint
          (result.2.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.2), tables))) <$>
        (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
          (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup) work)).run (joint, pool) := by
  have run := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    (serviceLayer setup t.kem p.chosen p.others p.challenge)
    (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen p.others p.challenge)
    (simulateQ (PqxdhRegistrationJointKemPostSkeleton.encLift (V := Output)) work)
    ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)
  change ((simulateQ (lowerE setup t p) (simulateQ (PqxdhRegistrationJointKemPostSkeleton.encLift (V := Output)) work)).run).run
    (eraseService ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) = _
  rw [← run, service_encProgram]
  have reservation : PqxdhDynamicKemRouter.selectedReservation t.kem p.chosen.1 p.others =
      PqxdhDynamicKemRouter.redact t.kem.val (p.pool t) := by
    rw [PqxdhDeploymentIdealParams.pool_eq, PqxdhDynamicKemRouter.selected_reservation]
  have present : (p.pool t)[t.kem.val]? = some (p.chosen.1, p.chosen.2) := PqxdhDeploymentIdealParams.pool_kem t p
  simp only [PqxdhDeploymentIdealPostRequests.postRouter, reservation]
  rw [PqxdhDeploymentIdealPostRequests.jointProgram_fresh setup.baseImpl setup.kem setup.joint t.kem.val (p.pool t)
      p.chosen.1 p.chosen.2 present p.challenge _ _ fresh,
    PqxdhDeploymentIdealPoolSource.stopped_program setup t.kem.val (p.pool t) _ 0 noCreate noReveal joint pool
      prefixed (by simpa using PqxdhDeploymentIdealPostRequests.prefix_length _ _ prefixed),
    PqxdhDeploymentIdealPoolSource.reserved_noCreate setup (p.pool t) _ noCreate]
  simp only [Functor.map_map]
  rfl

end Lowered

/-! ### The real raw accept -/

section Accept
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The upper layers on a raw accept: the skeleton's raw accept with its encapsulation exposed. -/
theorem upperLayer_accept (raw : Pqxdh.Bytes)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.accept raw)))).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (PqxdhRegistrationJointKemPostSkeleton.acceptStep setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity raw).run state.2 := by
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  simp only [PqxdhRegistrationJointKemPostSkeleton.liftGrouped, StateT.run, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, PqxdhRegistrationJointKemPostSkeleton.groupedLift,
    PqxdhRegistrationJointKemPostSkeleton.skelImpl]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run ((fun a => (a, state.1)) <$>
    PqxdhRegistrationJointKemPostSkeleton.acceptStep setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity raw) state.2 = _
  rw [StateT.run_map, Functor.map_map]
  rfl

/-- On a raw accept that is not the selected one, the middle source handler is item 2's annotated source accept, with the accept counter advanced. -/
theorem sourceMid_accept (raw : Pqxdh.Bytes) (m : Mid KemSK) (other : m.backend.2.2.accepts ≠ t.accept) :
    (sourceMid setup codec route checks t p created (.inl (.inr (.accept raw)))).run m =
      (fun result => (result.1,
        { m with joint := result.2, backend := PqxdhDeploymentIdealPostSource.bumpSource (KemSK := KemSK) (.inl (.inr (.accept raw))) m.backend })) <$>
        (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhRegistrationJointServerAccept.source setup codec checks
          created.seed created.server.server.metadata.identityIndex raw)).run m.joint := by
  change (if m.backend.2.2.accepts = t.accept then _ else _) = _
  simp only [other, ↓reduceIte]
  rfl

/-- The raw Server prefix with its encapsulation exposed, run by the actual encapsulator and the actual private services, is item 2's annotated source prefix, when the Server's identity slot holds its seed. -/
theorem prefix_chain (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) (raw : Pqxdh.Bytes)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (consumed : List Pqxdh.Bytes)
    (owned : pool.1.seeds[identityIndex]? = some seed) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
            (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run consumed))).run pool =
      (fun result => ((result.1, result.2.2), result.2.1)) <$>
        (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
          (PqxdhServerAuthExperiment.serverAux setup codec checks)) (PqxdhServerRootPreparation.collect raw)).run
            (pool, consumed) := by
  rw [PqxdhRegistrationJointKemEncapsulation.prefix_program]
  have chain := PqxdhRegistrationJointOpenBackend.prefix_program setup codec checks
    (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw) (pool, consumed)
  rw [PqxdhRegistrationJointServerPrefix.prefix_source setup codec checks seed identityIndex raw pool consumed owned]
    at chain
  rw [← chain]
  simp only [PqxdhRegistrationJointOpenBackend.run, Functor.map_map]
  exact (id_map _).symm

/-- Item 2's annotated source accept: the annotated prefix on the private pools and the consumed list, then the accept tail on the native state captured before it. -/
theorem source_accept_run (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhRegistrationJointServerAccept.source setup codec checks
      seed identityIndex raw)).run state =
      (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
          (PqxdhServerAuthExperiment.serverAux setup codec checks)) (PqxdhServerRootPreparation.collect raw)).run
          (state.pool, state.shared.2.server.consumed) >>= fun prepared =>
        (fun result => (result.1, { state with pool := prepared.2.1, shared := result.2 })) <$>
          (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) state.shared.2
            (prepared.1, prepared.2.2)).run state.shared := by
  show PqxdhRegistrationJointServerSchedule.onBackend _ state = _
  simp only [PqxdhRegistrationJointServerSchedule.onBackend, PqxdhRegistrationJointServerAccept.source,
    PqxdhRegistrationJointServerAccept.run]
  rw [StateT.run_bind]
  change _ <$> ((pure (state.shared.2, (state.pool, state.shared)) : ProbComp _) >>= _) = _
  rw [pure_bind, StateT.run_bind]
  simp only [PqxdhRegistrationJointServerAccept.sourcePrepare, StateT.run, bind_map_left, map_bind]
  refine bind_congr fun prepared => ?_
  simp only [PqxdhRegistrationJointFinish.onNative, Functor.map_map]

/-- A raw accept other than the selected one: the skeleton's raw accept through item 2's layers (its prefix through the actual encapsulator and the post-challenge router, its tail through the table layers) is item 2's annotated source accept on the middle state, with the accept counter advanced. It needs the Server's identity slot to hold its seed, the constructed Server's public identity to be that of its seed, and a prefix KEM pool. -/
theorem step_accept (raw : Pqxdh.Bytes) (m : Mid KemSK) (other : m.backend.2.2.accepts ≠ t.accept)
    (owned : m.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed)
    (identity : created.publicIdentity = setup.joint.publicKeys created.seed)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2) :
    StepAt setup codec route checks t p created (.inl (.inr (.accept raw))) m := by
  unfold StepAt
  rw [PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m), upperLayer_accept, Functor.map_map,
    simulateQ_map, OptionT.run_map, StateT.run_map, sourceMid_accept setup codec route checks t p created raw m other,
    source_accept_run]
  have noCreate : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
        (PqxdhRegistrationJointServerPrefix.clientPrefix created.server.server.metadata.identityIndex raw)).run
          m.joint.shared.2.server.consumed)).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
    rw [PqxdhRegistrationJointKemEncapsulation.prefix_program]
    refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr (by
      simpa using PqxdhRegistrationJointOpenCosts.prefix_bound (KemSK := KemSK) setup codec checks
        created.server.server.metadata.identityIndex raw m.joint.shared.2.server.consumed .kemCreate (by decide))
    rw [PqxdhDeploymentIdealPoolSource.isCreate_class]
  have noReveal : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
        (PqxdhRegistrationJointServerPrefix.clientPrefix created.server.server.metadata.identityIndex raw)).run
          m.joint.shared.2.server.consumed)).IsQueryBoundP
        (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .other) 0 := by
    rw [PqxdhRegistrationJointKemEncapsulation.prefix_program]
    simpa using PqxdhRegistrationJointOpenCosts.prefix_bound (KemSK := KemSK) setup codec checks
      created.server.server.metadata.identityIndex raw m.joint.shared.2.server.consumed .other (by decide)
  have fresh := PqxdhDeploymentIdealPostRequests.fresh_of_noDecaps t.kem.val p.challenge
    (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
        (PqxdhRegistrationJointServerPrefix.clientPrefix created.server.server.metadata.identityIndex raw)).run
          m.joint.shared.2.server.consumed)) (by
    rw [PqxdhRegistrationJointKemEncapsulation.prefix_program]
    simpa using PqxdhRegistrationJointOpenCosts.prefix_bound (KemSK := KemSK) setup codec checks
      created.server.server.metadata.identityIndex raw m.joint.shared.2.server.consumed .decapsulate (by decide))
  have stepT : (PqxdhRegistrationJointKemPostSkeleton.acceptStep (V := Output) setup codec checks
      created.server.server.metadata.identityIndex created.publicIdentity raw).run (encodeMid setup m).1.2 =
      ((fun result => (result, (encodeMid setup m).1.2)) <$>
        simulateQ (PqxdhRegistrationJointKemPostSkeleton.encLift (V := Output))
          ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
            (PqxdhRegistrationJointServerPrefix.clientPrefix created.server.server.metadata.identityIndex raw)).run
              m.joint.shared.2.server.consumed)) >>= fun result =>
        (PqxdhRegistrationJointKemPostSkeleton.liftT (PqxdhRegistrationJointKemPostSkeleton.acceptTail setup
          created.publicIdentity (clean m.joint.shared.2) result.1)).run result.2 := rfl
  rw [stepT, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, simulateQ_map, OptionT.run_map,
    StateT.run_map]
  rw [show (encodeMid setup m).2 = (PqxdhRegistrationJointKemObserverFree.eraseJoint
      (m.joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2),
      (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))) from rfl,
    lowerE_enc setup t p _ noCreate noReveal fresh m.joint.pool.1 m.joint.pool.2 prefixed,
    prefix_chain setup codec checks created.seed _ raw (m.joint.pool.1, m.joint.pool.2) _ owned]
  simp only [Functor.map_map, bind_map_left, map_bind, Prod.mk.eta]
  refine bind_congr fun prepared => ?_
  rw [identity] at *
  have native := PqxdhDeploymentIdealPostSteps.lowerE_native setup t p
    ((PqxdhRegistrationJointKemPostSkeleton.acceptTail setup (setup.joint.publicKeys created.seed)
      (clean m.joint.shared.2) (prepared.1, prepared.2.2)).run (encodeMid setup m).1.2)
    (PqxdhRegistrationJointKemObserverFree.eraseJoint (prepared.2.1.1, PqxdhDeploymentIdealPoolSource.routerOf
      prepared.2.1.2), (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1)))
    (by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
  simp only [Option.map_some, Option.elim_some]
  rw [show ∀ (work : PqxdhRegistrationJointKemPostSkeleton.NGame KemSK Output (Option ℕ)) (s : SkelState KemSK Output),
      (PqxdhRegistrationJointKemPostSkeleton.liftT work).run s =
        simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) (work.run s) from fun _ _ => rfl, native,
    show (encodeMid setup m).1.2 = (clean m.joint.shared.2, PqxdhDeploymentIdealPostSteps.skelMarks m) from rfl,
    splitT_tail setup _ m.joint.shared.2 (prepared.1, prepared.2.2) m.joint.shared
      (PqxdhDeploymentIdealPostSteps.skelMarks m) (m.backend.2.1, m.backend.1)]
  simp only [Functor.map_map]
  rfl

end Accept

/-! ### The real build -/

section Build
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- At a session that the marks do not designate, the response tail is the source's native one, for any services. -/
theorem buildService_real {V : Type} (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (marks : Marks V) (session : ℕ) (real : ∀ value, marks ≠ some (session, value)) :
    PqxdhRegistrationJointKemPostSkeleton.buildService setup codec checks services marks session =
      PqxdhRegistrationJointKemPostSkeleton.nativeResponse setup codec checks := by
  rcases marks with _ | ⟨slot, value⟩
  · rfl
  · have other : slot ≠ session := fun same => real value (by rw [same])
    simp only [PqxdhRegistrationJointKemPostSkeleton.buildService, other, ↓reduceIte]

/-- The Server build at a session that the marks do not designate while it has a pending token: the skeleton's build through the table layers is the native build, with the observers dropped and the marks and slot state kept. -/
theorem build_real (session : ℕ) (payload : Option Pqxdh.Bytes) (native : NativeState KemSK) (marks : Marks Output)
    (slots : SlotState) (real : (native.2.pending session).isSome = true → ∀ value, marks ≠ some (session, value)) :
    (simulateQ tableLayer ((PqxdhRegistrationJointKemPostSkeleton.buildStep setup codec checks
        (factoredServices setup codec checks) session payload).run (clean native.2, marks))).run (native.1.cache, slots) =
      (fun result => ((result.1, (clean result.2.2, marks)), (result.2.1.cache, slots))) <$>
        (PqxdhServerAuthNative.nativeBuild setup codec checks session payload).run native := by
  change _ = _ <$> PqxdhServerAuthNative.nativeBuild setup codec checks session payload native
  simp only [PqxdhServerAuthNative.nativeBuild, PqxdhServerAuthNative.native_bind_run, PqxdhServerAuthNative.nativeGet,
    PqxdhServerAuthNative.localState, pure_bind]
  change (simulateQ tableLayer (PqxdhRegistrationJointKemPostSkeleton.buildStep setup codec checks
    (factoredServices setup codec checks) session payload (clean native.2, marks))).run (native.1.cache, slots) = _
  rcases found : native.2.pending session with _ | token
  · have cleanFound : (clean native.2).pending session = none := found
    simp only [PqxdhRegistrationJointKemPostSkeleton.buildStep, cleanFound, PqxdhServerAuthNative.native_pure_run,
      map_pure, simulateQ_pure, StateT.run_pure]
  · have cleanFound : (clean native.2).pending session = some token := found
    simp only [PqxdhRegistrationJointKemPostSkeleton.buildStep, cleanFound]
    rw [buildService_real setup codec checks _ marks session (real (by simp [found]))]
    simp only [PqxdhServerAuthNative.native_bind_run, PqxdhServerAuthNative.nativeCoins,
      PqxdhServerAuthNative.nativeSet, bind_pure_comp, simulateQ_map, StateT.run_map,
      PqxdhDeploymentIdealPostItem.tableLayer_lift, Functor.map_map, PqxdhServerAuthNative.native_map_run,
      PqxdhServerAuthNative.localState, map_pure, PqxdhRegistrationJointKemPostSkeleton.nativeResponse]
    rfl

/-- The upper layers on a build: the skeleton's build on its state. -/
theorem upperLayer_build (session : ℕ) (payload : Option Pqxdh.Bytes)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.build session payload)))).run state =
      (fun result => (result.1, (state.1, result.2))) <$> simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK)))
        ((PqxdhRegistrationJointKemPostSkeleton.buildStep setup codec checks (factoredServices setup codec checks)
          session payload).run state.2) := by
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  simp only [PqxdhRegistrationJointKemPostSkeleton.liftGrouped, StateT.run, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, PqxdhRegistrationJointKemPostSkeleton.groupedLift,
    PqxdhRegistrationJointKemPostSkeleton.skelImpl]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run ((fun a => (a, state.1)) <$>
    PqxdhRegistrationJointKemPostSkeleton.liftT (V := Output)
      (PqxdhRegistrationJointKemPostSkeleton.buildStep setup codec checks (factoredServices setup codec checks)
        session payload)) state.2 = _
  rw [StateT.run_map, Functor.map_map]
  rfl

/-- On a build that is not the marked session's with a pending token, the middle source handler is the source's native build. -/
theorem sourceMid_build (session : ℕ) (payload : Option Pqxdh.Bytes) (m : Mid KemSK)
    (real : PqxdhDeploymentIdealPostSource.buildHiddenAt m session = false) :
    (sourceMid setup codec route checks t p created (.inl (.inr (.build session payload)))).run m =
      (fun result => (result.1, { m with joint := { m.joint with shared := result.2 } })) <$>
        (PqxdhServerAuthNative.nativeBuild setup codec checks session payload).run m.joint.shared := by
  change (if PqxdhDeploymentIdealPostSource.buildHiddenAt m session then _ else _) = _
  simp only [real, Bool.false_eq_true, ↓reduceIte]
  change (fun r => (r.1, { m with joint := r.2 })) <$> ((fun r => (r.1, { m.joint with shared := r.2 })) <$>
    (PqxdhServerAuthNative.nativeBuild setup codec checks session payload).run m.joint.shared) = _
  rw [Functor.map_map]

/-- At a build that is not hidden, the skeleton's marks do not designate the session while it has a pending token. -/
theorem skelMarks_real (session : ℕ) (m : Mid KemSK)
    (real : PqxdhDeploymentIdealPostSource.buildHiddenAt m session = false) :
    (m.joint.shared.2.pending session).isSome = true →
      ∀ value, PqxdhDeploymentIdealPostSteps.skelMarks m ≠ some (session, value) := by
  intro pending value designated
  unfold PqxdhDeploymentIdealPostSteps.skelMarks at designated
  unfold PqxdhDeploymentIdealPostSource.buildHiddenAt at real
  rcases marked : m.backend.2.2.marks with _ | ⟨index, coordinates⟩
  · simp [marked] at designated
  · simp only [marked, Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at designated
    obtain ⟨_, _, same, _⟩ := designated
    simp [marked, same, pending] at real

/-- A build that is not the marked session's with a pending token: the skeleton's build through item 2's layers is the source's native build on the middle state. -/
theorem step_build (session : ℕ) (payload : Option Pqxdh.Bytes) (m : Mid KemSK)
    (real : PqxdhDeploymentIdealPostSource.buildHiddenAt m session = false) :
    StepAt setup codec route checks t p created (.inl (.inr (.build session payload))) m := by
  unfold StepAt
  rw [PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m), upperLayer_build, Functor.map_map,
    simulateQ_map, OptionT.run_map, StateT.run_map,
    PqxdhDeploymentIdealPostSteps.lowerE_native setup t p _ _ (PqxdhDeploymentIdealPostSteps.encodeMid_erased setup m),
    sourceMid_build setup codec route checks t p created session payload m real,
    show (encodeMid setup m).1.2 = (clean m.joint.shared.2, PqxdhDeploymentIdealPostSteps.skelMarks m) from rfl,
    show (encodeMid setup m).2.2 = (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1)) from rfl,
    build_real setup codec checks session payload m.joint.shared _ _ (skelMarks_real session m real)]
  simp only [Functor.map_map]
  rfl

end Build

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_set

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_modify

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_consume

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.tableRead_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.tableRead_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_loggedRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_loggedRoot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_client

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.splitT_tail

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.fwdOption_liftComp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.fwdOption_liftComp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.service_enc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.service_enc

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.service_encProgram' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.service_encProgram

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.lowerE_enc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.lowerE_enc

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.upperLayer_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.upperLayer_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.sourceMid_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.sourceMid_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.prefix_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.prefix_chain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.source_accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.source_accept_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.step_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.step_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.buildService_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.buildService_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.build_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.build_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.upperLayer_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.upperLayer_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.sourceMid_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.sourceMid_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.skelMarks_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.skelMarks_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.step_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostServer.step_build

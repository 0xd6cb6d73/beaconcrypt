-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthEmbed

/-! The source14 operations read neither analysis history (CE-8). The source14 state keeps two histories that no operation reads: the Extract family's observation history and the ghost (table touches, sequence-one seals and the acceptance snapshot); `eraseObservers` clears both and keeps every operational field and both caches. An operation is `Stable` when erasing the histories before it changes nothing after erasing them again. Every source14 operation is stable: public HMAC, BLAKE2b, kernel reveal, accept and build on the shared state (`hmac_stable`, `hash_stable`, `reveal_stable`, `accept_stable`, `build_stable`), and every finish callback (`callbacks_stable`), hence every finish program (`callbacks_program`). A local Beacon's finish callbacks of `PqxdhDeploymentServerAuthEmbed`, run through the singleton route and the source14 handler, are the native finish callbacks on the shared state up to the histories (`localCallbacks_route`), and so is a whole finish program (`localFinish_route`): the local root reads and fills the same zero-salt Extract table entry through the public HMAC, and BLAKE2b fills the same shared cache. No security claim is made here. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity PqxdhSecretInputKdf
open PqxdhJointGapDh (ScalarBytes challenge)
open PqxdhDeploymentServerAuthEmbed (coins forward localRoot localCallbacks coins_route localRoot_route)
open PqxdhRegistrationR1Restriction (eraseShared route)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- A native operation that reads neither analysis history. -/
def Stable {α : Type} (op : NativeGame KemSK α) : Prop :=
  ∀ state, Prod.map id eraseObservers <$> op.run state = Prod.map id eraseObservers <$> op.run (eraseObservers state)

/-- Erasing the histories twice is erasing them once. -/
theorem eraseObservers_idem (state : NativeState KemSK) : eraseObservers (eraseObservers state) = eraseObservers state := rfl

/-- Erasing the shared histories twice is erasing them once. -/
theorem eraseShared_idem (state : PqxdhRegistrationSchedule.State KemSK) : eraseShared (eraseShared state) = eraseShared state :=
  rfl

/-- BLAKE2b reads only the shared cache. -/
theorem hash_stable (bytes : Pqxdh.Bytes) : Stable (KemSK := KemSK) (nativeHash bytes) := by
  intro state
  simp only [nativeHash, StateT.run, eraseObservers, Functor.map_map]
  rfl

/-- A kernel reveal reads only the Server's peers. -/
theorem reveal_stable (keyId : Std.U64) :
    Stable (KemSK := KemSK) (localState fun current => (revealKernel keyId current, current)) := by
  intro state
  simp only [localState, revealKernel, StateT.run, eraseObservers, map_pure]
  rfl

/-- The public HMAC reads only the Extract table. -/
theorem hmac_stable (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : HmacBlock) (message : Pqxdh.Bytes) : Stable (nativeHmac setup seed scalar key message) := by
  intro state
  simp only [nativeHmac]
  split_ifs with slice
  all_goals simp only [nativeTouch, localState, native_bind_run, PqxdhServerRelatedRootConsumer.familyImpl,
    QueryImpl.compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query, PqxdhExtractRomFamily.romImpl, slice,
    ite_false, StateT.run, eraseObservers, pure_bind, Functor.map_map]
  all_goals simp only [and_self, ite_true, map_bind, map_pure]
  all_goals rfl

/-- A build reads only its pending token, the Server and the shared cache. -/
theorem build_stable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (payload : Option Pqxdh.Bytes) : Stable (nativeBuild setup codec checks index payload) := by
  intro state
  simp only [nativeBuild, nativeGet]
  cases pending : state.2.pending index
  all_goals simp only [eraseObservers, pending, native_bind_run, nativeCoins, nativeSet, localState, native_pure_run,
    pure_bind, map_bind, bind_map_left, map_pure, StateT.run]
  all_goals rfl

/-- An accept reads only the Server, the session counter, the pending tokens and the Extract table. -/
theorem accept_stable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes) :
    Stable (nativeAccept setup codec checks seed scalar raw) := by
  intro state
  simp only [nativeAccept, native_bind_run, nativeCoins, map_bind, bind_map_left, StateT.run]
  simp only [nativeGet, nativeSet, localState, pure_bind]
  refine bind_congr fun collected => ?_
  rcases collected with ⟨_ | input, consumed⟩
  all_goals simp only [nativeClient, eraseObservers, binding, challenge, native_bind_run, native_pure_run, map_pure,
    map_bind]
  all_goals first
    | rfl
    | cases accepted : PqxdhServerRelatedRootInput.accept state.2.server.control
        (binding setup (challenge setup.joint setup.dh seed scalar)) input
  all_goals simp_all only [binding, challenge, native_pure_run, pure_bind, map_pure]
  all_goals first
    | rfl
    | rename_i value
  rcases value with ⟨⟨control, original⟩⟩ | error
  all_goals simp only [loggedRoot, romRoot, romRootBytes, nativeTouch, nativeConsume, nativeModify, localState,
    native_bind_run, native_pure_run, bind_map_left, pure_bind, map_pure, bind_assoc]
  all_goals rfl

/-- Every finish callback reads only the Extract table, the shared cache and its coins. -/
theorem callbacks_stable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain) :
    Stable (PqxdhRegistrationSchedule.callbacks setup codec query) := by
  intro state
  rcases query with query | (query | (input | request | response))
  · simp only [PqxdhRegistrationSchedule.callbacks, nativeCoins, StateT.run, Functor.map_map]
    rfl
  · simp only [PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, nativeCtx,
      StateT.run, eraseObservers, Functor.map_map]
    rfl
  · simp only [PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, sourceRoot,
      StateT.run, eraseObservers, Functor.map_map]
    rfl
  · simp only [PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, nativeCtx,
      StateT.run, eraseObservers, Functor.map_map]
    rfl
  · simp only [PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, nativeCtx,
      StateT.run, eraseObservers, Functor.map_map]
    rfl

/-- A handler whose every query is stable runs every program stably. -/
theorem program_stable {κ : Type} {spec : OracleSpec κ} {α : Type} (handler : QueryImpl spec (NativeGame KemSK))
    (stable : ∀ query, Stable (handler query)) (program : OracleComp spec α) :
    Stable (simulateQ handler program) := by
  intro state
  have erased := OracleComp.map_run_simulateQ_eq_of_query_map_eq handler
    (fun query => StateT.mk fun current => Prod.map id eraseObservers <$> (handler query).run current) eraseObservers
    (fun query current => stable query current) program
  rw [erased state, erased (eraseObservers state), eraseObservers_idem]

/-- Every finish program reads neither history. -/
theorem callbacks_program {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) α) :
    Stable (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program) :=
  program_stable _ (callbacks_stable setup codec) program

/-- One local finish callback through the singleton route and the source14 handler is the native finish callback on the shared state, up to the histories. -/
theorem localCallbacks_route (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    Prod.map id eraseShared <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ route (localCallbacks setup codec query))).run state =
      (fun result => (result.1, eraseShared { state with shared := result.2 })) <$>
        (PqxdhRegistrationSchedule.callbacks setup codec query).run state.shared := by
  rcases query with query | ((request | (bytes | input)) | (input | request | response))
  · simp only [localCallbacks]
    rw [coins_route]
    simp only [PqxdhRegistrationSchedule.callbacks, nativeCoins, StateT.run, Functor.map_map]
    rfl
  · simp only [localCallbacks, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · simp only [localCallbacks, forward, simulateQ_map, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, route, PqxdhRegistrationSchedule.handler, StateT.run_map, PqxdhRegistrationSchedule.onShared_run,
      Functor.map_map]
    simp only [nativeHash, PqxdhRegistrationSchedule.callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot,
      nativeCtx, beaconNative, RawCtxSharedPrimitive.nativeImpl, RawCtxSharedPrimitive.openingImpl, StateT.run,
      Functor.map_map, bind_pure_comp]
    rfl
  · simp only [localCallbacks, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · exact localRoot_route setup codec checks seed input state
  · simp only [localCallbacks, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · simp only [localCallbacks, simulateQ_pure, StateT.run_pure, map_pure]
    rfl

/-- A shared-state operation lifted to the source14 state is stable for the shared erasure when the operation is stable. -/
theorem onShared_stable {α : Type} (op : NativeGame KemSK α) (stable : Stable op) (state : PqxdhRegistrationSchedule.State KemSK) :
    Prod.map id eraseShared <$> (PqxdhRegistrationSchedule.onShared op).run state =
      Prod.map id eraseShared <$> (PqxdhRegistrationSchedule.onShared op).run (eraseShared state) := by
  have same := congrArg (fun computation => (fun result => (result.1, ({ shared := result.2, owners := state.owners } :
    PqxdhRegistrationSchedule.State KemSK))) <$> computation) (stable state.shared)
  simp only [Functor.map_map] at same
  rw [PqxdhRegistrationSchedule.onShared_run, PqxdhRegistrationSchedule.onShared_run]
  simp only [Functor.map_map]
  exact same

/-- A program of shared-state operations lifted to the source14 state runs on the shared state and keeps the owners. -/
theorem onShared_program {κ : Type} {spec : OracleSpec κ} {α : Type} (handler : QueryImpl spec (NativeGame KemSK))
    (program : OracleComp spec α) (state : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (fun query => PqxdhRegistrationSchedule.onShared (handler query)) program).run state =
      (fun result => (result.1, { state with shared := result.2 })) <$> (simulateQ handler program).run state.shared := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, PqxdhRegistrationSchedule.onShared_run, bind_map_left, map_bind]
      refine bind_congr fun result => ?_
      rw [ih]

/-- A whole local finish program through the singleton route and the source14 handler is the native finish program on the shared state, up to the histories. -/
theorem localFinish_route {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed)
    (program : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) α)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    Prod.map id eraseShared <$>
      (simulateQ (PqxdhRegistrationSchedule.handler setup codec checks seed)
        (simulateQ route (simulateQ (localCallbacks setup codec) program))).run state =
      (fun result => (result.1, eraseShared { state with shared := result.2 })) <$>
        (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec) program).run state.shared := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  have lifted := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (PqxdhRegistrationSchedule.handler setup codec checks seed ∘ₛ route ∘ₛ localCallbacks setup codec)
    (fun query => StateT.mk fun current => Prod.map id eraseShared <$>
      (PqxdhRegistrationSchedule.onShared (PqxdhRegistrationSchedule.callbacks setup codec query)).run current)
    eraseShared (fun query current => by
      simp only [QueryImpl.apply_compose, QueryImpl.simulateQ_compose, StateT.run_mk]
      rw [localCallbacks_route, ← onShared_stable _ (callbacks_stable setup codec query) current,
        PqxdhRegistrationSchedule.onShared_run, Functor.map_map]
      rfl) program state
  rw [lifted]
  have erased := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (fun query => PqxdhRegistrationSchedule.onShared (PqxdhRegistrationSchedule.callbacks setup codec query))
    (fun query => StateT.mk fun current => Prod.map id eraseShared <$>
      (PqxdhRegistrationSchedule.onShared (PqxdhRegistrationSchedule.callbacks setup codec query)).run current)
    eraseShared (fun query current => by
      rw [StateT.run_mk, ← onShared_stable _ (callbacks_stable setup codec query) current]) program state
  rw [← erased, onShared_program, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.eraseObservers_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.eraseObservers_idem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.eraseShared_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.eraseShared_idem

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.hash_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.hash_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.reveal_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.reveal_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.hmac_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.hmac_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.build_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.build_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.accept_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.accept_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.callbacks_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.callbacks_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.program_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.callbacks_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.callbacks_program

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.localCallbacks_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.localCallbacks_route

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.onShared_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.onShared_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.onShared_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.onShared_program

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.localFinish_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthStable.localFinish_route

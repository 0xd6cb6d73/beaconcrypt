import BeaconcryptCore.Computational.PqxdhBorrowedSharedPrefix

/-!
Common accepted candidates retain the actual registration builder. Every first-record commitment shares the preceding ROM, and non-hash validation/allocation/writer callbacks retain their complete local state. This source factorization makes no claim that attacker-owned or rejected common branches have a false final decision.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhCommonSharedRegistration
open PqxdhJointKdfGame CtxRomAuth AdaptiveCtxSharedHash
variable {M P I D K A Result : Type} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)

/-- The literal native send/compiler is shared with later records; actual auxiliary callbacks cannot access the shared ROM. -/
noncomputable def compiler : QueryImpl PqxdhServerRegistrationPublication.NativeSpec (StateT A (OracleComp HashSpec))
  | .inl query => StateT.mk fun state =>
      (fun reply => (reply, state)) <$> simulateQ (RawCtxSourceSharedRom.native source writer) (RawCtxMixedOwner.sendLift query)
  | .inr query => StateT.mk fun state =>
      simulateQ RawCtxSelectiveSharedRom.coins ((PqxdhSourceAuxiliary.localServer callbacks query).run state)

set_option backward.isDefEq.respectTransparency false in
/-- Every actual registration callback retains its exact reply, local state and common cache. -/
theorem step (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) (state : A) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((compiler source writer callbacks query).run state)).run cache =
      (PqxdhRegistrationProtocolState.registrationImpl source writer (PqxdhSourceAuxiliary.server callbacks) query).run (state, cache) := by
  rcases query with (request | (input | (bytes | frame))) | query
  all_goals simp only [compiler, StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map,
    RawCtxMixedOwner.sendLift, simulateQ_spec_query, PqxdhRegistrationProtocolState.registrationImpl, QueryImpl.compose]
  case inl.inl => exact (RawCtxSourceSharedRom.native_step source writer (.inl request) state cache).symm
  case inl.inr.inl => exact (RawCtxSourceSharedRom.native_step source writer (.inr (.inl input)) state cache).symm
  case inl.inr.inr.inl => exact (RawCtxSourceSharedRom.native_step source writer (.inr (.inr (.inr (.inl bytes)))) state cache).symm
  case inl.inr.inr.inr => exact (RawCtxSourceSharedRom.native_step source writer (.inr (.inr (.inr (.inr frame)))) state cache).symm
  case inr =>
    rw [RawCtxSelectiveSharedRom.coins_complete]
    simp only [Functor.map_map, PqxdhSourceAuxiliary.server, PqxdhSourceAuxiliary.lift_step]
    rfl

/-- The entire native builder preserves optional outputs, local effects and all prior ROM entries through its complete continuation. -/
theorem program (client : OracleComp PqxdhServerRegistrationPublication.NativeSpec Result)
    (state : A) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ hashImpl ((simulateQ (compiler source writer callbacks) client).run state)).run cache =
      (simulateQ (PqxdhRegistrationProtocolState.registrationImpl source writer (PqxdhSourceAuxiliary.server callbacks)) client).run
        (state, cache) := by
  have perQuery : ∀ query before,
      Prod.map id (id : A × CtxRO.QueryCache → A × CtxRO.QueryCache) <$>
        (((hashImpl.mapStateTBase (compiler source writer callbacks)).flattenStateT query).run before) =
        (PqxdhRegistrationProtocolState.registrationImpl source writer (PqxdhSourceAuxiliary.server callbacks) query).run before := by
    intro query before
    simpa only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq] using
      step source writer callbacks query before.1 before.2
  have whole := map_run_simulateQ_eq_of_query_map_eq
    ((hashImpl.mapStateTBase (compiler source writer callbacks)).flattenStateT)
    (PqxdhRegistrationProtocolState.registrationImpl source writer (PqxdhSourceAuxiliary.server callbacks)) id perQuery client (state, cache)
  have unpacked := congrArg (fun work => (fun result => (result.1.1, (result.1.2, result.2))) <$> work)
    (simulateQ_mapStateTBase_run_eq_map_flattenStateT hashImpl (compiler source writer callbacks) client state cache)
  simp only [Functor.map_map, Prod.map_def, id_eq] at unpacked whole
  exact unpacked.trans whole

/-- The cache is external interpreter state; this record retains every source role, control, consumed identifier and auxiliary value. -/
def withCache (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (cache : CtxRO.QueryCache) :
    PqxdhRegistrationProtocolState.State M P I D K A S B := {state with primitive := (state.primitive.1, cache)}

/-- Accepted common registration runs the original builder and source reinstall. Its executable copy contains only an empty cache placeholder. -/
noncomputable def build (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) :
    OracleComp HashSpec (RustM (Option PqxdhServerRegistrationPublication.Response) ×
      PqxdhRegistrationProtocolState.State M P I D K A S B) := do
  let current := PqxdhRegistrationProtocolState.consume index ready (withCache state ∅)
  let selected := PqxdhRegistrationProtocolState.input sender index metadata current
  let result ← (simulateQ (compiler source writer callbacks)
    (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
      (PqxdhAcceptedRegistration.buildReady source selected.binding ready metadata selected.state))).run current.primitive.1
  pure (PqxdhRegistrationProtocolState.reinstall index current (result.1, (result.2, ∅)))

set_option backward.isDefEq.respectTransparency false in
/-- The literal accepted builder, including successful publication, allocation rejection and diagnostic branches, preserves the complete actual source poststate and reached cache. -/
theorem build_source (sender : M → Std.U64) (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (state : PqxdhRegistrationProtocolState.State M P I D K A S B) (cache : CtxRO.QueryCache) :
    (fun result => (result.1.1, withCache result.1.2 result.2)) <$>
      (simulateQ hashImpl (build source writer callbacks sender index metadata ready state)).run cache =
      (PqxdhRegistrationProtocolState.build source writer (PqxdhSourceAuxiliary.server callbacks) sender index metadata ready).run
        (withCache state cache) := by
  have original := program source writer callbacks
    (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
      (PqxdhAcceptedRegistration.buildReady source
        (PqxdhRegistrationProtocolState.input sender index metadata
          (PqxdhRegistrationProtocolState.consume index ready (withCache state ∅))).binding
        ready metadata (PqxdhRegistrationProtocolState.input sender index metadata
          (PqxdhRegistrationProtocolState.consume index ready (withCache state ∅))).state)) state.primitive.1 cache
  have mapped := congrArg (fun work =>
    PqxdhRegistrationProtocolState.reinstall index
      (PqxdhRegistrationProtocolState.consume index ready (withCache state cache)) <$> work) original
  simp only [build, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
  simp only [Functor.map_map] at mapped
  convert mapped using 1
  · congr 1
    funext result
    rcases result with ⟨⟨value, auxiliary⟩, cache⟩
    cases value <;> rfl
  · rfl

end BeaconcryptCore.Computational.PqxdhCommonSharedRegistration


/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedRegistration.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedRegistration.step

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedRegistration.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedRegistration.program

/-- info: 'BeaconcryptCore.Computational.PqxdhCommonSharedRegistration.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCommonSharedRegistration.build_source

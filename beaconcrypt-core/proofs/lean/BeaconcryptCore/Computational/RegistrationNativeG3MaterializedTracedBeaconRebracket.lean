-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconTrace
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconComplete

/-! The complete actual local Beacon chronology reassociates into the private key/trace/receipt/World state. The observed fallback is executable and mode-independent; preparation and KEM callbacks keep their exact original replies and effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconRebracket
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {KemSK KeyState Value : Type}
abbrev Spec (n : Nat) (KemSK : Type) := RegistrationBeaconReferenceCompiler.Spec n KemSK
abbrev Old (n : Nat) (KeyState : Type) := RegistrationNativeG3MaterializedFrontend.State n KeyState
abbrev New (n : Nat) (KeyState : Type) := RegistrationNativeG3MaterializedTracedServerFrontend.State n KeyState

def join (trace : RegistrationNativeG2Trace.State) (before : Old n KeyState) : New n KeyState := (before.1, (trace, before.2))
def result (reached : (Value × RegistrationNativeG2Trace.State) × Old n KeyState) : Value × New n KeyState :=
  (reached.1.1, join reached.1.2 reached.2)

noncomputable def fallback (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp)) :
    QueryImpl (Spec n KemSK) (StateT (New n KeyState) ProbComp) := fun query before =>
  result <$> (simulateQ implementation ((RegistrationNativeG3MaterializedTracedBeaconTrace.handler query).run before.2.1)).run (before.1, before.2.2)

private theorem state_map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Every actual callback retains the same complete trace and source state under this exact rebracketing. -/
theorem query_source (full : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp))
    (query : (Spec n KemSK).Domain) (trace : RegistrationNativeG2Trace.State) (before : Old n KeyState) :
    result <$> (simulateQ (RegistrationNativeG3MaterializedBeaconComplete.localImpl full source writer sign seeds service implementation)
      ((RegistrationNativeG3MaterializedTracedBeaconTrace.handler query).run trace)).run before =
      (RegistrationNativeG3MaterializedTracedBeaconComplete.localImpl full source writer sign seeds service (fallback implementation) query).run (join trace before) := by
  rcases query with message | (message | (publication | effect)) | kem
  · rfl
  · cases full <;> simp only [RegistrationNativeG3MaterializedTracedBeaconTrace.handler, StateT.run,
      RegistrationNativeG3MaterializedTracedBeaconTrace.begin, RegistrationNativeG3MaterializedTracedBeaconTrace.finish,
      simulateQ_map, simulateQ_spec_query, RegistrationNativeG3MaterializedBeaconComplete.localImpl,
      RegistrationNativeG3MaterializedBeaconComplete.paired, RegistrationNativeG3MaterializedFrontend.known,
      RegistrationNativeG3MaterializedFrontend.thin, RegistrationNativeG3MaterializedFrontend.keys,
      RegistrationNativeG3MaterializedTracedBeaconComplete.localImpl, RegistrationNativeG3MaterializedTracedBeaconComplete.paired,
      RegistrationNativeG3MaterializedTracedServerFrontend.known, RegistrationNativeG3MaterializedTracedServerFrontend.thin,
      RegistrationNativeG3MaterializedTracedServerFrontend.keys, Functor.map_map, join, result,
      Bool.false_eq_true, ite_true, ite_false, state_map_apply, Prod.map_def, id_eq]
    all_goals rfl
  · cases full <;> simp only [RegistrationNativeG3MaterializedTracedBeaconTrace.handler, StateT.run,
      RegistrationNativeG3MaterializedTracedBeaconTrace.begin, RegistrationNativeG3MaterializedTracedBeaconTrace.finish,
      simulateQ_map, simulateQ_spec_query, RegistrationNativeG3MaterializedBeaconComplete.localImpl,
      RegistrationNativeG3MaterializedBeaconComplete.paired, RegistrationNativeG3MaterializedFrontend.known,
      RegistrationNativeG3MaterializedFrontend.thin, RegistrationNativeG3MaterializedFrontend.common,
      RegistrationNativeG3MaterializedTracedBeaconComplete.localImpl, RegistrationNativeG3MaterializedTracedBeaconComplete.paired,
      RegistrationNativeG3MaterializedTracedServerFrontend.known, RegistrationNativeG3MaterializedTracedServerFrontend.thin,
      RegistrationNativeG3MaterializedTracedServerFrontend.common, RegistrationNativeG3MaterializedTracedServerCommon.handler,
      RegistrationNativeG3MaterializedTracedServerCommon.onCommon, RegistrationNativeG3Common.handler,
      RegistrationNativeG3MaterializedCommon.handler, Functor.map_map, join, result,
      Bool.false_eq_true, ite_true, ite_false, state_map_apply, Prod.map_def, id_eq]
  · cases full <;> cases effect with
    | inl coin =>
        simp [RegistrationNativeG3MaterializedTracedBeaconTrace.handler, StateT.run,
          RegistrationNativeG3MaterializedTracedBeaconTrace.begin, RegistrationNativeG3MaterializedTracedBeaconTrace.finish,
          RegistrationNativeG3MaterializedBeaconComplete.localImpl, RegistrationNativeG3MaterializedBeaconComplete.paired,
          RegistrationNativeG3MaterializedTracedBeaconComplete.localImpl, RegistrationNativeG3MaterializedTracedBeaconComplete.paired,
          RegistrationNativeG3MaterializedTracedServerFrontend.known, RegistrationNativeG3MaterializedTracedServerFrontend.thin,
          RegistrationNativeG3MaterializedTracedServerFrontend.common, RegistrationNativeG3MaterializedFrontend.known,
          RegistrationNativeG3MaterializedFrontend.thin, RegistrationNativeG3MaterializedFrontend.common,
          RegistrationNativeG3MaterializedTracedServerCommon.handler, RegistrationNativeG3MaterializedTracedServerCommon.effect,
          RegistrationNativeG3MaterializedTracedServerCommon.effectQuery, RegistrationNativeG3Common.handler,
          RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.handler,
          RegistrationNativeG3MaterializedCommon.effect, join, result, Functor.map_map, state_map_apply, Prod.map_def, id_eq]
    | inr capability =>
        cases capability
        all_goals try (rename_i first second kernel; guard_hyp kernel : PqxdhRecordLiftInterface.KernelRef n; cases kernel)
        all_goals simp [RegistrationNativeG3MaterializedTracedBeaconTrace.handler, StateT.run,
          RegistrationNativeG3MaterializedTracedBeaconTrace.begin, RegistrationNativeG3MaterializedTracedBeaconTrace.finish,
          RegistrationNativeG3MaterializedBeaconComplete.localImpl, RegistrationNativeG3MaterializedBeaconComplete.paired,
          RegistrationNativeG3MaterializedTracedBeaconComplete.localImpl, RegistrationNativeG3MaterializedTracedBeaconComplete.paired,
          RegistrationNativeG3MaterializedTracedServerFrontend.known, RegistrationNativeG3MaterializedTracedServerFrontend.thin,
          RegistrationNativeG3MaterializedTracedServerFrontend.common, RegistrationNativeG3MaterializedFrontend.known,
          RegistrationNativeG3MaterializedFrontend.thin, RegistrationNativeG3MaterializedFrontend.common,
          RegistrationNativeG3MaterializedTracedServerCommon.handler, RegistrationNativeG3MaterializedTracedServerCommon.effect,
          RegistrationNativeG3MaterializedTracedServerCommon.effectQuery, RegistrationNativeG3Common.handler,
          RegistrationNativeG3Common.effect, RegistrationNativeG3MaterializedCommon.handler,
          RegistrationNativeG3MaterializedCommon.effect, join, result, Functor.map_map, state_map_apply, Prod.map_def, id_eq]
  · rfl

/-- The whole adaptive local source retains its original complete chronology and private state. -/
theorem program_source (full : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (Spec n KemSK) (StateT (Old n KeyState) ProbComp))
    (work : OracleComp (Spec n KemSK) Value) (trace : RegistrationNativeG2Trace.State) (before : Old n KeyState) :
    result <$> (simulateQ (RegistrationNativeG3MaterializedBeaconComplete.localImpl full source writer sign seeds service implementation)
      ((simulateQ RegistrationNativeG3MaterializedTracedBeaconTrace.handler work).run trace)).run before =
      (simulateQ (RegistrationNativeG3MaterializedTracedBeaconComplete.localImpl full source writer sign seeds service (fallback implementation)) work).run (join trace before) := by
  induction work using OracleComp.inductionOn generalizing trace before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query_source full source writer sign seeds service implementation query trace before]
      simp only [bind_map_left, result, ]
      apply bind_congr
      intro reached
      exact ih reached.1.1 reached.1.2 reached.2
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconRebracket
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconRebracket.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconRebracket.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconRebracket.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedBeaconRebracket.program_source

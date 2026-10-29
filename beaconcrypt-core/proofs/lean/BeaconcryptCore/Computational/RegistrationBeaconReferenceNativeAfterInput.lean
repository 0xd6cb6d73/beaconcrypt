-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeContinuation

/-! Incoming completion never reads the private record-request analysis ledger. Its complete source callback and terminal-phase continuation therefore have identical projected outputs with that ledger cleared on input. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAfterInput
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeRecord (erase environment)
open RegistrationBeaconReferenceNativeContinuation (view sourceAfter)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

private theorem lift_run {Value : Type} (work : OracleComp (Trusted n KemSK) Value)
    (before : RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary) :
    (liftM work : StateT (RegistrationBeaconReferenceNativeRecord.Flat mlSource Auxiliary)
      (OracleComp (Trusted n KemSK)) Value).run before = (fun result => (result, before)) <$> work := by
  change (work >>= fun result => pure (result, before)) = _
  exact bind_pure_comp _ _

/-- Every native incoming record program has precisely the actual effect program after its explicit request ledger is projected. -/
theorem record_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (env : EnvState Auxiliary) :
    Prod.map id erase <$>
      (simulateQ (RegistrationBeaconReferenceNativeOwner.record (n := n) (mlSource := mlSource) setup wire) work).run env =
      (fun value => (value, erase env)) <$>
        simulateQ environment (simulateQ (RegistrationBeaconRecordSourceProgram.native setup.source wire.frameWrite) work) := by
  have actual := RegistrationBeaconReferenceNativeRecord.program (n := n) (mlSource := mlSource) setup wire work ([], env)
  rw [OracleComp.simulateQ_flattenStateT_run, RegistrationBeaconReferenceNativeOwner.record_program] at actual
  have viewed := congrArg (fun script => Prod.map id Prod.snd <$> script) actual
  simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, Prod.map_def, id_eq,
    RegistrationBeaconReferenceNativeRecord.project, RegistrationBeaconReferenceNativeRecord.target,
    simulateQ_liftTarget, lift_run, QueryImpl.simulateQ_compose] using viewed

private theorem after_same (owner current : Owner mlSource) (result : RustM RegistrationBeaconRecordExecutor.Result)
    (env : EnvState Auxiliary) :
    view <$> ((RegistrationBeaconReferenceNativeOwner.after (n := n) (KemSK := KemSK) owner result).run current).run env =
      view <$> ((RegistrationBeaconReferenceNativeOwner.after (n := n) (KemSK := KemSK) owner result).run current).run (erase env) := by
  unfold RegistrationBeaconReferenceNativeContinuation.view
  have first := RegistrationBeaconReferenceNativeKnown.after_project (n := n) (KemSK := KemSK) owner current result env
  have second := RegistrationBeaconReferenceNativeKnown.after_project (n := n) (KemSK := KemSK) owner current result (erase env)
  simpa only [erase] using first.trans second.symm

/-- The full native agreement continuation preserves all source effects and public owner fields while ignoring only the prior record-request analysis ledger. -/
theorem source_after_input (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner current : Owner mlSource) (result : RustM agreement.AgreementEffect) (env : EnvState Auxiliary) :
    view <$> ((sourceAfter (n := n) setup wire owner result).run current).run env =
      view <$> ((sourceAfter (n := n) setup wire owner result).run current).run (erase env) := by
  cases result with
  | fail error | div => rfl
  | ok result =>
      cases result <;> try rfl
      rename_i completed
      have first := record_program (n := n) (mlSource := mlSource) setup wire (RegistrationBeaconRecordExecutor.begin completed) env
      have second := record_program (n := n) (mlSource := mlSource) setup wire (RegistrationBeaconRecordExecutor.begin completed) (erase env)
      have records : Prod.map id erase <$>
          (simulateQ (RegistrationBeaconReferenceNativeOwner.record (n := n) (mlSource := mlSource) setup wire)
            (RegistrationBeaconRecordExecutor.begin completed)).run env =
          Prod.map id erase <$>
            (simulateQ (RegistrationBeaconReferenceNativeOwner.record (n := n) (mlSource := mlSource) setup wire)
              (RegistrationBeaconRecordExecutor.begin completed)).run (erase env) := by
        simpa only [erase] using first.trans second.symm
      have continued := congrArg (fun script => script >>= fun reached =>
        view <$> ((RegistrationBeaconReferenceNativeOwner.after (n := n) (KemSK := KemSK) owner reached.1).run current).run reached.2) records
      simp only [sourceAfter, RegistrationBeaconReferenceNativeKnown.postRoot, StateT.run_bind,
        StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
      simp only [bind_map_left] at continued
      have firstAfter : ∀ (result : RustM RegistrationBeaconRecordExecutor.Result) (nextEnv : EnvState Auxiliary),
          view <$> ((RegistrationBeaconReferenceNativeOwner.after (n := n) (KemSK := KemSK) owner result).run current).run nextEnv =
            view <$> ((RegistrationBeaconReferenceNativeOwner.after (n := n) (KemSK := KemSK) owner result).run current).run (erase nextEnv) :=
        fun result nextEnv => after_same owner current result nextEnv
      calc
        _ = _ := by
          apply bind_congr
          rintro ⟨result, nextEnv⟩
          exact firstAfter result nextEnv
        _ = _ := continued
        _ = _ := by
          apply bind_congr
          rintro ⟨result, nextEnv⟩
          exact (firstAfter result nextEnv).symm

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAfterInput

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAfterInput.record_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAfterInput.record_program
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAfterInput.source_after_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeAfterInput.source_after_input

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeCallbacks
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord

/-! Actual agreement callbacks update their own request log and retain the unrelated record-request analysis ledger. Clearing only that ledger therefore commutes with every agreement continuation and its full external effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceNativeRecord (erase)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Actual agreement operands and results do not inspect the record analysis ledger. -/
theorem query (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (request : RegistrationAgreementExecutor.Request) (env : EnvState Auxiliary) :
    Prod.map id erase <$>
      (RegistrationBeaconReferenceNativeCallbacks.source (n := n) setup scalar owner oneTime request).run env =
      (RegistrationBeaconReferenceNativeCallbacks.source (n := n) setup scalar owner oneTime request).run (erase env) := by
  cases request with
  | convertPublic key | convertSecret role | generate role | encapsulate key | decapsulate ciphertext | root request =>
      simp only [RegistrationBeaconReferenceNativeCallbacks.source, RegistrationBeaconRootInterpreter.sourceImpl,
        RegistrationBeaconReferenceSource.backend, RegistrationBeaconReferenceCompiler.trustedBackend,
        StateT.run_bind, StateT.run_modify, StateT.run_lift, StateT.run_map,
        pure_bind, bind_pure_comp, map_pure, Functor.map_map, Prod.map_def, id_eq, erase]
  | dh request =>
      cases role : request.secret_role <;>
        simp only [RegistrationBeaconReferenceNativeCallbacks.source, RegistrationBeaconRootInterpreter.sourceImpl,
          role, RegistrationBeaconReferenceSource.backend, RegistrationBeaconReferenceSource.visit,
          RegistrationBeaconReferenceCompiler.trustedBackend, StateT.run_bind, StateT.run_modify,
          StateT.run_lift, StateT.run_map, pure_bind, bind_pure_comp, map_pure, Functor.map_map,
          Prod.map_def, id_eq, erase]

/-- The entire actual native agreement program retains the same complete external execution when its unrelated record-request analysis ledger is cleared. -/
theorem program (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (env : EnvState Auxiliary) :
    Prod.map id erase <$>
      (simulateQ (RegistrationBeaconReferenceNativeCallbacks.source (n := n) setup scalar owner oneTime) work).run env =
      (simulateQ (RegistrationBeaconReferenceNativeCallbacks.source (n := n) setup scalar owner oneTime) work).run (erase env) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ erase (query setup scalar owner oneTime) work env

/-- The record-ledger projection also retains the whole concrete native World and private KEM pool after actual interpretation. -/
theorem native_program (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner : SelectedOwner mlSource) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value)
    (env : EnvState RegistrationServerRoleBackend.State)
    (native : RegistrationNativeExperiment.State n KemSK mlSource) :
    (fun result => (result.1, (erase result.2.1, result.2.2))) <$>
      (simulateQ (RegistrationBeaconReferenceNativeStage.native setup checks representation created scalar owner oneTime) work).run
        (env, native) =
      (simulateQ (RegistrationBeaconReferenceNativeStage.native setup checks representation created scalar owner oneTime) work).run
        (erase env, native) := by
  rw [← RegistrationBeaconReferenceNativeCallbacks.lower_program]
  have actual := congrArg (fun script =>
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) script).run native)
    (program (n := n) setup scalar owner oneTime work env)
  simp only [simulateQ_map, StateT.run_map] at actual
  simpa only [RegistrationBeaconReferenceNativeStage.lower, StateT.run, Functor.map_map,
    Prod.map_def, id_eq] using congrArg (fun script =>
      (fun result => (result.1.1, (result.1.2, result.2))) <$> script) actual

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger.query
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger.program
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeLedger.native_program

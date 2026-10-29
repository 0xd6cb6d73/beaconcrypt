-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRecordSourceProgram
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend

/-! Actual first-record callbacks retain the source environment, owner roster and external effects. Only the explicit record-request analysis ledger is projected; the actual source retains it for separate resource bounds. Hash callbacks keep their literal shared-World request and every optional primitive result remains the source result. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}
variable {Value : Type}

def erase (env : EnvState Auxiliary) : EnvState Auxiliary := { env with recordRequests := [] }

def environment : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n)
    (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) :=
  fun query => (RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl query)

/-- Every actual native callback is the concrete source program; only its explicit analysis marker is omitted. -/
theorem query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (request : RegistrationRecordPrimitives.Request) (owners : RegistrationNativeBeaconFrontend.State mlSource)
    (env : EnvState Auxiliary) :
    (fun result => (result.1, erase result.2)) <$>
      (((RegistrationNativeBeaconFrontend.record (n := n) setup wire request).run owners).run env) =
      (fun reply => ((reply, owners), erase env)) <$>
        simulateQ environment (RegistrationBeaconRecordSourceProgram.native setup.source wire.frameWrite request) := by
  cases request <;> first | rfl | (rename_i writing; cases writing <;> rfl)

abbrev Flat (source : RegistrationNativeMldsa.Source) (Auxiliary : Type) :=
  RegistrationNativeBeaconFrontend.State source × EnvState Auxiliary

def project (state : Flat mlSource Auxiliary) : Flat mlSource Auxiliary := (state.1, erase state.2)

noncomputable def target (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) :
    QueryImpl RegistrationRecordPrimitives.Spec
      (StateT (Flat mlSource Auxiliary) (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK))) :=
  (environment (n := n) (KemSK := KemSK) ∘ₛ RegistrationBeaconRecordSourceProgram.native (n := n) setup.source wire.frameWrite).liftTarget _

private theorem lift_run (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : Flat mlSource Auxiliary) :
    (liftM work : StateT (Flat mlSource Auxiliary)
      (OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK)) Value).run before =
      (fun reply => (reply, before)) <$> work := by
  change (work >>= fun reply => pure (reply, before)) = _
  exact bind_pure_comp _ _

private theorem query_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (request : RegistrationRecordPrimitives.Request) (before : Flat mlSource Auxiliary) :
    Prod.map id project <$>
      ((RegistrationNativeBeaconFrontend.record (n := n) setup wire).flattenStateT request).run before =
      (target setup wire request).run (project before) := by
  have law := congrArg (fun computation => (fun result => (result.1.1, (result.1.2, result.2))) <$> computation)
    (query (n := n) setup wire request before.1 before.2)
  rw [target, QueryImpl.liftTarget_apply, lift_run]
  simpa only [QueryImpl.flattenStateT, StateT.run, StateT.mk, QueryImpl.apply_compose,
    Functor.map_map, Prod.map_def, id_eq, project, Function.comp_def] using law

/-- Arbitrary source record programs retain every owner/environment field after the stated analysis-only ledger projection. -/
theorem program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : Flat mlSource Auxiliary) :
    Prod.map id project <$>
      (simulateQ (RegistrationNativeBeaconFrontend.record (n := n) setup wire).flattenStateT work).run before =
      (simulateQ (target setup wire) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query_project setup wire) work before

/-- The actual native initial64/ongoing76 controller consumes the same bound source entry and public hash program. No kernel is reset after sequence one. -/
theorem controller (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (erased : Std.Array U8 357#usize) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (root : PqxdhSecretInputKdf.RootOutput) (before : Flat mlSource Auxiliary) :
    Prod.map id project <$>
      (simulateQ (RegistrationNativeBeaconFrontend.record (n := n) setup wire).flattenStateT
        (RegistrationBeaconRecordExecutor.begin (RegistrationBeaconBoundSource.atRoot descriptor root))).run before =
      (fun reply => (reply, project before)) <$>
        simulateQ environment (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite)
          (RegistrationNativePairedBeaconService.program setup.source descriptor
            (PqxdhServerAuthKeySchedule.fromRoot setup.source root))) := by
  rw [program, target, simulateQ_liftTarget]
  simp only [lift_run, QueryImpl.simulateQ_compose,
    RegistrationBeaconRecordSourceProgram.controller_source setup.source wire.frameWrite erased]


end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord.query

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord.program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord.controller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord.controller

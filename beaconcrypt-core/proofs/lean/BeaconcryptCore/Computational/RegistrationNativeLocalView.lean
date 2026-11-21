-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldViewAuthentication
import BeaconcryptCore.Computational.RegistrationStateView

/-! Agreement and first-record callbacks preserve their actual replies and all operational state under the private native, coin-effect and record-kind log view. The actual agreement log, signing receipts and shared cache remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLocalView
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
open RegistrationServerRecordWorldSource (project)
variable {n : Nat} {Auxiliary Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Applying the local source view twice retains its complete state. -/
theorem project_idempotent (before : State n Auxiliary) : project (project before) = project before := by
  simp only [project, RegistrationNativeWorldView.project_idempotent]

/-- Source agreement reads no omitted accounting coordinate and retains the entire chronological agreement log. -/
theorem agreement_input (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (query : RegistrationAgreementExecutor.Request) (before : State n Auxiliary) :
    Prod.map id project <$> (RegistrationWorldAgreement.agreement source primitive query).run before =
      Prod.map id project <$> (RegistrationWorldAgreement.agreement source primitive query).run (project before) := by
  have first := RegistrationNativeWorldView.sampled
    ((RegistrationAgreementShared.auxiliary source primitive query).run before.auxiliary) before.world.1
  have second := RegistrationNativeWorldView.sampled
    ((RegistrationAgreementShared.auxiliary source primitive query).run before.auxiliary)
      (RegistrationNativeWorldView.project before.world.1)
  rw [RegistrationNativeWorldView.project_idempotent] at second
  have law := congrArg (fun distribution => (fun result => (result.1.1,
    RegistrationWorldAgreement.State.mk result.1.2 (before.requests ++ RegistrationWorldAgreement.recorded query)
      [] (result.2, before.world.2))) <$> distribution) (first.trans second.symm)
  simpa only [RegistrationWorldAgreement.agreement, StateT.run, Functor.map_map,
    Prod.map, id_eq, project, Function.comp_def] using law

/-- Arbitrary native agreement programs keep every optional reply and reached local poststate. -/
theorem agreement_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (before : State n Auxiliary) :
    Prod.map id project <$> (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run before =
      Prod.map id project <$> (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run (project before) :=
  RegistrationStateView.program_stable project project_idempotent _ (agreement_input source primitive) work before

/-- Actual native record callbacks read the same full cache and retain their actual uniform sampling. -/
theorem record_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : State n Auxiliary) :
    Prod.map id project <$> (RegistrationWorldRecords.record setup codec query).run before =
      Prod.map id project <$> (RegistrationWorldRecords.record setup codec query).run (project before) := by
  have law := congrArg (fun distribution => (fun result => (result.1,
    { project before with world := ({ (project before).world.1 with primitive := result.2 }, before.world.2) })) <$> distribution)
    (RegistrationNativeWorldViewRecords.primitive_input setup codec query before.world.1.primitive)
  simpa only [RegistrationWorldRecords.record, StateT.run, Functor.map_map, Prod.map, id_eq,
    project, RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
    RegistrationWorldCoinCompiler.eraseCoin, RegistrationNativeWorldViewRecords.primitiveView,
    Function.comp_def, Function.update_idem] using law

/-- Hash and ordinary record branches preserve the same actual shared-cache operation. -/
theorem shared_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : State n Auxiliary) :
    Prod.map id project <$> (RegistrationWorldRecords.shared setup codec query).run before =
      Prod.map id project <$> (RegistrationWorldRecords.shared setup codec query).run (project before) := by
  cases query with
  | inr query => exact record_input setup codec query before
  | inl query =>
      have law := congrArg (fun distribution => (fun result => (result.1,
        { project before with world := (result.2, before.world.2) })) <$> distribution)
        (RegistrationNativeWorldViewEffects.effects_input (.inr (.hash query.2)) before.world.1)
      simpa only [RegistrationWorldRecords.shared, StateT.run, Functor.map_map,
        Prod.map, id_eq, project, Function.comp_def] using law

/-- Actual first-record callback logging changes only the omitted request-kind list. -/
theorem handler_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : State n Auxiliary) :
    Prod.map id project <$> (RegistrationWorldRecords.handler setup codec query).run before =
      Prod.map id project <$> (RegistrationWorldRecords.handler setup codec query).run (project before) := by
  have law := RegistrationStateView.program_stable project project_idempotent
    (RegistrationWorldRecords.shared setup codec) (shared_input setup codec)
    (RegistrationRecordPrimitives.callbacks setup.source query) before
  simp only [RegistrationWorldRecords.handler, StateT.run, Functor.map_map,
    Prod.map, id_eq, project] at law ⊢
  exact law

/-- Whole first-record executions keep the actual ciphertext, full kernel and all failure branches. -/
theorem record_program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RegistrationRecordPrimitives.Spec Value) (before : State n Auxiliary) :
    Prod.map id project <$> (simulateQ (RegistrationWorldRecords.handler setup codec) work).run before =
      Prod.map id project <$> (simulateQ (RegistrationWorldRecords.handler setup codec) work).run (project before) :=
  RegistrationStateView.program_stable project project_idempotent _ (handler_input setup codec) work before

/-- Real World capabilities retain actual occupancy, insertion, hash and reservation outcomes. -/
theorem capability_input (query : PqxdhRecordLiftInterface.Capability n) (before : State n Auxiliary) :
    Prod.map id project <$> (RegistrationWorldServerCompletion.capability query).run before =
      Prod.map id project <$> (RegistrationWorldServerCompletion.capability query).run (project before) := by
  have law := congrArg (fun distribution => (fun result => (result.1,
    { project before with world := (result.2, before.world.2) })) <$> distribution)
    (RegistrationNativeWorldViewEffects.effects_input (.inr query) before.world.1)
  simpa only [RegistrationWorldServerCompletion.capability, StateT.run, Functor.map_map,
    Prod.map, id_eq, project, Function.comp_def] using law

end BeaconcryptCore.Computational.RegistrationNativeLocalView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.project_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.project_idempotent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.agreement_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.agreement_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.agreement_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.agreement_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.record_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.record_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.shared_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.shared_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.handler_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.handler_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.record_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.record_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalView.capability_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalView.capability_input

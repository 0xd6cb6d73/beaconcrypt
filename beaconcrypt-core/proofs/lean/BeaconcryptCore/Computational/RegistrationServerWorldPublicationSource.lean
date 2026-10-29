-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerPublicationWorldCompiler
import BeaconcryptCore.Computational.RegistrationServerWorldSigningLift

/-! Actual native first-record and outgoing ML publication compose through their real optional results before peer insertion. Their source and bound108 forms have the same complete semantic World, actual published kernel and chronological signing receipts under the explicit instrumentation view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRecordWorldSource (project)
open RegistrationServerPublicationWorldCompiler (publication effect effect_program)
variable {n : Nat} {Auxiliary ι KemSK Reader Response Encoded : Type} {base : OracleSpec ι}

/-- The full native raw initial64/76 source and the actual bound108 raw component have the same complete source-view distribution. -/
theorem raw_factored (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (initial : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      (simulateQ (publication setup.source codec.frameWrite sign)
        (simulateQ RegistrationBoundPublication.rawLift
          (simulateQ RegistrationRawSealBridge.nativeAdapter
            (RegistrationBoundKeySchedule.factored (RegistrationBoundKeySchedule.publicInitial initial)
              (PqxdhServerAuthKeySchedule.fromRoot setup.source root))))).run before =
      Prod.map id project <$>
        (simulateQ (RegistrationWorldRecords.handler setup codec)
          (RegistrationServerRecordExecutor.fromInitial initial)).run before := by
  rw [RegistrationServerPublicationWorldCompiler.raw_program]
  calc
    _ = Prod.map id project <$>
        (simulateQ (RegistrationServerRecordWorldSource.target setup.source codec.frameWrite)
          (RegistrationBoundKeySchedule.factored (RegistrationBoundKeySchedule.publicInitial initial)
            (PqxdhServerAuthKeySchedule.fromRoot setup.source root))).run before := by
      rw [effect_program, RegistrationServerRecordWorldSource.target_program,
        RegistrationServerRecordSourceProgram.native, QueryImpl.simulateQ_compose]
    _ = _ := by
      rw [RegistrationServerRecordTargetProjection.program,
        RegistrationServerRecordWorldSource.target_program,
        RegistrationServerRecordSourceProgram.native, QueryImpl.simulateQ_compose]
      exact (RegistrationServerRecordWorldSource.initial setup codec initial root role before).symm

noncomputable def after
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) :
    RustM RegistrationServerRecordExecutor.Result → StateT (RegistrationWorldAgreement.State n Auxiliary)
      ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded))
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .ok (.Ok pending) => RegistrationWorldServerCompletion.signing sign encode pending

/-- Every native record outcome resumes the actual source publication controller, preserving late failure and signing history. -/
theorem after_source
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (record : RustM RegistrationServerRecordExecutor.Result) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> (after sign encode record).run before = (after sign encode record).run (project before) := by
  cases record with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err previous => rfl
      | Ok pending =>
          simp only [after, RegistrationServerWorldSigningLift.completion]
          exact RegistrationServerSigningWorldSource.source_program sign _ before

/-- The actual source compiler resumes the same native public record result on the current World and chronological receipts. -/
theorem after_compiler (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (record : RustM RegistrationServerRecordExecutor.Result) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      (simulateQ (publication hkdf writer sign) (RegistrationBoundPublication.after encode record)).run before =
        (after sign encode record).run (project before) := by
  cases record with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err previous => rfl
      | Ok pending =>
          simp only [RegistrationBoundPublication.after, RegistrationServerPublicationWorldCompiler.signing_program,
            after, RegistrationServerWorldSigningLift.completion]
          exact RegistrationServerSigningWorldSource.compiler_program hkdf writer sign _ before

noncomputable def source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (initial : registration.ServerInitialKdf) :
    StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded)) := do
  let record ← simulateQ (RegistrationWorldRecords.handler setup codec)
    (RegistrationServerRecordExecutor.fromInitial initial)
  after sign encode record

/-- The complete actual first-record/hash/sign/encode/publication experiment is the bound108 component on the same semantic World, before the actual native peer insertion. -/
theorem publication_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (initial : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      (simulateQ (publication setup.source codec.frameWrite sign)
        (RegistrationBoundPublication.program encode (RegistrationBoundKeySchedule.publicInitial initial)
          (PqxdhServerAuthKeySchedule.fromRoot setup.source root))).run before =
      Prod.map id project <$> (source setup codec sign encode initial).run before := by
  have raw := congrArg (fun distribution => distribution >>= fun result => (after sign encode result.1).run result.2)
    (raw_factored setup codec sign initial root role before)
  simp only [RegistrationBoundPublication.program, source, simulateQ_bind, StateT.run_bind, map_bind]
  simp only [after_compiler, after_source]
  simpa only [bind_map_left, Prod.map_def, id_eq] using raw

end BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.raw_factored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.raw_factored
/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.after_source
/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.after_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.after_compiler
/-- info: 'BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.publication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource.publication_source

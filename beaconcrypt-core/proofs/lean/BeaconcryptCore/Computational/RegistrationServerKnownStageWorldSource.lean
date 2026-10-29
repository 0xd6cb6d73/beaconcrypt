-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerWorldPublicationSource
import BeaconcryptCore.Computational.RegistrationServerKnownInstallProjection

/-! The bound108 Server known branch runs the actual first record, hash/ML signature, dynamic encoder, completed-kernel insertion and publication finish. The complete semantic World is retained through all failures under the explicit source analysis view. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRecordWorldSource (project)
open RegistrationServerPublicationWorldCompiler (publication effect)
variable {n : Nat} {Auxiliary ι KemSK Reader Response Encoded Value : Type} {base : OracleSpec ι}

noncomputable def common (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePairedServerService.Common n)
      (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp)
  | .inl query => publication hkdf writer sign query
  | .inr query => effect query

/-- Actual publication queries keep their same current-World/receipt compiler. -/
theorem publication_program (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Value) :
    simulateQ (common (n := n) (Auxiliary := Auxiliary) hkdf writer sign)
      (simulateQ RegistrationHiddenInstall.publicationLift work) = simulateQ (publication hkdf writer sign) work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreter => simulateQ interpreter work)
  funext query
  simp only [QueryImpl.apply_compose, RegistrationHiddenInstall.publicationLift, simulateQ_spec_query, common]

/-- Actual occupancy/installation effects keep the same current World. -/
theorem effect_program (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    simulateQ (common (Auxiliary := Auxiliary) hkdf writer sign)
      (simulateQ RegistrationHiddenInstall.effectLift work) = simulateQ effect work := by
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun interpreter => simulateQ interpreter work)
  funext query
  simp only [QueryImpl.apply_compose, RegistrationHiddenInstall.effectLift, simulateQ_spec_query, common]

noncomputable def source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : registration.ServerInitialKdf) :
    StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp
      (RustM (RegistrationWorldServerCompletion.Result Encoded)) := do
  let published ← RegistrationServerWorldPublicationSource.source setup codec sign encode initial
  RegistrationServerKnownInstallProjection.after control published

/-- Composing actual native record/publication and known insertion is literally the source SDK fromInitial component. -/
theorem source_exact (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : registration.ServerInitialKdf) :
    source (n := n) (Auxiliary := Auxiliary) setup codec sign encode control initial =
      RegistrationWorldServerCompletion.fromInitial setup codec sign encode control initial := by
  funext before
  change (source setup codec sign encode control initial).run before =
    (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control initial).run before
  simp only [source, RegistrationServerWorldPublicationSource.source,
    RegistrationWorldServerCompletion.fromInitial, StateT.run_bind, bind_assoc]
  apply bind_congr
  rintro ⟨record, current⟩
  cases record with
  | fail error => rfl
  | div => rfl
  | ok result =>
      cases result with
      | Err previous => rfl
      | Ok pending =>
          simp only [RegistrationServerWorldPublicationSource.after, ]
          apply bind_congr
          rintro ⟨published, state⟩
          cases published with
          | fail error => rfl
          | div => rfl
          | ok result => cases result <;> rfl

/-- The interpreted known material branch is exactly its real record/publication program followed by actual native insertion. -/
theorem known_stage (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output) :
    simulateQ (common (n := n) (Auxiliary := Auxiliary) hkdf writer sign)
        (RegistrationNativePairedServerService.knownStage encode control initial output) = (do
      let published ← simulateQ (publication hkdf writer sign) (RegistrationBoundPublication.program encode initial output)
      RegistrationServerKnownInstallProjection.after control published) := by
  simp only [RegistrationNativePairedServerService.knownStage, simulateQ_bind,
    publication_program, effect_program]
  apply congrArg (fun continuation =>
    simulateQ (publication hkdf writer sign) (RegistrationBoundPublication.program encode initial output) >>= continuation)
  funext published
  rw [RegistrationServerKnownInstallWorldSource.after]
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

/-- The entire known bound108 Server service is the concrete native source fromInitial controller, with no source-program equality premise. -/
theorem native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (initial : registration.ServerInitialKdf) (root : PqxdhSecretInputKdf.RootOutput)
    (role : initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root)) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      (simulateQ (common setup.source codec.frameWrite sign)
        (RegistrationNativePairedServerService.knownStage encode control (RegistrationBoundKeySchedule.publicInitial initial)
          (PqxdhServerAuthKeySchedule.fromRoot setup.source root))).run before =
      Prod.map id project <$>
        (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control initial).run before := by
  rw [known_stage, ← source_exact]
  have published := congrArg (fun distribution => distribution >>= fun result =>
    (RegistrationServerKnownInstallProjection.after control result.1).run result.2)
    (RegistrationServerWorldPublicationSource.publication_source setup codec sign encode initial root role before)
  simp only [source, StateT.run_bind, map_bind]
  simp only [RegistrationServerKnownInstallProjection.after_project]
  simpa only [bind_map_left, Prod.map_def, id_eq] using published

end BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.publication_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.publication_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.effect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.effect_program
/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.source_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.source_exact
/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.known_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.known_stage
/-- info: 'BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerKnownStageWorldSource.native

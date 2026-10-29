-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallAfter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallPublication

/-! Actual paired material branches have one successful own-role descriptor precisely when their original public result succeeds. Raw publication/opening/signature failures and rejected insertion Bool replies have no successful suffix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBranch
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordInstallOrdinals (messages)
open RegistrationNativeSecretWordInstallInsert (success effects)
open RegistrationNativeSecretWordInstallPublication (publication)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativePairedServerService (Common)
variable {n : Nat} {KemSK Value Encoded : Type}

def common : QueryImpl (Common n) (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) :=
  fun query => (RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inr query))))

def rawPublication : QueryImpl RegistrationRawSealBridge.Spec (OracleComp RegistrationBoundPublication.Spec) :=
  fun query => RegistrationBoundPublication.Spec.query (.inl query)

private theorem publication_program (work : OracleComp RegistrationBoundPublication.Spec Value) :
    simulateQ (common (n := n) (KemSK := KemSK)) (simulateQ RegistrationHiddenInstall.publicationLift work) =
      simulateQ publication work := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

private theorem effects_program (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    simulateQ (common (KemSK := KemSK)) (simulateQ RegistrationHiddenInstall.effectLift work) = simulateQ effects work := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

private theorem raw_program (work : OracleComp RegistrationRawSealBridge.Spec Value) :
    simulateQ (common (n := n) (KemSK := KemSK)) (simulateQ RegistrationNativePairedBeaconService.rawLift work) =
      simulateQ publication (simulateQ rawPublication work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  rfl

/-- Each actual Server branch retains the complete native successful descriptor bill, including the branch's publication failures. -/
theorem server (role : Role) (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : RegistrationNativePairedChoice.Choice n) (before : State) (message : Message)
    (active : before.current = some message)
    (result : RustM (RegistrationNativePairedServerService.Result Encoded) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (common (KemSK := KemSK))
      (RegistrationNativePairedServerService.publicBranch encode control initial choice))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1 = true then [message] else [] := by
  cases choice with
  | known output =>
      simp only [RegistrationNativePairedServerService.publicBranch, RegistrationNativePairedServerService.knownStage,
        simulateQ_bind, publication_program, effects_program] at supported
      rw [StateT.run_bind, RegistrationNativeSecretWordInstallPublication.source, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨published, _called, continued⟩ := supported
      exact RegistrationNativeSecretWordInstallAfter.server role control published before message active result continued
  | hidden reference =>
      simp only [RegistrationNativePairedServerService.publicBranch, RegistrationNativePairedServerService.hiddenStage,
        simulateQ_bind, publication_program, effects_program] at supported
      rw [StateT.run_bind, RegistrationNativeSecretWordInstallPublication.source, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨published, _called, continued⟩ := supported
      exact RegistrationNativeSecretWordInstallAfter.server_hidden role control reference.slot published before message active result continued

/-- Each actual Beacon branch retains its same successful descriptor bill through all native raw opening and admission failures. -/
theorem beacon (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (choice : RegistrationNativePairedChoice.Choice n) (before : State) (message : Message)
    (active : before.current = some message)
    (result : RustM RegistrationNativePairedBeaconService.Result × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (common (KemSK := KemSK))
      (RegistrationNativePairedBeaconService.publicBranch source owner sender descriptor choice))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .beacon ∧ success result.1 = true then [message] else [] := by
  cases choice with
  | known output =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.knownStage,
        simulateQ_bind, raw_program, effects_program] at supported
      rw [StateT.run_bind, RegistrationNativeSecretWordInstallPublication.source, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨opened, _called, continued⟩ := supported
      exact RegistrationNativeSecretWordInstallAfter.beacon role owner sender (fun completed => .known completed.kernel) opened before message active result continued
  | hidden reference =>
      simp only [RegistrationNativePairedBeaconService.publicBranch, RegistrationNativePairedBeaconService.hiddenStage,
        RegistrationNativePairedBeaconService.privateHiddenStage, simulateQ_bind, raw_program, effects_program] at supported
      rw [StateT.run_bind, RegistrationNativeSecretWordInstallPublication.source, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨opened, _called, continued⟩ := supported
      exact RegistrationNativeSecretWordInstallAfter.beacon role owner sender (fun _ => .hidden reference.slot) opened before message active result continued
end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBranch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBranch.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBranch.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBranch.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallBranch.beacon

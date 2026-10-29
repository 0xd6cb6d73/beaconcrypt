-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallBranch
import BeaconcryptCore.Computational.RegistrationNativePairedMaterialSource

/-! The actual material getter records its own descriptor before the same successful branch installation. No previous demanded descriptor can supply the successful public callback's installation event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallAdmitted
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeG2Trace (State handler begin finish)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallInsert (success)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePairedMaterialSource (nativeLift)
variable {n : Nat} {KemSK Value Encoded : Type}

private theorem common_program (work : OracleComp (RegistrationNativePairedServerService.Common n) Value) :
    simulateQ (nativeLift (KemSK := KemSK)) (simulateQ RegistrationNativePairedServerService.publicCommon work) =
      simulateQ RegistrationNativeInstallBranch.common work := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

/-- The original admitted Server material branch installs precisely its own descriptor when its original result succeeds. -/
theorem server (role : Role) (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (reference : Message) (before : State)
    (result : RustM (RegistrationNativePairedServerService.Result Encoded) × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (nativeLift (n := n) (KemSK := KemSK))
      (RegistrationNativePairedServerService.publicAdmitted encode control initial reference))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1 = true then [reference] else [] := by
  simp only [RegistrationNativePairedServerService.publicAdmitted, simulateQ_bind, simulateQ_spec_query] at supported
  rw [StateT.run_bind] at supported
  simp only [nativeLift, simulateQ_spec_query, handler, StateT.run,
    begin, finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨chosen, _called, continued⟩ := supported
  cases chosen with
  | none =>
      change result ∈ support (pure (.ok (.Err control), ⟨some reference, before.events ++ [RegistrationNativeG2Trace.Event.demand reference]⟩) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) at continued
      rw [mem_support_pure_iff] at continued
      cases continued
      simp only [success, Bool.false_eq_true, and_false, ite_false, messages, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, List.append_nil]
  | some choice =>
      simp only [] at continued
      rw [common_program] at continued
      have bill := RegistrationNativeInstallBranch.server role encode control initial choice
        ⟨some reference, before.events ++ [RegistrationNativeG2Trace.Event.demand reference]⟩ reference rfl result (by simpa only [StateT.run] using continued)
      simpa only [messages, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.nil_append, List.append_nil] using bill

/-- The original admitted Beacon material branch installs precisely its own descriptor when its native public result succeeds. -/
theorem beacon (role : Role) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (reference : Message) (before : State)
    (result : RustM RegistrationNativePairedBeaconService.Result × State)
    (supported : result ∈ support ((simulateQ handler (simulateQ (nativeLift (n := n) (KemSK := KemSK))
      (RegistrationNativePairedBeaconService.admitted source owner sender descriptor reference))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .beacon ∧ success result.1 = true then [reference] else [] := by
  simp only [RegistrationNativePairedBeaconService.admitted, simulateQ_bind, simulateQ_spec_query] at supported
  rw [StateT.run_bind] at supported
  simp only [nativeLift, simulateQ_spec_query, handler, StateT.run,
    begin, finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨chosen, _called, continued⟩ := supported
  cases chosen with
  | none =>
      change result ∈ support (pure (.ok (.Err ⟨sender⟩), ⟨some reference, before.events ++ [RegistrationNativeG2Trace.Event.demand reference]⟩) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) at continued
      rw [mem_support_pure_iff] at continued
      cases continued
      simp only [success, Bool.false_eq_true, and_false, ite_false, messages, List.filterMap_append,
        List.filterMap_cons, List.filterMap_nil, List.append_nil]
  | some choice =>
      simp only [] at continued
      rw [common_program] at continued
      have bill := RegistrationNativeInstallBranch.beacon role source owner sender descriptor choice
        ⟨some reference, before.events ++ [RegistrationNativeG2Trace.Event.demand reference]⟩ reference rfl result (by simpa only [StateT.run] using continued)
      simpa only [messages, List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.nil_append, List.append_nil] using bill
end BeaconcryptCore.Computational.RegistrationNativeInstallAdmitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallAdmitted.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallAdmitted.server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallAdmitted.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallAdmitted.beacon

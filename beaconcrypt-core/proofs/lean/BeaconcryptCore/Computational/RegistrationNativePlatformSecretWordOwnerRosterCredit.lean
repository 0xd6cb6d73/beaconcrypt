-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerFinishCredit
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRosterCredit
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformSecretWordOrdinary (State)
open RegistrationNativeSecretWordLifecycleOwnerPhase (Done Terminal)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
private theorem finish_view (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (target : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.1.beacons[target]? = some owner)
    (result : RustM (Option Pqxdh.Bytes) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) (KemSK := KemSK) setup wire source target packet).run before)) :
    ∃ middle, middle ∈ support (((RegistrationNativePlatformSecretWordFinish.finish (n := n) (KemSK := KemSK) setup wire source packet).run owner.view).run before.1.environment) ∧
      result = (middle.1.1, ({before.1 with beacons := before.1.beacons.set target {owner with view := middle.1.2}, environment := middle.2}, before.2)) := by
  simp only [RegistrationNativePlatformSecretWordFrontend.finish, StateT.run, found, support_map] at supported
  obtain ⟨middle, reached, equal⟩ := supported
  refine ⟨middle, ?_, equal.symm⟩
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  cases scalar : owner.scalar with
  | none => simpa only [scalar, StateT.run] using original
  | some scalar =>
      simp only [scalar] at original
      exact PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ original
/-- Actual new mixed-roster finish preserves every already consumed local owner, including missing and ordinary-owner routes. -/
theorem finish_done (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index target : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform)
    (result : RustM (Option Pqxdh.Bytes) × State source Platform) (valid : Done index before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) (KemSK := KemSK) setup wire source target packet).run before)) :
    Done index result.2.1.beacons := by
  cases found : before.1.beacons[target]? with
  | none =>
      simp only [RegistrationNativePlatformSecretWordFrontend.finish, StateT.run, found, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | some owner =>
      obtain ⟨middle, reached, rfl⟩ := finish_view setup wire target packet before owner found result supported
      by_cases same : index = target
      · subst target
        obtain ⟨earlier, atIndex, terminal⟩ := valid
        have equal := Option.some.inj (atIndex.symm.trans found)
        subst earlier
        have kept := RegistrationNativePlatformSecretWordOwnerFinishCredit.finish_terminal setup wire packet owner.view before.1.environment middle terminal reached
        exact ⟨{owner with view := middle.1.2}, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, kept⟩
      · obtain ⟨earlier, atIndex, terminal⟩ := valid
        exact ⟨earlier, by simpa only [List.getElem?_set_ne (Ne.symm same)] using atIndex, terminal⟩
/-- The literal selected pending move consumes precisely its current public owner position while retaining every other role and the common platform state. -/
theorem finish_consumes (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.1.beacons[index]? = some owner)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (aborted : pqxdh.BeaconAborted)
    (sent : owner.view.phase = .initSent pending oneTime) (moved : pending.aborted_state = .ok aborted)
    (result : RustM (Option Pqxdh.Bytes) × State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordFrontend.finish (n := n) (KemSK := KemSK) setup wire source index packet).run before)) :
    Done index result.2.1.beacons := by
  obtain ⟨middle, reached, rfl⟩ := finish_view setup wire index packet before owner found result supported
  have terminal := RegistrationNativePlatformSecretWordOwnerFinishCredit.finish_consumes setup wire packet owner.view before.1.environment
    pending oneTime aborted sent moved middle reached
  exact ⟨{owner with view := middle.1.2}, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, terminal⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRosterCredit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRosterCredit.finish_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRosterCredit.finish_done
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRosterCredit.finish_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRosterCredit.finish_consumes

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordSlots
/-! The computed opaque slot map is covered by actual role-correct successful installation receipts. Any persistent source interpretation preserves the same exact receipt coverage. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentInterface (Handle)
open RegistrationNativePlatformRecordSlotGhost (State Receipt slots)
variable {n : Nat} {KemSK A : Type}

def Complete (state : State n) : Prop :=
  ∀handle slot,slots state handle=some slot → ∃receipt∈state.installs,receipt.handle=handle ∧ receipt.slot=some slot ∧ receipt.role=(match handle with | .peer _=>.server | .owner _=>.beacon)

private theorem frame (before after : State n) (valid : Complete before)
    (same : slots after=slots before) (kept : ∀receipt∈before.installs,receipt∈after.installs) : Complete after := by
  intro handle slot present
  rw [same] at present
  obtain ⟨receipt,member,handled,hidden,typed⟩ := valid handle slot present
  exact ⟨receipt,kept receipt member,handled,hidden,typed⟩

private theorem peer (before : State n) (valid : Complete before) (keyId : Aeneas.Std.U64) (pending : Option (Slot n)) :
    Complete ⟨{before.origins with peers:=Function.update before.origins.peers keyId pending},
      before.installs++[⟨.server,.peer keyId,pending⟩]⟩ := by
  intro handle slot present
  cases handle with
  | peer other =>
    by_cases same : other=keyId
    · subst other
      simp only [slots,Function.update_self] at present
      exact ⟨⟨.server,.peer keyId,pending⟩,List.mem_append_right _ (List.mem_singleton_self _),rfl,present,rfl⟩
    · simp only [slots,Function.update_of_ne same] at present
      obtain ⟨receipt,member,handled,hidden,typed⟩ := valid (.peer other) slot present
      exact ⟨receipt,List.mem_append_left _ member,handled,hidden,typed⟩
  | owner owner =>
    obtain ⟨receipt,member,handled,hidden,typed⟩ := valid (.owner owner) slot present
    exact ⟨receipt,List.mem_append_left _ member,handled,hidden,typed⟩

private theorem owner (before : State n) (valid : Complete before) (index : Nat) (pending : Option (Slot n)) :
    Complete ⟨{before.origins with owners:=Function.update before.origins.owners index pending},
      before.installs++[⟨.beacon,.owner index,pending⟩]⟩ := by
  intro handle slot present
  cases handle with
  | peer keyId =>
    obtain ⟨receipt,member,handled,hidden,typed⟩ := valid (.peer keyId) slot present
    exact ⟨receipt,List.mem_append_left _ member,handled,hidden,typed⟩
  | owner other =>
    by_cases same : other=index
    · subst other
      simp only [slots,Function.update_self] at present
      exact ⟨⟨.beacon,.owner index,pending⟩,List.mem_append_right _ (List.mem_singleton_self _),rfl,present,rfl⟩
    · simp only [slots,Function.update_of_ne same] at present
      obtain ⟨receipt,member,handled,hidden,typed⟩ := valid (.owner other) slot present
      exact ⟨receipt,List.mem_append_left _ member,handled,hidden,typed⟩

private theorem appended (before : State n) (valid : Complete before) (index : Nat) :
    Complete ⟨{before.origins with owners:=Function.update before.origins.owners index none},before.installs⟩ := by
  intro handle slot present
  cases handle with
  | peer keyId => exact valid (.peer keyId) slot present
  | owner other =>
    by_cases same : other=index
    · subst other
      simp only [slots,Function.update_self,reduceCtorEq] at present
    · simp only [slots,Function.update_of_ne same] at present
      exact valid (.owner other) slot present

/-- Every newly observed hidden handle has its actual earlier successful installation receipt; owner allocation only clears its new handle. -/
theorem step (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (reply : (RegistrationNativePublicFrontend.Spec n KemSK).Range query)
    (before : RegistrationNativePlatformPublicRecordSlots.State n) (valid : Complete before.snapshot) :
    Complete (RegistrationNativePlatformPublicRecordSlots.step query reply before).snapshot := by
  rcases query with (prepare|(demand|(publication|environment))|kem)|record
  · exact valid
  · exact valid
  · exact valid
  · rcases environment with coin|capability
    · exact valid
    · cases capability with
      | installServer keyId binding kernel =>
        cases reply with
        | false => exact valid
        | true => exact peer before.snapshot valid keyId before.pending
      | installBeacon index binding kernel =>
        cases reply with
        | false => exact valid
        | true => exact owner before.snapshot valid index before.pending
      | appendOwner view sign row => exact appended before.snapshot valid reply
      | _ => exact valid
  · exact valid
  · exact valid

/-- The cold opaque observer has no hidden handle and needs no external slot-coverage invariant. -/
theorem initial : Complete (RegistrationNativePlatformRecordSlotGhost.initial (n := n)) := by
  intro handle slot present
  cases handle <;> cases present

/-- Any adaptive original public tree retains this exact hidden-handle receipt coverage. -/
theorem program (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (before : RegistrationNativePlatformPublicRecordSlots.State n) (valid : Complete before.snapshot)
    (result : A × RegistrationNativePlatformPublicRecordSlots.State n)
    (supported : result∈support (RegistrationNativePlatformPublicRecordSlots.program work before)) : Complete result.2.snapshot := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [RegistrationNativePlatformPublicRecordSlots.program,simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact valid
  | query_bind query next ih =>
    unfold RegistrationNativePlatformPublicRecordSlots.program at supported
    simp only [simulateQ_bind,simulateQ_spec_query] at supported
    change result∈support ((RegistrationNativePlatformPublicRecordSlots.handler query >>= fun reply =>
      simulateQ RegistrationNativePlatformPublicRecordSlots.handler (next reply)).run before) at supported
    rw [StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    change middle∈support ((fun reply => (reply,RegistrationNativePlatformPublicRecordSlots.step query reply before)) <$>
      (((RegistrationNativePublicFrontend.Spec n KemSK).query query) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _)) at called
    rw [support_map] at called
    obtain ⟨reply,_,equal⟩ := called
    cases equal
    exact ih reply _ (step query reply before valid) continued

/-- Any persistent interpretation preserves this computed receipt coverage, including arbitrary physical cache and journal state. -/
theorem interpreted {S : Type}
    (implementation : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT S ProbComp))
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) A)
    (ghost : RegistrationNativePlatformPublicRecordSlots.State n) (valid : Complete ghost.snapshot)
    (before : S) (result : (A × RegistrationNativePlatformPublicRecordSlots.State n) × S)
    (supported : result∈support ((simulateQ implementation (RegistrationNativePlatformPublicRecordSlots.program work ghost)).run before)) :
    Complete result.1.2.snapshot := by
  apply program work ghost valid result.1
  apply OracleComp.support_simulateQ_run'_subset implementation _ before
  rw [StateT.run'_eq,support_map]
  exact ⟨result,supported,rfl⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.initial' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotReceipt.interpreted

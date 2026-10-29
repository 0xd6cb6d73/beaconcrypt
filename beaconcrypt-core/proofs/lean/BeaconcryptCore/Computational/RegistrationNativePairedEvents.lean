-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedTrace

/-! The paired monitor keeps its flag sticky and its original native event list append-only. These operational facts retain chronological witnesses through later refused callbacks and failures. A clean final supported result therefore also certifies every earlier reached monitor state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedEvents
open RegistrationNativePairedTrace (State step handler)
open RegistrationNativeG2Trace (Event)
open RegistrationNativePublicFrontend (Spec)
variable {n : Nat} {KemSK Value : Type}

/-- A true paired-provenance flag can never be cleared by an actual adaptive continuation. -/
theorem sticky (work : OracleComp (Spec n KemSK) Value) (before : State n) (flagged : before.bad = true)
    (result : Value × State n) (supported : result ∈ support ((simulateQ handler work).run before)) : result.2.bad = true := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact flagged
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
      obtain ⟨reply, _possible, continued⟩ := supported
      exact ih reply _ (by simp only [step, flagged, Bool.true_or]) continued

/-- Any actual reached prefix of a clean final paired result was itself clean. -/
theorem clean_before (work : OracleComp (Spec n KemSK) Value) (before : State n) (result : Value × State n)
    (supported : result ∈ support ((simulateQ handler work).run before)) (clean : result.2.bad = false) : before.bad = false := by
  cases original : before.bad with
  | false => rfl
  | true => have impossible := sticky work before original result supported; rw [clean] at impossible; cases impossible

private theorem install_chunk (role : PqxdhRecordLiftInterface.Role) (reply : Bool) (before : RegistrationNativeG2Trace.State) :
    ∃ suffix, (RegistrationNativeG2Trace.installed role reply (RegistrationNativeG2Trace.attempt role before)).events = before.events ++ suffix := by
  cases current : before.current with
  | none => exact ⟨[], by simp [RegistrationNativeG2Trace.installed, RegistrationNativeG2Trace.attempt, current]⟩
  | some message =>
      cases reply with
      | false => exact ⟨[.installAttempt role message], by simp [RegistrationNativeG2Trace.installed, RegistrationNativeG2Trace.attempt, current]⟩
      | true => exact ⟨[.installAttempt role message, .install role message], by simp [RegistrationNativeG2Trace.installed, RegistrationNativeG2Trace.attempt, current, List.append_assoc]⟩

/-- Every actual callback appends its literal chronological events while retaining every earlier event. -/
theorem query_chunk (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : State n) :
    ∃ suffix, (step query reply before).trace.events = before.trace.events ++ suffix := by
  rcases query with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
  · exact ⟨[.prepare prepare], rfl⟩
  · exact ⟨[.demand demand], rfl⟩
  · exact ⟨[], by simp [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish]⟩
  · rcases environment with coin | capability
    · exact ⟨[], by simp [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish]⟩
    · cases capability with
      | installServer keyId binding kernel => exact install_chunk .server reply before.trace
      | installBeacon owner shell kernel => exact install_chunk .beacon reply before.trace
      | _ => exact ⟨[], by simp [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish]⟩
  · exact ⟨[], by simp [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish]⟩
  · exact ⟨[.encapsulate false key reply.1 reply.2], rfl⟩
  · exact ⟨[], by simp [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish]⟩
  · exact ⟨[.encapsulate true key reply.1 reply.2], rfl⟩
  · exact ⟨[], by simp [step, RegistrationNativeG2Trace.begin, RegistrationNativeG2Trace.finish]⟩

/-- Later actual events retain the exact ordered repeated-role-attempt witnesses. -/
theorem repeat_append (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes)
    (inside : Pqxdh.Bytes → Bool) (events suffix : List Event)
    (repeated : RegistrationNativeG2Trace.RepeatedRoleAttempt input inside events) :
    RegistrationNativeG2Trace.RepeatedRoleAttempt input inside (events ++ suffix) := by
  obtain ⟨earlier, middle, later, role, first, second, bytes, shape, firstInput, secondInput, selected⟩ := repeated
  refine ⟨earlier, middle, later ++ suffix, role, first, second, bytes, ?_, firstInput, secondInput, selected⟩
  rw [shape]
  simp only [List.append_assoc]

end BeaconcryptCore.Computational.RegistrationNativePairedEvents
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedEvents.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedEvents.sticky
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedEvents.clean_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedEvents.clean_before
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedEvents.query_chunk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedEvents.query_chunk
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedEvents.repeat_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedEvents.repeat_append

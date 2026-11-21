-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedProvenance
import BeaconcryptCore.Computational.RegistrationNativeG2Trace

/-! A private paired observer retains the exact chronological native descriptor trace together with the actual most recent material reply. Its flag tests every hidden installation against that same returned slot and demanded descriptor. Erasing only this additional reply/flag instrumentation recovers the literal original complete trace, including failed installation attempts. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedTrace
open PqxdhRecordLiftInterface (Role)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeG2Trace (begin finish)
variable {n : Nat} {KemSK Value : Type}
noncomputable section

structure State (n : Nat) where
  trace : RegistrationNativeG2Trace.State
  choice : Option (Choice n)
  bad : Bool

def initial : State n := ⟨RegistrationNativeG2Trace.initial, none, false⟩

def FitsKernel (before : State n) : PqxdhRecordLiftInterface.KernelRef n → Prop
  | .known _ => True
  | .hidden slot => before.trace.current.isSome = true ∧
      ∃ reference, before.choice = some (.hidden reference) ∧ slot = reference.slot

def Fits : (Spec n KemSK).Domain → State n → Prop
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer _ _ kernel)))))), before => FitsKernel before kernel
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon _ _ kernel)))))), before => FitsKernel before kernel
  | _, _ => True

instance (query : (Spec n KemSK).Domain) (before : State n) : Decidable (Fits query before) := by
  exact Classical.propDecidable _

def updateChoice : (query : (Spec n KemSK).Domain) → (Spec n KemSK).Range query → Option (Choice n) → Option (Choice n)
  | .inl (.inl _), _, _ => none
  | .inl (.inr (.inl (.inl _))), reply, _ => reply
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer ..)))))), _, _ => none
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon ..)))))), _, _ => none
  | _, _, previous => previous

def step (query : (Spec n KemSK).Domain) (reply : (Spec n KemSK).Range query) (before : State n) : State n :=
  ⟨finish query reply (begin query before.trace), updateChoice query reply before.choice, before.bad || !decide (Fits query before)⟩

def handler : QueryImpl (Spec n KemSK) (StateT (State n) (OracleComp (Spec n KemSK))) := fun query before =>
  (fun reply => (reply, step query reply before)) <$> (Spec n KemSK).query query

/-- The private paired callback forwards the same actual query and its complete original chronological state. -/
theorem query_source (query : (Spec n KemSK).Domain) (before : State n) :
    Prod.map id State.trace <$> (handler query).run before =
      (RegistrationNativeG2Trace.handler query).run before.trace := by
  simp only [handler, RegistrationNativeG2Trace.handler, StateT.run,
    Functor.map_map, Prod.map_def, id_eq, step]

/-- The paired monitor preserves the complete exact original trace on the same adaptive result. -/
theorem program_source (work : OracleComp (Spec n KemSK) Value) (before : State n) :
    Prod.map id State.trace <$> (simulateQ handler work).run before =
      (simulateQ RegistrationNativeG2Trace.handler work).run before.trace :=
  map_run_simulateQ_eq_of_query_map_eq _ _ State.trace query_source work before

def Safe (work : OracleComp (Spec n KemSK) Value) : Prop :=
  ∀ before result, before.bad = false → result ∈ support ((simulateQ handler work).run before) → result.2.bad = false

/-- Pure observations and early native failures preserve an already clean paired observer. -/
theorem pure_safe (value : Value) : Safe (n := n) (KemSK := KemSK) (pure value) := by
  intro before result clean supported
  simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  exact clean

/-- Adaptive composition retains the same paired monitor state at the actual supported continuation. -/
theorem bind_safe {Next : Type} (work : OracleComp (Spec n KemSK) Value)
    (next : Value → OracleComp (Spec n KemSK) Next) (first : Safe work) (later : ∀ value, Safe (next value)) :
    Safe (work >>= next) := by
  intro before result clean supported
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, actual, continued⟩ := supported
  exact later middle.1 middle.2 result (first before middle clean actual) continued

end
end BeaconcryptCore.Computational.RegistrationNativePairedTrace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedTrace.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedTrace.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedTrace.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedTrace.pure_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedTrace.pure_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedTrace.bind_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedTrace.bind_safe

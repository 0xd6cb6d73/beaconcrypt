-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPrefixHandoff

/-! The independently routed raw ideal handler advances the selected-accept counter exactly as the registration service does. Native record refusal and writer failure preserve the private mark. Once the selected ordinal has passed, every adaptive continuation retains that mark. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleMarks
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open CborRawPublicState (Public)
open CborRawMiddleSimulation (Native)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
section Marks
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

def counter (state : Public × Native KemSK) : Nat := state.2.backend.2.2.accepts

def marks (state : Public × Native KemSK) := state.2.backend.2.2.marks

theorem handler_core (query : Spec.Domain) (state : Public × Native KemSK)
    (result : Spec.Range query × (Public × Native KemSK))
    (member : result ∈ support ((CborRawMiddleSimulation.handler setup wire parse checks target parameters created
      query).run state)) :
    counter state ≤ counter result.2 ∧ (counter state ≠ target.accept → marks result.2 = marks state) := by
  cases record : CborSplitCompiler.recordCommand query with
  | true =>
      simp only [CborRawMiddleSimulation.handler, record, ite_true, CborRawMiddleSimulation.records,
        StateT.run, support_map] at member
      obtain ⟨inner, _, rfl⟩ := member
      exact ⟨Nat.le_refl _, fun _ => rfl⟩
  | false =>
      simp only [CborRawMiddleSimulation.handler, record, Bool.false_eq_true, ite_false,
        CborRawMiddleSimulation.registration, StateT.run, bind_pure_comp, support_map] at member
      obtain ⟨inner, reached, rfl⟩ := member
      exact PqxdhDeploymentIdealKeymatch.handler_core setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created _ state.2 inner reached

theorem run_settled (work : OracleComp Spec Result) (state : Public × Native KemSK)
    (beyond : target.accept < counter state) :
    ∀ result ∈ support ((simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
      work).run state), marks result.2 = marks state := by
  intro result member
  exact (PqxdhDeploymentIdealSlots.simulateQ_keeps _
    (fun current : Public × Native KemSK => target.accept < counter current ∧ marks current = marks state)
    (fun query current good after supported => by
      obtain ⟨grows, kept⟩ := handler_core setup wire parse checks target parameters created query current after supported
      exact ⟨lt_of_lt_of_le good.1 grows, (kept (Nat.ne_of_gt good.1)).trans good.2⟩)
    work state ⟨beyond, rfl⟩ result member).2

/-- Public accept bookkeeping surrounds the actual selected registration handler without changing its answer or private state. -/
theorem accept_run (raw : Pqxdh.Bytes) (state : Public × Native KemSK) :
    (CborRawMiddleSimulation.handler setup wire parse checks target parameters created (.inr (.accept raw))).run state =
      (fun value => (value.1,
        ((⟨CborRegistrationPublicLog.update state.1.log (.inr (.accept raw)) value.1, state.1.lastId⟩ : Public),
          PqxdhDeploymentIdealCut.unghost value.2))) <$>
        (PqxdhDeploymentBackend.handlerWith setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
          (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
            checks target parameters created) (.inr (.accept raw))).run state.2 := by
  change (CborRawMiddleSimulation.registration setup wire parse checks target parameters created
    (.inr (.accept raw))).run state = _
  simp only [CborRawMiddleSimulation.registration, StateT.run, bind_pure_comp]
  rfl

theorem accept_inactive (raw : Pqxdh.Bytes)
    (inactive : ∀ value, PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse)
      checks raw = some value → value.keys.pqKey ≠ parameters.chosen.1)
    (state : Public × Native KemSK) (selected : counter state = target.accept)
    (result : Option Nat × (Public × Native KemSK))
    (member : result ∈ support ((CborRawMiddleSimulation.handler setup wire parse checks target parameters created
      (.inr (.accept raw))).run state)) :
    counter result.2 = target.accept + 1 ∧ marks result.2 = none := by
  rw [accept_run, support_map] at member
  obtain ⟨inner, supported, rfl⟩ := member
  exact PqxdhDeploymentIdealKeymatch.handler_accept_inactive setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) checks target parameters created raw inactive state.2 selected inner supported

end Marks
end BeaconcryptCore.Computational.CborRawMiddleMarks

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleMarks.handler_core' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleMarks.handler_core
/-- info: 'BeaconcryptCore.Computational.CborRawMiddleMarks.run_settled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleMarks.run_settled
/-- info: 'BeaconcryptCore.Computational.CborRawMiddleMarks.accept_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleMarks.accept_run
/-- info: 'BeaconcryptCore.Computational.CborRawMiddleMarks.accept_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleMarks.accept_inactive

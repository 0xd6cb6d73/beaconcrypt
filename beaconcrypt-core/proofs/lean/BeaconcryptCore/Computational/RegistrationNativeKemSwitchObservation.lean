-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram

/-! The complete candidate observation retains the sampled private phase jointly with the original ledger and native poststate. This stronger operational law identifies the actual getter secret with the observation's candidate without inferring equality from a projected distribution. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State)
open RegistrationNativeKemCut (Cut scan finish)
open RegistrationNativeKemSwitchSource (Phase Switched carry)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

def phase (cut : Option (Cut ambient KemSK Value)) (pair : MlKem768Ciphertext × MlKemSharedSecret) : Phase :=
  match cut with
  | some (.pending _ _) => some pair
  | _ => none

variable (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
  (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
  (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemSwitchSource.source baseImpl kem other selected pairs publicKey real
local notation "stopped" => RegistrationNativeKemGame.stopped baseImpl kem other selected pairs

noncomputable def afterCut (cut : Option (Cut ambient KemSK Value)) (before : State Auxiliary KemSK) :
    ProbComp (Option Value × Switched Auxiliary KemSK) := do
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  let result ← (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs pair.1 candidate)
    (RegistrationNativeKemCutMap.resume publicKey pair.1 candidate cut)).run).run before)
  pure (result.1.join, (result.2, phase cut (pair.1, candidate)))

/-- The actual optional prefix stops before its first getter and retains an inactive phase and every private source coordinate. -/
theorem scan_pre (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    (((scan provider work 0).run).run (before, none)) =
      carry none <$> (((scan stopped work 0).run).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      rcases query with query | (query | key)
      · simp only [RegistrationNativeKemCut.scan_other, OptionT.run_bind, Option.elimM, StateT.run_bind]
        simp only [RegistrationNativeKemSwitchSource.source, OptionT.run_mk, StateT.run,
          bind_map_left, map_bind, carry]
        apply bind_congr
        rintro ⟨none | reply, after⟩
        · rfl
        · exact ih reply after
      · simp only [RegistrationNativeKemCut.scan_pool, OptionT.run_bind, Option.elimM, StateT.run_bind]
        simp only [RegistrationNativeKemSwitchSource.source, OptionT.run_mk, StateT.run,
          bind_map_left, map_bind, carry]
        apply bind_congr
        rintro ⟨none | reply, after⟩
        · rfl
        · exact ih reply after
      · rfl

private theorem join_some_carry (label : Phase)
    (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT (State Auxiliary KemSK) ProbComp)))
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    (fun result => (result.1.join, (result.2, label))) <$>
      (((simulateQ implementation (some <$> work)).run).run before) =
        carry label <$> (((simulateQ implementation work).run).run before) := by
  simp only [simulateQ_map, OptionT.run_map, StateT.run_map, Functor.map_map]
  congr 1
  funext result
  rcases result with ⟨none | value, after⟩ <;> rfl

private theorem after_pending (key : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Value)
    (before : State Auxiliary KemSK) :
    afterCut baseImpl kem other selected pairs publicKey real (some (.pending key next)) before =
      (do
        let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
        let uniform ← $ᵗ MlKemSharedSecret
        let candidate := if real then pair.2 else uniform
        carry (some (pair.1, candidate)) <$>
          (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs pair.1 candidate)
            (if key = publicKey then next (pair.1, candidate)
              else (Spec ambient KemSK).query (.inr (.inr key)) >>= next)).run).run before)) := by
  simp only [afterCut, phase, RegistrationNativeKemCutMap.resume, bind_pure_comp, join_some_carry]

private theorem pending_finish (key : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Value)
    (before : State Auxiliary KemSK) :
    (((finish provider (.pending key next)).run).run (before, none)) =
      afterCut baseImpl kem other selected pairs publicKey real (some (.pending key next)) before := by
  rw [after_pending]
  simp only [finish, OptionT.run_bind, Option.elimM]
  rw [StateT.run_bind]
  simp only [RegistrationNativeKemSwitchSource.source, OptionT.run_mk, StateT.run, bind_assoc]
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  by_cases matching : key = publicKey
  · subst key
    simp only [ite_true, pure_bind, Option.elim_some]
    exact RegistrationNativeKemSwitchSource.post_program baseImpl kem other selected pairs publicKey real _ _ _ before
  · simp only [matching, ite_false]
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM]
    simp only [StateT.monad_bind_def, StateT.bind]
    simp only [RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
      OptionT.run_mk, bind_map_left, bind_assoc, pure_bind, Option.elim_some, map_bind]
    apply bind_congr
    intro reply
    exact RegistrationNativeKemSwitchSource.post_program baseImpl kem other selected pairs publicKey real _ _ _ before

private theorem finish_after (cut : Option (Cut ambient KemSK Value)) (before : State Auxiliary KemSK) :
    EvalDistEq
      (match cut with
        | none => pure (none, (before, none))
        | some cut => (((finish provider cut).run).run (before, none)))
      (afterCut baseImpl kem other selected pairs publicKey real cut before) := by
  cases cut with
  | none =>
      simp only [afterCut, RegistrationNativeKemCutMap.resume, phase, simulateQ_pure, OptionT.run_pure,
        StateT.run_pure, pure_bind]
      exact ((OracleComp.EvalDistEq.bind_congr_of_support _
        (fun _ _ => OracleComp.EvalDistEq.bind_const _ _)).trans (OracleComp.EvalDistEq.bind_const _ _)).symm
  | some cut =>
      cases cut with
      | complete value =>
          simp only [afterCut, RegistrationNativeKemCutMap.resume, phase, simulateQ_pure, OptionT.run_pure,
            StateT.run_pure, pure_bind, finish]
          exact ((OracleComp.EvalDistEq.bind_congr_of_support _
            (fun _ _ => OracleComp.EvalDistEq.bind_const _ _)).trans (OracleComp.EvalDistEq.bind_const _ _)).symm
      | pending key next =>
          change EvalDistEq (((finish provider (.pending key next)).run).run (before, none)) _
          rw [pending_finish]

/-- The whole original optional source retains the same candidate label as its actual stopped-prefix and postphase program. -/
theorem program (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    EvalDistEq (((simulateQ provider work).run).run (before, none))
      (do
        let prefixResult ← (((scan stopped work 0).run).run before)
        afterCut baseImpl kem other selected pairs publicKey real prefixResult.1 prefixResult.2) := by
  have execution := congrArg (fun program : OptionT (StateT (Switched Auxiliary KemSK) ProbComp) Value =>
    (program.run).run (before, none)) (RegistrationNativeKemCut.scan_finish provider work 0)
  rw [← execution, OptionT.run_bind, Option.elimM, StateT.run_bind, scan_pre]
  simp only [bind_map_left, carry]
  apply OracleComp.EvalDistEq.bind_congr_of_support
  rintro ⟨none | cut, after⟩ _supported
  · exact finish_after baseImpl kem other selected pairs publicKey real none after
  · exact finish_after baseImpl kem other selected pairs publicKey real (some cut) after

def observe (real : Bool) (record : RegistrationNativeKemCandidateObservation.Record ambient KemSK Auxiliary Value) :
    Option Value × Switched Auxiliary KemSK :=
  (record.value, (record.finalState, phase record.cut (record.encapsulation.1, record.candidate real)))

/-- The full source observation retains its exact sampled ciphertext and candidate in the private phase. -/
theorem observation {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    observe real <$> RegistrationNativeKemCandidateObservation.run baseImpl kem other selected chosen others work before 0 real =
      (do
        let prefixResult ← (((scan (RegistrationNativeKemGame.stopped baseImpl kem other selected.val
          (List.ofFn (selected.insertNth chosen others))) work 0).run).run before)
        afterCut baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real
          prefixResult.1 prefixResult.2) := by
  simp only [RegistrationNativeKemCandidateObservation.run, RegistrationNativeKemGame.expose,
    RegistrationNativeKemCutStop.scan_simulate, afterCut, map_bind, map_pure, observe,
    RegistrationNativeKemCandidateObservation.Record.candidate]

/-- Every candidate observation is supported by the entire original optional provider with the same sampled candidate label, original ledger and native state. -/
theorem observation_support {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK)
    (record : RegistrationNativeKemCandidateObservation.Record ambient KemSK Auxiliary Value)
    (supported : record ∈ support (RegistrationNativeKemCandidateObservation.run
      baseImpl kem other selected chosen others work before 0 real)) :
    observe real record ∈ support
      (((simulateQ (RegistrationNativeKemSwitchSource.source baseImpl kem other selected.val
        (List.ofFn (selected.insertNth chosen others)) chosen.1 real) work).run).run (before, none)) := by
  rw [OracleComp.support_eq_of_evalDistEq
    (program baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real work before),
    ← observation baseImpl kem other real selected chosen others work before, support_map]
  exact Set.mem_image_of_mem (observe real) supported

end BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.scan_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.scan_pre
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.observation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.observation_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchObservation.observation_support

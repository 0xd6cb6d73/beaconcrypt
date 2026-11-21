-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchSource
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateObservation
import BeaconcryptCore.Computational.RegistrationNativeKemCutStop

/-! The candidate source's stopped prefix and private postphase reconstruct the whole original optional program. The private phase is dropped only after execution; every native operational state and literal ledger result is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram
open PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State)
open RegistrationNativeKemCut (Cut scan)
variable {κ ι KemSK Auxiliary Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

def project {Reply : Type} (result : Reply × RegistrationNativeKemSwitchSource.Switched Auxiliary KemSK) :
    Reply × State Auxiliary KemSK := (result.1, result.2.1)

variable (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
  (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
  (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)

noncomputable def afterCut (cut : Option (Cut ambient KemSK Value)) (before : State Auxiliary KemSK) :
    ProbComp (Option Value × State Auxiliary KemSK) := do
  let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
  let uniform ← $ᵗ MlKemSharedSecret
  let candidate := if real then pair.2 else uniform
  let result ← (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs pair.1 candidate)
    (RegistrationNativeKemCutMap.resume publicKey pair.1 candidate cut)).run).run before)
  pure (result.1.join, result.2)

noncomputable def cutRun (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    ProbComp (Option Value × State Auxiliary KemSK) := do
  let prefixResult ← (((scan (RegistrationNativeKemGame.stopped baseImpl kem other selected pairs) work 0).run).run before)
  afterCut baseImpl kem other selected pairs publicKey real prefixResult.1 prefixResult.2

noncomputable def direct (work : OracleComp (Spec ambient KemSK) Value)
    (before : State Auxiliary KemSK) (phase : RegistrationNativeKemSwitchSource.Phase) :
    ProbComp (Option Value × State Auxiliary KemSK) :=
  project <$> (((simulateQ (RegistrationNativeKemSwitchSource.source baseImpl kem other selected pairs publicKey real)
    work).run).run (before, phase))

private theorem direct_post (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    direct baseImpl kem other selected pairs publicKey real work before (some (challenge, candidate)) =
      (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs challenge candidate) work).run).run before) := by
  rw [direct, RegistrationNativeKemSwitchSource.post_program, Functor.map_map]
  change (fun result => result) <$> _ = _
  exact id_map _

private theorem join_some_run
    (implementation : QueryImpl (Spec ambient KemSK) (OptionT (StateT (State Auxiliary KemSK) ProbComp)))
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    (fun result => (result.1.join, result.2)) <$>
      (((simulateQ implementation (some <$> work)).run).run before) =
        (((simulateQ implementation work).run).run before) := by
  simp only [simulateQ_map, OptionT.run_map, StateT.run_map, Functor.map_map]
  have same : (fun result : Option Value × State Auxiliary KemSK => ((result.1.map some).join, result.2)) = id := by
    funext result
    rcases result with ⟨none | value, after⟩ <;> rfl
  rw [same]
  exact id_map _

private theorem after_pending (key : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Value)
    (before : State Auxiliary KemSK) :
    afterCut baseImpl kem other selected pairs publicKey real (some (.pending key next)) before =
      (do
        let pair ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
        let uniform ← $ᵗ MlKemSharedSecret
        let candidate := if real then pair.2 else uniform
        (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs pair.1 candidate)
          (if key = publicKey then next (pair.1, candidate)
            else (Spec ambient KemSK).query (.inr (.inr key)) >>= next)).run).run before)) := by
  simp only [afterCut, RegistrationNativeKemCutMap.resume, bind_pure_comp, join_some_run]

private theorem after_none (before : State Auxiliary KemSK) :
    EvalDistEq (afterCut baseImpl kem other selected pairs publicKey real (none : Option (Cut ambient KemSK Value)) before)
      (pure (none, before) : ProbComp (Option Value × State Auxiliary KemSK)) := by
  simp only [afterCut, RegistrationNativeKemCutMap.resume, simulateQ_pure, OptionT.run_pure,
    StateT.run_pure, pure_bind]
  exact (OracleComp.EvalDistEq.bind_congr_of_support _
    (fun _ _ => OracleComp.EvalDistEq.bind_const _ _)).trans (OracleComp.EvalDistEq.bind_const _ _)

private theorem after_complete (value : Value) (before : State Auxiliary KemSK) :
    EvalDistEq (afterCut baseImpl kem other selected pairs publicKey real (some (.complete value)) before)
      (pure (some value, before) : ProbComp (Option Value × State Auxiliary KemSK)) := by
  simp only [afterCut, RegistrationNativeKemCutMap.resume, simulateQ_pure, OptionT.run_pure,
    StateT.run_pure, pure_bind, Option.join_some]
  exact (OracleComp.EvalDistEq.bind_congr_of_support _
    (fun _ _ => OracleComp.EvalDistEq.bind_const _ _)).trans (OracleComp.EvalDistEq.bind_const _ _)

private theorem cut_other (query : ambient.Domain)
    (next : ambient.Range query → OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    cutRun baseImpl kem other selected pairs publicKey real ((Spec ambient KemSK).query (.inl query) >>= next) before =
      (do
        let first ← (((RegistrationNativeKemGame.stopped baseImpl kem other selected pairs (.inl query)).run).run before)
        match first.1 with
        | none => afterCut baseImpl kem other selected pairs publicKey real none first.2
        | some reply => cutRun baseImpl kem other selected pairs publicKey real (next reply) first.2) := by
  simp only [cutRun, RegistrationNativeKemCut.scan_other, OptionT.run_bind, Option.elimM,
    StateT.run_bind, bind_assoc]
  congr 1
  funext first
  rcases first with ⟨none | reply, after⟩ <;> simp only [Option.elim_none, Option.elim_some,
    StateT.run_pure, pure_bind]

private theorem cut_pool (query : PqxdhLiveKemBirth.Query)
    (next : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query → OracleComp (Spec ambient KemSK) Value)
    (before : State Auxiliary KemSK) :
    cutRun baseImpl kem other selected pairs publicKey real ((Spec ambient KemSK).query (.inr (.inl query)) >>= next) before =
      (do
        let first ← (((RegistrationNativeKemGame.stopped baseImpl kem other selected pairs (.inr (.inl query))).run).run before)
        match first.1 with
        | none => afterCut baseImpl kem other selected pairs publicKey real none first.2
        | some reply => cutRun baseImpl kem other selected pairs publicKey real (next reply) first.2) := by
  simp only [cutRun, RegistrationNativeKemCut.scan_pool, OptionT.run_bind, Option.elimM,
    StateT.run_bind, bind_assoc]
  congr 1
  funext first
  rcases first with ⟨none | reply, after⟩ <;> simp only [Option.elim_none, Option.elim_some,
    StateT.run_pure, pure_bind]

private theorem direct_other (query : ambient.Domain)
    (next : ambient.Range query → OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    direct baseImpl kem other selected pairs publicKey real ((Spec ambient KemSK).query (.inl query) >>= next) before none =
      (do
        let first ← (((RegistrationNativeKemGame.stopped baseImpl kem other selected pairs (.inl query)).run).run before)
        match first.1 with
        | none => pure (none, first.2)
        | some reply => direct baseImpl kem other selected pairs publicKey real (next reply) first.2 none) := by
  simp only [direct, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM]
  rw [StateT.run_bind]
  simp only [RegistrationNativeKemSwitchSource.source, OptionT.run_mk,
    StateT.run, bind_map_left, map_bind, RegistrationNativeKemSwitchSource.carry]
  congr 1
  funext first
  rcases first with ⟨none | reply, after⟩ <;> rfl

private theorem direct_pool (query : PqxdhLiveKemBirth.Query)
    (next : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query → OracleComp (Spec ambient KemSK) Value)
    (before : State Auxiliary KemSK) :
    direct baseImpl kem other selected pairs publicKey real ((Spec ambient KemSK).query (.inr (.inl query)) >>= next) before none =
      (do
        let first ← (((RegistrationNativeKemGame.stopped baseImpl kem other selected pairs (.inr (.inl query))).run).run before)
        match first.1 with
        | none => pure (none, first.2)
        | some reply => direct baseImpl kem other selected pairs publicKey real (next reply) first.2 none) := by
  simp only [direct, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM]
  rw [StateT.run_bind]
  simp only [RegistrationNativeKemSwitchSource.source, OptionT.run_mk,
    StateT.run, bind_map_left, map_bind, RegistrationNativeKemSwitchSource.carry]
  congr 1
  funext first
  rcases first with ⟨none | reply, after⟩ <;> rfl

private theorem direct_getter (key : MlKem768PublicKey)
    (next : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec ambient KemSK) Value)
    (before : State Auxiliary KemSK) :
    direct baseImpl kem other selected pairs publicKey real ((Spec ambient KemSK).query (.inr (.inr key)) >>= next) before none =
      afterCut baseImpl kem other selected pairs publicKey real (some (.pending key next)) before := by
  rw [after_pending]
  simp only [direct, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM]
  rw [StateT.run_bind]
  simp only [RegistrationNativeKemSwitchSource.source, OptionT.run_mk,
    StateT.run, bind_assoc, map_bind]
  apply bind_congr
  intro pair
  apply bind_congr
  intro uniform
  by_cases matching : key = publicKey
  · subst key
    simp only [ite_true, pure_bind, Option.elim_some]
    change direct baseImpl kem other selected pairs publicKey real
      (next (pair.1, if real then pair.2 else uniform)) before
        (some (pair.1, if real then pair.2 else uniform)) = _
    exact direct_post baseImpl kem other selected pairs publicKey real _ _ _ before
  · simp only [matching, ite_false]
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM]
    simp only [StateT.monad_bind_def, StateT.bind]
    simp only [RegistrationNativeKemCandidateSource.source, RegistrationNativeKemGame.combine,
      OptionT.run_mk, bind_map_left, bind_assoc, pure_bind, Option.elim_some]
    apply bind_congr
    intro reply
    change direct baseImpl kem other selected pairs publicKey real (next reply) before
      (some (pair.1, if real then pair.2 else uniform)) = _
    exact direct_post baseImpl kem other selected pairs publicKey real _ _ _ before

/-- The genuine first-getter cut and complete candidate continuation equal the whole optional provider, including executions that never reach a getter. -/
theorem program (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    EvalDistEq (direct baseImpl kem other selected pairs publicKey real work before none)
      (cutRun baseImpl kem other selected pairs publicKey real work before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      change EvalDistEq (pure (some value, before) : ProbComp _) _
      change EvalDistEq _ (afterCut baseImpl kem other selected pairs publicKey real (some (.complete value)) before)
      exact (after_complete baseImpl kem other selected pairs publicKey real value before).symm
  | query_bind query next ih =>
      rcases query with query | (query | key)
      · rw [direct_other, cut_other]
        apply OracleComp.EvalDistEq.bind_congr_of_support
        intro first _supported
        rcases first with ⟨none | reply, after⟩
        · exact (after_none baseImpl kem other selected pairs publicKey real after).symm
        · exact ih reply after
      · rw [direct_pool, cut_pool]
        apply OracleComp.EvalDistEq.bind_congr_of_support
        intro first _supported
        rcases first with ⟨none | reply, after⟩
        · exact (after_none baseImpl kem other selected pairs publicKey real after).symm
        · exact ih reply after
      · rw [direct_getter]
        change EvalDistEq _ (afterCut baseImpl kem other selected pairs publicKey real (some (.pending key next)) before)
        rfl

/-- The source observation's retained value and complete poststate are exactly the stopped first-getter program. -/
theorem observation {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK) :
    (fun record => (record.value, record.finalState)) <$>
      RegistrationNativeKemCandidateObservation.run baseImpl kem other selected chosen others work before 0 real =
        cutRun baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real work before := by
  simp only [RegistrationNativeKemCandidateObservation.run, RegistrationNativeKemGame.expose,
    RegistrationNativeKemCutStop.scan_simulate, cutRun, afterCut, map_bind, map_pure]

/-- Every actual candidate-hybrid observation is supported by the complete original optional provider with the same literal value and every base-state coordinate. -/
theorem observation_support {count : Nat} (selected : Fin (count + 1))
    (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) Value) (before : State Auxiliary KemSK)
    (record : RegistrationNativeKemCandidateObservation.Record ambient KemSK Auxiliary Value)
    (supported : record ∈ support (RegistrationNativeKemCandidateObservation.run
      baseImpl kem other selected chosen others work before 0 real)) :
    ∃ phase, (record.value, (record.finalState, phase)) ∈ support
      (((simulateQ (RegistrationNativeKemSwitchSource.source baseImpl kem other selected.val
        (List.ofFn (selected.insertNth chosen others)) chosen.1 real) work).run).run (before, none)) := by
  have retained : (record.value, record.finalState) ∈ support
      (cutRun baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real work before) := by
    rw [← observation baseImpl kem other real selected chosen others work before, support_map]
    exact ⟨record, supported, rfl⟩
  rw [← OracleComp.support_eq_of_evalDistEq
    (program baseImpl kem other selected.val (List.ofFn (selected.insertNth chosen others)) chosen.1 real work before),
    direct, support_map] at retained
  obtain ⟨⟨value, reached, phase⟩, reachedSupport, equal⟩ := retained
  change (value, reached) = (record.value, record.finalState) at equal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact ⟨phase, reachedSupport⟩

end BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram.observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram.observation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram.observation_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchProgram.observation_support

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSwitchReserved

/-! Actual creation caps and the source's zero-reveal bill prevent either outer stop reason in the online candidate provider. Full adaptive source execution projects to the same total reserved live-pool provider, retaining all protocol failures, query replies, histories and first-getter phase. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSwitchTotal
open PqxdhKemIndCca
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemSwitchSource (Switched)
open RegistrationNativeKemReservation (IsCreate)
open RegistrationNativeKemPoolSource (IsReveal)
open RegistrationNativeKemSwitchReserved (project)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- Every affordable candidate callback retains its creation allowance and cannot exhaust its finite reserved table. -/
theorem step_capacity (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
    (query : (Spec ambient KemSK).Domain) (before : Switched Auxiliary KemSK) (clear : before.1.2.exhausted = false)
    (room : before.1.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((Spec ambient KemSK).Range query) × Switched Auxiliary KemSK)
    (supported : result ∈ support (((RegistrationNativeKemSwitchSource.source baseImpl kem other selected pairs publicKey real query).run).run before)) :
    result.2.1.2.exhausted = false ∧ result.2.1.2.created ≤ before.1.2.created + (if IsCreate query then 1 else 0) := by
  cases phaseRun : before.2 with
  | some phase =>
      simp only [RegistrationNativeKemSwitchSource.source, phaseRun, RegistrationNativeKemSwitchSource.post,
        RegistrationNativeKemSwitchSource.carry, OptionT.run_mk, StateT.run, support_map] at supported
      obtain ⟨inner, called, rfl⟩ := supported
      exact RegistrationNativeKemCandidateReserved.step_capacity baseImpl kem other selected pairs phase.1 phase.2 query before.1 clear room inner called
  | none =>
      rcases query with query | (query | key)
      · simp only [RegistrationNativeKemSwitchSource.source, phaseRun, RegistrationNativeKemSwitchSource.carry,
          OptionT.run_mk, StateT.run, support_map] at supported
        obtain ⟨inner, called, rfl⟩ := supported
        exact RegistrationNativeKemPoolSource.step_capacity baseImpl kem other selected pairs (.inl query) before.1 clear room inner called
      · simp only [RegistrationNativeKemSwitchSource.source, phaseRun, RegistrationNativeKemSwitchSource.carry,
          OptionT.run_mk, StateT.run, support_map] at supported
        obtain ⟨inner, called, rfl⟩ := supported
        exact RegistrationNativeKemPoolSource.step_capacity baseImpl kem other selected pairs (.inr (.inl query)) before.1 clear room inner called
      · simp only [RegistrationNativeKemSwitchSource.source, phaseRun, OptionT.run_mk, StateT.run,
          mem_support_bind_iff] at supported
        obtain ⟨pair, _sampled, uniform, _uniformSupport, continued⟩ := supported
        by_cases matching : key = publicKey
        · simp only [matching, ite_true, pure_bind, support_pure, Set.mem_singleton_iff] at continued
          cases continued
          exact ⟨clear, by simp only [IsCreate, ite_false, Nat.add_zero]; exact le_rfl⟩
        · simp only [matching, ite_false, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continued
          obtain ⟨reply, _replySupport, rfl⟩ := continued
          exact ⟨clear, by simp only [IsCreate, ite_false, Nat.add_zero]; exact le_rfl⟩

private theorem step_answer (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
    (query : (Spec ambient KemSK).Domain) (before : Switched Auxiliary KemSK) (noReveal : ¬IsReveal query)
    (room : before.1.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((Spec ambient KemSK).Range query) × Switched Auxiliary KemSK)
    (supported : result ∈ support (((RegistrationNativeKemSwitchSource.source baseImpl kem other selected pairs publicKey real query).run).run before)) :
    result.1.isSome = true := by
  have mapped : Prod.map id (project pairs) result ∈ support
      (Prod.map id (project pairs) <$> (((RegistrationNativeKemSwitchSource.source baseImpl kem other selected pairs publicKey real query).run).run before)) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [RegistrationNativeKemSwitchReserved.step_source baseImpl kem other selected pairs publicKey real query before noReveal room, support_map] at mapped
  obtain ⟨reply, _reached, same⟩ := mapped
  exact congrArg (fun value => value.1.isSome) same.symm

/-- The full online native program equals its total reserved candidate provider, retaining the actual live pool, private reply history and getter phase on every branch. -/
theorem program_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool) (work : OracleComp (Spec ambient KemSK) Result) (qCreate : Nat)
    (bounded : work.IsQueryBoundP (IsCreate (ambient := ambient) (KemSK := KemSK)) qCreate)
    (noReveal : work.IsQueryBoundP (IsReveal (ambient := ambient) (KemSK := KemSK)) 0)
    (before : Switched Auxiliary KemSK) (clear : before.1.2.exhausted = false)
    (room : before.1.2.created + qCreate ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((simulateQ (RegistrationNativeKemSwitchSource.source baseImpl kem other selected pairs publicKey real) work).run).run before) =
    (fun result => (some result.1, result.2)) <$>
      (simulateQ (RegistrationNativeKemSwitchReserved.source baseImpl kem other selected pairs publicKey real) work).run (project pairs before) := by
  induction work using OracleComp.inductionOn generalizing qCreate before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded noReveal
    have quiet : ¬IsReveal query := noReveal.1.resolve_right (Nat.not_lt_zero _)
    have affordable : before.1.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length := by
      split_ifs with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega
    have sameHead := congrArg (fun work => work >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun reply =>
          (fun output => (some output.1, output.2)) <$>
            (simulateQ (RegistrationNativeKemSwitchReserved.source baseImpl kem other selected pairs publicKey real) (next reply)).run result.2))
      (RegistrationNativeKemSwitchReserved.step_source baseImpl kem other selected pairs publicKey real query before quiet affordable)
    simp only [bind_map_left, Prod.map_def, id_eq, Option.elim_some] at sameHead
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
    refine Eq.trans ?_ sameHead
    apply bind_congr_of_forall_mem_support
    rintro ⟨answer, after⟩ supported
    have present := step_answer baseImpl kem other selected pairs publicKey real query before quiet affordable (answer, after) supported
    have capacity := step_capacity baseImpl kem other selected pairs publicKey real query before clear affordable (answer, after) supported
    dsimp only at capacity
    cases answer with
    | none => exact False.elim (Bool.noConfusion present)
    | some answer =>
      have tailRoom : after.1.2.created + (if IsCreate query then qCreate - 1 else qCreate) ≤ pairs.length := by
        split_ifs at capacity ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      exact ih answer _ (bounded.2 answer) (by simpa using noReveal.2 answer) after capacity.1 tailRoom

end BeaconcryptCore.Computational.RegistrationNativeKemSwitchTotal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchTotal.step_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchTotal.step_capacity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSwitchTotal.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSwitchTotal.program_source

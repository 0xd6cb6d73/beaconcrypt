-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCandidateReserved

/-! The complete affordable non-revealing candidate source has the same total live-key pool semantics, including all generated private pairs and the full typed history. The proof derives no-stop and remaining capacity from the original AST bills at every actual callback. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCandidateReservedProgram
open PqxdhKemIndCca
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State)
open RegistrationNativeKemPoolSource (project IsReveal)
open RegistrationNativeKemReservation (IsCreate)
open RegistrationNativeKemCandidateReserved (reserved step_source step_answer step_capacity)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- The full actual native non-revealing program equals its concrete reserved key-pool execution, with no artificial stop or missing generated owner. -/
theorem program_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret) (work : OracleComp (Spec ambient KemSK) Result) (qCreate : Nat)
    (bounded : work.IsQueryBoundP (IsCreate (ambient := ambient) (KemSK := KemSK)) qCreate)
    (noReveal : work.IsQueryBoundP (IsReveal (ambient := ambient) (KemSK := KemSK)) 0)
    (before : State Auxiliary KemSK) (clear : before.2.exhausted = false)
    (room : before.2.created + qCreate ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((simulateQ (RegistrationNativeKemCandidateSource.source baseImpl kem other selected pairs challenge candidate) work).run).run before) =
    (fun result => (some result.1, result.2)) <$>
      (simulateQ (reserved baseImpl kem other selected pairs challenge candidate) work).run (project pairs before) := by
  induction work using OracleComp.inductionOn generalizing qCreate before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded noReveal
    have quiet : ¬IsReveal query := noReveal.1.resolve_right (Nat.not_lt_zero _)
    have affordable : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length := by
      split_ifs with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega
    have sameHead := congrArg (fun work => work >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun reply =>
          (fun output => (some output.1, output.2)) <$>
            (simulateQ (reserved baseImpl kem other selected pairs challenge candidate) (next reply)).run result.2))
      (step_source baseImpl kem other selected pairs challenge candidate query before quiet affordable)
    simp only [bind_map_left, Prod.map_def, id_eq, Option.elim_some] at sameHead
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
    refine Eq.trans ?_ sameHead
    apply bind_congr_of_forall_mem_support
    rintro ⟨answer, after⟩ supported
    have present := step_answer baseImpl kem other selected pairs challenge candidate query before quiet affordable (answer, after) supported
    have capacity := step_capacity baseImpl kem other selected pairs challenge candidate query before clear affordable (answer, after) supported
    dsimp only at capacity
    cases answer with
    | none => exact False.elim (Bool.noConfusion present)
    | some answer =>
      have tailRoom : after.2.created + (if IsCreate query then qCreate - 1 else qCreate) ≤ pairs.length := by
        split_ifs at capacity ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      exact ih answer _ (bounded.2 answer) (by simpa using noReveal.2 answer) after capacity.1 tailRoom

end BeaconcryptCore.Computational.RegistrationNativeKemCandidateReservedProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCandidateReservedProgram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCandidateReservedProgram.program_source

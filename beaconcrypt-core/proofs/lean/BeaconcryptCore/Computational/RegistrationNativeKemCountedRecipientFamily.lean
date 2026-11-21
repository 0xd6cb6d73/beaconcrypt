-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedReservation

/-! A finite family of genuine recipient rows monitors the actual same encapsulation replies in a complete reserved execution. The joint row/cost sampler is retained, aliases are allowed and every adaptive continuation may depend on the entire private family. The bound concerns the operational primitive marker; protocol-root coverage is a separate source theorem. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily
open PqxdhServerAuthExperiment (Setup)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemCountedProgram (Spec)
open RegistrationNativeKemCountedRecipient (Bad Charged)
open RegistrationNativeKemCountedRecipientSample (Draw generation)
open RegistrationNativeKemCountedReservation (family reserved)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {count : Nat}

def AnyBad (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (rows : Fin count → Draw KemSK) (query : (Spec KemSK).Domain) (reply : (Spec KemSK).Range query) : Prop :=
  ∃ target, Bad setup functional (rows target).1 query reply

private theorem reserved_step (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (pair : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (tape : List (Draw KemSK))
    (query : (Spec KemSK).Domain) (before : Pool KemSK) :
    Pr{let result ← (reserved setup tape query).run before}[Bad setup functional pair query result.1] ≤
      if Charged query then RegistrationNativeRecipientFixedBound.error setup functional pair else 0 := by
  rcases query with uniform | (pool | key)
  · simp only [Bad, prEvent_false, Charged, ite_false, le_refl]
  · simp only [Bad, prEvent_false, Charged, ite_false, le_refl]
  · exact RegistrationNativeKemCountedRecipient.step setup functional pair (.inr (.inr key)) before

/-- The finite row union is charged on the same actual encapsulation reply, including public-key aliases. -/
theorem step (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (rows : Fin count → Draw KemSK) (tape : List (Draw KemSK))
    (query : (Spec KemSK).Domain) (before : Pool KemSK) :
    Pr{let result ← (reserved setup tape query).run before}[AnyBad setup functional rows query result.1] ≤
      if Charged query then ∑ target, RegistrationNativeRecipientFixedBound.error setup functional (rows target).1 else 0 := by
  calc
    _ ≤ ∑ target, Pr{let result ← (reserved setup tape query).run before}[Bad setup functional (rows target).1 query result.1] :=
      prEvent_exists_le _ _
    _ ≤ ∑ target, if Charged query then RegistrationNativeRecipientFixedBound.error setup functional (rows target).1 else 0 := by
      apply Finset.sum_le_sum
      intro target _member
      exact reserved_step setup functional (rows target).1 tape query before
    _ = _ := by
      by_cases charged : Charged query <;> simp only [charged, ite_true, ite_false, Finset.sum_const_zero]

/-- Each genuine family coordinate retains exactly its actual joint key/cost marginal. -/
theorem marginal (setup : Setup base KemSK) (target : Fin count) :
    EvalDistEq ((fun rows : Fin count → Draw KemSK => rows target) <$> family setup count) (generation setup) := by
  cases count with
  | zero => exact Fin.elim0 target
  | succ count =>
      have law := RegistrationNativeKemCountedReservation.family_target_first setup count target
        (fun rows => pure (rows target))
      simp only [Fin.insertNth_apply_same] at law
      have tail : EvalDistEq
          (do let chosen ← generation setup
              let others ← family setup count
              pure chosen) (generation setup) := by
        refine (EvalDistEq.bind_right _ (fun chosen => OracleComp.EvalDistEq.bind_const (family setup count) (pure chosen))).trans ?_
        simpa only [bind_pure] using (EvalDistEq.rfl : EvalDistEq (generation setup) (generation setup))
      simpa only [bind_pure_comp] using law.trans tail

/-- Averaging the exact joint family marginal gives the ordinary primitive recipient failure probability. -/
theorem error_average (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (target : Fin count) :
    (∑' rows, Pr{let sampled ← family setup count}[sampled = rows] *
      RegistrationNativeRecipientFixedBound.error setup functional (rows target).1) =
      RegistrationNativeRecipientFailure.failureRate setup := by
  calc
    _ = ∑' drawn, Pr{let sampled ← (fun rows : Fin count → Draw KemSK => rows target) <$> family setup count}[sampled = drawn] *
        RegistrationNativeRecipientFixedBound.error setup functional drawn.1 := (OracleComp.tsum_prEvent_map_mul _ _ _).symm
    _ = ∑' drawn, Pr{let sampled ← generation setup}[sampled = drawn] *
        RegistrationNativeRecipientFixedBound.error setup functional drawn.1 := by
      apply tsum_congr
      intro drawn
      rw [(marginal setup target).prEvent_eq (fun sampled => sampled = drawn)]
    _ = _ := (RegistrationNativeKemCountedRecipientSample.average_error setup functional).symm

/-- The expected sum of genuine row errors is count times the ordinary primitive error, with no distinct-public-key premise. -/
theorem total_error (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem) (count : Nat) :
    (∑' rows, Pr{let sampled ← family setup count}[sampled = rows] *
      ∑ target, RegistrationNativeRecipientFixedBound.error setup functional (rows target).1) =
      count * RegistrationNativeRecipientFailure.failureRate setup := by
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp only [error_average, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The actual same-reply family marker has a row-count times encapsulation-cap correctness bill. Native draw costs and full private source histories remain in the monitored execution. -/
theorem bound (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem) (count cap : Nat)
    (work : (Fin count → Draw KemSK) → OracleComp (Spec KemSK) Value)
    (bounded : ∀ rows, (work rows).IsQueryBoundP (Charged (KemSK := KemSK)) cap)
    (before : (Fin count → Draw KemSK) → Pool KemSK) :
    Pr{let result ← (family setup count >>= fun rows =>
      (simulateQ (RegistrationNativeRecipientQueryBound.handler (reserved setup (List.ofFn rows))
        (AnyBad setup functional rows)) (work rows)).run (before rows, false))}[result.2.2 = true] ≤
      count * cap * RegistrationNativeRecipientFailure.failureRate setup := by
  rw [prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' rows, Pr{let sampled ← family setup count}[sampled = rows] *
        (cap * ∑ target, RegistrationNativeRecipientFixedBound.error setup functional (rows target).1) := by
      apply ENNReal.tsum_le_tsum
      intro rows
      apply mul_le_mul' le_rfl
      simpa only [prEvent_norm] using RegistrationNativeRecipientQueryBound.bound
        (reserved setup (List.ofFn rows)) (AnyBad setup functional rows) Charged
        (∑ target, RegistrationNativeRecipientFixedBound.error setup functional (rows target).1)
        (step setup functional rows (List.ofFn rows)) (work rows) cap (bounded rows) (before rows)
    _ = cap * (∑' rows, Pr{let sampled ← family setup count}[sampled = rows] *
        ∑ target, RegistrationNativeRecipientFixedBound.error setup functional (rows target).1) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun rows => by ac_rfl
    _ = _ := by rw [total_error]; ac_rfl
end BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.marginal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.marginal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.error_average' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.error_average

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.total_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.total_error

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientFamily.bound

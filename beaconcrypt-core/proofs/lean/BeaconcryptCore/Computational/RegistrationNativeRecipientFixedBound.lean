-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecipientQueryBound
import BeaconcryptCore.Computational.PqxdhChallengeSecretRouting

/-! Actual fresh native encapsulation replies at one fixed generated recipient have a private correctness-failure marker bounded by their syntactic request cap. Averaging that fixed-recipient bound charges the literal ordinary honest-recipient failure probability. Functional decapsulation is explicit and does not imply perfect correctness. Selecting a recipient from the complete dynamic native family remains a separate ordinal/source coupling obligation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemInterface (Spec)
variable {κ ι KemSK Auxiliary V : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- The probability of an honestly encapsulated ciphertext failing at this exact recipient row. -/
noncomputable def error (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (pair : MlKem768PublicKey × KemSK) : ENNReal :=
  Pr{let encapsulated ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1)}[
    functional.result pair.2 encapsulated.1 ≠ some encapsulated.2]

def Charged : (Spec ambient KemSK).Domain → Prop
  | .inr (.inr _) => True
  | _ => False
instance : DecidablePred (Charged (ambient := ambient) (KemSK := KemSK)) := fun query => by
  rcases query with other | (pool | key) <;> simp only [Charged] <;> infer_instance

def Bad (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (pair : MlKem768PublicKey × KemSK) (query : (Spec ambient KemSK).Domain) : (Spec ambient KemSK).Range query → Prop :=
  match query with
  | .inr (.inr key) => fun reply => key = pair.1 ∧ functional.result pair.2 reply.1 ≠ some reply.2
  | _ => fun _ => False

/-- The literal native source response law is charged only at actual encapsulation requests. -/
theorem step (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pair : MlKem768PublicKey × KemSK)
    (query : (Spec ambient KemSK).Domain) (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    Pr{let result ← (RegistrationNativeKemInterface.source setup.baseImpl setup.kem ambient other query).run before}[
      Bad setup functional pair query result.1] ≤ if Charged query then error setup functional pair else 0 := by
  rcases query with otherQuery | (poolQuery | key)
  · simp [Bad, Charged]
  · simp [Bad, Charged]
  · by_cases same : key = pair.1
    · subst key
      simp only [RegistrationNativeKemInterface.source, StateT.run_lift, prEvent_norm, Bad,
        true_and, Charged, ite_true, error]
      exact le_rfl
    · simp [Bad, same, Charged]

/-- An actual bounded adaptive native source program has at most cap times the fixed recipient's actual primitive failure mass. -/
theorem bound (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pair : MlKem768PublicKey × KemSK)
    (work : OracleComp (Spec ambient KemSK) V) (cap : Nat) (bounded : work.IsQueryBoundP (Charged (ambient := ambient) (KemSK := KemSK)) cap)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    Pr{let result ← (simulateQ (RegistrationNativeRecipientQueryBound.handler
      (RegistrationNativeKemInterface.source setup.baseImpl setup.kem ambient other) (Bad setup functional pair)) work).run
        (before, false)}[result.2.2 = true] ≤ cap * error setup functional pair :=
  RegistrationNativeRecipientQueryBound.bound _ _ (Charged (ambient := ambient) (KemSK := KemSK)) _ (step setup functional other pair) work cap bounded before

/-- Averaging over one literal source-generated recipient gives the ordinary primitive experiment's failure mass, with no zero-error assumption. -/
theorem average_error (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem) :
    RegistrationNativeRecipientFailure.failureRate setup =
      ∑' pair, Pr{let sampled ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen}[sampled = pair] *
        error setup functional pair := by
  unfold RegistrationNativeRecipientFailure.failureRate RegistrationNativeRecipientFailure.experiment
  simp_rw [functional.exact, simulateQ_pure, pure_bind]
  rw [prEvent_bind_eq_tsum]
  simp only [error, prEvent_norm]

/-- The fixed-recipient source bound averages to cap times the literal ordinary recipient-failure probability, allowing an arbitrary adaptive program and initial state for each generated pair. -/
theorem averaged (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (work : (MlKem768PublicKey × KemSK) → OracleComp (Spec ambient KemSK) V) (cap : Nat)
    (bounded : ∀ pair, (work pair).IsQueryBoundP (Charged (ambient := ambient) (KemSK := KemSK)) cap)
    (before : (MlKem768PublicKey × KemSK) → Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    Pr{let result ← (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
      (simulateQ (RegistrationNativeRecipientQueryBound.handler
        (RegistrationNativeKemInterface.source setup.baseImpl setup.kem ambient other) (Bad setup functional pair)) (work pair)).run
          (before pair, false))}[result.2.2 = true] ≤ cap * RegistrationNativeRecipientFailure.failureRate setup := by
  rw [prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' pair, Pr{let sampled ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen}[sampled = pair] *
        (cap * error setup functional pair) := by
      apply ENNReal.tsum_le_tsum
      intro pair
      exact mul_le_mul' le_rfl (by simpa only [prEvent_norm] using bound setup functional other pair (work pair) cap (bounded pair) (before pair))
    _ = cap * (∑' pair, Pr{let sampled ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen}[sampled = pair] *
        error setup functional pair) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun pair => by ac_rfl
    _ = _ := by rw [← average_error setup functional]

end BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.average_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.average_error

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.averaged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound.averaged

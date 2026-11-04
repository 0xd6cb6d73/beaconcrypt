-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedProgram
import BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound

/-! A fixed genuine recipient is monitored on actual counted indexed encapsulation replies. Private source draw costs, the entire private pool and every adaptive continuation remain present. Averaging this local primitive bound charges the ordinary honest-recipient failure probability; selecting an actual generated protocol row still requires the separate family/source coupling. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemCountedProgram (Spec handler)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

def Charged : (Spec KemSK).Domain → Prop
  | .inr (.inr _) => True
  | _ => False
instance : DecidablePred (Charged (KemSK := KemSK)) := fun query => by
  rcases query with ordinary | (pool | key) <;> simp only [Charged] <;> infer_instance

def Bad (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (pair : MlKem768PublicKey × KemSK) (query : (Spec KemSK).Domain) : (Spec KemSK).Range query → Prop :=
  match query with
  | .inr (.inr key) => fun reply => key = pair.1 ∧ functional.result pair.2 reply.1.1 ≠ some reply.1.2
  | _ => fun _ => False

/-- Actual counted source encapsulation replies have their ordinary fixed-recipient failure law. -/
theorem step (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (pair : MlKem768PublicKey × KemSK) (query : (Spec KemSK).Domain) (before : Pool KemSK) :
    Pr{let result ← (handler setup.baseImpl setup.kem query).run before}[Bad setup functional pair query result.1] ≤
      if Charged query then RegistrationNativeRecipientFixedBound.error setup functional pair else 0 := by
  rcases query with ordinary | (pool | key)
  · simp only [Bad, prEvent_false, Charged, ite_false, le_refl]
  · simp only [Bad, prEvent_false, Charged, ite_false, le_refl]
  · by_cases same : key = pair.1
    · subst key
      have law := congrArg (fun distribution => Pr{let result ← distribution}[
          functional.result pair.2 result.1.1 ≠ some result.1.2])
        (RegistrationNativeKemCountedCapability.actual_forget setup.baseImpl setup.kem (.inr pair.1) before)
      simp only [RegistrationNativeKemCountedCapability.draw, StateT.run_lift,
        prEvent_norm] at law
      simp only [handler, Bad, true_and, Charged, ite_true, RegistrationNativeRecipientFixedBound.error]
      convert le_of_eq law using 1 <;> rfl
    · simp only [Bad, same, false_and, prEvent_false, Charged, ite_true, zero_le]

/-- The syntactic actual encapsulation cap bounds the private sticky error flag without dropping counts or native continuation state. -/
theorem bound (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (pair : MlKem768PublicKey × KemSK) (work : OracleComp (Spec KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (Charged (KemSK := KemSK)) cap) (before : Pool KemSK) :
    Pr{let result ← (simulateQ (RegistrationNativeRecipientQueryBound.handler
      (handler setup.baseImpl setup.kem) (Bad setup functional pair)) work).run (before, false)}[result.2.2 = true] ≤
      cap * RegistrationNativeRecipientFixedBound.error setup functional pair :=
  RegistrationNativeRecipientQueryBound.bound _ _ Charged _ (step setup functional pair) work cap bounded before

/-- A generated fixed target averages to the literal ordinary primitive failure probability, even when its complete program depends on that target. -/
theorem averaged (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : (MlKem768PublicKey × KemSK) → OracleComp (Spec KemSK) Value) (cap : Nat)
    (bounded : ∀ pair, (work pair).IsQueryBoundP (Charged (KemSK := KemSK)) cap)
    (before : (MlKem768PublicKey × KemSK) → Pool KemSK) :
    Pr{let result ← (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
      (simulateQ (RegistrationNativeRecipientQueryBound.handler (handler setup.baseImpl setup.kem)
        (Bad setup functional pair)) (work pair)).run (before pair, false))}[result.2.2 = true] ≤
      cap * RegistrationNativeRecipientFailure.failureRate setup := by
  rw [prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' pair, Pr{let sampled ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen}[sampled = pair] *
        (cap * RegistrationNativeRecipientFixedBound.error setup functional pair) := by
      apply ENNReal.tsum_le_tsum
      intro pair
      exact mul_le_mul' le_rfl (by simpa only [prEvent_norm] using bound setup functional pair (work pair) cap (bounded pair) (before pair))
    _ = cap * (∑' pair, Pr{let sampled ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen}[sampled = pair] *
        RegistrationNativeRecipientFixedBound.error setup functional pair) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun pair => by ac_rfl
    _ = _ := by rw [← RegistrationNativeRecipientFixedBound.average_error setup functional]
end BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient.averaged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient.averaged

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipient

/-! Honest recipient targets are sampled jointly with their actual source uniform cost. The cost may affect every later native continuation; averaging the error discards only that cost in the primitive error expression, never in source execution. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca (MlKem768PublicKey)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemCountedProgram (Spec handler)
open RegistrationNativeKemCountedRecipient (Bad Charged)
open PqxdhLiveKemBirth (Pool)
variable {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Draw (KemSK : Type) := (MlKem768PublicKey × KemSK) × Nat

noncomputable def generation (setup : Setup base KemSK) : ProbComp (Draw KemSK) :=
  (simulateQ PqxdhRecordLiftWorld.countCoin
    (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)).run 0

/-- Dropping the private cost from the sampled row leaves exactly the ordinary primitive key generation law. -/
theorem generation_forget (setup : Setup base KemSK) :
    Prod.fst <$> generation setup = simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen :=
  PqxdhRecordLiftWorld.countCoin_forget _ 0

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

set_option backward.isDefEq.respectTransparency false in
/-- Creating one actual row samples its real private key and exact count together, then appends the actual handle and complete source history. -/
theorem actual_create (setup : Setup base KemSK) (before : Pool KemSK) :
    (RegistrationNativeKemCountedCapability.actual setup.baseImpl setup.kem (.inl .create)).run before =
      (fun drawn => let result := PqxdhLiveKemBirth.created before drawn.1
        ((result.1, drawn.2), result.2)) <$> generation setup := by
  simp only [RegistrationNativeKemCountedCapability.actual, RegistrationNativeKemCountedCapability.draw,
    PqxdhLiveKemBirth.poolImpl, StateT.run, generation]
  rw [simulateQ_map, map_apply, Functor.map_map]
  rfl

/-- The exact joint row/cost expectation is still the ordinary one-key recipient error probability. -/
theorem average_error (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem) :
    RegistrationNativeRecipientFailure.failureRate setup =
      ∑' drawn, Pr{let sampled ← generation setup}[sampled = drawn] *
        RegistrationNativeRecipientFixedBound.error setup functional drawn.1 := by
  rw [RegistrationNativeRecipientFixedBound.average_error, ← generation_forget setup]
  exact OracleComp.tsum_prEvent_map_mul _ Prod.fst _

/-- Every later adaptive action may depend on both the actual private recipient and its exact source cost; the error still charges only the actual encapsulation cap. -/
theorem averaged (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (work : Draw KemSK → OracleComp (Spec KemSK) Value) (cap : Nat)
    (bounded : ∀ drawn, (work drawn).IsQueryBoundP (Charged (KemSK := KemSK)) cap)
    (before : Draw KemSK → Pool KemSK) :
    Pr{let result ← (generation setup >>= fun drawn =>
      (simulateQ (RegistrationNativeRecipientQueryBound.handler (handler setup.baseImpl setup.kem)
        (Bad setup functional drawn.1)) (work drawn)).run (before drawn, false))}[result.2.2 = true] ≤
      cap * RegistrationNativeRecipientFailure.failureRate setup := by
  rw [prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' drawn, Pr{let sampled ← generation setup}[sampled = drawn] *
        (cap * RegistrationNativeRecipientFixedBound.error setup functional drawn.1) := by
      apply ENNReal.tsum_le_tsum
      intro drawn
      exact mul_le_mul' le_rfl (by simpa only [prEvent_norm] using
        RegistrationNativeKemCountedRecipient.bound setup functional drawn.1 (work drawn) cap (bounded drawn) (before drawn))
    _ = cap * (∑' drawn, Pr{let sampled ← generation setup}[sampled = drawn] *
        RegistrationNativeRecipientFixedBound.error setup functional drawn.1) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun drawn => by ac_rfl
    _ = _ := by rw [← average_error setup functional]
end BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.generation_forget' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.generation_forget

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.actual_create' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.actual_create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.average_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.average_error

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.averaged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCountedRecipientSample.averaged

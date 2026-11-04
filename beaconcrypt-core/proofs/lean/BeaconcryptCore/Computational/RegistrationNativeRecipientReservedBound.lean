-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecipientFixedBound
import BeaconcryptCore.Computational.RegistrationNativeKemReservation

/-! The actual selected-first private-key reservation source has the same fresh encapsulation law. A bounded adaptive fixed-recipient marker therefore averages to the ordinary primitive error rate while retaining all reserved keys and actual source continuation state. Native whole-family bad-event coverage is a separate coupling obligation. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca (MlKem768PublicKey)
open PqxdhChallengeSecretRouting (FunctionalDecapsulation)
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeRecipientFixedBound (Bad Charged error)
variable {κ ι KemSK Auxiliary V : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- Literal reservation changes only private key birth and preserves the actual encapsulation response law. -/
theorem step (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pair : MlKem768PublicKey × KemSK)
    (pairs : List (MlKem768PublicKey × KemSK)) (query : (Spec ambient KemSK).Domain)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    Pr{let result ← (RegistrationNativeKemReservation.reserved setup.baseImpl setup.kem other pairs query).run before}[
      Bad setup functional pair query result.1] ≤ if Charged query then error setup functional pair else 0 := by
  rcases query with otherQuery | (poolQuery | key)
  · simp [Bad, Charged]
  · simp [Bad, Charged]
  · exact RegistrationNativeRecipientFixedBound.step setup functional other pair (.inr (.inr key)) before

/-- Every actual bounded adaptive reserved-source execution has the primitive fixed-recipient query bound. -/
theorem bound (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (pair : MlKem768PublicKey × KemSK)
    (pairs : List (MlKem768PublicKey × KemSK)) (work : OracleComp (Spec ambient KemSK) V) (cap : Nat)
    (bounded : work.IsQueryBoundP (Charged (ambient := ambient) (KemSK := KemSK)) cap)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    Pr{let result ← (simulateQ (RegistrationNativeRecipientQueryBound.handler
      (RegistrationNativeKemReservation.reserved setup.baseImpl setup.kem other pairs) (Bad setup functional pair)) work).run
        (before, false)}[result.2.2 = true] ≤ cap * error setup functional pair :=
  RegistrationNativeRecipientQueryBound.bound _ _ (Charged (ambient := ambient) (KemSK := KemSK)) _
    (step setup functional other pair pairs) work cap bounded before

noncomputable def selected {count : Nat} (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (target : Fin (count + 1))
    (work : (MlKem768PublicKey × KemSK) → (Fin count → MlKem768PublicKey × KemSK) → OracleComp (Spec ambient KemSK) V)
    (before : (MlKem768PublicKey × KemSK) → (Fin count → MlKem768PublicKey × KemSK) → Auxiliary × PqxdhLiveKemBirth.Pool KemSK) : ProbComp Bool := do
  let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let others ← PqxdhLiveKemSelection.sampleFamily (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) count
  let pairs := List.ofFn (target.insertNth chosen others)
  let result ← (simulateQ (RegistrationNativeRecipientQueryBound.handler
    (RegistrationNativeKemReservation.reserved setup.baseImpl setup.kem other pairs) (Bad setup functional chosen)) (work chosen others)).run
      (before chosen others, false)
  pure result.2.2

/-- Every selected-first reservation game is bounded by its actual encapsulation request cap times the ordinary recipient failure rate. The adaptive work may depend on every generated row. -/
theorem selected_bound {count : Nat} (setup : Setup base KemSK) (functional : FunctionalDecapsulation setup.kem)
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (target : Fin (count + 1))
    (work : (MlKem768PublicKey × KemSK) → (Fin count → MlKem768PublicKey × KemSK) → OracleComp (Spec ambient KemSK) V)
    (before : (MlKem768PublicKey × KemSK) → (Fin count → MlKem768PublicKey × KemSK) → Auxiliary × PqxdhLiveKemBirth.Pool KemSK)
    (cap : Nat) (bounded : ∀ pair others, (work pair others).IsQueryBoundP (Charged (ambient := ambient) (KemSK := KemSK)) cap) :
    Pr{let won ← selected setup functional other target work before}[won = true] ≤ cap * RegistrationNativeRecipientFailure.failureRate setup := by
  unfold selected
  rw [prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' chosen, Pr{let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen}[pair = chosen] *
        (cap * error setup functional chosen) := by
      apply ENNReal.tsum_le_tsum
      intro chosen
      apply mul_le_mul' le_rfl
      apply prEvent_bind_le_of_forall_le
      intro others
      simpa only [prEvent_norm] using bound setup functional other chosen (List.ofFn (target.insertNth chosen others))
        (work chosen others) cap (bounded chosen others) (before chosen others)
    _ = cap * (∑' chosen, Pr{let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen}[pair = chosen] *
        error setup functional chosen) := by
      rw [← ENNReal.tsum_mul_left]
      exact tsum_congr fun pair => by ac_rfl
    _ = _ := by rw [← RegistrationNativeRecipientFixedBound.average_error setup functional]

end BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound.bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound.selected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientReservedBound.selected_bound

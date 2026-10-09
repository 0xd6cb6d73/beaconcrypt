-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealTrace

/-!
# Guesser programs for the KEM ciphertext guess of the Beacon-side anomaly (CE-11b, unit U4)

The quantity that CE-12a's predict-then-compare IND-CCA reduction for `PqxdhDeploymentIdealTrace.Anomaly` can consume (plan section 49, Q2, option (b)):

- `ctGuessBy setup guess`: the probability that a guesser program, run on the public key of a fresh key pair before the encapsulation to that key, outputs the encapsulation's ciphertext. The guesser is an explicit program over the KEM's ambient oracles (`unifSpec + baseSpec`), the oracles of the pre-challenge phase of a `PqxdhKemIndCca.OneKeyAdversary` without its decapsulation oracle. `guess_preChallenge`: lifted into the IND-CCA oracle spec by `ambientLift`, it runs unchanged under the pre-challenge decapsulation oracle, which it never calls; `ctGuessBy_probComp`: the form for a guesser that is a `ProbComp`.
- `ctGuessBy_le`: every guesser's `ctGuessBy` is at most `PqxdhDeploymentIdealTrace.ctGuessPk` (through the best guess for each public key, `encapsHit_max`), hence at most `ctGuess` (`ctGuessBy_le_ctGuess`); `ctGuessPk_eq_iSup`: `ctGuessPk` is the supremum of `ctGuessBy` over all guessers, including inefficient ones. `ctGuessPk` is therefore an information-theoretic quantity of the scheme, which no approved assumption or contract bounds (plan section 40); the reduction needs `ctGuessBy` at a guesser constructed from the adversary.

Not here: `anomaly_le` (`Anomaly` on the record world with `envGD` bounded by `ctGuess`) and its public-key-only form, `Anomaly` bounded by `ctGuessBy` at an explicit guesser that runs the game prefix up to owner `k`'s first finish from the public key alone (CE-11b unit U4 guide, open points). These are definitions and inequalities between them; no security claim is made here.
-/

open OracleComp OracleSpec ENNReal MeasureTheory

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhInitializerSecrecy (kemAmbientImpl)
open PqxdhDeploymentIdealTrace (ctGuess ctGuessPk)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type} (setup : Setup baseSpec KemSK)

/-- The ciphertext guess of a guesser program (plan section 49, Q2): the probability that `guess`, run on the public key of a fresh key pair before the encapsulation to that key, outputs the encapsulation's ciphertext. The guesser runs over the KEM's ambient oracles, interpreted by the setup's fixed ambient interpreter like key generation and encapsulation. A definition, not an assumption. -/
noncomputable def ctGuessBy
    (guess : MlKem768PublicKey → OracleComp (unifSpec + baseSpec) MlKem768Ciphertext) : ENNReal :=
  𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (do
      let pair ← setup.kem.keygen
      let guessed ← guess pair.1
      let encapsulated ← setup.kem.encaps pair.1
      pure (decide (encapsulated.1 = guessed)))] {true}

/-- The probability that an encapsulation to the public key `pk` has the ciphertext `guessed`. -/
noncomputable def encapsHit (pk : MlKem768PublicKey) (guessed : MlKem768Ciphertext) : ENNReal :=
  𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pk) >>= fun encapsulated =>
      pure (decide (encapsulated.1 = guessed))] {true}

/-- For each public key some ciphertext is a best guess: ciphertexts form a finite type. -/
theorem encapsHit_max (pk : MlKem768PublicKey) :
    ∃ best, ∀ guessed, encapsHit setup pk guessed ≤ encapsHit setup pk best :=
  Finite.exists_max (encapsHit setup pk)

/-- Every guesser program's ciphertext guess is at most the public-key-only supremum `ctGuessPk`: replace each output of the guesser by the best guess for the public key. -/
theorem ctGuessBy_le
    (guess : MlKem768PublicKey → OracleComp (unifSpec + baseSpec) MlKem768Ciphertext) :
    ctGuessBy setup guess ≤ ctGuessPk setup := by
  let : MeasurableSpace MlKem768Ciphertext := ⊤
  let : DiscreteMeasurableSpace MlKem768Ciphertext := ⟨fun _ => trivial⟩
  let : MeasurableSpace (PqxdhLiveKemReservation.Pair KemSK) := ⊤
  let : DiscreteMeasurableSpace (PqxdhLiveKemReservation.Pair KemSK) := ⟨fun _ => trivial⟩
  choose best bestMax using encapsHit_max setup
  refine le_iSup_of_le best ?_
  simp only [ctGuessBy, simulateQ_bind, simulateQ_pure]
  rw [evalDist_bind_of_discrete, evalDist_bind_of_discrete,
    Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable),
    Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable)]
  refine lintegral_mono fun pair => ?_
  rw [evalDist_bind_of_discrete, Measure.bind_apply (.of_discrete) (Measurable.of_discrete.aemeasurable)]
  refine (lintegral_mono fun guessed => bestMax pair.1 guessed).trans ?_
  rw [lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)

/-- Every guesser program's ciphertext guess is at most `ctGuess`. -/
theorem ctGuessBy_le_ctGuess
    (guess : MlKem768PublicKey → OracleComp (unifSpec + baseSpec) MlKem768Ciphertext) :
    ctGuessBy setup guess ≤ ctGuess setup :=
  (ctGuessBy_le setup guess).trans (PqxdhDeploymentIdealTrace.ctGuessPk_le setup)

/-- `ctGuessPk` is the supremum of `ctGuessBy` over all guesser programs, including inefficient ones; the deterministic guessers already reach it. -/
theorem ctGuessPk_eq_iSup :
    ctGuessPk setup = ⨆ guess : MlKem768PublicKey → OracleComp (unifSpec + baseSpec) MlKem768Ciphertext,
      ctGuessBy setup guess :=
  le_antisymm
    (iSup_le fun guess => le_iSup_of_le (fun pk => pure (guess pk)) (le_of_eq (by simp only [ctGuessBy, pure_bind])))
    (iSup_le (ctGuessBy_le setup))

/-- The ciphertext guess of a guesser that is a `ProbComp`, lifted into the ambient oracles: the fixed ambient interpreter leaves it unchanged. -/
theorem ctGuessBy_probComp (guess : MlKem768PublicKey → ProbComp MlKem768Ciphertext) :
    ctGuessBy setup (fun pk => (liftM (guess pk) : OracleComp (unifSpec + baseSpec) MlKem768Ciphertext)) =
      𝒟[do
        let pair ← simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen
        let guessed ← guess pair.1
        let encapsulated ← simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1)
        pure (decide (encapsulated.1 = guessed))] {true} := by
  simp only [ctGuessBy, simulateQ_bind, simulateQ_pure, PqxdhInitializerSecrecy.simulateQ_kemAmbient_liftM_ProbComp]

/-- Forward the KEM's ambient oracles to the ambient part of the IND-CCA oracle spec: the lift of a guesser program into the pre-challenge phase of a `PqxdhKemIndCca.OneKeyAdversary`. -/
def ambientLift : QueryImpl (unifSpec + baseSpec) (OracleComp setup.kem.IND_CCA_oracleSpec) :=
  fun query => liftM (setup.kem.IND_CCA_oracleSpec.query (.inl query))

/-- A guesser program lifted into the IND-CCA oracle spec (`ambientLift`) runs unchanged under the pre-challenge decapsulation oracle of every secret key: it never queries decapsulation. -/
theorem guess_preChallenge
    (guess : MlKem768PublicKey → OracleComp (unifSpec + baseSpec) MlKem768Ciphertext) (sk : KemSK)
    (pk : MlKem768PublicKey) :
    simulateQ (setup.kem.IND_CCA_preChallengeImpl sk) (simulateQ (ambientLift setup) (guess pk)) = guess pk := by
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_id' (guess pk)]
  congr 1

end BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.encapsHit_max' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.encapsHit_max

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessBy_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessBy_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessBy_le_ctGuess' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessBy_le_ctGuess

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessPk_eq_iSup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessPk_eq_iSup

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessBy_probComp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.ctGuessBy_probComp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.guess_preChallenge' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomaly.guess_preChallenge

import BeaconcryptCore.Computational.PqxdhChallengeSecretRouting

/-!
The ordinary correctness-error endpoint samples one actual key pair, encapsulates to its public key, and invokes actual decapsulation. Rejection and recovery of a different secret both win. This error is separate from IND-CCA; no primitive internals or zero-error contract are proved.

A sampled secret key and encapsulated secret belong only to the private challenger and mathematical coupling context. Concrete private-root clients receive public key/ciphertext and their original permitted state, never this whole sample. Functional decapsulation remains an explicit complete-program contract, so agreement on a good sample preserves every repeated private root and the complete continuation. Query bills describe actual oracle syntax; local primitive invocation and computation are not erased by the functional equality.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhKemCorrectnessError
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting
open PqxdhJointKdfGame

variable {ι KemSK : Type} {baseSpec : OracleSpec ι}

/-- Private challenger state. It is never an argument to an executable adversarial client. -/
structure Sample (KemSK : Type) where
  publicKey : MlKem768PublicKey
  secretKey : KemSK
  ciphertext : MlKem768Ciphertext
  secret : MlKemSharedSecret

/-- Original key-generation then encapsulation order, retaining the complete joint result. -/
def sample (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    OracleComp (unifSpec + baseSpec) (Sample KemSK) := do
  let (publicKey, secretKey) ← kem.keygen
  let (ciphertext, secret) ← kem.encaps publicKey
  pure ⟨publicKey, secretKey, ciphertext, secret⟩

/-- An actual ordinary recipient error: absent or unequal recovered secret. -/
noncomputable def errorExperiment (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    OracleComp (unifSpec + baseSpec) Bool := do
  let drawn ← sample kem
  let recovered ← kem.decaps drawn.secretKey drawn.ciphertext
  pure (decide (recovered ≠ some drawn.secret))

def Bad (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem) (drawn : Sample KemSK) : Prop :=
  functional.result drawn.secretKey drawn.ciphertext ≠ some drawn.secret

instance (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem) : DecidablePred (Bad kem functional) :=
  fun drawn => inferInstanceAs (Decidable (functional.result drawn.secretKey drawn.ciphertext ≠ some drawn.secret))

/-- The actual decapsulation invocation has the given complete functional result; this does not assert correctness or zero local computation. -/
theorem error_functional (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem) :
    errorExperiment kem = (fun drawn => decide (Bad kem functional drawn)) <$> sample kem := by
  classical
  simp only [errorExperiment, functional.exact, map_pure, bind_pure_comp, Bad]
  rfl

/-- The ordinary endpoint is exactly the unconditioned bad-sample probability. -/
theorem error_probability (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem) :
    Pr[= true | simulateQ (kemAmbientImpl baseImpl) (errorExperiment kem)] =
      Pr[Bad kem functional | simulateQ (kemAmbientImpl baseImpl) (sample kem)] := by
  classical
  rw [error_functional kem functional, simulateQ_map, ← probEvent_eq_eq_probOutput, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq]

/-- Good samples give a literal decapsulation program equality without a perfect-correctness premise. -/
theorem good_agreement (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem) (drawn : Sample KemSK)
    (good : ¬ Bad kem functional drawn) :
    kem.decaps drawn.secretKey drawn.ciphertext = pure (some drawn.secret) := by
  rw [functional.exact]
  exact congrArg pure (Classical.not_not.mp good)

/-- Mathematical full-result coupling over private challenger samples. Concrete adversarial continuations must separately obey their public interface. -/
theorem continuation_bound {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (left right : Sample KemSK → ProbComp Result)
    (agree : ∀ drawn, ¬ Bad kem functional drawn → left drawn = right drawn) :
    tvDist (simulateQ (kemAmbientImpl baseImpl) (sample kem) >>= left)
      (simulateQ (kemAmbientImpl baseImpl) (sample kem) >>= right) ≤
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (errorExperiment kem)].toReal := by
  rw [error_probability baseImpl kem functional]
  have point : ∀ drawn, tvDist (left drawn) (right drawn) ≤
      Pr[Bad kem functional | (pure drawn : ProbComp (Sample KemSK))].toReal := by
    intro drawn
    by_cases bad : Bad kem functional drawn
    · simpa [probEvent_pure, bad] using tvDist_le_one (left drawn) (right drawn)
    · rw [agree drawn bad]
      simp [probEvent_pure, bad]
  simpa only [bind_pure] using PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind
    (simulateQ (kemAmbientImpl baseImpl) (sample kem)) left right
    (fun drawn => (pure drawn : ProbComp (Sample KemSK))) (Bad kem functional) point

/-- A public-key/ciphertext client may issue arbitrarily many private roots. The same one sampled correctness event bounds the full result and complete ambient poststate. -/
theorem routed_bound {Result State : Type}
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (client : MlKem768PublicKey → MlKem768Ciphertext → OracleComp (LocalPostSpec baseSpec) Result)
    (ambient : QueryImpl (unifSpec + baseSpec) (StateT State ProbComp))
    (initial : MlKem768PublicKey → MlKem768Ciphertext → State) :
    tvDist
      (do
        let drawn ← simulateQ (kemAmbientImpl baseImpl) (sample kem)
        (simulateQ ambient (simulateQ (actualImpl source kem drawn.secretKey drawn.ciphertext)
          (client drawn.publicKey drawn.ciphertext))).run (initial drawn.publicKey drawn.ciphertext))
      (do
        let drawn ← simulateQ (kemAmbientImpl baseImpl) (sample kem)
        (simulateQ ambient (simulateQ (publicImpl kem drawn.secretKey drawn.ciphertext)
          (simulateQ (route source drawn.ciphertext drawn.secret)
            (client drawn.publicKey drawn.ciphertext)))).run (initial drawn.publicKey drawn.ciphertext)) ≤
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (errorExperiment kem)].toReal := by
  apply continuation_bound baseImpl kem functional
  intro drawn good
  exact (route_stateful source kem drawn.secretKey drawn.ciphertext drawn.secret
    (good_agreement kem functional drawn good) (client drawn.publicKey drawn.ciphertext)
    ambient (initial drawn.publicKey drawn.ciphertext)).symm

/-- The actual sampling syntax pays key generation and encapsulation under every possible reply. -/
theorem sample_bound (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (predicate : (unifSpec + baseSpec).Domain → Prop) [DecidablePred predicate]
    (qKey qEncapsulation : Nat) (keyBound : kem.keygen.IsQueryBoundP predicate qKey)
    (encapsulationBound : ∀ key, (kem.encaps key).IsQueryBoundP predicate qEncapsulation) :
    (sample kem).IsQueryBoundP predicate (qKey + qEncapsulation) := by
  unfold sample
  apply isQueryBoundP_bind keyBound
  rintro ⟨publicKey, secretKey⟩ _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using encapsulationBound publicKey

/-- The error endpoint invokes actual decapsulation once and includes its explicit oracle-work allowance. Functional zero-query specialization does not erase that primitive's local invocation or runtime. -/
theorem error_bound (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (predicate : (unifSpec + baseSpec).Domain → Prop) [DecidablePred predicate]
    (qKey qEncapsulation qDecapsulation : Nat)
    (keyBound : kem.keygen.IsQueryBoundP predicate qKey)
    (encapsulationBound : ∀ key, (kem.encaps key).IsQueryBoundP predicate qEncapsulation)
    (decapsulationBound : ∀ key ciphertext, (kem.decaps key ciphertext).IsQueryBoundP predicate qDecapsulation) :
    (errorExperiment kem).IsQueryBoundP predicate (qKey + qEncapsulation + qDecapsulation) := by
  unfold errorExperiment
  apply isQueryBoundP_bind (sample_bound kem predicate qKey qEncapsulation keyBound encapsulationBound)
  intro drawn _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using decapsulationBound drawn.secretKey drawn.ciphertext

end BeaconcryptCore.Computational.PqxdhKemCorrectnessError

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessError.error_functional' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessError.error_functional

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessError.error_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessError.error_probability

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessError.good_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessError.good_agreement

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessError.continuation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessError.continuation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessError.routed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessError.routed_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessError.sample_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessError.sample_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessError.error_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessError.error_bound

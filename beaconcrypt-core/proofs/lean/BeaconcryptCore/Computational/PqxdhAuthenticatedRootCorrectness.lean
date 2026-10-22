import BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped

/-!
The same original key generation and unblocked prechallenge computation precede a possible stop and actual encapsulation. Two complete private continuations may retain the encapsulated secret in the initial Server root and every later native effect. Equality on supported good samples charges one unconditioned ordinary KEM correctness event, including every repeated matching root. No generator-order interchange or perfect-recipient premise is used.

Secret-bearing continuation arguments belong only to mathematical coupling and private interpreters. They are not an executable adversary interface. The concrete protocol must separately construct its routed client without the selected secret key or encapsulated secret and derive the good-sample equality from its complete source simulation. Functional decapsulation, primitive and native contracts retain their existing scope; no global protocol, evolving-chain or storage theorem is asserted.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
open PqxdhKemCorrectnessError
open PqxdhKemCorrectnessStopped (keyError)

variable {ι KemSK Result : Type} {baseSpec : OracleSpec ι}

/-- The actual public-key interface before encapsulation. It has no secret-key or shared-secret argument. -/
structure Prefix (baseSpec : OracleSpec ι) (Result : Type) where
  Context : Type
  prepare : MlKem768PublicKey → OracleComp (MlKemCCAOracleSpec baseSpec) Context
  proceed : MlKem768PublicKey → Context → Bool
  abort : MlKem768PublicKey → Context → OracleComp (MlKemCCAOracleSpec baseSpec) Result

/-- Complete private interpreter continuation; this type is not exposed to an adversary. -/
abbrev After (Context KemSK Result : Type) :=
  MlKem768PublicKey → KemSK → Context → MlKem768Ciphertext → MlKemSharedSecret → ProbComp Result

/-- The original unblocked prechallenge execution keeps its complete result and all effects. -/
noncomputable def prepare (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (stopped : Prefix baseSpec Result) (publicKey : MlKem768PublicKey) (secretKey : KemSK) : ProbComp stopped.Context :=
  simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (stopped.prepare publicKey))

/-- Only the continuing branch encapsulates; the same private callback receives the original ciphertext and shared secret. -/
noncomputable def after (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (stopped : Prefix baseSpec Result) (next : After stopped.Context KemSK Result)
    (publicKey : MlKem768PublicKey) (secretKey : KemSK) (context : stopped.Context) : ProbComp Result :=
  if stopped.proceed publicKey context then do
    let (ciphertext, secret) ← simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)
    next publicKey secretKey context ciphertext secret
  else simulateQ (kemAmbientImpl baseImpl)
    (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (stopped.abort publicKey context))

/-- Actual source order, with the full prechallenge result retained on both branches. -/
noncomputable def main (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (stopped : Prefix baseSpec Result) (next : After stopped.Context KemSK Result) : ProbComp Result := do
  let (publicKey, secretKey) ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  let context ← prepare baseImpl kem stopped publicKey secretKey
  after baseImpl kem stopped next publicKey secretKey context

-- The existing PqxdhHiddenRoot averaging argument, restricted to supported samples.
private theorem average_supported {Alpha Beta Gamma : Type} (sample : ProbComp Alpha)
    (left right : Alpha → ProbComp Beta) (badRun : Alpha → ProbComp Gamma) (bad : Gamma → Prop)
    (point : ∀ value ∈ support sample, discreteDistance (left value) (right value) ≤ Pr{let x ← badRun value}[bad x].toReal) :
    discreteDistance (sample >>= left) (sample >>= right) ≤ Pr{let x ← sample >>= badRun}[bad x].toReal := by
  rw [OracleComp.prEvent_bind_eq_tsum]
  rw [ENNReal.tsum_toReal_eq (fun value =>
    ENNReal.mul_ne_top (prEvent_ne_top _) (prEvent_ne_top _))]
  simp_rw [ENNReal.toReal_mul]
  refine (discreteDistance_bind_left_le sample left right).trans ?_
  refine Summable.tsum_le_tsum (fun value => ?_) ?_ ?_
  · by_cases present : value ∈ support sample
    · exact mul_le_mul_of_nonneg_left (point value present) ENNReal.toReal_nonneg
    · rw [prEvent_eq_zero_of_not_mem_support sample present, ENNReal.toReal_zero, zero_mul, zero_mul]
  · exact Summable.of_nonneg_of_le
      (fun value => mul_nonneg ENNReal.toReal_nonneg
        (discreteDistance_nonneg (left value) (right value)))
      (fun value => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (discreteDistance_le_one (left value) (right value)))
      (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (OracleComp.tsum_prEvent_le_one sample)))
  · exact Summable.of_nonneg_of_le
      (fun value => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun value => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (ENNReal.toReal_mono one_ne_top (prEvent_le_one _)))
      (ENNReal.summable_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (OracleComp.tsum_prEvent_le_one sample)))

/-- At one reached prechallenge state, complete continuations agree except on this key's ordinary correctness event. -/
theorem after_bound (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (stopped : Prefix baseSpec Result) (left right : After stopped.Context KemSK Result)
    (publicKey : MlKem768PublicKey) (secretKey : KemSK) (context : stopped.Context)
    (agreement : stopped.proceed publicKey context = true →
      ∀ pair ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)),
        functional.result secretKey pair.1 = some pair.2 →
          left publicKey secretKey context pair.1 pair.2 = right publicKey secretKey context pair.1 pair.2) :
    discreteDistance (after baseImpl kem stopped left publicKey secretKey context)
      (after baseImpl kem stopped right publicKey secretKey context) ≤
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (keyError kem publicKey secretKey)}[x = true].toReal := by
  by_cases proceed : stopped.proceed publicKey context = true
  · simp only [after, proceed, ite_true, keyError, simulateQ_bind]
    apply average_supported
    intro pair supported
    by_cases good : functional.result secretKey pair.1 = some pair.2
    · simp only [agreement proceed pair supported good, discreteDistance_self, ENNReal.toReal_nonneg]
    · simp only [functional.exact, simulateQ_pure]
      rw [pure_bind (functional.result secretKey pair.1), prEvent_pure]
      simpa only [decide_eq_true good, ite_true, ENNReal.toReal_one] using
        discreteDistance_le_one (left publicKey secretKey context pair.1 pair.2)
          (right publicKey secretKey context pair.1 pair.2)
  · refine le_of_eq_of_le ?_ ENNReal.toReal_nonneg
    simp [after, proceed]

/-- Averaging the original prechallenge execution requires agreement only on its actual supported states and does not condition the error on proceeding. -/
theorem prepared_bound (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (stopped : Prefix baseSpec Result) (left right : After stopped.Context KemSK Result)
    (publicKey : MlKem768PublicKey) (secretKey : KemSK)
    (agreement : ∀ context ∈ support (prepare baseImpl kem stopped publicKey secretKey),
      stopped.proceed publicKey context = true →
      ∀ pair ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)),
        functional.result secretKey pair.1 = some pair.2 →
          left publicKey secretKey context pair.1 pair.2 = right publicKey secretKey context pair.1 pair.2) :
    discreteDistance
      (prepare baseImpl kem stopped publicKey secretKey >>= after baseImpl kem stopped left publicKey secretKey)
      (prepare baseImpl kem stopped publicKey secretKey >>= after baseImpl kem stopped right publicKey secretKey) ≤
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (keyError kem publicKey secretKey)}[x = true].toReal := by
  exact discreteDistance_bind_left_le_const _ _ _ _ (fun context supported =>
    after_bound baseImpl kem functional stopped left right publicKey secretKey context (agreement context supported))

/-- One unconditioned ordinary correctness error bounds the complete original stopped execution. The only simulation premise concerns generated, reached, continuing good samples; it is not a primitive security assumption. -/
theorem main_bound (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (stopped : Prefix baseSpec Result) (left right : After stopped.Context KemSK Result)
    (agreement : ∀ keys ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen),
      ∀ context ∈ support (prepare baseImpl kem stopped keys.1 keys.2),
      stopped.proceed keys.1 context = true →
      ∀ pair ∈ support (simulateQ (kemAmbientImpl baseImpl) (kem.encaps keys.1)),
        functional.result keys.2 pair.1 = some pair.2 →
          left keys.1 keys.2 context pair.1 pair.2 = right keys.1 keys.2 context pair.1 pair.2) :
    discreteDistance (main baseImpl kem stopped left) (main baseImpl kem stopped right) ≤
      Pr{let x ← simulateQ (kemAmbientImpl baseImpl) (errorExperiment kem)}[x = true].toReal := by
  simp only [main, PqxdhKemCorrectnessStopped.error_keygen, simulateQ_bind]
  apply average_supported
  exact fun keys supported =>
    prepared_bound baseImpl kem functional stopped left right keys.1 keys.2 (agreement keys supported)

/-- Stopping retains the original abort computation and makes no encapsulation call. -/
theorem stopped_branch (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (stopped : Prefix baseSpec Result) (next : After stopped.Context KemSK Result)
    (publicKey : MlKem768PublicKey) (secretKey : KemSK) (context : stopped.Context)
    (stop : stopped.proceed publicKey context = false) :
    after baseImpl kem stopped next publicKey secretKey context =
      simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (stopped.abort publicKey context)) := by
  simp only [after, stop, Bool.false_eq_true, ite_false]

/-- The actual interpreted branch pays encapsulation and its entire continuation, or the original abort. These are all-reply uniform-query bills, not local machine-work claims or consequences of distribution equality. -/
theorem after_uniform_bound (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (stopped : Prefix baseSpec Result) (next : After stopped.Context KemSK Result)
    (publicKey : MlKem768PublicKey) (secretKey : KemSK) (context : stopped.Context)
    (qAbort qEncapsulation qNext : Nat)
    (abortBound : (simulateQ (kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (stopped.abort publicKey context))).IsTotalQueryBound qAbort)
    (encapsulationBound : (simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)).IsTotalQueryBound qEncapsulation)
    (nextBound : ∀ ciphertext secret, (next publicKey secretKey context ciphertext secret).IsTotalQueryBound qNext) :
    (after baseImpl kem stopped next publicKey secretKey context).IsTotalQueryBound
      (max qAbort (qEncapsulation + qNext)) := by
  unfold after
  split
  · exact (isTotalQueryBound_bind encapsulationBound (fun pair => nextBound pair.1 pair.2)).mono
      (Nat.le_max_right _ _)
  · exact abortBound.mono (Nat.le_max_left _ _)

/-- The source program pays actual key generation and all prechallenge work before its chosen branch. Each side of the coupling receives its own syntactic bill, including all continuation decapsulation/root work; probability equality is not used for resource transport. -/
theorem main_uniform_bound (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (stopped : Prefix baseSpec Result) (next : After stopped.Context KemSK Result)
    (qKey qPrepare qAbort qEncapsulation qNext : Nat)
    (keyBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKey)
    (prepareBound : ∀ publicKey secretKey,
      (prepare baseImpl kem stopped publicKey secretKey).IsTotalQueryBound qPrepare)
    (abortBound : ∀ publicKey secretKey context, (simulateQ (kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (stopped.abort publicKey context))).IsTotalQueryBound qAbort)
    (encapsulationBound : ∀ publicKey,
      (simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)).IsTotalQueryBound qEncapsulation)
    (nextBound : ∀ publicKey secretKey context ciphertext secret,
      (next publicKey secretKey context ciphertext secret).IsTotalQueryBound qNext) :
    (main baseImpl kem stopped next).IsTotalQueryBound
      (qKey + qPrepare + max qAbort (qEncapsulation + qNext)) := by
  simpa only [main, Nat.add_assoc] using isTotalQueryBound_bind keyBound
    (fun keys => isTotalQueryBound_bind (prepareBound keys.1 keys.2)
      (fun context => after_uniform_bound baseImpl kem stopped next keys.1 keys.2 context
        qAbort qEncapsulation qNext (abortBound keys.1 keys.2 context)
        (encapsulationBound keys.1) (nextBound keys.1 keys.2 context)))

end BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.after_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.prepared_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.prepared_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.main_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.main_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.stopped_branch' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.stopped_branch

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.after_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.after_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.main_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhAuthenticatedRootCorrectness.main_uniform_bound

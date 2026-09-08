import BeaconcryptCore.Computational.PqxdhKemCorrectnessError

/-!
An actual prechallenge program may stop before encapsulation. Its full private result is retained on either branch. The continuation receives only public key/ciphertext and that original permitted state; sampled key and shared-secret bytes stay in the challenger/interpreter. Correctness error is charged without conditioning on reaching the challenge, and every repeated matching root shares the same event. All original perfect-correctness theorems remain unchanged.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
open PqxdhKemCorrectnessError

variable {ι KemSK Result : Type} {baseSpec : OracleSpec ι}

/-- Clients never receive the sampled secret key or encapsulated secret. Context retains their actual permitted private state. -/
structure StoppedProtocol (baseSpec : OracleSpec ι) (Result : Type) where
  Context : Type
  prepare : MlKem768PublicKey → OracleComp (MlKemCCAOracleSpec baseSpec) Context
  proceed : MlKem768PublicKey → Context → Bool
  abort : MlKem768PublicKey → Context → OracleComp (MlKemCCAOracleSpec baseSpec) Result
  resume : MlKem768PublicKey → MlKem768Ciphertext → Context → OracleComp (LocalPostSpec baseSpec) Result

/-- The ordinary error endpoint at one private sampled key pair. -/
noncomputable def keyError (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (publicKey : MlKem768PublicKey) (secretKey : KemSK) : OracleComp (unifSpec + baseSpec) Bool := do
  let (ciphertext, secret) ← kem.encaps publicKey
  let recovered ← kem.decaps secretKey ciphertext
  pure (decide (recovered ≠ some secret))

/-- The same original ordinary endpoint, with no protocol selection or conditioning. -/
theorem error_keygen (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    errorExperiment kem = (do
      let (publicKey, secretKey) ← kem.keygen
      keyError kem publicKey secretKey) := by
  simp only [errorExperiment, sample, keyError, bind_assoc, pure_bind]

/-- Both modes execute a stopped branch before encapsulation; the mode selects only the private challenge interpretation after an actual continuation. -/
noncomputable def after (routed : Bool) (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (protocol : StoppedProtocol baseSpec Result) (publicKey : MlKem768PublicKey) (secretKey : KemSK)
    (context : protocol.Context) : OracleComp (unifSpec + baseSpec) Result :=
  if protocol.proceed publicKey context then do
    let (ciphertext, secret) ← kem.encaps publicKey
    if routed then
      simulateQ (publicImpl kem secretKey ciphertext)
        (simulateQ (route source ciphertext secret) (protocol.resume publicKey ciphertext context))
    else simulateQ (actualImpl source kem secretKey ciphertext) (protocol.resume publicKey ciphertext context)
  else simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.abort publicKey context)

/-- Actual source generation and prechallenge effects keep their order, including the complete state used to stop or resume. -/
noncomputable def main (routed : Bool) (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (protocol : StoppedProtocol baseSpec Result) : OracleComp (unifSpec + baseSpec) Result := do
  let (publicKey, secretKey) ← kem.keygen
  let context ← simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.prepare publicKey)
  after routed source kem protocol publicKey secretKey context

/-- Once the actual prechallenge state is fixed, the full continuation differs only on this key's ordinary encapsulation/decapsulation error. -/
theorem after_bound (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (protocol : StoppedProtocol baseSpec Result) (publicKey : MlKem768PublicKey) (secretKey : KemSK)
    (context : protocol.Context) :
    tvDist (simulateQ (kemAmbientImpl baseImpl) (after false source kem protocol publicKey secretKey context))
      (simulateQ (kemAmbientImpl baseImpl) (after true source kem protocol publicKey secretKey context)) ≤
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (keyError kem publicKey secretKey)].toReal := by
  by_cases proceed : protocol.proceed publicKey context = true
  · simp only [after, proceed, if_true, Bool.false_eq_true, if_false, simulateQ_bind]
    let left (pair : MlKem768Ciphertext × MlKemSharedSecret) :=
      simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (actualImpl source kem secretKey pair.1) (protocol.resume publicKey pair.1 context))
    let right (pair : MlKem768Ciphertext × MlKemSharedSecret) :=
      simulateQ (kemAmbientImpl baseImpl) (simulateQ (publicImpl kem secretKey pair.1)
        (simulateQ (route source pair.1 pair.2) (protocol.resume publicKey pair.1 context)))
    let badRun (pair : MlKem768Ciphertext × MlKemSharedSecret) : ProbComp Bool :=
      simulateQ (kemAmbientImpl baseImpl) (do
        let recovered ← kem.decaps secretKey pair.1
        pure (decide (recovered ≠ some pair.2)))
    have point : ∀ pair, tvDist (left pair) (right pair) ≤ Pr[= true | badRun pair].toReal := by
      rintro ⟨ciphertext, secret⟩
      by_cases good : functional.result secretKey ciphertext = some secret
      · have agreement : kem.decaps secretKey ciphertext = pure (some secret) :=
          (functional.exact secretKey ciphertext).trans (congrArg pure good)
        have equal : left (ciphertext, secret) = right (ciphertext, secret) :=
          congrArg (simulateQ (kemAmbientImpl baseImpl))
            (route_complete source kem secretKey ciphertext secret agreement
              (protocol.resume publicKey ciphertext context)).symm
        rw [equal]
        simp
      · simpa only [badRun, functional.exact, pure_bind, simulateQ_pure, probOutput_pure,
          decide_eq_true good, if_true, ENNReal.toReal_one] using
          tvDist_le_one (left (ciphertext, secret)) (right (ciphertext, secret))
    have averaged := PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind
      (simulateQ (kemAmbientImpl baseImpl) (kem.encaps publicKey)) left right badRun (fun result => result = true)
      (fun pair => by simpa only [probEvent_eq_eq_probOutput] using point pair)
    simpa only [keyError, left, right, badRun, simulateQ_bind, ← probEvent_eq_eq_probOutput] using averaged
  · simp [after, proceed]

/-- The actual prechallenge state may select an immediate abort. Averaging its complete continuation never conditions the correctness endpoint on continuing. -/
theorem prepared_bound (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (protocol : StoppedProtocol baseSpec Result) (publicKey : MlKem768PublicKey) (secretKey : KemSK) :
    tvDist
      (do
        let context ← simulateQ (kemAmbientImpl baseImpl)
          (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.prepare publicKey))
        simulateQ (kemAmbientImpl baseImpl) (after false source kem protocol publicKey secretKey context))
      (do
        let context ← simulateQ (kemAmbientImpl baseImpl)
          (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.prepare publicKey))
        simulateQ (kemAmbientImpl baseImpl) (after true source kem protocol publicKey secretKey context)) ≤
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (keyError kem publicKey secretKey)].toReal := by
  have averaged := PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind
    (simulateQ (kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.prepare publicKey)))
    (fun context => simulateQ (kemAmbientImpl baseImpl) (after false source kem protocol publicKey secretKey context))
    (fun context => simulateQ (kemAmbientImpl baseImpl) (after true source kem protocol publicKey secretKey context))
    (fun _ => simulateQ (kemAmbientImpl baseImpl) (keyError kem publicKey secretKey))
    (fun result => result = true)
    (fun context => by
      simpa only [probEvent_eq_eq_probOutput] using
        (after_bound source baseImpl kem functional protocol publicKey secretKey context))
  simpa only [probEvent_bind_const, probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul,
    probEvent_eq_eq_probOutput] using averaged

/-- One ordinary correctness error bounds the same full stopped adaptive protocol. Every matching root shares that event; neither a reached-challenge condition nor an authentication premise appears. -/
theorem stopped_bound (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (functional : FunctionalDecapsulation kem)
    (protocol : StoppedProtocol baseSpec Result) :
    tvDist (simulateQ (kemAmbientImpl baseImpl) (main false source kem protocol))
      (simulateQ (kemAmbientImpl baseImpl) (main true source kem protocol)) ≤
      Pr[= true | simulateQ (kemAmbientImpl baseImpl) (errorExperiment kem)].toReal := by
  simp only [main, simulateQ_bind]
  have averaged := PqxdhHiddenRoot.tvDist_bind_left_le_probEvent_bind
    (simulateQ (kemAmbientImpl baseImpl) kem.keygen)
    (fun pair => do
      let context ← simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (kem.IND_CCA_preChallengeImpl pair.2) (protocol.prepare pair.1))
      simulateQ (kemAmbientImpl baseImpl) (after false source kem protocol pair.1 pair.2 context))
    (fun pair => do
      let context ← simulateQ (kemAmbientImpl baseImpl)
        (simulateQ (kem.IND_CCA_preChallengeImpl pair.2) (protocol.prepare pair.1))
      simulateQ (kemAmbientImpl baseImpl) (after true source kem protocol pair.1 pair.2 context))
    (fun pair => simulateQ (kemAmbientImpl baseImpl) (keyError kem pair.1 pair.2))
    (fun result => result = true)
    (fun pair => by
      simpa only [probEvent_eq_eq_probOutput] using
        (prepared_bound source baseImpl kem functional protocol pair.1 pair.2))
  simpa only [error_keygen, simulateQ_bind, probEvent_eq_eq_probOutput] using averaged

/-- A source stop performs the original abort program without drawing a ciphertext or shared secret. -/
theorem stopped_branch (routed : Bool) (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (protocol : StoppedProtocol baseSpec Result) (publicKey : MlKem768PublicKey) (secretKey : KemSK)
    (context : protocol.Context) (stopped : protocol.proceed publicKey context = false) :
    after routed source kem protocol publicKey secretKey context =
      simulateQ (kem.IND_CCA_preChallengeImpl secretKey) (protocol.abort publicKey context) := by
  simp only [after, stopped, Bool.false_eq_true, if_false]

/-- The actual selected branch pays its own interpreted callbacks, including all private-root work. This syntactic bill does not use an evaluated-distribution equality. -/
theorem after_query_bound (routed : Bool) (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (protocol : StoppedProtocol baseSpec Result) (publicKey : MlKem768PublicKey) (secretKey : KemSK)
    (context : protocol.Context) (predicate : (unifSpec + baseSpec).Domain → Prop)
    [DecidablePred predicate] (qAbort qEncapsulation qResume : Nat)
    (abortBound : (simulateQ (kem.IND_CCA_preChallengeImpl secretKey)
      (protocol.abort publicKey context)).IsQueryBoundP predicate qAbort)
    (encapsulationBound : (kem.encaps publicKey).IsQueryBoundP predicate qEncapsulation)
    (resumeBound : ∀ ciphertext secret,
      (if routed then
        simulateQ (publicImpl kem secretKey ciphertext)
          (simulateQ (route source ciphertext secret) (protocol.resume publicKey ciphertext context))
      else simulateQ (actualImpl source kem secretKey ciphertext)
        (protocol.resume publicKey ciphertext context)).IsQueryBoundP predicate qResume) :
    (after routed source kem protocol publicKey secretKey context).IsQueryBoundP predicate
      (max qAbort (qEncapsulation + qResume)) := by
  unfold after
  split
  · apply IsQueryBoundP.mono (n := qEncapsulation + qResume)
    · apply isQueryBoundP_bind encapsulationBound
      rintro ⟨ciphertext, secret⟩ _
      exact resumeBound ciphertext secret
    · exact Nat.le_max_right _ _
  · exact abortBound.mono (Nat.le_max_left _ _)

/-- The complete actual source pays generation and prechallenge work before the maximum of its abort and continuing bills. Encapsulation is charged only on the continuing branch; every later callback is included in the supplied interpreted continuation cap. -/
theorem main_query_bound (routed : Bool) (source : FixedHkdfSha512NoSaltSource)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (protocol : StoppedProtocol baseSpec Result)
    (predicate : (unifSpec + baseSpec).Domain → Prop) [DecidablePred predicate]
    (qKey qPrepare qAbort qEncapsulation qResume : Nat)
    (keyBound : kem.keygen.IsQueryBoundP predicate qKey)
    (prepareBound : ∀ publicKey secretKey,
      (simulateQ (kem.IND_CCA_preChallengeImpl secretKey)
        (protocol.prepare publicKey)).IsQueryBoundP predicate qPrepare)
    (abortBound : ∀ publicKey secretKey context,
      (simulateQ (kem.IND_CCA_preChallengeImpl secretKey)
        (protocol.abort publicKey context)).IsQueryBoundP predicate qAbort)
    (encapsulationBound : ∀ publicKey, (kem.encaps publicKey).IsQueryBoundP predicate qEncapsulation)
    (resumeBound : ∀ publicKey secretKey context ciphertext secret,
      (if routed then
        simulateQ (publicImpl kem secretKey ciphertext)
          (simulateQ (route source ciphertext secret) (protocol.resume publicKey ciphertext context))
      else simulateQ (actualImpl source kem secretKey ciphertext)
        (protocol.resume publicKey ciphertext context)).IsQueryBoundP predicate qResume) :
    (main routed source kem protocol).IsQueryBoundP predicate
      (qKey + qPrepare + max qAbort (qEncapsulation + qResume)) := by
  unfold main
  rw [Nat.add_assoc]
  apply isQueryBoundP_bind keyBound
  rintro ⟨publicKey, secretKey⟩ _
  apply isQueryBoundP_bind (prepareBound publicKey secretKey)
  intro context _
  exact after_query_bound routed source kem protocol publicKey secretKey context predicate
    qAbort qEncapsulation qResume (abortBound publicKey secretKey context)
    (encapsulationBound publicKey) (resumeBound publicKey secretKey context)

end BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.error_keygen' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.error_keygen

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.after_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.prepared_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.prepared_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.stopped_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.stopped_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.stopped_branch' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.stopped_branch

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.after_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.after_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.main_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCorrectnessStopped.main_query_bound

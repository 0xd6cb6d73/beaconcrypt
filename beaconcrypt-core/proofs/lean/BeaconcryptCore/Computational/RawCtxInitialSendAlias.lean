import BeaconcryptCore.Computational.RawCtxSendLineageCollision
import BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy

/-!
The initial cross-direction send-chain alias is charged through the actual fixed-HKDF output at its exact joint root/context sampler. The complete supplied continuation runs with both native constructors and one shared64 response. The bound retains explicit Extract and HMAC advantages; the 256-bit term applies only after their checked comparison. No entropy, secrecy or independence of an arbitrary caller's root sampler is asserted.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInitialSendAlias
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhInitialRootLabelService RawCtxSendLineageCollision

abbrev Continue (Context Result : Type) := Context → Response →
  RustM ConcreteRatchetKernel → RustM ConcreteRatchetKernel → ProbComp Result

def Alias (response : Response) : Prop :=
  PqxdhInitialRatchetComplementarity.firstHalf response.bytes =
    PqxdhInitialRatchetComplementarity.secondHalf response.bytes

noncomputable def observe {Context Result : Type} (resume : Continue Context Result)
    (context : Context) (response : Response) : ProbComp Bool := by
  classical
  exact (fun _ => decide (Alias response)) <$> resume context response
    (PqxdhInitialReplyErasure.kernelOf true response) (PqxdhInitialReplyErasure.kernelOf false response)

noncomputable def sampler {Context : Type} (sample : ProbComp (Context × RootOutput)) : SecretInputSampler Context :=
  ((fun pair => (pair.1, pair.2.toList)) <$> sample : ProbComp (Context × Pqxdh.Bytes))

noncomputable def observer {Context Result : Type} (resume : Continue Context Result) : FullObserver Context :=
  fun context output => observe resume context (RawCtxSelectedInitialConstructor.response64 (initialPrefix output))

noncomputable def real {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × RootOutput)) (resume : Continue Context Result) : ProbComp Bool :=
  sample >>= fun pair => observe resume pair.1 (realInitial source pair.2)

noncomputable def random {Context Result : Type} (sample : ProbComp (Context × RootOutput))
    (resume : Continue Context Result) : ProbComp Bool := do
  let pair ← sample
  let output ← $ᵗ HmacBlock
  observe resume pair.1 (RawCtxSelectedInitialConstructor.response64 output)

/-- The native comparison of two source initialization halves is equality of those same retained64-byte coordinates. -/
theorem response_alias (output : HmacBlock) :
    Alias (RawCtxSelectedInitialConstructor.response64 output) ↔ InitialAlias output := by
  have halves := initial_half_alias (PqxdhSecretInputKdf.first32 output)
    (RawCtxSelectedInitialSampler.initialOther output)
  simpa only [RawCtxSelectedInitialConstructor.split_reconstruct, Alias, InitialAlias] using halves

/-- The real primitive observer is the actual source initializer and both native constructors under the original joint root/context sampler. -/
theorem real_source {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (sample : ProbComp (Context × RootOutput)) (resume : Continue Context Result) :
    sourceFullGame source .ratchet (sampler sample) (observer resume) = real source sample resume := by
  simp only [sourceFullGame, sampler, bind_map_left, observer, real, PqxdhInitialCurrentSecrecy.response_prefix]

/-- The ideal comparison gives the same one shared64 response to both directions and the complete original continuation. -/
theorem random_source {Context Result : Type} (sample : ProbComp (Context × RootOutput))
    (resume : Continue Context Result) :
    𝒟[independentFullGame (sampler sample) (observer resume)] = 𝒟[random sample resume] := by
  apply EvalDistEq.evalDist_eq
  simp only [independentFullGame, sampler, bind_map_left, random]
  refine EvalDistEq.bind_right sample fun pair => ?_
  have projected := initialPrefix_uniform.bind_left fun output =>
    observe resume pair.1 (RawCtxSelectedInitialConstructor.response64 output)
  simpa only [bind_map_left, observer] using projected

/-- All source continuation effects occur before the collision decision; even failure or adaptive stopping does not increase the uniform64 half-equality probability. -/
theorem random_bound {Context Result : Type} (sample : ProbComp (Context × RootOutput))
    (resume : Continue Context Result) :
    Pr{let x ← random sample resume}[x = true] ≤ (1 : ENNReal) / (2 ^ 256 : ENNReal) := by
  classical
  unfold random
  have aliasBound := initial_alias_uniform
  generalize sampled : ($ᵗ HmacBlock : ProbComp HmacBlock) = block at aliasBound ⊢
  refine prEvent_bind_le_of_forall_le _ _ _ fun pair => ?_
  refine (prEvent_bind_le_prEvent_of_support _ _ InitialAlias _ ?_).trans aliasBound
  intro output _ different
  have noAlias := (response_alias output).not.mpr different
  simp only [observe, prEvent_map, decide_eq_false noAlias, Bool.false_eq_true]
  exact prEvent_false _

/-- Both advantages retain the exact joint root/context sampler and literal native continuation. No smallness is postulated. -/
noncomputable def reductionLoss {Context Result : Type} (hmac : HmacSha512)
    (sample : ProbComp (Context × RootOutput)) (resume : Continue Context Result) : ℝ :=
  (extractRealGame hmac (sampler sample) (fullExtractReduction hmac .ratchet (observer resume))).boolDistAdvantage
    (extractUniformGame (sampler sample) (fullExtractReduction hmac .ratchet (observer resume))) +
  (hmacPrfRealGame hmac (fullExpandReduction .ratchet (sampler sample) (observer resume))).boolDistAdvantage
    (hmacPrfRandomGame (fullExpandReduction .ratchet (sampler sample) (observer resume)))

/-- The actual fixed-HKDF comparison pays one exact-sampler Extract advantage and one ordinary secret-key HMAC PRF advantage, with coefficient one each. -/
theorem primitive_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp (Context × RootOutput)) (resume : Continue Context Result) :
    (real source sample resume).boolDistAdvantage (random sample resume) ≤ reductionLoss hmac sample resume := by
  have ideal := random_source sample resume
  simpa only [real_source, ProbComp.boolDistAdvantage, ideal, reductionLoss] using
    sourceFullAdvantage_le_extract_add_hmac source hmac correct .ratchet (sampler sample) (observer resume)

/-- The actual source initial send-alias probability is bounded only after charging its two displayed computational reductions. The final statistical term uses one shared64 response. -/
theorem source_bound {Context Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (hmac : HmacSha512) (correct : SourceFullCorrect source hmac)
    (sample : ProbComp (Context × RootOutput)) (resume : Continue Context Result) :
    Pr{let x ← real source sample resume}[x = true] ≤
      (1 : ENNReal) / (2 ^ 256 : ENNReal) + ENNReal.ofReal (reductionLoss hmac sample resume) := by
  have randomMeasure : 𝒟[random sample resume] {true} ≤ (1 : ENNReal) / (2 ^ 256 : ENNReal) := by
    rw [← prEvent_eq_evalDist_singleton]
    exact random_bound sample resume
  have result := (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage
    (real source sample resume) (random sample resume)).trans
      (add_le_add randomMeasure
        (ENNReal.ofReal_le_ofReal (primitive_bound source hmac correct sample resume)))
  rw [prEvent_eq_evalDist_singleton]
  exact result

/-- The bad event is literal equality of the two actual initial sending chains when the original native constructors return. -/
theorem native_event (c : Pqxdh.Crypto) (response : Response) (beacon server : ConcreteRatchetKernel)
    (left : PqxdhInitialReplyErasure.kernelOf true response = ok beacon)
    (right : PqxdhInitialReplyErasure.kernelOf false response = ok server) :
    beacon.refined.send_chain = server.refined.send_chain ↔ Alias response :=
  initial_send_alias c response beacon server left right

/-- Encoding the actual root bytes changes no original sampler-query allowance. -/
theorem sampler_uniform {Context : Type} (sample : ProbComp (Context × RootOutput)) (qSample : Nat)
    (bounded : sample.IsTotalQueryBound qSample) : (sampler sample).IsTotalQueryBound qSample := by
  simpa only [sampler, IsTotalQueryBound, isQueryBound_map_iff] using bounded

/-- The observer pays every supplied continuation query; native projections and the final equality decision add no oracle requests. -/
theorem observer_uniform {Context Result : Type} (resume : Continue Context Result) (qObserve : Nat)
    (bounded : ∀ context response beacon server, (resume context response beacon server).IsTotalQueryBound qObserve)
    (context : Context) (output : FullOutput) :
    (observer resume context output).IsTotalQueryBound qObserve := by
  simpa only [observer, observe, IsTotalQueryBound, isQueryBound_map_iff] using bounded context _ _ _

/-- The full76 comparison makes exactly the maintained two challenge-HMAC requests while keeping every public HKDF evaluation in the original continuation. -/
theorem hmac_queries {Context Result : Type} (sample : ProbComp (Context × RootOutput)) (resume : Continue Context Result) :
    (fullExpandReduction .ratchet (sampler sample) (observer resume)).IsQueryBoundP IsHmacChallengeQuery 2 :=
  fullExpandReduction_hmac_query_bound _ _ _

/-- Local uniform work in the PRF reduction is the complete original sampler plus continuation; the two HMAC challenge calls remain a separate category. -/
theorem hmac_uniform {Context Result : Type} (sample : ProbComp (Context × RootOutput))
    (resume : Continue Context Result) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context response beacon server, (resume context response beacon server).IsTotalQueryBound qObserve) :
    (fullExpandReduction .ratchet (sampler sample) (observer resume)).IsQueryBoundP IsHmacUniformQuery (qSample + qObserve) :=
  fullExpandReduction_uniform_query_bound .ratchet (sampler sample) (observer resume)
    (sampler_uniform sample qSample sampleBound) (observer_uniform resume qObserve observeBound)

set_option maxRecDepth 2048 in
/-- Real source, uniform Extract, real/random HMAC and projected ideal worlds all retain their complete sampler, challenger and continuation random bills. -/
theorem game_bills {Context Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (sample : ProbComp (Context × RootOutput)) (resume : Continue Context Result) (qSample qObserve : Nat)
    (sampleBound : sample.IsTotalQueryBound qSample)
    (observeBound : ∀ context response beacon server, (resume context response beacon server).IsTotalQueryBound qObserve) :
    (real source sample resume).IsTotalQueryBound (qSample + qObserve) ∧
      (extractUniformGame (sampler sample) (fullExtractReduction hmac .ratchet (observer resume))).IsTotalQueryBound
        (qSample + (64 + qObserve)) ∧
      (hmacPrfRealGame hmac (fullExpandReduction .ratchet (sampler sample) (observer resume))).IsTotalQueryBound
        (64 + (qSample + qObserve)) ∧
      (hmacPrfRandomGame (fullExpandReduction .ratchet (sampler sample) (observer resume))).IsTotalQueryBound
        (qSample + (64 + (64 + qObserve))) ∧
      (random sample resume).IsTotalQueryBound (qSample + (64 + qObserve)) := by
  have sampled := sampler_uniform sample qSample sampleBound
  have observed := observer_uniform resume qObserve observeBound
  refine ⟨?_, fullExtractUniform_uniform_query_bound hmac .ratchet _ _ sampled observed,
    fullHmacReal_uniform_query_bound hmac .ratchet _ _ sampled observed,
    fullHmacRandom_uniform_query_bound .ratchet _ _ sampled observed, ?_⟩
  · rw [← real_source]
    exact sourceFullGame_uniform_query_bound source .ratchet _ _ sampled observed
  · unfold random
    exact isTotalQueryBound_bind sampleBound fun pair =>
      isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64) fun output => by
        simpa only [observe, IsTotalQueryBound, isQueryBound_map_iff] using observeBound pair.1
          (RawCtxSelectedInitialConstructor.response64 output) _ _

end BeaconcryptCore.Computational.RawCtxInitialSendAlias

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.response_alias' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.response_alias

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.real_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.real_source

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.random_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.random_source

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.random_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.random_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.primitive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.primitive_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.source_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.native_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.native_event

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.sampler_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.sampler_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.observer_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.observer_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.hmac_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.hmac_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.hmac_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.hmac_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxInitialSendAlias.game_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInitialSendAlias.game_bills

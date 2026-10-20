import BeaconcryptCore.Computational.PqxdhCorrelatedExpand

/-!
Ordinary HMAC Expand hybrids at every original root-query position. The scan retains prior explicit coins, cache entries and the full continuation; hits and completed scans still perform the separately charged ordinary challenge. The source capstone retains the explicit unreduced secret-input Extract-family term and makes no multiple-family or global authentication claim.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid
open PqxdhSecretInputKdf PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpand

noncomputable def uniformImpl : QueryImpl RootSpec (StateT RootOracle.QueryCache ProbComp) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT RootOracle.QueryCache ProbComp) +
    RootOracle.randomOracle

inductive Stopped (Result : Type) where
  | complete (result : Result)
  | pending (message : Message) (next : RootOutput → OracleComp RootSpec Result)

abbrev Prefix (Result : Type) := Stopped Result × RootOracle.QueryCache

/-- Execute every original query before the selected root position, retaining its unexecuted continuation and full cache. -/
noncomputable def scan {Result : Type} (client : OracleComp RootSpec Result) :
    Nat → RootOracle.QueryCache → ProbComp (Prefix Result) :=
  OracleComp.recOn client
    (fun result _ cache => pure (.complete result, cache))
    (fun query next recurse index cache => match query with
      | .inl coin => do
          let answer ← unifSpec.query coin
          recurse answer index cache
      | .inr message => match index with
        | 0 => pure (.pending message next, cache)
        | index + 1 => do
            let (answer, updated) ← (uniformImpl (.inr message)).run cache
            recurse answer index updated)

@[simp]
theorem scan_pure {Result : Type} (result : Result) (index : Nat) (cache : RootOracle.QueryCache) :
    scan (pure result) index cache = pure (.complete result, cache) := rfl

@[simp]
theorem scan_coin {Result : Type} (coin : unifSpec.Domain)
    (next : unifSpec.Range coin → OracleComp RootSpec Result) (index : Nat) (cache : RootOracle.QueryCache) :
    scan (RootSpec.query (.inl coin) >>= next) index cache = (do
      let answer ← unifSpec.query coin
      scan (next answer) index cache) := rfl

@[simp]
theorem scan_root_zero {Result : Type} (message : Message)
    (next : RootOutput → OracleComp RootSpec Result) (cache : RootOracle.QueryCache) :
    scan (RootSpec.query (.inr message) >>= next) 0 cache = pure (.pending message next, cache) := rfl

@[simp]
theorem scan_root_succ {Result : Type} (message : Message)
    (next : RootOutput → OracleComp RootSpec Result) (index : Nat) (cache : RootOracle.QueryCache) :
    scan (RootSpec.query (.inr message) >>= next) (index + 1) cache = (do
      let (answer, updated) ← (uniformImpl (.inr message)).run cache
      scan (next answer) index updated) := rfl

noncomputable def finishReal {Result : Type} (hmac : HmacSha512) (frame : Prefix Result) :
    ProbComp (Result × RootOracle.QueryCache) :=
  match frame.1 with
  | .complete result => pure (result, frame.2)
  | .pending message next =>
      (simulateQ (rootImpl hmac) (RootSpec.query (.inr message) >>= next)).run frame.2

noncomputable def finishRandom {Result : Type} (hmac : HmacSha512) (frame : Prefix Result) :
    ProbComp (Result × RootOracle.QueryCache) :=
  match frame.1 with
  | .complete result => pure (result, frame.2)
  | .pending message next => do
      let (answer, updated) ← (uniformImpl (.inr message)).run frame.2
      (simulateQ (rootImpl hmac) (next answer)).run updated

set_option backward.isDefEq.respectTransparency false in
/-- Before the first root request, the exact explicit coin prefix and full original source are unchanged. -/
theorem scan_zero_complete {Result : Type} (hmac : HmacSha512)
    (client : OracleComp RootSpec Result) (cache : RootOracle.QueryCache) :
    (scan client 0 cache >>= finishReal hmac) = (simulateQ (rootImpl hmac) client).run cache := by
  induction client using OracleComp.inductionOn generalizing cache with
  | pure result => simp [finishReal]
  | query_bind request next ih =>
      cases request with
      | inl coin =>
          simp only [scan_coin, bind_assoc, ih, simulateQ_query_bind, StateT.run_bind]
          simp [rootImpl]
      | inr message =>
          rw [scan_root_zero, pure_bind]
          rfl

set_option backward.isDefEq.respectTransparency false in
/-- Advancing the boundary changes only the selected original root slot, even when it is a cache hit. -/
theorem scan_succ_complete {Result : Type} (hmac : HmacSha512)
    (client : OracleComp RootSpec Result) (index : Nat) (cache : RootOracle.QueryCache) :
    (scan client (index + 1) cache >>= finishReal hmac) =
      (scan client index cache >>= finishRandom hmac) := by
  induction client using OracleComp.inductionOn generalizing index cache with
  | pure result => simp [finishReal, finishRandom]
  | query_bind request next ih =>
      cases request with
      | inl coin =>
          simp only [scan_coin, bind_assoc]
          simp_rw [ih]
      | inr message =>
          cases index with
          | zero =>
              simp only [scan_root_succ, scan_root_zero, pure_bind, bind_assoc,
                scan_zero_complete, finishRandom]
          | succ index =>
              simp only [scan_root_succ, bind_assoc]
              simp_rw [ih]

def IsRoot : RootSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsRoot
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

set_option backward.isDefEq.respectTransparency false in
/-- A bound on every original root request makes the final hybrid exactly the consistent uniform-root source. -/
theorem scan_bound_complete {Result : Type} (hmac : HmacSha512)
    (client : OracleComp RootSpec Result) (q : Nat) (bounded : client.IsQueryBoundP IsRoot q)
    (cache : RootOracle.QueryCache) :
    (scan client q cache >>= finishReal hmac) = (simulateQ uniformImpl client).run cache := by
  induction client using OracleComp.inductionOn generalizing q cache with
  | pure result => simp [finishReal]
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      cases request with
      | inl coin =>
          simp only [scan_coin, bind_assoc]
          have tails : ∀ answer, (next answer).IsQueryBoundP IsRoot q := by
            intro answer
            simpa [IsRoot] using bounded.2 answer
          simp_rw [ih _ q (tails _)]
          simp [uniformImpl]
      | inr message =>
          have positive : 0 < q := by simpa [IsRoot] using bounded.1
          cases q with
          | zero => omega
          | succ q =>
              simp only [scan_root_succ, bind_assoc]
              have tails : ∀ answer, (next answer).IsQueryBoundP IsRoot q := by
                intro answer
                simpa [IsRoot] using bounded.2 answer
              simp_rw [ih _ q (tails _)]
              simp [StateT.run_bind]

noncomputable def hybridGame (hmac : HmacSha512) (client : OracleComp RootSpec Bool)
    (index : Nat) : ProbComp Bool :=
  Prod.fst <$> (scan client index ∅ >>= finishReal hmac)

noncomputable def uniformGame (client : OracleComp RootSpec Bool) : ProbComp Bool :=
  (simulateQ uniformImpl client).run' ∅

theorem hybrid_zero (hmac : HmacSha512) (client : OracleComp RootSpec Bool) :
    hybridGame hmac client 0 = expandedGame hmac client := by
  simp only [hybridGame, scan_zero_complete, expandedGame, StateT.run'_eq]

theorem hybrid_bound (hmac : HmacSha512) (client : OracleComp RootSpec Bool)
    (q : Nat) (bounded : client.IsQueryBoundP IsRoot q) :
    hybridGame hmac client q = uniformGame client := by
  simp only [hybridGame, scan_bound_complete hmac client q bounded, uniformGame, StateT.run'_eq]

/-- The supplied root is used only for an actual selected miss; completed and repeated slots keep their original reply/state. -/
noncomputable def finishWithRoot {Result : Type} (hmac : HmacSha512) (frame : Prefix Result)
    (root : RootOutput) : ProbComp (Result × RootOracle.QueryCache) :=
  match frame.1 with
  | .complete result => pure (result, frame.2)
  | .pending message next => match frame.2 message with
    | some answer => (simulateQ (rootImpl hmac) (next answer)).run frame.2
    | none => (simulateQ (rootImpl hmac) (next root)).run (frame.2.cacheQuery message root)

set_option backward.isDefEq.respectTransparency false in
/-- Delaying an independent PRK to the selected slot retains the complete continuation, even when that sample is unused. -/
theorem finishReal_sample {Result : Type} (hmac : HmacSha512) (frame : Prefix Result) :
    EvalDistEq (($ᵗ HmacBlock) >>= fun key => finishWithRoot hmac frame (expandRoot hmac key))
      (finishReal hmac frame) := by
  rcases frame with ⟨stopped, cache⟩
  cases stopped with
  | complete result =>
      exact OracleComp.EvalDistEq.bind_const _ _
  | pending message next =>
      cases hit : cache message with
      | none =>
          simp only [finishWithRoot, hit, finishReal, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, rootImpl, QueryImpl.add_apply_inr,
            QueryImpl.withCaching_run_none _ hit, rootSampler, bind_map_left, EvalDistEq.refl]
      | some answer =>
          simp only [finishWithRoot, hit, finishReal, simulateQ_bind, simulateQ_spec_query,
            StateT.run_bind, rootImpl, QueryImpl.add_apply_inr,
            QueryImpl.withCaching_run_some _ hit, pure_bind]
          exact OracleComp.EvalDistEq.bind_const _ _

set_option backward.isDefEq.respectTransparency false in
/-- The ideal selected root is uniform, with the same ignored-sample behavior for completed and cached slots. -/
theorem finishRandom_sample {Result : Type} (hmac : HmacSha512) (frame : Prefix Result) :
    EvalDistEq (($ᵗ RootOutput) >>= fun root => finishWithRoot hmac frame root)
      (finishRandom hmac frame) := by
  rcases frame with ⟨stopped, cache⟩
  cases stopped with
  | complete result =>
      exact OracleComp.EvalDistEq.bind_const _ _
  | pending message next =>
      cases hit : cache message with
      | none =>
          simp only [finishWithRoot, hit, finishRandom, uniformImpl, QueryImpl.add_apply_inr,
            OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hit,
            uniformSampleImpl, bind_map_left, EvalDistEq.refl]
      | some answer =>
          simp only [finishWithRoot, hit, finishRandom, uniformImpl, QueryImpl.add_apply_inr,
            OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hit, pure_bind]
          exact OracleComp.EvalDistEq.bind_const _ _

noncomputable def scanSampler (client : OracleComp RootSpec Bool) (index : Nat) :
    SecretInputSampler (Prefix Bool) := (do
  let frame ← scan client index ∅
  pure (frame, []) : ProbComp (Prefix Bool × Pqxdh.Bytes))

noncomputable def scanObserver (hmac : HmacSha512) : RootObserver (Prefix Bool) :=
  fun frame root => Prod.fst <$> finishWithRoot hmac frame root

/-- Every indexed reduction uses the same ordinary fixed-label HMAC query after the complete stopped prefix. -/
noncomputable def indexedReduction (hmac : HmacSha512) (client : OracleComp RootSpec Bool)
    (index : Nat) : OracleComp HmacAdversarySpec Bool :=
  expandReduction (scanSampler client index) (scanObserver hmac)

theorem hybrid_eq_extractUniform (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat) :
    𝒟[hybridGame hmac client index] =
      𝒟[extractUniformGame (scanSampler client index) (extractReduction hmac (scanObserver hmac))] := by
  refine EvalDistEq.evalDist_eq ?_
  simp only [hybridGame, extractUniformGame, extractReduction, scanSampler, scanObserver,
    bind_assoc, pure_bind, map_bind]
  refine EvalDistEq.bind_right (scan client index ∅) fun frame => ?_
  have complete := (finishReal_sample hmac frame).symm.map
    (fun pair : Bool × RootOracle.QueryCache => pair.1)
  simpa only [map_bind] using complete

theorem hybrid_succ_eq_independent (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat) :
    𝒟[hybridGame hmac client (index + 1)] =
      𝒟[independentRootGame (scanSampler client index) (scanObserver hmac)] := by
  refine EvalDistEq.evalDist_eq ?_
  simp only [hybridGame, scan_succ_complete, independentRootGame, scanSampler, scanObserver,
    bind_assoc, pure_bind, map_bind]
  refine EvalDistEq.bind_right (scan client index ∅) fun frame => ?_
  have complete := (finishRandom_sample hmac frame).symm.map
    (fun pair : Bool × RootOracle.QueryCache => pair.1)
  simpa only [map_bind] using complete

/-- Each real HMAC challenger is exactly one adjacent hybrid with the entire stopped prefix retained. -/
theorem indexed_real (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat) :
    𝒟[hybridGame hmac client index] = 𝒟[hmacPrfRealGame hmac (indexedReduction hmac client index)] :=
  (hybrid_eq_extractUniform hmac client index).trans
    (EvalDistEq.evalDist_eq
      (extractUniform_eq_hmacReal hmac (scanSampler client index) (scanObserver hmac)))

/-- The random HMAC answer changes precisely the selected miss and preserves every repeated-input root. -/
theorem indexed_random (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat) :
    𝒟[hybridGame hmac client (index + 1)] = 𝒟[hmacPrfRandomGame (indexedReduction hmac client index)] :=
  (hybrid_succ_eq_independent hmac client index).trans
    (EvalDistEq.evalDist_eq
      (hmacRandom_eq_independentRoot (scanSampler client index) (scanObserver hmac)).symm)

theorem indexed_advantage (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (index : Nat) :
    (hybridGame hmac client index).boolDistAdvantage (hybridGame hmac client (index + 1)) =
      (hmacPrfRealGame hmac (indexedReduction hmac client index)).boolDistAdvantage
        (hmacPrfRandomGame (indexedReduction hmac client index)) := by
  simp only [ProbComp.boolDistAdvantage]
  rw [indexed_real hmac client index, indexed_random hmac client index]

/-- The ordered family has one ordinary HMAC term per original root position, without another selection factor. -/
theorem hybrid_distance_sum (hmac : HmacSha512) (client : OracleComp RootSpec Bool) (q : Nat) :
    (hybridGame hmac client 0).boolDistAdvantage (hybridGame hmac client q) ≤
      ∑ index ∈ Finset.range q,
        (hmacPrfRealGame hmac (indexedReduction hmac client index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac client index)) := by
  induction q with
  | zero => simp only [ProbComp.boolDistAdvantage, sub_self, abs_zero, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ q ih =>
      rw [Finset.sum_range_succ]
      exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans
        (add_le_add ih (le_of_eq (indexed_advantage hmac client q)))

/-- A bounded arbitrary adaptive root client reaches the consistent uniform-root source using only ordinary HMAC advantages. -/
theorem expanded_uniform_bound (hmac : HmacSha512) (client : OracleComp RootSpec Bool)
    (q : Nat) (bounded : client.IsQueryBoundP IsRoot q) :
    (expandedGame hmac client).boolDistAdvantage (uniformGame client) ≤
      ∑ index ∈ Finset.range q,
        (hmacPrfRealGame hmac (indexedReduction hmac client index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac client index)) := by
  simpa only [hybrid_zero, hybrid_bound hmac client q bounded] using hybrid_distance_sum hmac client q

open PqxdhEd25519EufCma PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhJointPhase1SourceWriter PqxdhJointPhase1AcceptanceComposition
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins PqxdhPrivateCandidateAcceptance
open PqxdhPrivateKemSource PqxdhPrivatePhase1Prefix PqxdhStatefulPhase1EufCma
open PqxdhPrivateRootSource PqxdhCorrelatedRootSource
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhChallengeSecretRouting PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The actual optional authenticated source reaches a consistent uniform-root table with the explicit Extract-family term and an ordered ordinary HMAC sum. -/
theorem authenticated_uniform_roots_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem parameters.native)
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem (runtimeOfImpl (kemAmbientImpl baseImpl)))
    (hmac : HmacSha512) (sourceCorrect : SourceRootCorrect parameters.source hmac)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : PqxdhJointIdentity.Primitives)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (selectorNoSign : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) PqxdhJointPhase1AcceptanceComposition.IsSigning) 0)
    (selectorNoCreate : ∀ publicTranscript, (selector.main publicTranscript).IsQueryBoundP
      (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec) Creating) 0)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : PqxdhJointIdentity.Forgery)
    (observer : CorrelatedObserver setup selector.State) (q : Nat)
    (rootBound : (rootReduction parameters.source baseImpl kem
      (rootProtocol kem parameters attachedVerify primitives setup selector observer)).IsQueryBoundP IsRoot q) :
    let protocol := rootProtocol kem parameters attachedVerify primitives setup selector observer
    (PqxdhCorrelatedRootSource.actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).boolDistAdvantage
      (uniformGame (rootReduction parameters.source baseImpl kem protocol)) ≤
      (PqxdhJointIdentity.advantage primitives
        (privateReduction primitives baseImpl kem setup selector fallback ordinaryFallback)).toReal +
      kem.IND_CCA_Advantage (runtimeOfImpl (kemAmbientImpl baseImpl))
        (PqxdhChallengeSecretRouting.reduction parameters.source kem protocol).toINDCCA +
      PqxdhCorrelatedExtractFamily.advantage hmac
        (PqxdhCorrelatedExtractFamily.reduction parameters.source hmac baseImpl kem protocol) +
      ∑ index ∈ Finset.range q,
        (hmacPrfRealGame hmac (indexedReduction hmac
          (rootReduction parameters.source baseImpl kem protocol) index)).boolDistAdvantage
          (hmacPrfRandomGame (indexedReduction hmac
            (rootReduction parameters.source baseImpl kem protocol) index)) := by
  dsimp only
  have family := PqxdhCorrelatedExtractFamily.authenticated_family_bound baseImpl kem parameters compatible
    functional correct hmac sourceCorrect attachedVerify primitives adapter setup selector selectorNoSign
    selectorNoCreate fallback ordinaryFallback observer
  have expanded := expanded_uniform_bound hmac (rootReduction parameters.source baseImpl kem
    (rootProtocol kem parameters attachedVerify primitives setup selector observer)) q rootBound
  rw [← reduction_expanded_eq parameters.source hmac baseImpl kem] at expanded
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans (add_le_add family expanded)

end BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid

/-! Persistent kernel-dependency audit for every statement in this module. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_root_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_root_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_root_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_root_succ

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_zero_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_zero_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_succ_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_succ_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_bound_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.scan_bound_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.finishReal_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.finishReal_sample

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.finishRandom_sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.finishRandom_sample

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_eq_extractUniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_eq_extractUniform

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_succ_eq_independent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_succ_eq_independent

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.indexed_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.indexed_real

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.indexed_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.indexed_random

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.indexed_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.indexed_advantage

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_distance_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.hybrid_distance_sum

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.expanded_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.expanded_uniform_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.authenticated_uniform_roots_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhCorrelatedExpandHybrid.authenticated_uniform_roots_bound

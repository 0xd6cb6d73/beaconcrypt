import BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets
import BeaconcryptCore.Computational.PqxdhInitialBuilderQueryBounds

/-!
The current initializer sampler and complete response-only observer consume only source caller and primitive callback resource certificates. The sampler includes actual key generation, preparation, encapsulation and the independent32-byte comparison root. The observer retains all real public and nonselected initializer work; no costs are transported through an evaluated-distribution equality.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialObserverBudgets
open PqxdhInitialObserverCallbackBudgets PqxdhInitialLegalObserver PqxdhInitialRootLabelService
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhAuthenticatedRootExperiment PqxdhAuthenticatedRootBudgets
open PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The literal current secret-input sampler pays real key generation, full preparation, encapsulation and its independent32-byte root, including completed branches. -/
theorem sample_uniform {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : Certificate env baseImpl kem program post) :
    (sample env baseImpl kem attachedVerify primitives program post).IsTotalQueryBound
      (c.qKeygen + ((c.uPre + c.qBase * c.bPre + c.qDecap * c.dPre) + c.qEncap) + 32) := by
  unfold sample
  apply isTotalQueryBound_bind
    (PqxdhCorrelatedExtractQueryBounds.prepare_uniform_bound baseImpl kem
      (protocol env kem attachedVerify primitives program post) _ _ _ _ _ _ _ _ _ _ _
      (PqxdhAuthenticatedRootBudgets.sampler_bounds env baseImpl kem attachedVerify primitives program post c))
  intro context
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32

def postCost (qLocal qBase qDecap : Nat) (kind : PqxdhPhase2SourceSchedulerBounds.Kind) : Nat :=
  PqxdhPhase2PostSchedulerBounds.cost qLocal .uniform kind +
  qBase * PqxdhPhase2PostSchedulerBounds.cost qLocal .base kind +
  qDecap * PqxdhPhase2PostSchedulerBounds.cost qLocal .decapsulation kind

def postBill (qLocal qBase qDecap : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) : Nat :=
  ∑ kind, postCost qLocal qBase qDecap kind * budget kind

section Post
open PqxdhPhase2SourceAux PqxdhPrivateKemSource PqxdhPhase1AcceptanceOracle
open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhInitializerSecrecy
variable
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qLocal qBase qDecap : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)

set_option backward.isDefEq.respectTransparency false in
include localBound baseBound decapBound in
/-- The exact post scheduler callback retains its original resource class, and each attempted finish pays the complete fused-owner primitive bill. -/
theorem target_uniform
    (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((PqxdhInitialLabelPost.target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge query).run state).IsQueryBoundP
      IsCoin (postCost qLocal qBase qDecap (PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec) query)) := by
  cases query with
  | inl query =>
      simp only [PqxdhInitialLabelPost.target, StateT.run]
      apply coins_uniform
      apply public_uniform baseImpl kem secret challenge qBase qDecap baseBound decapBound
      · exact PqxdhPhase2PostSchedulerBounds.target_step attachedVerify primitives count fixed localImpl qLocal localBound
          writer sender route decode challenge .uniform (.inl query) state
      · exact PqxdhPhase2PostSchedulerBounds.target_step attachedVerify primitives count fixed localImpl qLocal localBound
          writer sender route decode challenge .base (.inl query) state
      · exact PqxdhPhase2PostSchedulerBounds.target_step attachedVerify primitives count fixed localImpl qLocal localBound
          writer sender route decode challenge .decapsulation (.inl query) state
  | inr query =>
      cases query with
      | finish index raw =>
          simp only [PqxdhInitialLabelPost.target, PqxdhInitialLabelPost.finish, StateT.run, isQueryBoundP_map_iff]
          simpa only [postCost, PqxdhPhase2SourceSchedulerBounds.classify,
            PqxdhPhase2PostSchedulerBounds.cost, PqxdhPhase2PostSchedulerBounds.finishCost,
            ite_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero, PqxdhBeaconPhase2Preparation.State,
            StateT.run] using
            (owner_bounds attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
              qLocal qBase qDecap localBound baseBound decapBound decode raw (state.1.roles.1.2 index) (state.1.primitive, state.2)).1

set_option backward.isDefEq.respectTransparency false in
/-- Only an attempted original Beacon finish can make a private initializer request; ordinary records, reveals and public operations cannot. -/
theorem target_service
    (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((PqxdhInitialLabelPost.target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge query).run state).IsQueryBoundP
      IsService (if PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec) query = .inr 5 then 1 else 0) := by
  cases query with
  | inl query =>
      have zero := coins_service
        (simulateQ (PqxdhInitialRootFreeCallbacks.publicOnly baseImpl kem secret challenge)
          ((PqxdhPhase2PostScheduler.target attachedVerify primitives count fixed localImpl writer sender route decode challenge (.inl query)).run state))
      apply zero.mono
      exact Nat.zero_le _
  | inr query =>
      cases query with
      | finish index raw =>
          simp only [PqxdhInitialLabelPost.target, PqxdhInitialLabelPost.finish, StateT.run, isQueryBoundP_map_iff,
            PqxdhPhase2SourceSchedulerBounds.classify, ite_true]
          exact (PqxdhInitialFusedBudgets.owner_service decode raw (state.1.roles.1.2 index)).simulateQ_run_StateT_of_step
            (fun query before => compiler_service attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query before)
            (state.1.primitive, state.2)

include localBound baseBound decapBound in
/-- Every adaptive original post continuation is bounded by its source partition, including all attempted finishes and private initializer repeats. -/
theorem post_bounds (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhPhase2SourceSchedulerBounds.Bounded client budget)
    (state : PqxdhPhase2PostScheduler.State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    let actual := (simulateQ (PqxdhInitialLabelPost.target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge) client).run state
    actual.IsQueryBoundP IsCoin (postBill qLocal qBase qDecap budget) ∧
    actual.IsQueryBoundP IsService (budget (.inr 5)) := by
  constructor
  · exact FinitePartitionQueryBounds.weighted_bound (PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec))
      (postCost qLocal qBase qDecap) budget
      (PqxdhInitialLabelPost.target attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge)
      IsCoin client bounded
      (target_uniform attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge
        qLocal qBase qDecap localBound baseBound decapBound) state
  · exact (bounded (.inr 5)).simulateQ_run_StateT_of_step
      (target_service attachedVerify primitives count fixed localImpl writer sender route decode baseImpl kem secret challenge) state

end Post

/-- The concrete post bill exposes original source uniform, base and decapsulation counts, with one decapsulation allowance per attempted finish. -/
theorem post_bill (qLocal qBase qDecap : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) :
    postBill qLocal qBase qDecap budget =
      PqxdhPhase2PostSchedulerBounds.bill qLocal .uniform budget +
      qBase * budget (.inr 3) + qDecap * (budget (.inr 4) + budget (.inr 5)) := by
  simp only [postBill, postCost, Nat.add_mul, Finset.sum_add_distrib, Nat.mul_assoc, ← Finset.mul_sum]
  change PqxdhPhase2PostSchedulerBounds.bill qLocal .uniform budget +
    qBase * PqxdhPhase2PostSchedulerBounds.bill qLocal .base budget +
    qDecap * PqxdhPhase2PostSchedulerBounds.bill qLocal .decapsulation budget = _
  rw [PqxdhPhase2PostSchedulerBounds.base_bill, PqxdhPhase2PostSchedulerBounds.decapsulation_bill]

set_option backward.isDefEq.respectTransparency false in
/-- Every fresh nonselected family root costs32 ordinary samples; selected, known and cached responses preserve their actual cheaper behavior. -/
theorem labelled_step (fixed : FixedHkdfSha512NoSaltSource) (selected : PqxdhCorrelatedExtractFamily.Message)
    (response : PqxdhInitialRootLabelService.Response) (query : PqxdhInitialLabelCompiler.Spec.Domain)
    (cache : RootOracle.QueryCache) :
    ((labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response query).run cache).IsTotalQueryBound
      ((if IsCoin query then 1 else 0) + (if IsService query then 32 else 0)) := by
  cases query with
  | inl coin =>
      change ((fun answer => (answer, cache)) <$>
        (liftM (unifSpec.query coin) : ProbComp _)).IsTotalQueryBound 1
      exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr query =>
      simp only [labelledFull, QueryImpl.add_apply_inr, IsCoin, IsService, ite_true, ite_false, Nat.zero_add]
      cases query with
      | known root => trivial
      | family message =>
          by_cases same : message = selected
          · simp only [labelled, same, ite_true]
            trivial
          · simp only [labelled, same, ite_false]
            simp only [native, StateT.run, bind_pure_comp]
            rw [IsTotalQueryBound, isQueryBound_map_iff]
            exact PqxdhCorrelatedExpandQueryBounds.cached_step ($ᵗ RootOutput) 32
              (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (.inr message) cache

/-- The literal private response cache pays each original client coin and at most32 samples per service attempt, with every adaptive reply and complete cache retained. -/
theorem labelled_uniform (fixed : FixedHkdfSha512NoSaltSource) (selected : PqxdhCorrelatedExtractFamily.Message)
    (response : PqxdhInitialRootLabelService.Response) (client : OracleComp PqxdhInitialLabelCompiler.Spec Result)
    (u r : Nat) (coins : client.IsQueryBoundP IsCoin u) (services : client.IsQueryBoundP IsService r)
    (cache : RootOracle.QueryCache) :
    ((simulateQ (labelledFull fixed (QueryImpl.ofLift unifSpec ProbComp) selected response) client).run cache).IsTotalQueryBound
      (u + 32 * r) := by
  induction client using OracleComp.inductionOn generalizing u r cache with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at coins services
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isTotalQueryBound_bind (labelled_step fixed selected response query cache)
        (fun answer => ih answer.1 _ _ (coins.2 answer.1) (services.2 answer.1) answer.2)).mono
      have hu := coins.1
      have hr := services.1
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or] <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- The actual accepted initializer observer pays its full original Server builder, adaptive post source work and every possible fresh nonselected root draw. The selected builder response adds no root draw. -/
theorem accepted_uniform {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : Certificate env baseImpl kem program post) (secret : KemSK) (selected : PqxdhCorrelatedExtractFamily.Message)
    (prepared : PqxdhPrivateRootSource.Prepared setup (driver env.toDriverEnvironment program).State)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (response : PqxdhInitialRootLabelService.Response) :
    (acceptedDecision env baseImpl kem attachedVerify primitives program post secret selected prepared ready response).IsTotalQueryBound
      (c.uPost + c.qBase * c.bPost + c.qDecap * c.dPost + 32 * c.privatePost) := by
  unfold acceptedDecision
  simp only [StateT.run'_eq, IsTotalQueryBound, isQueryBound_map_iff]
  change ((simulateQ (labelledFull env.source (QueryImpl.ofLift unifSpec ProbComp) selected response)
    (accepted env baseImpl kem attachedVerify primitives program post secret selected prepared ready)).run ∅).IsTotalQueryBound _
  simp only [accepted, simulateQ_bind, StateT.run_bind, PqxdhInitialLabelBuilder.build_response, bind_map_left]
  have builder := PqxdhInitialBuilderQueryBounds.protocol_uniform env.source env.recordWriter
    (PqxdhInitialReplyErasure.kernelOf false response) env.aux c.qAux c.auxBound env.senderId env.index env.metadata
    (PqxdhInitialBuilderCut.eraseRoot ready) prepared.1.context.selection.2
  refine (isTotalQueryBound_bind builder (n₂ := postBill c.qLocal c.qBase c.qDecap c.postBudget + 32 * c.privatePost) ?_).mono ?_
  · intro result
    have bounds := post_bounds attachedVerify primitives 1 env.source env.localImpl env.recordWriter env.senderId env.route env.decode
      baseImpl kem secret ready.ciphertext c.qLocal c.qBase c.qDecap c.localBound c.baseBound (c.decapsBound secret)
      (post prepared.1.context.selection.1 result.1) c.postBudget (c.postBound _ _) (result.2, prepared.2)
    have cost := labelled_uniform env.source selected response _ _ _ bounds.1 bounds.2 ∅
    simpa only [simulateQ_map, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff,
      Certificate.privatePost] using cost
  · rw [post_bill]
    simp only [Certificate.uPost, Certificate.bPost, Certificate.dPost]
    omega

set_option backward.isDefEq.respectTransparency false in
/-- The complete current initializer observer has the same explicit source-derived uniform bill on both completed and accepted branches. -/
theorem observe_uniform {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1)) (post : Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : Certificate env baseImpl kem program post)
    (context : PqxdhInitialLegalObserver.Context env kem attachedVerify primitives program post)
    (response : PqxdhInitialRootLabelService.Response) :
    (observe env baseImpl kem attachedVerify primitives program post context response).IsTotalQueryBound
      (c.uPost + c.qBase * c.bPost + c.qDecap * c.dPost + 32 * c.privatePost) := by
  cases mode : context.state with
  | completed decision => simp only [observe, mode]; trivial
  | pending prepared ephemeral =>
      simp only [observe, mode]
      exact accepted_uniform env baseImpl kem attachedVerify primitives program post c _ _ _ _ _

end BeaconcryptCore.Computational.PqxdhInitialObserverBudgets

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.sample_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.sample_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.target_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.target_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.target_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.target_service
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.post_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.post_bounds
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.post_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.post_bill
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.labelled_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.labelled_step
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.labelled_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.labelled_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.accepted_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.accepted_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.observe_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverBudgets.observe_uniform

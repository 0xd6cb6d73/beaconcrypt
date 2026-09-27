import BeaconcryptCore.Computational.PqxdhJointDhExtractRoot
import BeaconcryptCore.Computational.FinitePartitionQueryBounds

/-!
The additional related-DH Extract service has four explicit query classes: coins, signing, public HMAC and family derivation. The ideal pays at most 64 fresh byte draws per protected-input miss; real side evaluations and every explicit public evaluation remain actual deterministic primitive work. Root expansion adds one public-HMAC request per successful root and every attempted root pays one derivation request.
-/
open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhJointDhExtractBounds
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointIdentity PqxdhJointDhExtractFamily
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)

/-- 0: uniform; 1: signing; 2: fixed public HMAC; 3: related input. -/
def classify : Spec.Domain → Fin 4
  | .inl _ => 0
  | .inr (.sign _) => 1
  | .inr (.publicHmac _ _) => 2
  | .inr (.derive _) => 3

def realCost : Fin 4 → Nat := fun kind => if kind = 0 then 1 else 0
def idealCost : Fin 4 → Nat := fun kind => if kind = 0 then 1 else if kind = 3 then 64 else 0

set_option backward.isDefEq.respectTransparency false in
/-- A protected miss pays all 64 uniform bytes; a hit or actual side evaluation pays none. No deterministic primitive operation is declared free by this random-query bound. -/
theorem extract_uniform (hmac : HmacSha512) (target : Option DhOutput)
    (bytes : Pqxdh.Bytes) (cache : HmacOracle.QueryCache) :
    ((protectedExtract hmac target bytes).run cache).IsTotalQueryBound 64 := by
  by_cases inside : Protected target bytes
  · cases hit : cache bytes with
    | none =>
        rw [protected_miss hmac target bytes cache inside hit]
        simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
          CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 64
    | some prk =>
        rw [protected_hit hmac target bytes cache prk inside hit]
        trivial
  · simp only [protectedExtract, if_neg inside, actualExtract, StateT.run]
    trivial

/-- Real fixed primitives add no random draws; explicit client coins still cost one request. -/
theorem real_step (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : Spec.Domain) (state : State) :
    ((realImpl hmac joint dh seed scalar query).run state).IsTotalQueryBound (realCost (classify query)) := by
  cases query with
  | inl coin =>
      change OracleComp.IsTotalQueryBound
        ((unifSpec.query coin : ProbComp _) >>= fun value => pure (value, state)) 1
      exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr request =>
      cases request with
      | sign bytes => change (pure _ : ProbComp _).IsTotalQueryBound 0; trivial
      | publicHmac key bytes => change (pure _ : ProbComp _).IsTotalQueryBound 0; trivial
      | derive message =>
          cases actual : input joint dh seed scalar message <;>
            simp [realImpl, impl, actual, actualExtract, StateT.run, realCost, classify] <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- An ideal derivation pays at most one fresh 64-byte block, including all actual optional-DH and table-hit branches. -/
theorem ideal_step (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : Spec.Domain) (state : State) :
    ((idealImpl hmac joint dh seed scalar query).run state).IsTotalQueryBound (idealCost (classify query)) := by
  cases query with
  | inl coin =>
      change OracleComp.IsTotalQueryBound
        ((unifSpec.query coin : ProbComp _) >>= fun value => pure (value, state)) 1
      exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  | inr request =>
      cases request with
      | sign bytes => change (pure _ : ProbComp _).IsTotalQueryBound 0; trivial
      | publicHmac key bytes => change (pure _ : ProbComp _).IsTotalQueryBound 0; trivial
      | derive message =>
          cases actual : input joint dh seed scalar message with
          | none => simp only [idealImpl, impl, StateT.run, actual]; trivial
          | some bytes =>
              simp only [idealImpl, impl, StateT.run, actual, idealCost, classify]
              simpa [StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
                extract_uniform hmac (joint.staticDh seed (dh.publicKey scalar)) bytes state.cache

/-- Every adaptive real-service continuation keeps the original uniform cap, including all prior instrumentation. Signing/HMAC/DH work is a separate request ledger. -/
theorem real_run {Result : Type} (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (client : OracleComp Spec Result) (budget : Fin 4 → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => classify query = kind) (budget kind)) (state : State) :
    ((simulateQ (realImpl hmac joint dh seed scalar) client).run state).IsTotalQueryBound (budget 0) := by
  have bound := FinitePartitionQueryBounds.weighted_bound classify realCost budget
    (realImpl hmac joint dh seed scalar) (fun _ => True) client bounded
    (fun query state => (real_step hmac joint dh seed scalar query state).isQueryBoundP) state
  simpa [Fin.sum_univ_succ, realCost, isQueryBoundP_true_iff] using bound

/-- An entire ideal continuation pays every possible protected miss; repeated inputs and rejected requests are still included in its logical derivation cap. -/
theorem ideal_run {Result : Type} (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (client : OracleComp Spec Result) (budget : Fin 4 → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => classify query = kind) (budget kind)) (state : State) :
    ((simulateQ (idealImpl hmac joint dh seed scalar) client).run state).IsTotalQueryBound
      (budget 0 + 64 * budget 3) := by
  have bound := FinitePartitionQueryBounds.weighted_bound classify idealCost budget
    (idealImpl hmac joint dh seed scalar) (fun _ => True) client bounded
    (fun query state => (ideal_step hmac joint dh seed scalar query state).isQueryBoundP) state
  simpa [Fin.sum_univ_succ, idealCost, isQueryBoundP_true_iff] using bound

/-- Both challengers pay the actual 32-byte identity seed and 32-byte prekey sampler before the full adaptive client. -/
theorem game_uniform (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp Spec Bool) (budget : Fin 4 → Nat)
    (bounded : ∀ publicValue kind,
      (client publicValue).IsQueryBoundP (fun query => classify query = kind) (budget kind)) :
    (realGame hmac joint dh client).IsTotalQueryBound (64 + budget 0) ∧
      (idealGame hmac joint dh client).IsTotalQueryBound (64 + (budget 0 + 64 * budget 3)) := by
  constructor
  · have split : 64 + budget 0 = 32 + (32 + budget 0) := by omega
    rw [split]
    unfold realGame
    apply isTotalQueryBound_bind sampleSeed_uniform_bound
    intro seed
    apply isTotalQueryBound_bind PqxdhJointGapDh.sampleScalar_uniform
    intro scalar
    change ((fun result => result.1) <$> (simulateQ (realImpl hmac joint dh seed scalar)
      (client (PqxdhJointGapDh.challenge joint dh seed scalar))).run empty).IsTotalQueryBound (budget 0)
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      real_run hmac joint dh seed scalar (client _) budget (bounded _) empty
  · have split : 64 + (budget 0 + 64 * budget 3) = 32 + (32 + (budget 0 + 64 * budget 3)) := by omega
    rw [split]
    unfold idealGame
    apply isTotalQueryBound_bind sampleSeed_uniform_bound
    intro seed
    apply isTotalQueryBound_bind PqxdhJointGapDh.sampleScalar_uniform
    intro scalar
    change ((fun result => result.1) <$> (simulateQ (idealImpl hmac joint dh seed scalar)
      (client (PqxdhJointGapDh.challenge joint dh seed scalar))).run empty).IsTotalQueryBound (budget 0 + 64 * budget 3)
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      ideal_run hmac joint dh seed scalar (client _) budget (bounded _) empty

def rootClassify : PqxdhJointDhExtractRoot.RootSpec.Domain → Fin 4
  | .inl _ => 0
  | .inr (.sign _) => 1
  | .inr (.publicHmac _ _) => 2
  | .inr (.derive _) => 3

def rootCost (target source : Fin 4) : Nat :=
  (if source = target then 1 else 0) + (if source = 3 ∧ target = 2 then 1 else 0)

set_option backward.isDefEq.respectTransparency false in
/-- Every attempted root has one derivation query and at most one explicitly real Expand query; it cannot sign or draw coins. -/
theorem root_bills (message : Message) (kind : Fin 4) :
    (PqxdhJointDhExtractRoot.root message).IsQueryBoundP (fun query => classify query = kind) (rootCost kind 3) := by
  have different : (3 : Fin 4) ≠ 2 := by decide
  simp only [PqxdhJointDhExtractRoot.root, isQueryBoundP_query_bind_iff, classify]
  constructor
  · simp only [rootCost]
    split_ifs <;> simp_all [eq_comm]
  · rintro (_ | value)
    · trivial
    · simp only [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff, rootCost]
      split_ifs <;> simp_all [eq_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Forwarded ordinary requests retain their class; a root request alone may also perform one public Expand evaluation. -/
theorem reduction_step (query : PqxdhJointDhExtractRoot.RootSpec.Domain) (kind : Fin 4) :
    (PqxdhJointDhExtractRoot.reduction query).IsQueryBoundP (fun request => classify request = kind)
      (rootCost kind (rootClassify query)) := by
  cases query with
  | inl coin =>
      simp only [PqxdhJointDhExtractRoot.reduction, isQueryBoundP_query_iff, classify, rootCost, rootClassify]
      split_ifs <;> simp_all
  | inr request =>
      cases request with
      | derive message => exact root_bills message kind
      | sign bytes =>
          simp only [PqxdhJointDhExtractRoot.reduction, isQueryBoundP_query_iff, classify, rootCost, rootClassify]
          split_ifs <;> simp_all
      | publicHmac key bytes =>
          simp only [PqxdhJointDhExtractRoot.reduction, isQueryBoundP_query_iff, classify, rootCost, rootClassify]
          split_ifs <;> simp_all

set_option backward.isDefEq.respectTransparency false in
/-- The complete adaptive reduction keeps one shared four-class budget across every possible optional reply. -/
theorem reduction_weighted {Result : Type} (client : OracleComp PqxdhJointDhExtractRoot.RootSpec Result)
    (budget : Fin 4 → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => rootClassify query = kind) (budget kind))
    (kind : Fin 4) :
    (simulateQ PqxdhJointDhExtractRoot.reduction client).IsQueryBoundP (fun query => classify query = kind)
      (FinitePartitionQueryBounds.bill (rootCost kind) budget) := by
  induction client using OracleComp.inductionOn generalizing budget with
  | pure result => trivial
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff] at bounded
      have positive : 0 < budget (rootClassify query) := by simpa using (bounded (rootClassify query)).1
      let remaining := Function.update budget (rootClassify query) (budget (rootClassify query) - 1)
      have tail reply selected : (next reply).IsQueryBoundP
          (fun request => rootClassify request = selected) (remaining selected) := by
        by_cases same : rootClassify query = selected
        · subst selected
          simpa only [remaining, Function.update_self, if_true] using (bounded (rootClassify query)).2 reply
        · simpa only [remaining, Function.update_of_ne (Ne.symm same), same, if_false] using (bounded selected).2 reply
      simp only [simulateQ_bind, simulateQ_spec_query]
      have combined := isQueryBoundP_bind (reduction_step query kind) (fun reply _ => ih reply remaining (tail reply))
      simpa only [remaining, FinitePartitionQueryBounds.bill_step (rootCost kind) budget (rootClassify query) positive] using combined

/-- Signing, uniform and family caps stay unchanged; the public-HMAC cap additionally charges every possible root expansion. -/
theorem reduction_bills {Result : Type} (client : OracleComp PqxdhJointDhExtractRoot.RootSpec Result)
    (budget : Fin 4 → Nat)
    (bounded : ∀ kind, client.IsQueryBoundP (fun query => rootClassify query = kind) (budget kind))
    (kind : Fin 4) :
    (simulateQ PqxdhJointDhExtractRoot.reduction client).IsQueryBoundP (fun query => classify query = kind)
      (budget kind + if kind = 2 then budget 3 else 0) := by
  have cost : FinitePartitionQueryBounds.bill (rootCost kind) budget =
      budget kind + if kind = 2 then budget 3 else 0 := by
    by_cases same : kind = 2 <;>
      simp [FinitePartitionQueryBounds.bill, rootCost, same, Nat.add_mul, Finset.sum_add_distrib, ite_mul]
  rw [← cost]
  exact reduction_weighted client budget bounded kind

/-- The concrete coefficient-one root comparison has the same seed bill and complete adaptive random-query caps after the explicit expansion compiler. -/
theorem root_game_uniform (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp PqxdhJointDhExtractRoot.RootSpec Bool) (budget : Fin 4 → Nat)
    (bounded : ∀ publicValue kind,
      (client publicValue).IsQueryBoundP (fun query => rootClassify query = kind) (budget kind)) :
    (PqxdhJointDhExtractRoot.sourceGame source hmac joint dh client).IsTotalQueryBound (64 + budget 0) ∧
      (PqxdhJointDhExtractRoot.idealRootGame hmac joint dh client).IsTotalQueryBound
        (64 + (budget 0 + 64 * budget 3)) := by
  let compiled : Fin 4 → Nat := fun kind => budget kind + if kind = 2 then budget 3 else 0
  have caps publicValue kind := reduction_bills (client publicValue) budget (bounded publicValue) kind
  have bound := game_uniform hmac joint dh
    (fun publicValue => simulateQ PqxdhJointDhExtractRoot.reduction (client publicValue)) compiled caps
  constructor
  · rw [← PqxdhJointDhExtractRoot.game_real source hmac correct]
    simpa [compiled] using bound.1
  · simpa [PqxdhJointDhExtractRoot.idealRootGame, compiled] using bound.2

end BeaconcryptCore.Computational.PqxdhJointDhExtractBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.extract_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.extract_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.real_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.real_step

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.ideal_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.ideal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.real_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.real_run

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.ideal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.ideal_run

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.game_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.root_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.root_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.reduction_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.reduction_step

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.reduction_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.reduction_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.reduction_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.reduction_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.root_game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointDhExtractBounds.root_game_uniform

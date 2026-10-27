import BeaconcryptCore.Computational.PqxdhJointIdentity
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
# Bounded family of correlated identity services

The family samples independent seed values in index order and retains every identity's complete sign/DH history. Target selection addresses a generated identity index; equality of public bytes is not assumed to identify that index. Public-lookup collisions and adaptive identity reveals belong to the source/global wrapper.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhJointIdentityFamily

open PqxdhJointIdentity

/-- Index-ordered generation of the exact independent 32-byte identity seeds. -/
def sampleFamily : (count : ℕ) → ProbComp (Fin count → IdentitySeed)
  | 0 => pure Fin.elim0
  | count + 1 => do
    let seed ← sampleSeed
    let rest ← sampleFamily count
    pure (Fin.cons seed rest)

/-- Moving a chosen identity's independent seed draw preserves every complete evaluated continuation. -/
theorem sampleFamily_target_first {Result : Type} (count : ℕ) (target : Fin (count + 1))
    (next : (Fin (count + 1) → IdentitySeed) → ProbComp Result) :
    EvalDistEq (sampleFamily (count + 1) >>= next)
      (do
        let seed ← sampleSeed
        let rest ← sampleFamily count
        next (target.insertNth seed rest)) := by
  induction count with
  | zero =>
      have targetZero : target = 0 := by apply Fin.ext; omega
      subst target
      simp [sampleFamily, Fin.insertNth_zero']
  | succ count ih =>
      induction target using Fin.cases with
      | zero => simp [sampleFamily, Fin.insertNth_zero']
      | succ target =>
          have step : EvalDistEq (sampleFamily (count + 1 + 1) >>= next)
              (do
                let first ← sampleSeed
                let chosen ← sampleSeed
                let rest ← sampleFamily count
                next (Fin.cons first (target.insertNth chosen rest))) := by
            change EvalDistEq ((do
              let first ← sampleSeed
              let rest ← sampleFamily (count + 1)
              pure (Fin.cons first rest)) >>= next) _
            simp only [bind_assoc, pure_bind]
            refine EvalDistEq.bind_right _ fun first => ?_
            exact ih target (fun rest => next (Fin.cons first rest))
          refine step.trans ((PqxdhSecretInputKdf.evalSPMF_sample_comm sampleSeed sampleSeed
            (fun first chosen => do
              let rest ← sampleFamily count
              next (Fin.cons first (target.insertNth chosen rest)))).trans ?_)
          simp [sampleFamily, Fin.insertNth_succ_cons, bind_assoc]

/-- Exact family generation cost, including every byte of each independent identity seed. -/
theorem sampleFamily_uniform_bound (count : ℕ) :
    (sampleFamily count).IsTotalQueryBound (32 * count) := by
  induction count with
  | zero => simp [sampleFamily, OracleComp.IsTotalQueryBound]
  | succ count ih =>
      rw [sampleFamily, show 32 * (count + 1) = 32 + 32 * count by omega]
      apply OracleComp.isTotalQueryBound_bind sampleSeed_uniform_bound
      intro seed
      simpa only [bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using ih

abbrev FamilySpec (count : ℕ) : OracleSpec (Fin count × JointSpec.Domain) :=
  fun query => JointSpec.Range query.2

abbrev FamilyAdversarySpec (count : ℕ) := unifSpec + FamilySpec count
abbrev FamilyHistory (count : ℕ) := Fin count → History

def emptyHistory (count : ℕ) : FamilyHistory count := fun _ => []

/-- Each identity shares one seed across its complete adaptively scheduled service history. -/
def familyImpl (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed) :
    QueryImpl (FamilyAdversarySpec count) (StateT (FamilyHistory count) ProbComp) := fun query history =>
  match query with
  | .inl coin => do
    let answer ← unifSpec.query coin
    pure (answer, history)
  | .inr (index, request) =>
    let answer := primitiveReply primitives (seeds index) request
    pure (answer, Function.update history index (history index ++ [requestEvent request answer]))

/-- Only non-target histories are held locally; the primitive challenger retains the complete target history. -/
def reductionImpl (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (others : Fin count → IdentitySeed) :
    QueryImpl (FamilyAdversarySpec (count + 1))
      (StateT (FamilyHistory count) (OracleComp AdversarySpec)) := fun query history =>
  match query with
  | .inl coin => do
    let answer ← AdversarySpec.query (.inl coin)
    pure (answer, history)
  | .inr (index, request) =>
    Fin.succAboveCases target
      (do
        let answer ← AdversarySpec.query (.inr request)
        pure (answer, history))
      (fun other =>
        let answer := primitiveReply primitives (others other) request
        pure (answer, Function.update history other (history other ++ [requestEvent request answer]))) index

/-- Reconstruct every identity's exact log without discarding the challenger's prior target observations. -/
def combineHistory {count : ℕ} (target : Fin (count + 1))
    (state : FamilyHistory count × History) : FamilyHistory (count + 1) :=
  target.insertNth state.2 state.1

/-- Combining empty local and target histories retains the source's completely empty initial history. -/
theorem combineHistory_empty {count : ℕ} (target : Fin (count + 1)) :
    combineHistory target (emptyHistory count, []) = emptyHistory (count + 1) := by
  funext index
  induction index using Fin.succAboveCases target <;> simp [combineHistory, emptyHistory]

/-- A routed call preserves its actual reply and every identity history, including all earlier target DH/sign observations. -/
theorem targetRouting_step (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (targetSeed : IdentitySeed) (others : Fin count → IdentitySeed)
    (query : (FamilyAdversarySpec (count + 1)).Domain)
    (state : FamilyHistory count × History) :
    Prod.map id (combineHistory target) <$>
      (QueryImpl.Stateful.link (reductionImpl primitives target others)
        (jointImpl primitives targetSeed) query).run state =
    (familyImpl primitives (target.insertNth targetSeed others) query).run (combineHistory target state) := by
  rcases state with ⟨localHistory, targetHistory⟩
  rw [QueryImpl.Stateful.link_impl_apply_run, Functor.map_map]
  change (fun result : ((FamilyAdversarySpec (count + 1)).Range query × FamilyHistory count) × History =>
    (result.1.1, combineHistory target (result.1.2, result.2))) <$>
    (simulateQ (jointImpl primitives targetSeed)
      ((reductionImpl primitives target others query).run localHistory)).run targetHistory = _
  cases query with
  | inl coin =>
      simp [reductionImpl, StateT.run, familyImpl, combineHistory]
      change (fun result : ((unifSpec.Range coin × FamilyHistory count) × History) =>
        (result.1.1, combineHistory target (result.1.2, result.2))) <$>
        (do
          let answer ← unifSpec.query coin
          pure (answer, targetHistory) >>= fun result => pure ((result.1, localHistory), result.2) : ProbComp ((unifSpec.Range coin × FamilyHistory count) × History)) = _
      simp [combineHistory, Functor.map_map]
  | inr query =>
      rcases query with ⟨index, request⟩
      induction index using Fin.succAboveCases target with
      | x =>
          simp [reductionImpl, StateT.run, familyImpl, combineHistory]
          change (fun result : ((JointSpec.Range request × FamilyHistory count) × History) =>
            (result.1.1, combineHistory target (result.1.2, result.2))) <$>
            (pure ((primitiveReply primitives targetSeed request, localHistory),
              targetHistory ++ [requestEvent request (primitiveReply primitives targetSeed request)])) = _
          simp [combineHistory]
      | p other =>
          simp [reductionImpl, StateT.run, familyImpl, combineHistory]
          change (fun result : ((JointSpec.Range request × FamilyHistory count) × History) =>
            (result.1.1, combineHistory target (result.1.2, result.2))) <$>
            pure ((primitiveReply primitives (others other) request,
              Function.update localHistory other (localHistory other ++
                [requestEvent request (primitiveReply primitives (others other) request)])), targetHistory) = _
          simp [combineHistory, Fin.insertNth_update]

/-- Complete adaptive routing retains every reply, final client value, and prior identity log. -/
theorem targetRouting_complete (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (targetSeed : IdentitySeed) (others : Fin count → IdentitySeed) {Result : Type}
    (client : OracleComp (FamilyAdversarySpec (count + 1)) Result)
    (localHistory : FamilyHistory count) (targetHistory : History) :
    (fun result : (Result × FamilyHistory count) × History =>
      (result.1.1, combineHistory target (result.1.2, result.2))) <$>
      (simulateQ (jointImpl primitives targetSeed)
        ((simulateQ (reductionImpl primitives target others) client).run localHistory)).run targetHistory =
    (simulateQ (familyImpl primitives (target.insertNth targetSeed others)) client).run
      (combineHistory target (localHistory, targetHistory)) := by
  have projection := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (QueryImpl.Stateful.link (reductionImpl primitives target others) (jointImpl primitives targetSeed))
    (familyImpl primitives (target.insertNth targetSeed others)) (combineHistory target)
    (targetRouting_step primitives target targetSeed others) client (localHistory, targetHistory)
  rw [QueryImpl.Stateful.simulateQ_link_run, Functor.map_map] at projection
  exact projection

/-- Source identity lookup remains by generated index; public-key collisions do not silently merge signing histories. -/
structure FamilyForgery (count : ℕ) where
  identity : Fin count
  forgery : Forgery

def familyPublic (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed) :
    Fin count → PublicIdentity := fun index => primitives.publicKeys (seeds index)

/-- Exact public family after embedding one challenger identity. -/
theorem familyPublic_insertNth (primitives : Primitives) {count : ℕ}
    (target : Fin (count + 1)) (seed : IdentitySeed) (others : Fin count → IdentitySeed) :
    familyPublic primitives (target.insertNth seed others) =
      target.insertNth (primitives.publicKeys seed) (familyPublic primitives others) := by
  funext index
  induction index using Fin.succAboveCases target <;> simp [familyPublic]

/-- Forward all locally sampled uniform values, preserving the target's complete earlier history. -/
theorem simulate_joint_uniform (primitives : Primitives) (seed : IdentitySeed)
    {Result : Type} (work : ProbComp Result) (history : History) :
    (simulateQ (jointImpl primitives seed) (OracleComp.liftComp work AdversarySpec)).run history =
      (fun answer => (answer, history)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  change (do let answer ← unifSpec.query coin; pure (answer, before) : ProbComp _) = _
  simp only [bind_pure_comp]

/-- A single-target reduction samples exactly the other identities and returns the adversary's unchanged ordinary forgery. -/
def reduction (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (FamilyAdversarySpec (count + 1)) (FamilyForgery (count + 1)))
    (jointPublic : PublicIdentity) : OracleComp AdversarySpec Forgery := do
  let others ← OracleComp.liftComp (sampleFamily count) AdversarySpec
  let (result, _) ← (simulateQ (reductionImpl primitives target others)
    (adversary (target.insertNth jointPublic (familyPublic primitives others)))).run (emptyHistory count)
  pure result.forgery

/-- Full source execution exposes the public family and retains all exact logs. -/
def familyRun (primitives : Primitives) (count : ℕ)
    (adversary : (Fin count → PublicIdentity) →
      OracleComp (FamilyAdversarySpec count) (FamilyForgery count)) :
    ProbComp ((Fin count → PublicIdentity) × FamilyForgery count × FamilyHistory count) := do
  let seeds ← sampleFamily count
  let (result, history) ← (simulateQ (familyImpl primitives seeds)
    (adversary (familyPublic primitives seeds))).run (emptyHistory count)
  pure (familyPublic primitives seeds, result, history)

/-- Ordinary weak-EUF test at a fixed generated identity, even when the adversary finally labels another identity. -/
def targetTest (primitives : Primitives) {count : ℕ} (target : Fin count)
    (result : (Fin count → PublicIdentity) × FamilyForgery count × FamilyHistory count) : Bool :=
  wins primitives (result.1 target) result.2.1.forgery (result.2.2 target)

/-- A source forgery succeeds under its adaptively selected identity's complete signing history. -/
def familyTest (primitives : Primitives) {count : ℕ}
    (result : (Fin count → PublicIdentity) × FamilyForgery count × FamilyHistory count) : Bool :=
  targetTest primitives result.2.1.identity result

/-- A selected-identity test is precisely the single joint-use challenger experiment under the constructed reduction. -/
theorem targetGame_eq_reduction (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (FamilyAdversarySpec (count + 1)) (FamilyForgery (count + 1))) :
    EvalDistEq (targetTest primitives target <$> familyRun primitives (count + 1) adversary)
      (game primitives (reduction primitives target adversary)) := by
  simp only [familyRun, map_bind, map_pure]
  refine (sampleFamily_target_first count target _).trans ?_
  simp only [game, run, reduction, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, simulate_joint_uniform,
    bind_map_left, pure_bind, bind_assoc]
  refine EvalDistEq.bind_right _ fun seed => ?_
  refine EvalDistEq.bind_right _ fun others => ?_
  rw [familyPublic_insertNth]
  rw [← combineHistory_empty target, ← targetRouting_complete]
  simp [targetTest, combineHistory]

/-- Adaptive final identity selection costs the explicit sum of constructed joint-use reductions. -/
theorem family_advantage_le_sum (primitives : Primitives) (count : ℕ)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (FamilyAdversarySpec (count + 1)) (FamilyForgery (count + 1))) :
    Pr{let result ← familyRun primitives (count + 1) adversary}[familyTest primitives result = true] ≤
      ∑ target : Fin (count + 1), advantage primitives (reduction primitives target adversary) := by
  classical
  calc
    _ ≤ Pr{let result ← familyRun primitives (count + 1) adversary}[
        ∃ target ∈ (Finset.univ : Finset (Fin (count + 1))),
          targetTest primitives target result = true] :=
      prEvent_mono _ _ _ (fun result accepted =>
        ⟨result.2.1.identity, Finset.mem_univ _, accepted⟩)
    _ ≤ ∑ target : Fin (count + 1), Pr{let result ← familyRun primitives (count + 1) adversary}[
        targetTest primitives target result = true] :=
      prEvent_exists_finset_le Finset.univ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro target _
      have same := (targetGame_eq_reduction primitives target adversary).prEvent_eq (· = true)
      rw [prEvent_map] at same
      exact same

/-- A uniform per-reduction assumption incurs exactly the number of generated identities. -/
theorem family_advantage_le_count (primitives : Primitives) (count : ℕ)
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (FamilyAdversarySpec (count + 1)) (FamilyForgery (count + 1)))
    (epsilon : ℝ≥0∞)
    (bounded : ∀ target, advantage primitives (reduction primitives target adversary) ≤ epsilon) :
    Pr{let result ← familyRun primitives (count + 1) adversary}[familyTest primitives result = true] ≤
      (count + 1 : ℕ) * epsilon := by
  exact (family_advantage_le_sum primitives count adversary).trans
    ((Finset.sum_le_sum fun target _ => bounded target).trans_eq (by simp))

/-- Pull a primitive query class back to every generated identity, preserving the uniform class. -/
def familyClass {count : ℕ} (predicate : AdversarySpec.Domain → Prop) :
    (FamilyAdversarySpec count).Domain → Prop
  | .inl coin => predicate (.inl coin)
  | .inr (_, request) => predicate (.inr request)

instance {count : ℕ} (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (familyClass (count := count) predicate) := fun query => by
  cases query with
  | inl coin => exact inferInstanceAs (Decidable (predicate (.inl coin)))
  | inr query => exact inferInstanceAs (Decidable (predicate (.inr query.2)))

/-- Routing never exceeds one corresponding primitive call and counts rejected DH attempts exactly like successful attempts. -/
theorem reductionImpl_query_bound (primitives : Primitives) {count : ℕ}
    (target : Fin (count + 1)) (others : Fin count → IdentitySeed)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    (query : (FamilyAdversarySpec (count + 1)).Domain) (history : FamilyHistory count) :
    ((reductionImpl primitives target others query).run history).IsQueryBoundP predicate
      (if familyClass predicate query then 1 else 0) := by
  cases query with
  | inl coin =>
    simp [reductionImpl, StateT.run, familyClass, bind_pure_comp]
    intro selected
    simp [selected]
  | inr query =>
    rcases query with ⟨index, request⟩
    induction index using Fin.succAboveCases target with
    | x =>
      simp [reductionImpl, StateT.run, familyClass, bind_pure_comp]
      intro selected
      simp [selected]
    | p other => simp [reductionImpl, StateT.run]

/-- The complete adaptive routing inherits each source oracle class separately. -/
theorem routed_query_bound (primitives : Primitives) {count : ℕ}
    (target : Fin (count + 1)) (others : Fin count → IdentitySeed)
    (predicate : AdversarySpec.Domain → Prop) [DecidablePred predicate]
    {Result : Type} (client : OracleComp (FamilyAdversarySpec (count + 1)) Result)
    (bound : ℕ) (bounded : client.IsQueryBoundP (familyClass predicate) bound)
    (history : FamilyHistory count) :
    ((simulateQ (reductionImpl primitives target others) client).run history).IsQueryBoundP predicate bound :=
  bounded.simulateQ_run_StateT_of_step
    (reductionImpl_query_bound primitives target others predicate) history

/-- Uniform requests, signing requests, and all raw 32-byte DH attempts have separate budgets. -/
inductive Kind where
  | uniform | sign | staticDh
  deriving DecidableEq

def IsClass (kind : Kind) : AdversarySpec.Domain → Prop
  | .inl _ => kind = .uniform
  | .inr (.sign _) => kind = .sign
  | .inr (.staticDh _) => kind = .staticDh

instance (kind : Kind) : DecidablePred (IsClass kind) := fun query => by
  cases query with
  | inl coin => exact inferInstanceAs (Decidable (kind = .uniform))
  | inr query => cases query with
    | sign message => exact inferInstanceAs (Decidable (kind = .sign))
    | staticDh peer => exact inferInstanceAs (Decidable (kind = .staticDh))

/-- Local identity generation adds its exact uniform byte draws and no signing/DH oracle requests. -/
theorem sampleFamily_lift_bound (count : ℕ) (kind : Kind) :
    (OracleComp.liftComp (sampleFamily count) AdversarySpec).IsQueryBoundP (IsClass kind)
      (if kind = .uniform then 32 * count else 0) := by
  cases kind with
  | uniform =>
    apply OracleComp.IsQueryBoundP.liftComp_subSpec
      (spec := unifSpec) (superSpec := AdversarySpec) (p := fun _ => True)
      (hpq := fun query => by simp [IsClass, SubSpec.onQuery])
    exact (OracleComp.isQueryBoundP_true_iff _ _).mpr (sampleFamily_uniform_bound count)
  | sign =>
    exact OracleComp.IsQueryBoundP.liftComp_subSpec
      (spec := unifSpec) (superSpec := AdversarySpec) (p := fun _ => False)
      (hpq := fun query => by simp [IsClass, SubSpec.onQuery])
      (OracleComp.isQueryBoundP_false _ 0)
  | staticDh =>
    exact OracleComp.IsQueryBoundP.liftComp_subSpec
      (spec := unifSpec) (superSpec := AdversarySpec) (p := fun _ => False)
      (hpq := fun query => by simp [IsClass, SubSpec.onQuery])
      (OracleComp.isQueryBoundP_false _ 0)

/-- Each constructed reduction pays for all locally generated seeds plus the complete source class cap. -/
theorem reduction_query_bound (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (FamilyAdversarySpec (count + 1)) (FamilyForgery (count + 1)))
    (kind : Kind) (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (familyClass (IsClass kind)) bound)
    (jointPublic : PublicIdentity) :
    (reduction primitives target adversary jointPublic).IsQueryBoundP (IsClass kind)
      ((if kind = .uniform then 32 * count else 0) + bound) := by
  unfold reduction
  apply OracleComp.isQueryBoundP_bind (sampleFamily_lift_bound count kind)
  intro others _
  simpa only [bind_pure_comp, OracleComp.isQueryBoundP_map_iff] using
    routed_query_bound primitives target others (IsClass kind) _ bound (bounded _) (emptyHistory count)

/-- Exact event counts use actual returned DH options; rejected requests remain visible. -/
def EventInClass (kind : Kind) : Event → Bool
  | .signed _ _ => decide (kind = .sign)
  | .staticDh _ _ => decide (kind = .staticDh)

def historyCount (kind : Kind) (history : History) : ℕ := history.countP (EventInClass kind)

def rejectedDhCount (history : History) : ℕ := history.countP fun event => match event with
  | .staticDh _ none => true
  | _ => false

/-- Invalid-point and other checked DH rejections occupy the same DH request budget. -/
theorem rejectedDhCount_le (history : History) :
    rejectedDhCount history ≤ historyCount .staticDh history := by
  induction history with
  | nil => simp [rejectedDhCount, historyCount]
  | cons event rest ih =>
    cases event with
    | signed message signature => simpa [rejectedDhCount, historyCount, EventInClass] using ih
    | staticDh peer reply =>
      cases reply <;> simp [rejectedDhCount, historyCount, EventInClass] at ih ⊢ <;> omega

/-- Every source call increases any fixed identity's class counter by at most its one classified request. -/
theorem familyImpl_count (primitives : Primitives) {count : ℕ} (seeds : Fin count → IdentitySeed)
    (kind : Kind) (target : Fin count) (query : (FamilyAdversarySpec count).Domain)
    (history : FamilyHistory count) (result : (FamilyAdversarySpec count).Range query × FamilyHistory count)
    (supported : result ∈ support ((familyImpl primitives seeds query).run history)) :
    historyCount kind (result.2 target) ≤ historyCount kind (history target) +
      if familyClass (IsClass kind) query then 1 else 0 := by
  cases query with
  | inl coin =>
    simp only [familyImpl, StateT.run, mem_support_bind_iff] at supported
    obtain ⟨answer, _, supported⟩ := supported
    simp only [mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | inr query =>
    rcases query with ⟨index, request⟩
    simp only [familyImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    by_cases same : target = index
    · subst target
      cases request <;> cases kind <;> simp [historyCount, EventInClass, requestEvent, familyClass, IsClass]
    · simp [same]

/-- Complete adaptive family histories satisfy the source class caps, including all failed raw DH requests. -/
theorem familyRun_history_bound (primitives : Primitives) {count : ℕ}
    (seeds : Fin count → IdentitySeed) (kind : Kind) (target : Fin count)
    {Result : Type} (client : OracleComp (FamilyAdversarySpec count) Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP (familyClass (IsClass kind)) bound)
    (history : FamilyHistory count) (result : Result × FamilyHistory count)
    (supported : result ∈ support ((simulateQ (familyImpl primitives seeds) client).run history)) :
    historyCount kind (result.2 target) ≤ historyCount kind (history target) + bound := by
  induction client using OracleComp.inductionOn generalizing bound history result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨⟨answer, next⟩, step, restSupport⟩ := supported
    have stepCount := familyImpl_count primitives seeds kind target query history (answer, next) step
    have remaining := ih answer _ (bounded.2 answer) next result restSupport
    by_cases selected : familyClass (IsClass kind) query
    · have positive : 0 < bound := bounded.1.resolve_left (not_not.mpr selected)
      simp only [selected, ite_eq_left] at stepCount remaining
      omega
    · simp only [selected, ite_false] at stepCount remaining
      omega

/-- Rejected static-DH responses are explicitly bounded by all source DH attempts. -/
theorem familyRun_rejectedDh_bound (primitives : Primitives) {count : ℕ}
    (seeds : Fin count → IdentitySeed) (target : Fin count)
    {Result : Type} (client : OracleComp (FamilyAdversarySpec count) Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP (familyClass (IsClass .staticDh)) bound)
    (result : Result × FamilyHistory count)
    (supported : result ∈ support ((simulateQ (familyImpl primitives seeds) client).run (emptyHistory count))) :
    rejectedDhCount (result.2 target) ≤ bound := by
  exact (rejectedDhCount_le _).trans (by
    simpa [emptyHistory, historyCount] using
      familyRun_history_bound primitives seeds .staticDh target client bound bounded (emptyHistory count) result supported)

/-- The ordinary challenger forwards each requested uniform value and uses no hidden randomness for deterministic sign/DH replies. -/
theorem jointImpl_uniform_step (primitives : Primitives) (seed : IdentitySeed)
    (query : AdversarySpec.Domain) (history : History) :
    ((jointImpl primitives seed query).run history).IsQueryBoundP (fun _ => True)
      (if IsClass .uniform query then 1 else 0) := by
  cases query with
  | inl coin =>
    change OracleComp.IsQueryBoundP
      ((fun answer => (answer, history)) <$> (unifSpec.query coin : ProbComp _)) (fun _ => True) 1
    simp only [OracleComp.isQueryBoundP_map_iff]
    exact (OracleComp.isQueryBoundP_query_iff (spec := unifSpec) (p := fun _ => True) coin 1).mpr (by simp)
  | inr request =>
    cases request <;> change (pure _ : ProbComp _).IsQueryBoundP (fun _ => True) 0 <;> trivial

/-- Interpreting a complete joint-use adversary retains its entire uniform-oracle cap. -/
theorem jointRun_uniform_bound (primitives : Primitives) (seed : IdentitySeed) {Result : Type}
    (client : OracleComp AdversarySpec Result) (bound : ℕ)
    (bounded : client.IsQueryBoundP (IsClass .uniform) bound) (history : History) :
    ((simulateQ (jointImpl primitives seed) client).run history).IsTotalQueryBound bound := by
  exact (OracleComp.isQueryBoundP_true_iff _ _).mp
    (bounded.simulateQ_run_StateT_of_step (jointImpl_uniform_step primitives seed) history)

/-- The complete single-identity challenger pays its own 32 seed draws in addition to the adversary's uniform work. -/
theorem jointGame_uniform_bound (primitives : Primitives)
    (adversary : PublicIdentity → OracleComp AdversarySpec Forgery) (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (IsClass .uniform) bound) :
    (game primitives adversary).IsTotalQueryBound (32 + bound) := by
  unfold game
  apply OracleComp.isTotalQueryBound_bind sampleSeed_uniform_bound
  intro seed
  simpa only [run, bind_pure_comp, OracleComp.IsTotalQueryBound, OracleComp.isQueryBound_map_iff] using
    jointRun_uniform_bound primitives seed (adversary (primitives.publicKeys seed)) bound (bounded _) []

/-- Full interpreted reduction cost includes both the challenger identity and every locally generated identity. -/
theorem reductionGame_uniform_bound (primitives : Primitives) {count : ℕ} (target : Fin (count + 1))
    (adversary : (Fin (count + 1) → PublicIdentity) →
      OracleComp (FamilyAdversarySpec (count + 1)) (FamilyForgery (count + 1)))
    (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (familyClass (IsClass .uniform)) bound) :
    (game primitives (reduction primitives target adversary)).IsTotalQueryBound (32 * (count + 1) + bound) := by
  have counted := jointGame_uniform_bound primitives (reduction primitives target adversary) (32 * count + bound)
    (fun publicKeys => by simpa only [ite_true] using
      reduction_query_bound primitives target adversary .uniform bound bounded publicKeys)
  convert counted using 1
  omega

end BeaconcryptCore.Computational.PqxdhJointIdentityFamily

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFamily.sampleFamily_target_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFamily.sampleFamily_target_first

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFamily.targetRouting_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFamily.targetRouting_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFamily.family_advantage_le_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFamily.family_advantage_le_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFamily.reduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFamily.reduction_query_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFamily.familyRun_rejectedDh_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFamily.familyRun_rejectedDh_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentityFamily.reductionGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentityFamily.reductionGame_uniform_bound

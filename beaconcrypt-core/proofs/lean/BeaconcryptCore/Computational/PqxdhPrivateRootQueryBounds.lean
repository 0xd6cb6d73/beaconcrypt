import BeaconcryptCore.Computational.PqxdhPrivateRootSource

/-!
Logical bounds retain source creation, public/private coins, base calls, attempted decapsulation and typed public KDF queries through full adaptive state. Completed/abort source work precedes the separate challenger encapsulation. Blocked attempts remain charged. Full primitive sampling is established in PrivateRootGameBudgets; deterministic signing/DH/verification remains computational work.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhJointPhase1AcceptanceComposition PqxdhPrivateSourceCoins
open PqxdhPrivateKemSource PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhPrivateRootSource PqxdhKemIndCca PqxdhInitializerSecrecy
open PqxdhDynamicIdentityRouting
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev SourceUniform := IsSourceClass (PqxdhJointPhase1Reports.SourceClass PqxdhDynamicIdentityPool.IsUniform)

/-- Every actual source request retains its history and costs32 only for creation, one only for explicit public coins. -/
theorem bare_uniform_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (query : SourceSpec.Domain) (state : BareState count) :
    ((bareImpl attachedVerify primitives count query).run state).IsTotalQueryBound
      ((if Creating query then 32 else 0) + (if SourceUniform query then 1 else 0)) := by
  rcases state with ⟨history, pool⟩
  cases query with
  | inl request =>
      change ((sourceWithHistory count (PqxdhDynamicIdentityPool.lazyImpl primitives) request).run
        (history, pool)).IsTotalQueryBound
        ((if PqxdhDynamicIdentityPool.IsCreate request then 32 else 0) +
         (if PqxdhDynamicIdentityPool.IsUniform request then 1 else 0))
      rw [sourceWithHistory_run]
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        PqxdhDynamicIdentityPool.lazyImpl_uniform_step primitives request pool
  | inr candidate => trivial

set_option backward.isDefEq.respectTransparency false in
/-- Ordinary KEM uniform embedding retains each real coin query. -/
theorem ccaCoins_uniform {Result : Type} (client : ProbComp Result) (q : Nat)
    (bound : client.IsTotalQueryBound q) :
    (ccaCoins (baseSpec := baseSpec) client).IsQueryBoundP IsMlKemUniformQuery q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => simp [ccaCoins]
  | query_bind coin next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bound
      simp only [ccaCoins, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP (((MlKemCCAOracleSpec baseSpec).query (.inl (.inl coin)) :
        OracleComp (MlKemCCAOracleSpec baseSpec) ((MlKemCCAOracleSpec baseSpec).Range (.inl (.inl coin)))) >>=
        fun answer => ccaCoins (next answer)) IsMlKemUniformQuery q
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr bound.1, ?_⟩
      intro answer
      simpa only [IsMlKemUniformQuery, ite_true] using ih answer _ (bound.2 answer)

set_option backward.isDefEq.respectTransparency false in
/-- Source interpreter coins issue no other CCA resource class. -/
theorem ccaCoins_excluded {Result : Type} (client : ProbComp Result)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin))) :
    (ccaCoins (baseSpec := baseSpec) client).IsQueryBoundP predicate 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => simp [ccaCoins]
  | query_bind coin next ih =>
      simp only [ccaCoins, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP (((MlKemCCAOracleSpec baseSpec).query (.inl (.inl coin)) :
        OracleComp (MlKemCCAOracleSpec baseSpec) ((MlKemCCAOracleSpec baseSpec).Range (.inl (.inl coin)))) >>=
        fun answer => ccaCoins (next answer)) predicate 0
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (excluded coin), ?_⟩
      intro answer
      simpa only [excluded coin, ite_false, ccaCoins] using ih answer

/-- The selector's direct ordinary CCA resource remains distinct from every identity source service. -/
def SelectorCCA (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) :
    (SelectorSpec baseSpec).Domain → Prop
  | .inl _ => False
  | .inr query => predicate query
instance (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (SelectorCCA (baseSpec := baseSpec) predicate) := fun query => by
  cases query <;> dsimp [SelectorCCA] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Borrowing the challenger preserves all source state; only creation and original uniform requests add ordinary coins. -/
theorem borrowed_uniform_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (query : (SelectorSpec baseSpec).Domain)
    (state : BareState count) :
    ((borrowedSelector attachedVerify primitives count query).run state).IsQueryBoundP IsMlKemUniformQuery
      ((if SelectorSource (baseSpec := baseSpec) Creating query then 32 else 0) +
       (if SelectorSource (baseSpec := baseSpec) SourceUniform query then 1 else 0) +
       (if SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery query then 1 else 0)) := by
  cases query with
  | inl request =>
      simpa only [borrowedSelector, StateT.run, SelectorSource, SelectorCCA, ite_false, Nat.add_zero] using
        ccaCoins_uniform ((bareImpl attachedVerify primitives count request).run state) _
          (bare_uniform_step attachedVerify primitives count request state)
  | inr request =>
      simp only [borrowedSelector, StateT.run, SelectorSource, SelectorCCA, ite_false, Nat.zero_add,
        bind_pure_comp, isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec)
        (p := IsMlKemUniformQuery) request _).2 (by split_ifs <;> simp_all)

/-- Full adaptive borrowing charges all original source creation/coin requests and every direct CCA uniform request. -/
theorem borrowed_uniform_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp (SelectorSpec baseSpec) Result)
    (qCreate qSourceCoins qCcaCoins : Nat)
    (creates : client.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : client.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinBound : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (state : BareState count) :
    ((simulateQ (borrowedSelector attachedVerify primitives count) client).run state).IsQueryBoundP
      IsMlKemUniformQuery (32 * qCreate + qSourceCoins + qCcaCoins) := by
  induction client using OracleComp.inductionOn generalizing qCreate qSourceCoins qCcaCoins state with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at creates sourceCoins ccaCoinBound
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isQueryBoundP_bind (borrowed_uniform_step attachedVerify primitives count query state)
        (fun result _ => ih result.1 _ _ _ (creates.2 result.1) (sourceCoins.2 result.1)
          (ccaCoinBound.2 result.1) result.2)).mono
      have hc := creates.1
      have hs := sourceCoins.1
      have hk := ccaCoinBound.1
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or] <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- Non-uniform ordinary resources are forwarded exactly; identity interpretation uses only its separately counted coins. -/
theorem borrowed_class_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin)))
    (query : (SelectorSpec baseSpec).Domain) (state : BareState count) :
    ((borrowedSelector attachedVerify primitives count query).run state).IsQueryBoundP predicate
      (if SelectorCCA (baseSpec := baseSpec) predicate query then 1 else 0) := by
  cases query with
  | inl request =>
      simpa only [borrowedSelector, StateT.run, SelectorCCA, ite_false] using
        ccaCoins_excluded ((bareImpl attachedVerify primitives count request).run state) predicate excluded
  | inr request =>
      simp only [borrowedSelector, StateT.run, SelectorCCA, bind_pure_comp, isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := MlKemCCAOracleSpec baseSpec)
        (p := predicate) request _).2 (by split_ifs <;> simp_all)

/-- Arbitrary adaptive borrowed continuations inherit every non-uniform direct CCA class, including all attempted decapsulations. -/
theorem borrowed_class_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp (SelectorSpec baseSpec) Result)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl coin))) (q : Nat)
    (bounded : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) predicate) q) (state : BareState count) :
    ((simulateQ (borrowedSelector attachedVerify primitives count) client).run state).IsQueryBoundP predicate q :=
  bounded.simulateQ_run_StateT_of_step
    (borrowed_class_step attachedVerify primitives count predicate excluded) state

set_option backward.isDefEq.respectTransparency false in
/-- Initializer uniform embedding retains each real coin query. -/
theorem postCoins_uniform {Result : Type} (client : ProbComp Result) (q : Nat)
    (bound : client.IsTotalQueryBound q) :
    (postCoins (baseSpec := baseSpec) client).IsQueryBoundP IsInitializerUniformQuery q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => simp [postCoins]
  | query_bind coin next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bound
      simp only [postCoins, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP (((InitializerPostSpec baseSpec).query (.inl (.inl (.inl coin))) :
        OracleComp (InitializerPostSpec baseSpec) ((InitializerPostSpec baseSpec).Range (.inl (.inl (.inl coin))))) >>=
        fun answer => postCoins (next answer)) IsInitializerUniformQuery q
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr bound.1, ?_⟩
      intro answer
      simpa only [IsInitializerUniformQuery, IsMlKemUniformQuery, ite_true] using ih answer _ (bound.2 answer)

set_option backward.isDefEq.respectTransparency false in
/-- Source interpreter coins issue no other initializer resource class. -/
theorem postCoins_excluded {Result : Type} (client : ProbComp Result)
    (predicate : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin)))) :
    (postCoins (baseSpec := baseSpec) client).IsQueryBoundP predicate 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => simp [postCoins]
  | query_bind coin next ih =>
      simp only [postCoins, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP (((InitializerPostSpec baseSpec).query (.inl (.inl (.inl coin))) :
        OracleComp (InitializerPostSpec baseSpec) ((InitializerPostSpec baseSpec).Range (.inl (.inl (.inl coin))))) >>=
        fun answer => postCoins (next answer)) predicate 0
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (excluded coin), ?_⟩
      intro answer
      simpa only [excluded coin, ite_false, postCoins] using ih answer

/-- Original source classes in the post-root protocol interface. -/
def PostSource (predicate : SourceSpec.Domain → Prop) : (PostSourceSpec baseSpec).Domain → Prop
  | .inl query => predicate query
  | .inr _ => False
instance (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (PostSource (baseSpec := baseSpec) predicate) := fun query => by
  cases query <;> dsimp [PostSource] <;> infer_instance

/-- Direct post-root CCA/public-KDF classes remain separate from identity services. -/
def PostDirect (predicate : (InitializerPostSpec baseSpec).Domain → Prop) :
    (PostSourceSpec baseSpec).Domain → Prop
  | .inl _ => False
  | .inr query => predicate query
instance (predicate : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred predicate] :
    DecidablePred (PostDirect (baseSpec := baseSpec) predicate) := fun query => by
  cases query <;> dsimp [PostDirect] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting post-root source services preserves all source state; only creation and original uniform requests add ordinary coins. -/
theorem postSource_uniform_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (query : (PostSourceSpec baseSpec).Domain)
    (state : BareState count) :
    ((postSourceImpl attachedVerify primitives count query).run state).IsQueryBoundP IsInitializerUniformQuery
      ((if PostSource (baseSpec := baseSpec) Creating query then 32 else 0) +
       (if PostSource (baseSpec := baseSpec) SourceUniform query then 1 else 0) +
       (if PostDirect (baseSpec := baseSpec) IsInitializerUniformQuery query then 1 else 0)) := by
  cases query with
  | inl request =>
      simpa only [postSourceImpl, StateT.run, PostSource, PostDirect, ite_false, Nat.add_zero] using
        postCoins_uniform ((bareImpl attachedVerify primitives count request).run state) _
          (bare_uniform_step attachedVerify primitives count request state)
  | inr request =>
      simp only [postSourceImpl, StateT.run, PostSource, PostDirect, ite_false, Nat.zero_add,
        bind_pure_comp, isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := InitializerPostSpec baseSpec)
        (p := IsInitializerUniformQuery) request _).2 (by split_ifs <;> simp_all)

/-- Full adaptive post-root interpretation charges all original source creation/coin requests and every direct initializer uniform request. -/
theorem postSource_uniform_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp (PostSourceSpec baseSpec) Result)
    (qCreate qSourceCoins qCcaCoins : Nat)
    (creates : client.IsQueryBoundP (PostSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : client.IsQueryBoundP (PostSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinBound : client.IsQueryBoundP (PostDirect (baseSpec := baseSpec) IsInitializerUniformQuery) qCcaCoins)
    (state : BareState count) :
    ((simulateQ (postSourceImpl attachedVerify primitives count) client).run state).IsQueryBoundP
      IsInitializerUniformQuery (32 * qCreate + qSourceCoins + qCcaCoins) := by
  induction client using OracleComp.inductionOn generalizing qCreate qSourceCoins qCcaCoins state with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at creates sourceCoins ccaCoinBound
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isQueryBoundP_bind (postSource_uniform_step attachedVerify primitives count query state)
        (fun result _ => ih result.1 _ _ _ (creates.2 result.1) (sourceCoins.2 result.1)
          (ccaCoinBound.2 result.1) result.2)).mono
      have hc := creates.1
      have hs := sourceCoins.1
      have hk := ccaCoinBound.1
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or] <;> omega

set_option backward.isDefEq.respectTransparency false in
/-- Non-uniform initializer resources are forwarded exactly; identity interpretation uses only its separately counted coins. -/
theorem postSource_class_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat)
    (predicate : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin))))
    (query : (PostSourceSpec baseSpec).Domain) (state : BareState count) :
    ((postSourceImpl attachedVerify primitives count query).run state).IsQueryBoundP predicate
      (if PostDirect (baseSpec := baseSpec) predicate query then 1 else 0) := by
  cases query with
  | inl request =>
      simpa only [postSourceImpl, StateT.run, PostDirect, ite_false] using
        postCoins_excluded ((bareImpl attachedVerify primitives count request).run state) predicate excluded
  | inr request =>
      simp only [postSourceImpl, StateT.run, PostDirect, bind_pure_comp, isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := InitializerPostSpec baseSpec)
        (p := predicate) request _).2 (by split_ifs <;> simp_all)

/-- Arbitrary adaptive post-root continuations inherit every non-uniform direct initializer class, including all attempted decapsulations. -/
theorem postSource_class_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp (PostSourceSpec baseSpec) Result)
    (predicate : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin)))) (q : Nat)
    (bounded : client.IsQueryBoundP (PostDirect (baseSpec := baseSpec) predicate) q) (state : BareState count) :
    ((simulateQ (postSourceImpl attachedVerify primitives count) client).run state).IsQueryBoundP predicate q :=
  bounded.simulateQ_run_StateT_of_step
    (postSource_class_step attachedVerify primitives count predicate excluded) state

set_option backward.isDefEq.respectTransparency false in
/-- The explicit ambient embedding is the same standard source lift used by common branches. -/
theorem ccaAmbient_eq_lift {Result : Type} (client : OracleComp (unifSpec + baseSpec) Result) :
    ccaAmbient client = client.liftComp (MlKemCCAOracleSpec baseSpec) := by
  induction client using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [ccaAmbient, simulateQ_bind, simulateQ_spec_query, liftComp_bind,
        PqxdhStatefulPhase1EufCma.phase1Base_cca_query_liftComp]
      congr 1
      funext answer
      exact ih answer

set_option backward.isDefEq.respectTransparency false in
/-- The exact ordinary ambient embedding preserves each chosen source class. -/
theorem ccaAmbient_bound {Result : Type} (client : OracleComp (unifSpec + baseSpec) Result)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (q : Nat) (bounded : client.IsQueryBoundP (fun query => predicate (.inl query)) q) :
    (ccaAmbient client).IsQueryBoundP predicate q := by
  induction client using OracleComp.inductionOn generalizing q with
  | pure value => simp [ccaAmbient]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [ccaAmbient, simulateQ_bind, simulateQ_spec_query]
      change OracleComp.IsQueryBoundP (((MlKemCCAOracleSpec baseSpec).query (.inl query) :
        OracleComp (MlKemCCAOracleSpec baseSpec) ((MlKemCCAOracleSpec baseSpec).Range (.inl query))) >>=
        fun answer => ccaAmbient (next answer)) predicate q
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

/-- The source-generated prefix pays for its actual identity, prekey, one-time and full adaptive selector work; signing is separately charged as three local operations. -/
theorem borrowedPrefix_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qSeed qPrekey qOneTime qSelector : Nat)
    (seedBound : (ccaCoins (baseSpec := baseSpec) sampleSeed).IsQueryBoundP predicate qSeed)
    (prekeyBound : ∀ identity, (ccaAmbient (setup.prekey identity)).IsQueryBoundP predicate qPrekey)
    (oneTimeBound : ∀ identity before target, (ccaAmbient (setup.oneTime identity before target)).IsQueryBoundP predicate qOneTime)
    (selectorBound : ∀ transcript state,
      ((simulateQ (borrowedSelector attachedVerify primitives 1) (selector.main transcript)).run state).IsQueryBoundP predicate qSelector)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) :
    (borrowedPrefix attachedVerify primitives setup selector target).IsQueryBoundP predicate
      (qSeed + (qPrekey + (qOneTime + qSelector))) := by
  unfold borrowedPrefix
  apply isQueryBoundP_bind seedBound
  intro seed _
  apply isQueryBoundP_bind (prekeyBound _)
  intro before _
  apply isQueryBoundP_bind (oneTimeBound _ _ _)
  intro after _
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using selectorBound _ _

/-- Real accepted non-target candidates pay actual native optional encapsulation, with every rejection and observer effect retained. -/
theorem acceptedCommon_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ output execution state,
      (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (state : BareState 1) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    (acceptedCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer output state
      parameters.server parameters.application parameters.ephemeralGen identity keys).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold acceptedCommon
  split
  · exact (observerBound _ _ _).mono (by omega)
  · apply isQueryBoundP_bind (by simpa only [ccaAmbient_eq_lift] using ephemeralBound)
    intro ephemeral _
    apply isQueryBoundP_bind (by simpa only [ccaAmbient_eq_lift] using nativeBound keys.pqKey)
    intro encapsulated _
    cases encapsulated <;> exact observerBound _ _ _

/-- All original acceptance/rejection branches share the same charged optional source bound. -/
theorem allCandidateCommon_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ output execution state,
      (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (state : BareState 1) :
    (allCandidateCommon parameters.source kem parameters.native attachedVerify primitives 1 setup observer output state
      parameters.server parameters.application parameters.ephemeralGen).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold allCandidateCommon
  cases output.bind (·.accepted) with
  | none => exact (observerBound _ _ _).mono (by omega)
  | some selected =>
      exact acceptedCommon_bound kem parameters attachedVerify primitives setup observer predicate
        qEphemeral qNative qObserver ephemeralBound nativeBound observerBound output state selected.1 selected.2

/-- The real abort encapsulation and every completed common branch precede challenger completion and remain charged. -/
theorem dispatch_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qTotal qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (observerBound : ∀ output execution state,
      (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) :
    (dispatch kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP predicate
      (qEphemeral + (max qNative qTotal + qObserver)) := by
  unfold dispatch
  split
  · simp
  · split
    · apply isQueryBoundP_bind ephemeralBound
      intro ephemeral _
      split
      · simp
      · apply isQueryBoundP_bind ((totalBound _).mono (Nat.le_max_right _ _))
        intro encapsulated _
        simpa only [bind_pure_comp, isQueryBoundP_map_iff] using observerBound _ _ _
    · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
        (allCandidateCommon_bound kem parameters attachedVerify primitives setup observer predicate
          qEphemeral qNative qObserver ephemeralBound nativeBound observerBound _ _).mono
          (by omega)

/-- Every prechallenge class is the complete generated prefix plus the full source dispatch; ghost challenger encapsulation is separately charged later. -/
theorem rootInitializer_prefix_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (observer : Observer setup selector.State)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qPrefix qEphemeral qNative qTotal qObserver : Nat)
    (prefixBound : ∀ target, (borrowedPrefix attachedVerify primitives setup selector target).IsQueryBoundP predicate qPrefix)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (totalBound : ∀ target, (ccaAmbient (kem.encaps target)).IsQueryBoundP predicate qTotal)
    (observerBound : ∀ output execution state,
      (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (target : PqxdhStatefulPhase1EufCma.TargetKemPublicKey) :
    ((rootInitializer kem parameters attachedVerify primitives setup selector observer).preChallenge target).IsQueryBoundP predicate
      (qPrefix + (qEphemeral + (max qNative qTotal + qObserver))) :=
  isQueryBoundP_bind (prefixBound target) (fun prepared _ => dispatch_bound kem parameters attachedVerify primitives
    setup observer predicate qEphemeral qNative qTotal qObserver ephemeralBound nativeBound totalBound observerBound prepared)

set_option backward.isDefEq.respectTransparency false in
/-- Public blocking does not increase any ordinary resource class; blocked attempts remain charged in the supplied original client budget. -/
theorem blockChallenge_bound {Result : Type} (challenge : MlKem768Ciphertext)
    (client : OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (q : Nat) (bounded : client.IsQueryBoundP predicate q) :
    (simulateQ (blockChallenge challenge) client).IsQueryBoundP predicate q := by
  have step : ∀ query, (blockChallenge (baseSpec := baseSpec) challenge query).IsQueryBoundP predicate
      (if predicate query then 1 else 0) := by
    intro query
    cases query with
    | inl request =>
        unfold blockChallenge
        rw [isQueryBoundP_query_iff]
        split_ifs <;> simp_all
    | inr ciphertext =>
        by_cases same : ciphertext = challenge
        · simp only [blockChallenge, same, ite_true, isQueryBoundP_pure]
        · simp only [blockChallenge, same, ite_false]
          rw [isQueryBoundP_query_iff]
          split_ifs <;> simp_all
  exact isQueryBoundP_simulateQ_of_step_noUniform bounded
    (fun query hit => by simpa only [hit, ite_true] using step query)
    (fun query miss => by simpa only [miss, ite_false] using step query)

/-- The actual target encapsulation continuation retains all observer work and counts its logical blocked requests before suppression. -/
theorem targetAfterEncapsulation_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qObserver : Nat)
    (observerBound : ∀ output execution state,
      (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (encapsulated : Option (MlKem768Ciphertext × MlKemSharedSecret)) :
    (targetAfterEncapsulation kem parameters attachedVerify primitives setup observer prepared ephemeral encapsulated).IsQueryBoundP
      predicate qObserver := by
  unfold targetAfterEncapsulation
  cases encapsulated with
  | none => exact observerBound _ _ _
  | some pair =>
      rcases pair with ⟨ciphertext, secret⟩
      dsimp only
      split
      · exact observerBound _ _ _
      · exact blockChallenge_bound _ _ predicate qObserver (observerBound _ _ _)

/-- The actual native game pays one source ephemeral and optional encapsulation on every eligible accepted branch, without assuming success. -/
theorem nativeNext_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qEphemeral qNative qObserver : Nat)
    (ephemeralBound : (ccaAmbient parameters.ephemeralGen).IsQueryBoundP predicate qEphemeral)
    (nativeBound : ∀ target, (ccaAmbient (parameters.native.encaps target)).IsQueryBoundP predicate qNative)
    (observerBound : ∀ output execution state,
      (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP predicate qObserver)
    (prepared : Prepared setup Selection) :
    (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP predicate
      (qEphemeral + (qNative + qObserver)) := by
  unfold nativeNext
  split
  · unfold nativeTargetContinuation
    apply isQueryBoundP_bind ephemeralBound
    intro ephemeral _
    apply isQueryBoundP_bind (nativeBound _)
    intro encapsulated _
    exact targetAfterEncapsulation_bound kem parameters attachedVerify primitives setup observer predicate qObserver
      observerBound prepared ephemeral encapsulated
  · exact allCandidateCommon_bound kem parameters attachedVerify primitives setup observer predicate
      qEphemeral qNative qObserver ephemeralBound nativeBound observerBound _ _

/-- Actual source-observer uniform cost includes every newly created identity and both explicit coin channels. -/
theorem observe_uniform_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState 1)
    (qCreate qSourceCoins qDirectCoins : Nat)
    (creates : (observer.main output execution).IsQueryBoundP (PostSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : (observer.main output execution).IsQueryBoundP (PostSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (directCoins : (observer.main output execution).IsQueryBoundP (PostDirect (baseSpec := baseSpec) IsInitializerUniformQuery) qDirectCoins) :
    (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP
      IsMlKemUniformQuery (32 * qCreate + qSourceCoins + qDirectCoins) := by
  unfold observe
  apply (OracleComp.isQueryBoundP_map_iff _ _ _).2
  exact initializerPostRealImpl_uniform_query_bound parameters.source kem
    (postSource_uniform_bound attachedVerify primitives 1 (observer.main output execution)
      qCreate qSourceCoins qDirectCoins creates sourceCoins directCoins state)

/-- Only original direct base requests reach the ordinary base oracle; source identity work retains its separate local cost. -/
theorem observe_base_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState 1) (q : Nat)
    (bounded : (observer.main output execution).IsQueryBoundP
      (PostDirect (baseSpec := baseSpec) IsInitializerBaseQuery) q) :
    (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP
      IsMlKemBaseQuery q := by
  unfold observe
  apply (OracleComp.isQueryBoundP_map_iff _ _ _).2
  exact initializerPostRealImpl_base_query_bound parameters.source kem
    (postSource_class_bound attachedVerify primitives 1 (observer.main output execution)
      IsInitializerBaseQuery (fun _ => by simp [IsInitializerBaseQuery, IsMlKemBaseQuery]) q bounded state)

/-- Every original logical decapsulation remains in the observer budget, including target-ciphertext requests later blocked by the ordinary challenger. -/
theorem observe_decap_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (output : Option (PqxdhPrivateCandidateAcceptance.Outcome (Retained setup Unit Selection)))
    (execution : PqxdhSourceAuthenticatedRoot.ServerExecution) (state : BareState 1) (q : Nat)
    (bounded : (observer.main output execution).IsQueryBoundP
      (PostDirect (baseSpec := baseSpec) IsInitializerLogicalDecapsulationQuery) q) :
    (observe parameters.source kem attachedVerify primitives 1 setup observer output execution state).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery q := by
  unfold observe
  apply (OracleComp.isQueryBoundP_map_iff _ _ _).2
  exact initializerPostRealImpl_decapsulation_query_bound parameters.source kem
    (postSource_class_bound attachedVerify primitives 1 (observer.main output execution)
      IsInitializerLogicalDecapsulationQuery
      (fun _ => by simp [IsInitializerLogicalDecapsulationQuery, IsMlKemLogicalDecapsulationQuery]) q bounded state)

/-- Root-dependent finishing preserves each non-uniform protocol class, including public root/symmetric KDF calls. -/
theorem finishTarget_class_bound
    (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection)
    (predicate : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (excluded : ∀ coin, ¬ predicate (.inl (.inl (.inl coin)))) (q : Nat)
    (bounded : ∀ output execution,
      (observer.main output execution).IsQueryBoundP (PostDirect (baseSpec := baseSpec) predicate) q)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : PqxdhSecretInputKdf.RootOutput) :
    (finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext root).IsQueryBoundP predicate q := by
  simp only [finishTarget, isQueryBoundP_map_iff]
  exact postSource_class_bound attachedVerify primitives 1 _ predicate excluded q (bounded _ _) prepared.2

/-- Pending finishing charges identity creation plus public-source and direct post-root coin requests through the supplied root. -/
theorem finishTarget_uniform_bound
    (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) {Selection : Type}
    (observer : Observer setup Selection) (qCreate qSourceCoins qDirectCoins : Nat)
    (creates : ∀ output execution, (observer.main output execution).IsQueryBoundP (PostSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : ∀ output execution, (observer.main output execution).IsQueryBoundP (PostSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (directCoins : ∀ output execution, (observer.main output execution).IsQueryBoundP (PostDirect (baseSpec := baseSpec) IsInitializerUniformQuery) qDirectCoins)
    (prepared : Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (ciphertext : MlKem768Ciphertext) (root : PqxdhSecretInputKdf.RootOutput) :
    (finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext root).IsQueryBoundP
      IsInitializerUniformQuery (32 * qCreate + qSourceCoins + qDirectCoins) := by
  simp only [finishTarget, isQueryBoundP_map_iff]
  exact postSource_uniform_bound attachedVerify primitives 1 _ qCreate qSourceCoins qDirectCoins
    (creates _ _) (sourceCoins _ _) (directCoins _ _) prepared.2

/-- Completed branches make no postchallenge calls; pending state inherits every exact observer class cap. -/
theorem rootInitializer_post_bound
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (observer : Observer setup selector.State)
    (predicate : (InitializerPostSpec baseSpec).Domain → Prop) [DecidablePred predicate] (q : Nat)
    (bounded : ∀ prepared ephemeral ciphertext root,
      (finishTarget parameters attachedVerify primitives setup observer prepared ephemeral ciphertext root).IsQueryBoundP predicate q)
    (transcript : InitializerPublicTranscript (Mode setup selector.State))
    (known : PqxdhHiddenRoot.KnownPqxdhRootCoordinates) (root : PqxdhSecretInputKdf.RootOutput) :
    ((rootInitializer kem parameters attachedVerify primitives setup selector observer).main transcript known root).IsQueryBoundP predicate q := by
  cases mode : transcript.context with
  | completed decision => simp [rootInitializer, mode]
  | pending prepared ephemeral => simpa only [rootInitializer, mode] using bounded prepared ephemeral transcript.ciphertext root

end BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.bare_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.bare_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaCoins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaCoins_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaCoins_excluded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaCoins_excluded

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_class_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_class_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowed_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postCoins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postCoins_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postCoins_excluded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postCoins_excluded

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_uniform_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_class_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_class_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.postSource_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaAmbient_eq_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaAmbient_eq_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaAmbient_bound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.ccaAmbient_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowedPrefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.borrowedPrefix_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.acceptedCommon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.acceptedCommon_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.allCandidateCommon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.allCandidateCommon_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.dispatch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.dispatch_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.rootInitializer_prefix_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.rootInitializer_prefix_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.blockChallenge_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.blockChallenge_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.targetAfterEncapsulation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.targetAfterEncapsulation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.nativeNext_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.nativeNext_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.observe_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.observe_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.observe_base_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.observe_base_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.observe_decap_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.observe_decap_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.finishTarget_class_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.finishTarget_class_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.finishTarget_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.finishTarget_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.rootInitializer_post_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds.rootInitializer_post_bound

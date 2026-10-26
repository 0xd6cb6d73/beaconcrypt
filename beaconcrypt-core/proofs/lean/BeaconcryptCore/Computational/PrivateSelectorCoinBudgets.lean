import BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets

/-!
Syntactic private-program coin accounting retains every possible public source reply and complete primitive sampling. Creation stays a separate source service: its 32-byte seed belongs to the actual source/challenger ledger, not a second client coin allowance. The same constructed joint-use reduction retains signing, attempted static-DH and uniform caps; no primitive endpoint or global policy is changed.
-/

/-!
These bounds count the uniform requests in the actual compiled private selector before its source interpreter runs. Private local computation forwards each actual coin request; public source creation remains one separate creation request with no syntactic uniform query. Interpreting that creation later still incurs its existing 32-byte seed budget. All complete adaptive continuations and possible oracle replies remain quantified. Opaque base and decapsulation sampling caps are explicit; deterministic primitive, verification, logging and byte-processing work is not declared free.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PrivateSelectorCoinBudgets
open PqxdhPhase1AcceptanceOracle PqxdhPrivateSourceCoins
open PqxdhPrivateKemSource PqxdhPrivateKemQueryBounds
open PqxdhPrivateRootQueryBounds PqxdhPrivateRootGameBudgets PqxdhKemIndCca
open PqxdhInitializerSecrecy
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Private evaluated coins become exactly the compiler's uniform query class; no creation draw is included here. -/
theorem localCoins_uniform {Result : Type} (client : ProbComp Result) (bound : Nat)
    (bounded : client.IsTotalQueryBound bound) :
    (localCoins client).IsQueryBoundP (fun query => SourceUniform (translated query)) bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => simp [localCoins]
  | query_bind query next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      simp only [localCoins, simulateQ_bind, simulateQ_spec_query]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inr bounded.1, ?_⟩
      intro answer
      exact ih answer _ (bounded.2 answer)

/-- Source creation remains its own forwarded query; only source coins and interpreted direct CCA work are local uniform requests. -/
theorem localSelector_uniform_step
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (query : (SelectorSpec baseSpec).Domain) :
    (localSelector baseImpl kem secret query).IsQueryBoundP
      (fun query => SourceUniform (translated query))
      ((if SelectorSource (baseSpec := baseSpec) SourceUniform query then 1 else 0) +
       (if SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery query then 1 else 0) +
       (if SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery query then qBase else 0) +
       (if SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery query then qDecap else 0)) := by
  cases query with
  | inl request =>
      simp only [localSelector, SelectorCCA, SelectorSource]
      apply publicSource_bound
      apply (isQueryBoundP_query_iff (spec := SourceSpec) (p := SourceUniform) request _).2
      split_ifs <;> simp_all
  | inr request =>
      simp only [localSelector, SelectorCCA]
      simpa only [ite_eq_right (show ¬ SelectorSource (baseSpec := baseSpec) SourceUniform
        (.inr request) from id), Nat.zero_add] using localCoins_uniform _ _
        (evalKem_query_uniform_bound baseImpl kem secret qBase qDecap baseBound decapBound request)

/-- The syntactic private selector budget retains every possible source and CCA reply, without charging source creation twice. -/
theorem localSelector_uniform_bound {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (SelectorSpec baseSpec) Result)
    (qSourceCoins qCcaCoins qBaseCalls qDecapCalls : Nat)
    (sourceCoins : client.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinsBound : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (bases : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls) :
    (simulateQ (localSelector baseImpl kem secret) client).IsQueryBoundP
      (fun query => SourceUniform (translated query))
      (qSourceCoins + qCcaCoins + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  induction client using OracleComp.inductionOn generalizing qSourceCoins qCcaCoins qBaseCalls qDecapCalls with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at sourceCoins ccaCoinsBound bases decaps
      rw [simulateQ_bind, simulateQ_spec_query]
      apply (isQueryBoundP_bind
        (localSelector_uniform_step baseImpl kem secret qBase qDecap baseBound decapBound query)
        (fun answer _ => ih answer _ _ _ _ (sourceCoins.2 answer) (ccaCoinsBound.2 answer)
          (bases.2 answer) (decaps.2 answer))).mono
      have hs := sourceCoins.1
      have hu := ccaCoinsBound.1
      have hb := bases.1
      have hd := decaps.1
      have baseStep : ∀ n, 0 < n → qBase * (n - 1) + qBase = qBase * n := by
        intro n hn
        rw [← Nat.mul_succ]
        congr 1
        omega
      have decapStep : ∀ n, 0 < n → qDecap * (n - 1) + qDecap = qDecap * n := by
        intro n hn
        rw [← Nat.mul_succ]
        congr 1
        omega
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or]
      all_goals try have := baseStep qBaseCalls (by omega)
      all_goals try have := decapStep qDecapCalls (by omega)
      all_goals omega

end BeaconcryptCore.Computational.PrivateSelectorCoinBudgets

/--
info: 'BeaconcryptCore.Computational.PrivateSelectorCoinBudgets.localCoins_uniform' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PrivateSelectorCoinBudgets.localCoins_uniform

/--
info: 'BeaconcryptCore.Computational.PrivateSelectorCoinBudgets.localSelector_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PrivateSelectorCoinBudgets.localSelector_uniform_step

/--
info: 'BeaconcryptCore.Computational.PrivateSelectorCoinBudgets.localSelector_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PrivateSelectorCoinBudgets.localSelector_uniform_bound

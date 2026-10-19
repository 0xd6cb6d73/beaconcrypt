import BeaconcryptCore.Computational.PqxdhPrivateRootQueryBounds

/-!
Actual source generation and optional execution are accounted before evaluated generator interchange. Explicit primitive sampling caps expand logical base/decapsulation counts; native and ordinary encapsulation costs remain separate. Both KEM worlds pay the ghost secret32 and the exact fair-bit game additionally pays one uniform query. Uniform requests count as calls, with fixed vectors drawing once per byte. Deterministic source and primitive work is not declared free.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhJointPhase1AcceptanceComposition PqxdhPrivateSourceCoins
open PqxdhPrivateKemSource PqxdhPrivateKemQueryBounds PqxdhPrivatePhase1Prefix
open PqxdhPrivateRootSource PqxdhPrivateRootQueryBounds PqxdhKemIndCca
open PqxdhInitializerSecrecy PqxdhStatefulPhase1EufCma PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Interpreting an ordinary query charges the actual opaque base or decapsulation work, including failed replies. -/
theorem evalKem_query_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (query : (MlKemCCAOracleSpec baseSpec).Domain) :
    (evalKem baseImpl kem secret ((MlKemCCAOracleSpec baseSpec).query query)).IsTotalQueryBound
      ((if IsMlKemUniformQuery query then 1 else 0) +
       (if IsMlKemBaseQuery query then qBase else 0) +
       (if IsMlKemLogicalDecapsulationQuery query then qDecap else 0)) := by
  simp only [evalKem, simulateQ_spec_query]
  rcases query with (coin | query) | ciphertext
  all_goals simp only [localKemPreChallengeImpl, KEMScheme.IND_CCA_preChallengeImpl,
    IsMlKemUniformQuery, IsMlKemBaseQuery,
    IsMlKemLogicalDecapsulationQuery, ite_true, ite_false, Nat.zero_add, Nat.add_zero]
  · change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inl coin))).IsTotalQueryBound 1
    rw [simulateQ_spec_query]
    change OracleComp.IsTotalQueryBound (unifSpec.query coin : ProbComp _) 1
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · change (simulateQ (kemAmbientImpl baseImpl)
      ((unifSpec + baseSpec).query (.inr query))).IsTotalQueryBound qBase
    rw [simulateQ_spec_query]
    exact baseBound query
  · exact decapBound ciphertext

/-- The whole adaptive interpreter expands all three resource classes against explicit primitive sampling caps. -/
theorem evalKem_uniform_bound {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (qUniform qBaseCalls qDecapCalls : Nat)
    (uniforms : client.IsQueryBoundP IsMlKemUniformQuery qUniform)
    (bases : client.IsQueryBoundP IsMlKemBaseQuery qBaseCalls)
    (decaps : client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapCalls) :
    (evalKem baseImpl kem secret client).IsTotalQueryBound
      (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  induction client using OracleComp.inductionOn generalizing qUniform qBaseCalls qDecapCalls with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at uniforms bases decaps
      rw [evalKem_bind]
      apply (isTotalQueryBound_bind
        (evalKem_query_uniform_bound baseImpl kem secret qBase qDecap baseBound decapBound query)
        (fun answer => ih answer _ _ _ (uniforms.2 answer) (bases.2 answer) (decaps.2 answer))).mono
      have hu := uniforms.1
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

/-- Actual prekey, KEM and one-time generation is charged in source order, retaining all private results. -/
theorem generate_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (qPrekey qKeygen qOneTime : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (identity : Ed25519PublicKey) :
    (generate baseImpl kem setup identity).IsTotalQueryBound (qPrekey + (qKeygen + qOneTime)) := by
  unfold generate
  apply isTotalQueryBound_bind (prekeyBound identity)
  intro before
  apply isTotalQueryBound_bind keygenBound
  rintro ⟨target, secret⟩
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    oneTimeBound identity before target

/-- The source selector's complete private evaluation expands its original service and CCA budgets. -/
theorem localSelector_uniform_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (SelectorSpec baseSpec) Result)
    (qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls : Nat)
    (creates : client.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : client.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinsBound : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (bases : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : client.IsQueryBoundP (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls)
    (state : BareState count) :
    ((simulateQ (privateImpl attachedVerify primitives count)
      (simulateQ (localSelector baseImpl kem secret) client)).run state).IsTotalQueryBound
      (32 * qCreate + qSourceCoins + qCcaCoins + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  rw [localSelector_complete]
  exact evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound decapBound _ _ _ _
    (borrowed_uniform_bound attachedVerify primitives count client _ _ _ creates sourceCoins ccaCoinsBound state)
    (borrowed_class_bound attachedVerify primitives count client IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery])
      qBaseCalls bases state)
    (borrowed_class_bound attachedVerify primitives count client IsMlKemLogicalDecapsulationQuery (fun _ => by simp [IsMlKemLogicalDecapsulationQuery])
      qDecapCalls decaps state)

/-- The actual private source prefix charges its identity seed and complete generation/selection executions in their original order. -/
theorem program_uniform_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context) (qGeneration qSelector : Nat)
    (generationBound : ∀ identity, (generate baseImpl kem setup identity).IsTotalQueryBound qGeneration)
    (selectorBound : ∀ secret publicTranscript state,
      ((simulateQ (privateImpl attachedVerify primitives count)
        (simulateQ (localSelector baseImpl kem secret) (selector.main publicTranscript))).run state).IsTotalQueryBound qSelector) :
    (privateRun attachedVerify primitives count (program baseImpl kem setup selector)).IsTotalQueryBound
      (32 + (qGeneration + qSelector)) := by
  rw [program_complete]
  apply isTotalQueryBound_bind sampleSeed_uniform_bound
  intro seed
  apply isTotalQueryBound_bind (generationBound _)
  intro generated
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    selectorBound generated.secret _ _

/-- Exact challenge blocking can reduce interpreted work, while the budget still charges every original logical attempt. -/
theorem postChallenge_uniform_bound {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (ciphertext : MlKem768Ciphertext) (qBase qDecap : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (qUniform qBaseCalls qDecapCalls : Nat)
    (uniforms : client.IsQueryBoundP IsMlKemUniformQuery qUniform)
    (bases : client.IsQueryBoundP IsMlKemBaseQuery qBaseCalls)
    (decaps : client.IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapCalls) :
    (simulateQ (kemAmbientImpl baseImpl)
      (simulateQ (kem.IND_CCA_postChallengeImpl secret ciphertext) client)).IsTotalQueryBound
        (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  rw [← evalKem_blockChallenge]
  exact evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound decapBound _ _ _ _
    (blockChallenge_bound ciphertext client IsMlKemUniformQuery qUniform uniforms)
    (blockChallenge_bound ciphertext client IsMlKemBaseQuery qBaseCalls bases)
    (blockChallenge_bound ciphertext client IsMlKemLogicalDecapsulationQuery qDecapCalls decaps)

/-- Full source execution is bounded before any evaluated generator reordering, so sampling costs are not inferred from marginal equality. -/
theorem continuedSource_uniform_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (next : Prepared setup selector.State → OracleComp (MlKemCCAOracleSpec baseSpec) Result)
    (fallback : Result) (qPrefix qNext : Nat)
    (prefixBound : (privateRun attachedVerify primitives 1
      (program baseImpl kem setup selector)).IsTotalQueryBound qPrefix)
    (nextBound : ∀ secret prepared,
      (evalKem baseImpl kem secret (next prepared)).IsTotalQueryBound qNext) :
    (continuedSource attachedVerify primitives baseImpl kem setup selector next fallback).IsTotalQueryBound
      (qPrefix + qNext) := by
  unfold continuedSource
  apply isTotalQueryBound_bind prefixBound
  rintro ⟨output, state⟩
  cases output with
  | none => trivial
  | some output => exact nextBound output.context.generated.secret (eraseOutput output, state)

/-- The KDF sampler prefix includes an ordinary challenger encapsulation on every branch, separately from any completed source work. -/
theorem initializerKdfPrefix_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (adversary : InitializerAdversary kem)
    (qKeygen qEncap qBase qDecap qUniform qBaseCalls qDecapCalls : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (uniforms : ∀ target, (adversary.preChallenge target).IsQueryBoundP IsMlKemUniformQuery qUniform)
    (bases : ∀ target, (adversary.preChallenge target).IsQueryBoundP IsMlKemBaseQuery qBaseCalls)
    (decaps : ∀ target, (adversary.preChallenge target).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapCalls) :
    (initializerKdfPrefixProb baseImpl kem adversary).IsTotalQueryBound
      (qKeygen + ((qUniform + qBase * qBaseCalls + qDecap * qDecapCalls) + qEncap)) := by
  unfold initializerKdfPrefixProb
  apply isTotalQueryBound_bind keygenBound
  rintro ⟨target, secret⟩
  apply isTotalQueryBound_bind
    (evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound (decapBound secret)
      (adversary.preChallenge target) _ _ _ (uniforms target) (bases target) (decaps target))
  intro state
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using encapBound target

/-- The complete supplied-root observer expands its actual source/base/decapsulation work; public deterministic KDF calls retain separate logical caps. -/
theorem rootObserver_uniform_bound
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (adversary : InitializerAdversary kem)
    (qBase qDecap qUniform qBaseCalls qDecapCalls : Nat)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (uniforms : ∀ transcript known root, (adversary.main transcript known root).IsQueryBoundP IsInitializerUniformQuery qUniform)
    (bases : ∀ transcript known root, (adversary.main transcript known root).IsQueryBoundP IsInitializerBaseQuery qBaseCalls)
    (decaps : ∀ transcript known root,
      (adversary.main transcript known root).IsQueryBoundP IsInitializerLogicalDecapsulationQuery qDecapCalls)
    (sampled : InitializerKdfPrefix kem adversary) (root : PqxdhSecretInputKdf.RootOutput) :
    (PqxdhSecretInputInitializer.rootObserver source baseImpl kem adversary sampled root).IsTotalQueryBound
      (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls) := by
  unfold PqxdhSecretInputInitializer.rootObserver
  apply postChallenge_uniform_bound baseImpl kem sampled.secretKey sampled.ciphertext qBase qDecap
    baseBound (decapBound sampled.secretKey)
  · exact initializerPostRealImpl_uniform_query_bound source kem (uniforms _ _ _)
  · exact initializerPostRealImpl_base_query_bound source kem (bases _ _ _)
  · exact initializerPostRealImpl_decapsulation_query_bound source kem (decaps _ _ _)

/-- Both fixed ordinary KEM worlds pay every challenger draw, including the unused 32-byte secret, independently of the selected branch. -/
theorem oneKeyBranch_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (adversary : OneKeyAdversary kem)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (bounds : adversary.MakesAtMostQueries uPre bPre dPre uPost bPost dPost) (bit : Bool) :
    (simulateQ (kemAmbientImpl baseImpl)
      (oneKeyBranchMain kem (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary bit)).IsTotalQueryBound
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) +
        (qEncap + (32 + (uPost + qBase * bPost + qDecap * dPost))))) := by
  simp only [oneKeyBranchMain, oneKeyPrefix, oneKeyFinish, bind_assoc, pure_bind,
    simulateQ_bind, runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftProbComp]
  apply isTotalQueryBound_bind keygenBound
  rintro ⟨target, secret⟩
  apply isTotalQueryBound_bind
    (evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound (decapBound secret)
      (adversary.preChallenge target) _ _ _ (bounds.1 target).1 (bounds.1 target).2.1 (bounds.1 target).2.2)
  intro state
  apply isTotalQueryBound_bind (encapBound target)
  rintro ⟨ciphertext, realSecret⟩
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro randomSecret
  exact postChallenge_uniform_bound baseImpl kem secret ciphertext qBase qDecap baseBound
    (decapBound secret) _ _ _ _
    (bounds.2 ⟨target, ciphertext, state⟩ (if bit then realSecret else randomSecret)).1
    (bounds.2 ⟨target, ciphertext, state⟩ (if bit then realSecret else randomSecret)).2.1
    (bounds.2 ⟨target, ciphertext, state⟩ (if bit then realSecret else randomSecret)).2.2

/-- The unchanged optional-source root game has its own full sampling ledger; native encapsulation costs are not inferred from honest-key output compatibility. -/
theorem actualGame_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : Parameters baseSpec)
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (selector : Selector baseSpec setup.Context)
    (observer : Observer setup selector.State)
    (qPrefix qBase qDecap qUniform qBaseCalls qDecapCalls : Nat)
    (prefixBound : (privateRun attachedVerify primitives 1
      (program baseImpl kem setup selector)).IsTotalQueryBound qPrefix)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (uniforms : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemUniformQuery qUniform)
    (bases : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemBaseQuery qBaseCalls)
    (decaps : ∀ prepared, (nativeNext kem parameters attachedVerify primitives setup observer prepared).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery qDecapCalls) :
    (actualGame baseImpl kem parameters attachedVerify primitives setup selector observer).IsTotalQueryBound
      (qPrefix + (qUniform + qBase * qBaseCalls + qDecap * qDecapCalls)) := by
  apply continuedSource_uniform_bound attachedVerify primitives baseImpl kem setup selector _ false _ _ prefixBound
  intro secret prepared
  exact evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound (decapBound secret) _ _ _ _
    (uniforms prepared) (bases prepared) (decaps prepared)

/-- Concrete private source generation and adaptive selector budgets combine without an unexpanded protocol-prefix allowance. -/
theorem program_uniform_from_calls
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (setup : StatefulPhase1Setup baseSpec)
    (selector : Selector baseSpec setup.Context)
    (qPrekey qKeygen qOneTime qBase qDecap qCreate qSourceCoins qCcaCoins qBaseCalls qDecapCalls : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (creates : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) Creating) qCreate)
    (sourceCoins : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorSource (baseSpec := baseSpec) SourceUniform) qSourceCoins)
    (ccaCoinsBound : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemUniformQuery) qCcaCoins)
    (bases : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemBaseQuery) qBaseCalls)
    (decaps : ∀ transcript, (selector.main transcript).IsQueryBoundP
      (SelectorCCA (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) qDecapCalls) :
    (privateRun attachedVerify primitives count (program baseImpl kem setup selector)).IsTotalQueryBound
      (32 + ((qPrekey + (qKeygen + qOneTime)) +
        (32 * qCreate + qSourceCoins + qCcaCoins + qBase * qBaseCalls + qDecap * qDecapCalls))) := by
  apply program_uniform_bound attachedVerify primitives count baseImpl kem setup selector
  · exact generate_uniform_bound baseImpl kem setup qPrekey qKeygen qOneTime prekeyBound keygenBound oneTimeBound
  · intro secret transcript state
    exact localSelector_uniform_bound attachedVerify primitives count baseImpl kem secret qBase qDecap
      baseBound (decapBound secret) (selector.main transcript) _ _ _ _ _
      (creates transcript) (sourceCoins transcript) (ccaCoinsBound transcript) (bases transcript) (decaps transcript) state

/-- The ordinary fair-bit challenger as a concrete probabilistic program, with its original prefix-before-bit order. -/
noncomputable def oneKeyFairProgram
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (adversary : OneKeyAdversary kem) : ProbComp Bool :=
  simulateQ (kemAmbientImpl baseImpl) do
    let preState ← oneKeyPrefix kem adversary
    let bit ← (runtimeOfImpl (kemAmbientImpl baseImpl)).liftProbComp ($ᵗ Bool)
    let decision ← oneKeyFinish kem (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary preState bit
    pure (bit == decision)

/-- The accounted fair-bit program is exactly the ordinary IND-CCA endpoint used by the root reduction. -/
theorem oneKeyFairProgram_eq
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (adversary : OneKeyAdversary kem) :
    𝒟[oneKeyFairProgram baseImpl kem adversary] =
      kem.IND_CCA_Game (runtimeOfImpl (kemAmbientImpl baseImpl)) adversary.toINDCCA := by
  simp only [oneKeyFairProgram, KEMScheme.IND_CCA_Game, OneKeyAdversary.toINDCCA,
    oneKeyPrefix, oneKeyFinish, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind,
    runtimeOfImpl_evalDist]

/-- The fair ordinary challenger adds exactly one permitted coin-query allowance to the fixed-world ledger. -/
theorem oneKeyFairProgram_uniform_bound
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (adversary : OneKeyAdversary kem)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (bounds : adversary.MakesAtMostQueries uPre bPre dPre uPost bPost dPost) :
    (oneKeyFairProgram baseImpl kem adversary).IsTotalQueryBound
      (qKeygen + ((uPre + qBase * bPre + qDecap * dPre) +
        (1 + (qEncap + (32 + (uPost + qBase * bPost + qDecap * dPost)))))) := by
  simp only [oneKeyFairProgram, oneKeyPrefix, oneKeyFinish, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_pure, runtimeOfImpl_liftProbComp, simulateQ_kemAmbient_liftProbComp]
  apply isTotalQueryBound_bind keygenBound
  rintro ⟨target, secret⟩
  apply isTotalQueryBound_bind
    (evalKem_uniform_bound baseImpl kem secret qBase qDecap baseBound (decapBound secret)
      (adversary.preChallenge target) _ _ _ (bounds.1 target).1 (bounds.1 target).2.1 (bounds.1 target).2.2)
  intro state
  apply isTotalQueryBound_bind (show ($ᵗ Bool : ProbComp Bool).IsTotalQueryBound 1 from
    ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩)
  intro bit
  apply isTotalQueryBound_bind (encapBound target)
  rintro ⟨ciphertext, realSecret⟩
  apply isTotalQueryBound_bind (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32)
  intro randomSecret
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    postChallenge_uniform_bound baseImpl kem secret ciphertext qBase qDecap baseBound
      (decapBound secret) _ _ _ _
      (bounds.2 ⟨target, ciphertext, state⟩ (if bit then realSecret else randomSecret)).1
      (bounds.2 ⟨target, ciphertext, state⟩ (if bit then realSecret else randomSecret)).2.1
      (bounds.2 ⟨target, ciphertext, state⟩ (if bit then realSecret else randomSecret)).2.2

/-- The concrete initializer's eight logical caps determine full real-world, sampled-input and observer costs without an opaque prefix/post allowance. -/
theorem initializer_uniform_ledger
    (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (adversary : InitializerAdversary kem)
    (qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost qRoot qSym : Nat)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (encapBound : ∀ target, (simulateQ (kemAmbientImpl baseImpl) (kem.encaps target)).IsTotalQueryBound qEncap)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ secret ciphertext,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (bounds : adversary.MakesAtMostQueries uPre bPre dPre uPost bPost dPost qRoot qSym) :
    let prefixCost := qKeygen + ((uPre + qBase * bPre + qDecap * dPre) + qEncap)
    let post := uPost + qBase * bPost + qDecap * dPost
    (PqxdhSecretInputInitializer.secretInputSample baseImpl kem adversary).IsTotalQueryBound (prefixCost + 32) ∧
    (∀ sampled root,
      (PqxdhSecretInputInitializer.rootObserver source baseImpl kem adversary sampled root).IsTotalQueryBound post) ∧
    (initializerRealGame source baseImpl kem adversary).IsTotalQueryBound (prefixCost + 32 + post) := by
  dsimp only
  refine ⟨PqxdhSecretInputInitializer.secretInputSample_uniform_query_bound baseImpl kem adversary
    (initializerKdfPrefix_uniform_bound baseImpl kem adversary _ _ _ _ _ _ _ keygenBound encapBound
      baseBound decapBound (fun target => (bounds.1 target).1)
      (fun target => (bounds.1 target).2.1) (fun target => (bounds.1 target).2.2)), ?_, ?_⟩
  · exact rootObserver_uniform_bound source baseImpl kem adversary qBase qDecap uPost bPost dPost
      baseBound decapBound (fun t k r => (bounds.2 t k r).1)
      (fun t k r => (bounds.2 t k r).2.1) (fun t k r => (bounds.2 t k r).2.2.1)
  · simpa only [initializerRealGame, Nat.add_assoc] using
      oneKeyBranch_uniform_bound baseImpl kem (toKemOneKeyAdversary source kem adversary)
        qKeygen qEncap qBase qDecap uPre bPre dPre uPost bPost dPost keygenBound encapBound baseBound decapBound
        (toKemOneKeyAdversary_makesAtMostQueries source kem adversary bounds) true

end BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.evalKem_query_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.evalKem_query_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.evalKem_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.evalKem_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.generate_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.generate_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.localSelector_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.localSelector_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.program_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.program_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.postChallenge_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.postChallenge_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.continuedSource_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.continuedSource_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.initializerKdfPrefix_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.initializerKdfPrefix_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.rootObserver_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.rootObserver_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.oneKeyBranch_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.oneKeyBranch_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.actualGame_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.actualGame_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.program_uniform_from_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.program_uniform_from_calls

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.oneKeyFairProgram_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.oneKeyFairProgram_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.oneKeyFairProgram_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.oneKeyFairProgram_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.initializer_uniform_ledger' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets.initializer_uniform_ledger

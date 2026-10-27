import BeaconcryptCore.Computational.RawCtxSelectedNativeFreshLift
import BeaconcryptCore.Computational.RawCtxBadEventMixture

/-!
The actual compiled record/public/reveal client supplies its own adaptive final Boolean after seeing its original query replies. This ordinary confidentiality observer projects only that optional Boolean, mapping an explicit compiler stop to false. It never tests private role state, the selected key, or a key-dependent terminal freshness predicate. The same actual client consumes the existing ordinary CTX privacy endpoint with all source query classes retained.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxSelectedFamilyLiveCompiler (Front)
open RawCtxSelectedFamilyNonceCoupling (Full)
variable {A M P I D K : Type} {S B : Nat}

def finalBit : Option Bool → Bool := fun result => result.getD false

noncomputable def decision (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  (fun result => finalBit result.1) <$>
    RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before

/-- The executable observer retains the original final Boolean and maps explicit stopping to false without inspecting any private state. -/
theorem optional_cases (value : Bool) : finalBit (some value) = value ∧ finalBit none = false := ⟨rfl, rfl⟩

/-- Observing the original final Boolean preserves every actual compiled query predicate and allowance exactly. -/
theorem decision_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    (decision source writer prior parent target nonce next sender route read client before).IsQueryBoundP predicate bound ↔
      (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP predicate bound := by
  simp only [decision, isQueryBoundP_map_iff]

/-- The original six source budget coordinates still bound all component attempts; neither the final decision nor any reveal adds a component call. -/
theorem source_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget) :
    (decision source writer prior parent target nonce next sender route read client before).IsTotalQueryBound
      (RawCtxRevealBudgets.bill (fun _ => 1) 0 budget) := by
  simpa only [decision, IsTotalQueryBound, isQueryBound_map_iff] using
    RawCtxSelectedFamilyLiveCompiler.client_queries source writer prior parent target nonce next sender route read client budget bounded before

/-- Projecting the complete interpreted compiler result gives exactly the ordinary decision under the same selected-key interpreter and complete component state. -/
theorem source_projection (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Full M P I D K A S B) :
    (fun result => finalBit result.1) <$>
      RawCtxSelectedNativeFreshLift.compiledGame source writer prior parent key target nonce next sender route read client before =
      Prod.fst <$> (simulateQ
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (decision source writer prior parent target nonce next sender route read client before.1)).run before.2.2 := by
  simp only [RawCtxSelectedNativeFreshLift.compiledGame,
    decision, simulateQ_map, StateT.run_map, Functor.map_map, RawCtxSelectedFamilyLiveCompiler.output]
  unfold RawCtxSelectedReceiveCompiler.evaluated
  simp only [StateT.run, Functor.map_map]

/-- The original hidden-disclosure-stopped source view reaches that same executable observer at the coefficient-one source nonce-refusal cost. No private freshness event is substituted for the adversary's Boolean. -/
theorem stopped_distance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Full M P I D K A S B) :
    ((fun result => finalBit result.1) <$>
      RawCtxSelectedNativeFreshLift.stoppedGame source writer prior parent key target nonce next sender route read client before).boolDistance
      (Prod.fst <$> (simulateQ
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (decision source writer prior parent target nonce next sender route read client before.1)).run before.2.2) ≤
      (𝒟[RawCtxSelectedNativeFreshLift.nonceGame source writer prior parent key target nonce next sender route read client before] {true}).toReal := by
  have projected := discreteDistance_map_le
    (fun result : Option Bool × RawCtxSelectedFamilyNonceCoupling.SourceFull M P I D K A S B => finalBit result.1)
    (RawCtxSelectedNativeFreshLift.stoppedGame source writer prior parent key target nonce next sender route read client before)
    (RawCtxSelectedNativeFreshLift.compiledGame source writer prior parent key target nonce next sender route read client before)
  have distance := projected.trans
    (RawCtxSelectedFamilyNonceCoupling.executable_distance source writer prior parent key target nonce next sender route read client before)
  rw [source_projection source writer prior parent key target nonce next sender route read client before] at distance
  refine le_trans ?_ distance
  simpa only [ProbComp.boolDistance, ← prEvent_eq_evalDist_singleton] using
    abs_prEvent_toReal_sub_le_discreteDistance _ _

/-- The ordinary endpoint is exactly the actual compiled source view under one explicit uniform selected-key draw and its specified empty component state. No independence statement about arbitrary native contexts is inferred here. -/
theorem uniform_source_view (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B) (ambient : A) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder read) source.crypto
      (decision source writer prior parent target nonce next sender route read client before) =
      (do let key ← $ᵗ RootOutput
          (fun result => finalBit result.1) <$>
            RawCtxSelectedNativeFreshLift.compiledGame source writer prior parent key target nonce next sender route read client
              (before, (ambient, AdaptiveCtxDynamicKnownKeys.initialSource))) := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, map_bind]
  apply bind_congr
  intro key
  exact (source_projection source writer prior parent key target nonce next sender route read client
    (before, (ambient, AdaptiveCtxDynamicKnownKeys.initialSource))).symm

/-- The same explicit uniform source mixture pays the nonce-refusal probability in that very mixture, preserving adaptive source replies and stopping before the ordinary privacy comparison. -/
theorem uniform_stopped_distance (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B) (ambient : A) :
    ((do let key ← $ᵗ RootOutput
         (fun result : Option Bool × RawCtxSelectedFamilyNonceCoupling.SourceFull M P I D K A S B => finalBit result.1) <$>
          RawCtxSelectedNativeFreshLift.stoppedGame source writer prior parent key target nonce next sender route read client
            (before, (ambient, AdaptiveCtxDynamicKnownKeys.initialSource))) : ProbComp Bool).boolDistance
      (Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder read) source.crypto
        (decision source writer prior parent target nonce next sender route read client before)) ≤
      (𝒟[(do let key ← $ᵗ RootOutput
             RawCtxSelectedNativeFreshLift.nonceGame source writer prior parent key target nonce next sender route read client
               (before, (ambient, AdaptiveCtxDynamicKnownKeys.initialSource)))] {true}).toReal := by
  have averaged := RawCtxBadEventMixture.bind_bound ($ᵗ RootOutput)
    (fun key : RootOutput => (fun result => finalBit result.1) <$>
      RawCtxSelectedNativeFreshLift.stoppedGame source writer prior parent key target nonce next sender route read client
        (before, (ambient, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (fun key : RootOutput => Prod.fst <$> (simulateQ
      (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (decision source writer prior parent target nonce next sender route read client before)).run AdaptiveCtxDynamicKnownKeys.initialSource)
    (fun key : RootOutput => RawCtxSelectedNativeFreshLift.nonceGame source writer prior parent key target nonce next sender route read client
      (before, (ambient, AdaptiveCtxDynamicKnownKeys.initialSource)))
    (fun key : RootOutput => by
      rw [prEvent_eq_evalDist_singleton]
      exact (stopped_distance source writer prior parent key target nonce next sender route read client
        (before, (ambient, AdaptiveCtxDynamicKnownKeys.initialSource))))
  rw [← prEvent_eq_evalDist_singleton]
  simpa only [AdaptiveCtxDynamicKnownKeys.sourceGame, map_bind] using averaged

open AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxSharedReplayBounds
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation AdaptiveCtxReceive

/-- The concrete one-key privacy reduction retains each compiled source class separately: all explicit uniforms, selected/public or known-key hashes, selected seal attempts and selected raw attempts. -/
theorem reduction_budgets (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B)
    (qUniform qHash qSeal qRaw : Nat)
    (uniformBound : (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP UniformRoute qUniform)
    (hashBound : (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP HashRoute qHash)
    (sealBound : (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP (TargetClass IsRawQuery) qRaw) :
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient source.crypto
      (decision source writer prior parent target nonce next sender route read client before)
    reduction.IsQueryBoundP SourceUniform qUniform ∧ reduction.IsQueryBoundP SourceHash qHash ∧
      reduction.IsQueryBoundP SourceSeal qSeal ∧ reduction.IsQueryBoundP IsRawQuery qRaw := by
  apply AdaptiveCtxDynamicKnownBounds.decision_budgets
  · exact (decision_queries source writer prior parent target nonce next sender route read client before UniformRoute qUniform).mpr uniformBound
  · exact (decision_queries source writer prior parent target nonce next sender route read client before HashRoute qHash).mpr hashBound
  · exact (decision_queries source writer prior parent target nonce next sender route read client before (TargetClass SourceSeal) qSeal).mpr sealBound
  · exact (decision_queries source writer prior parent target nonce next sender route read client before (TargetClass IsRawQuery) qRaw).mpr rawBound

/-- The actual compiled public decision consumes the existing ordinary CTX privacy endpoint, with both explicit IND$ reductions, every indexed INT-CTXT reduction and the unchanged statistical terms. -/
theorem privacy_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B)
    (fallback : ModifiedNonceAeadForgery) (qHash qSeal qRaw : Nat)
    (hashBound : (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP HashRoute qHash)
    (sealBound : (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read client before).IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    let executable := decision source writer prior parent target nonce next sender route read client before
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient source.crypto executable
    let decode := RawCtxUniversalDecoder.decoder read
    ENNReal.ofReal ((Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode source.crypto executable).boolDistance
      (AdaptiveCtxPrivacyGuard.randomView decode reduction)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage source.crypto
        (AdaptiveCtxPrefixValidation.validationReduction decode source.crypto reduction qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage source.crypto
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (AdaptiveCtxReceive.wrapped decode reduction) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage source.crypto
        (AdaptiveCtxPrivacyGuard.viewReduction decode reduction)) := by
  apply AdaptiveCtxDynamicKnownBounds.selected_privacy
  · exact (decision_queries source writer prior parent target nonce next sender route read client before HashRoute qHash).mpr hashBound
  · exact (decision_queries source writer prior parent target nonce next sender route read client before (TargetClass SourceSeal) qSeal).mpr sealBound
  · exact (decision_queries source writer prior parent target nonce next sender route read client before (TargetClass IsRawQuery) qRaw).mpr rawBound
  · exact small

/-- A complete source-derived fallback uses the actual six-coordinate attempt bill for every component class, discharging all privacy-query premises without an opaque ambient-work allowance. Sharper per-class caps remain available through privacy_bound. -/
theorem privacy_source_bound (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Bool) (before : Front M P I D K S B)
    (fallback : ModifiedNonceAeadForgery) (budget : RawCtxRevealBudgets.Budget)
    (bounded : RawCtxRevealBudgets.Bounded client budget)
    (small : RawCtxRevealBudgets.bill (fun _ => 1) 0 budget < 2 ^ 96) :
    let q := RawCtxRevealBudgets.bill (fun _ => 1) 0 budget
    let executable := decision source writer prior parent target nonce next sender route read client before
    let reduction := AdaptiveCtxDynamicKnownKeys.decisionClient source.crypto executable
    let decode := RawCtxUniversalDecoder.decoder read
    ENNReal.ofReal ((Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode source.crypto executable).boolDistance
      (AdaptiveCtxPrivacyGuard.randomView decode reduction)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage source.crypto
        (AdaptiveCtxPrefixValidation.validationReduction decode source.crypto reduction q)) +
      (q : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range q, modifiedNonceAeadINTCTXTAdvantage source.crypto
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback (AdaptiveCtxReceive.wrapped decode reduction) index) +
      (q : ℝ≥0∞) / (2 ^ 512 : Nat) +
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage source.crypto
        (AdaptiveCtxPrivacyGuard.viewReduction decode reduction)) := by
  have cap := RawCtxSelectedFamilyLiveCompiler.client_queries source writer prior parent target nonce next sender route read client budget bounded before
  exact privacy_bound source writer prior parent target nonce next sender route read client before fallback
    _ _ _ cap.isQueryBoundP cap.isQueryBoundP cap.isQueryBoundP small

end BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.optional_cases' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.optional_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.decision_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.decision_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.source_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.source_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.source_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.source_projection

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.stopped_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.stopped_distance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.uniform_source_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.uniform_source_view

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.uniform_stopped_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.uniform_stopped_distance

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.reduction_budgets' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.reduction_budgets

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.privacy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.privacy_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.privacy_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver.privacy_source_bound

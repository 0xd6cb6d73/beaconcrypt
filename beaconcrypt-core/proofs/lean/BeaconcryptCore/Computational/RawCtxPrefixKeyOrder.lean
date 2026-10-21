import BeaconcryptCore.Computational.RawCtxSourceSharedRom
import BeaconcryptCore.Computational.JointEagerTable

/-!
The selected uniform message key can be sampled before the complete executed source prelude. The proof uses the entire evaluated prelude and continuation, including the actual shared ROM cache and added hash-observation history. The prelude program has no selected-key argument. It executes from the ordinary empty initial cache; no locally generated cache is installed into the challenger. Known byte aliases are retained.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPrefixKeyOrder
open CtxRomAuth AdaptiveCtxSharedHash AdaptiveCtxDynamicKnownKeys RawCtxSourceSharedRom

/-- The ordinary challenge experiment starts with the single empty ROM cache. -/
theorem initial_cache : initialSource.cache = ∅ := rfl

/-- Sampling the hidden key early preserves the complete evaluated continuation after the actual key-free prelude, including every prior known-key and public hash effect. -/
theorem complete {Context Result : Type} (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (prelude : OracleComp HashSpec Context)
    (continuation : CtxKey → Context → SourceState → ProbComp Result) :
    EvalDistEq (do
      let result ← (simulateQ AdaptiveCtxSharedTarget.sharedImpl prelude).run (∅, [])
      let key ← $ᵗ CtxKey
      continuation key result.1 (install initialSource result.2))
      (do
      let key ← $ᵗ CtxKey
      let result ← (simulateQ (sourceImpl real decode c key) (simulateQ forward prelude)).run initialSource
      continuation key result.1 result.2) := by
  simp_rw [forward_complete, bind_map_left]
  exact JointEagerTable.independent_comm_spmf
    ((simulateQ AdaptiveCtxSharedTarget.sharedImpl prelude).run (∅, [])) ($ᵗ CtxKey)
    (fun result key => continuation key result.1 (install initialSource result.2))

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.complete_vcvioLegacy :
    ∀ {Context Result : Type} (real : Bool) (decode : BeaconcryptCore.Computational.AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto) (prelude : OracleComp BeaconcryptCore.Computational.AdaptiveCtxSharedHash.HashSpec Context) (continuation : BeaconcryptCore.Computational.CtxRomAuth.CtxKey → Context → BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.SourceState → ProbComp Result),
      𝒮[do
          let result ← (simulateQ BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.sharedImpl prelude).run (∅, [])
          let key ← $ᵗ BeaconcryptCore.Computational.CtxRomAuth.CtxKey
          continuation key result.1 (BeaconcryptCore.Computational.RawCtxSourceSharedRom.install BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.initialSource result.2)] =
        𝒮[do
          let key ← $ᵗ BeaconcryptCore.Computational.CtxRomAuth.CtxKey
          let result ← (simulateQ (BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) (simulateQ BeaconcryptCore.Computational.RawCtxSourceSharedRom.forward prelude)).run BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.initialSource
          continuation key result.1 result.2] :=
  by simpa only [BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] using @BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.complete

/-- A key-free adaptive suffix runs in the ordinary initialized CTX experiment after the actual shared-ROM prelude, retaining the final result and complete challenger state. -/
theorem source_game {Context Result : Type} (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder)
    (c : Pqxdh.Crypto) (prelude : OracleComp HashSpec Context)
    (suffix : Context → OracleComp Spec Result) :
    EvalDistEq (sourceGame real decode c (simulateQ forward prelude >>= suffix))
      (do
        let result ← (simulateQ AdaptiveCtxSharedTarget.sharedImpl prelude).run (∅, [])
        let key ← $ᵗ CtxKey
        (simulateQ (sourceImpl real decode c key) (suffix result.1)).run (install initialSource result.2)) := by
  simp only [sourceGame, simulateQ_bind, StateT.run_bind]
  exact (complete real decode c prelude
    (fun key context state => (simulateQ (sourceImpl real decode c key) (suffix context)).run state)).symm

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.source_game_vcvioLegacy :
    ∀ {Context Result : Type} (real : Bool) (decode : BeaconcryptCore.Computational.AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto) (prelude : OracleComp BeaconcryptCore.Computational.AdaptiveCtxSharedHash.HashSpec Context) (suffix : Context → OracleComp BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.Spec Result),
      𝒮[BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.sourceGame real decode c (simulateQ BeaconcryptCore.Computational.RawCtxSourceSharedRom.forward prelude >>= suffix)] =
        𝒮[do
          let result ← (simulateQ BeaconcryptCore.Computational.AdaptiveCtxSharedTarget.sharedImpl prelude).run (∅, [])
          let key ← $ᵗ BeaconcryptCore.Computational.CtxRomAuth.CtxKey
          (simulateQ (BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.sourceImpl real decode c key) (suffix result.1)).run (BeaconcryptCore.Computational.RawCtxSourceSharedRom.install BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.initialSource result.2)] :=
  by simpa only [BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] using @BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.source_game

/-- Prefix forwarding preserves the exact public-hash and uniform budgets and makes no selected seal or raw-opening request. Known local primitive work remains in the source ledger. -/
theorem forward_bills {Result : Type} (prelude : OracleComp HashSpec Result) (qHash qUniform : Nat)
    (hashBound : prelude.IsQueryBoundP (HashClass true) qHash)
    (uniformBound : prelude.IsQueryBoundP (HashClass false) qUniform) :
    (simulateQ forward prelude).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute qHash ∧
    (simulateQ forward prelude).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute qUniform ∧
    (simulateQ forward prelude).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
    (simulateQ forward prelude).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 := by
  simp only [forward, QueryImpl.simulateQ_compose]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply RawCtxSelectedSealConsumer.lifted_bound
    change (simulateQ AdaptiveCtxSharedTarget.forward prelude).IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash qHash
    apply AdaptiveCtxSharedTarget.forward_bound
    simpa only [AdaptiveCtxSharedTarget.forward_hash_class] using hashBound
  · apply RawCtxSelectedSealConsumer.lifted_bound
    change (simulateQ AdaptiveCtxSharedTarget.forward prelude).IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform qUniform
    apply AdaptiveCtxSharedTarget.forward_bound
    simpa only [AdaptiveCtxSharedTarget.forward_uniform_class] using uniformBound
  · apply RawCtxSelectedSealConsumer.lifted_bound
    change (simulateQ AdaptiveCtxSharedTarget.forward prelude).IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal 0
    apply AdaptiveCtxSharedTarget.forward_bound
    simp only [AdaptiveCtxSharedTarget.forward_seal_class]
    exact isQueryBoundP_false prelude 0
  · apply RawCtxSelectedSealConsumer.lifted_bound
    change (simulateQ AdaptiveCtxSharedTarget.forward prelude).IsQueryBoundP AdaptiveCtxReceive.IsRawQuery 0
    apply AdaptiveCtxSharedTarget.forward_bound
    simp only [AdaptiveCtxSharedTarget.forward_raw_class]
    exact isQueryBoundP_false prelude 0

end BeaconcryptCore.Computational.RawCtxPrefixKeyOrder


/-- info: 'BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.initial_cache' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.initial_cache

/-- info: 'BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.complete

/-- info: 'BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.source_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.source_game

/-- info: 'BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.forward_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPrefixKeyOrder.forward_bills

import BeaconcryptCore.Computational.RawCtxReachedParentCut

/-!
Concrete source opening and receive interpretation of the reached predecessor cut. The same pending receive state, prior cache, original full76 response and complete shared primitive state feed the retained-entry continuation. The equations preserve rejected openings and every remaining skipped derivation. Selected-output uniformity and live freshness remain separate hybrid obligations.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxReachedParentSource
open RawCtxChainReceive RawCtxInterpretedOpening RawCtxChainInterpretation
open RawCtxReachedParentCut RawCtxSelectedParentEntry RawCtxSelectedParentTable
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

noncomputable def chainView {Context Plaintext Auxiliary : Type}
    (prior : Prior) (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp)) :
    QueryImpl (ReceiveSpec RatchetChain RatchetChain RatchetMaterial Context Plaintext)
      (StateT Auxiliary ProbComp)
  | .inl chain => pure (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
      (prior (RawCtxSelectedPendingCut.requestAddress chain))))
  | .inr pending => other pending

/-- Erasing only the enriched pending-query payload retains the exact original chain program and full stateful opening effects. -/
theorem view_program {Context Plaintext Auxiliary : Type}
    (prior : Prior) (other : QueryImpl (OpenSpec Context Plaintext) (StateT Auxiliary ProbComp))
    (effect : Effect RatchetChain RatchetChain RatchetMaterial Context) :
    simulateQ (viewHandler prior other) (RawCtxPendingReceiveQueries.program effect) =
      simulateQ (chainView prior other) (RawCtxChainReceive.program effect) := by
  have same : viewHandler prior other = chainView prior other ∘ₛ RawCtxPendingReceiveQueries.forward := by
    funext query state
    cases query <;> rfl
  rw [same, RawCtxPendingReceiveQueries.program_interpreted]

noncomputable def sourceOpening {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) :
    QueryImpl (OpenSpec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp) :=
  fun pending => RawCtxSourceChainHandles.receiveNative source writer (.inr (toNative pending))

/-- The retained cache lookup and actual source opening run the unchanged native typed receive driver with its complete shared primitive state. -/
theorem view_native {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput)
    (effect : Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    simulateQ (viewHandler (lookup prior entry target) (sourceOpening (Auxiliary := Auxiliary) source writer))
      (RawCtxPendingReceiveQueries.program effect) =
      simulateQ (RawCtxSelectedParentSource.nativeReceive source writer prior entry target)
        (RawCtxInterpretedReceive.program (nativeEffect id id effect)) := by
  rw [view_program]
  have actual := RawCtxChainReceive.program_native id id
    (chainView (lookup prior entry target) (sourceOpening (Auxiliary := Auxiliary) source writer))
    (RawCtxSelectedParentSource.nativeReceive source writer prior entry target)
    (fun request => by rfl) (fun pending => by
      rcases pending with ⟨kernel, context, prepared⟩
      cases prepared <;> rfl) effect
  have mapped : (fun result : RefinedRatchet RatchetChain RatchetChain RatchetMaterial ×
      core.option.Option RawCtxWholeOwner.Decrypted => (mapChains id id result.1, result.2)) = id := by
    funext result
    rcases result with ⟨kernel, opened⟩
    cases kernel
    rfl
  simpa only [mapped, Functor.map_id, id_eq] using actual.symm

/-- The actual continued memo cache after insertion realizes the original native receive with precisely that retained entry and the same shared primitive state. -/
theorem recorded_native {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (effect : Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) (cache : RawCtxKdfRequestTable.Table)
    (address : JointKdfAddress) (output : FullOutput) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) (sourceOpening source writer))
        (RawCtxPendingReceiveQueries.program effect)).run (state, cache.cacheQuery address output) =
      (simulateQ (RawCtxSelectedParentSource.nativeReceive source writer (view (productionStream source.crypto) cache)
        (fromOutput address output) (PqxdhOrderedChainHybrids.nextChain output))
        (RawCtxInterpretedReceive.program (nativeEffect id id effect))).run state := by
  rw [← retained_entry, view_native]

/-- The original pending resumption with its exact sampled response is the retained-entry label cut, before all remaining native skip and opening work. -/
theorem recorded_cut {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) (cache : RawCtxKdfRequestTable.Table)
    (output : FullOutput) :
    (fun result => (result.1, result.2.1)) <$>
      (simulateQ (handler (RawCtxKdfRequestTable.memoImpl source) (sourceOpening source writer))
        (RawCtxPendingReceiveQueries.program (normalResume pending
          (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))))).run
            (state, cache.cacheQuery (RawCtxSelectedPendingCut.requestAddress pending.request) output) =
      ((fun result => (mapChains (RawCtxSelectedChain.interpret
          (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output)))
        (RawCtxSelectedChain.interpret (RawCtxFreshChainCut.concreteChain
          (PqxdhOrderedChainHybrids.nextChain output))) result.1, result.2)) <$>
        simulateQ (RawCtxSelectedParentSource.labelReceive source writer (view (productionStream source.crypto) cache)
          (fromOutput (RawCtxSelectedPendingCut.requestAddress pending.request) output)
          (RawCtxSelectedParentSource.response (view (productionStream source.crypto) cache)
            (fromOutput (RawCtxSelectedPendingCut.requestAddress pending.request) output)
            (PqxdhOrderedChainHybrids.nextChain output)
            (RawCtxChainSend.nativeRequest (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output)))))
          (RawCtxChainReceive.program (RawCtxSelectedPendingCut.receiveStop pending
            (PqxdhOrderedChainHybrids.material output)))).run state := by
  rw [recorded_native, ← normalResume_native]
  exact congrArg (fun program => program.run state)
    (RawCtxSelectedPendingCut.receive_cut source writer (view (productionStream source.crypto) cache) pending output)

/-- Every supported original receive stop at a reached miss consumes its actual pending state and retained prior cache in the concrete native continuation, with the real opening interpreter. -/
theorem reached_native {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (before : QueryImpl (Spec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary × RawCtxKdfRequestTable.Table) ProbComp))
    (effect : Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) (index : Nat)
    (initial state : RawCtxSharedPrimitive.SharedState Auxiliary × RawCtxKdfRequestTable.Table)
    (pending : Kdf RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (next : RatchetChain × RatchetMaterial → OracleComp
      (Spec RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted)
      (RefinedRatchet RatchetChain RatchetChain RatchetMaterial × core.option.Option RawCtxWholeOwner.Decrypted))
    (supported : (.pending pending next, state) ∈ support
      (RawCtxPendingReceivePrefix.scan before (RawCtxPendingReceiveQueries.program effect) index initial))
    (sample : JointKdfAddress → ProbComp FullOutput)
    (miss : state.2 (RawCtxSelectedPendingCut.requestAddress pending.request) = none) :
    (fun result => (result.1, result.2.1)) <$>
      atStop source (sourceOpening source writer) sample (.pending pending next, state) =
      (do let output ← sample (RawCtxSelectedPendingCut.requestAddress pending.request)
          (simulateQ (RawCtxSelectedParentSource.nativeReceive source writer
            (view (productionStream source.crypto) state.2)
            (fromOutput (RawCtxSelectedPendingCut.requestAddress pending.request) output)
            (PqxdhOrderedChainHybrids.nextChain output))
            (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalResume (nativeKdf id id pending)
              (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse output))))).run state.1) := by
  rw [reached_miss source (sourceOpening source writer) before effect index initial state pending next supported sample miss,
    map_bind]
  apply bind_congr
  intro output
  rw [recorded_native, ← normalResume_native]
  rfl

end BeaconcryptCore.Computational.RawCtxReachedParentSource

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentSource.view_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentSource.view_program

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentSource.view_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentSource.view_native

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentSource.recorded_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentSource.recorded_native

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentSource.recorded_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentSource.recorded_cut

/-- info: 'BeaconcryptCore.Computational.RawCtxReachedParentSource.reached_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxReachedParentSource.reached_native

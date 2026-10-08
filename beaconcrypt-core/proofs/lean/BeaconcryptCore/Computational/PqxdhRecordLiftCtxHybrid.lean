-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxNoRefusal

/-!
# Record-lift CTX hybrid: source equality and the key-indexed hybrid family (items 4 and 5, stage S4, X1)

**Source equality.** The all-real CTX world `PqxdhRecordLiftIdeal.ctxRun (fun _ => .real) id` is exactly the chain-ideal world `PqxdhRecordLiftIdeal.idealChains` once the per-coordinate CTX states and the native and uniform analysis counters are erased (`allReal_bare`): the complete client result (adversary output, ledger, environment state and record control) and the counter-erased private state of `PqxdhRecordLiftCtxProtocol.Bare` (shared BLAKE2b cache, effect ledger, seeds, full chain table, tagged produced frames, pending writer log) have the same law. Hence the permitted view (`allReal_view`) and every cache-free decision on it (`allReal_decision`) have the same law in both worlds. Per service: a hidden opening of the CTX world (one keyed raw request with the universal envelope, answered by the real one-key CTX state with the key and nonce of the coordinate's table entry) is the chain world's native opening, including a malformed payload, missing material and the API reply (`opening_bare`, through `real_open_cache`); a hidden seal with a nonce that its coordinate has not attempted is the native seal, including writer failure, the logged frame and invalid associated-data width (`sealing_bare`, through `real_seal_cache`); every other service is the chain world's own service (`base_bare`). The per-coordinate nonce stop of the real CTX states never fires: a coordinate outside the attempted-seal history has attempted no nonce (`Unsealed`, preserved by `step_unsealed`), and every hidden coordinate is sealed at most once on every reply path of the frozen program (`PqxdhRecordLiftProtocolHistory.program_fresh`); every hidden opening carries the source parser's admission facts (`PqxdhRecordLiftCtxProtocol.program_admitted`). The induction over the whole adaptive program is `schedule_bare`.

**Hybrid family.** `hybridModes positions cut` puts the bounded coordinates of `PqxdhRecordLiftChainOrder` index below `cut` in replay mode and every other coordinate in real mode; `hybrid` is the CTX world under it. The first hybrid is the all-real world (`hybridModes_zero`) with the view law of `idealChains` (`hybrid_zero_view`); after all `positions * (n * 2)` steps exactly the bounded coordinates are in replay mode (`hybridModes_last`); one step changes the mode of its own coordinate only, from real to replay (`hybridModes_unchanged`, `hybridModes_step`).

**Scope.** Later S4 stages supply the reduction of one hybrid step to `PqxdhRecordLiftCtxModes.sourceGame` (the selected coordinate's key at the challenger, every other coordinate as a known real or replay call), the lazy/eager law of the selected coordinate's key, the support invariant that identifies the last hybrid with `PqxdhRecordLiftIdeal.idealAuth` (every keyed request is at a coordinate that is present in the table and below the depth cap `Budget.sends + 51 * Budget.receives`), the per-key hops, the bills and the correspondence of `PqxdhRecordLiftIdeal.randomImpl` with the IND$ random experiment. No assumption or contract is used, and every theorem carries an exact `#print axioms` guard allowing only `propext`, `Classical.choice` and `Quot.sound`. New Claude work; nothing adapted from Codex WIP. Guide: `doc/impl/record-lift-ctx-hybrid.md`.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-- The counter-erased source view of a CTX-world private state: the chain world's bare state of its base. The per-coordinate CTX states are dropped. -/
def ctxBare (state : CtxPrivate n) : PqxdhRecordLiftCtxProtocol.Bare n :=
  PqxdhRecordLiftCtxProtocol.erasePrivate state.base

/-- A keyed request changes only the shared cache of the bare view (and the coordinate's own CTX state, which the bare view drops); its reply is the coordinate's one-key CTX reply. -/
theorem keyed_bare (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n) :
    Prod.map id ctxBare <$> (keyed modes decode crypto query).run state =
      (fun result => (result.1.1, { ctxBare state with cache := result.2 })) <$>
        (simulateQ AdaptiveCtxSharedHash.hashImpl
          ((keyImpl decode crypto (materialAt state.base.chain query.1).1 (modes query.1) query.2).run
            (state.keys query.1))).run state.base.primitive.2 := by
  have erased := congrArg (fun work => (fun result => (result.1.1.1,
      { result.2 with cache := result.1.2 })) <$> work)
    (PqxdhRecordLiftCtxProtocol.sampled_bare ((simulateQ AdaptiveCtxSharedHash.hashImpl
      ((keyImpl decode crypto (materialAt state.base.chain query.1).1 (modes query.1) query.2).run
        (state.keys query.1))).run state.base.primitive.2) state.base)
  simp only [Functor.map_map, Prod.map_def, id_eq] at erased
  simp only [keyed, StateT.run, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
  exact erased

/-- Exact selected arguments retain the original opening context and prepared sequence, for every material type. -/
theorem openArguments_facts {Material Context : Type}
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Material Context)
    (input : RawCtxInterpretedArguments.Input Material Context)
    (present : RawCtxInterpretedArguments.openArguments pending = some input) :
    RawCtxInterpretedOpening.sequence pending = .ok input.sequence ∧ input.context = pending.context := by
  unfold RawCtxInterpretedArguments.openArguments at present
  split at present
  · cases present
  · cases Option.some.inj present
    exact ⟨(RawCtxInterpretedArguments.sequence_total pending).choose_spec, rfl⟩

/-- The real one-key raw opening of a hidden coordinate, with its shared cache only, is the literal native shared-ROM opening of the coordinate's material. -/
theorem real_open_cache (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (crypto : Pqxdh.Crypto)
    (key : PqxdhSecretInputKdf.RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput) (sequence : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (entry : KeyEntry) (cache : CtxRO.QueryCache)
    (width : context.associatedData.length = 153)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame expected context.associatedData context.frame)
    (sequenceMatches : sequence = context.frame.sequence) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices) :
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ AdaptiveCtxSharedHash.hashImpl
        ((AdaptiveCtxSharedModes.localImpl true (RawCtxUniversalDecoder.decoder read) crypto key
          (.inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width)))).run entry)).run cache =
      (simulateQ ctxRandomOracle (simulateQ (RawCtxSourceOpen.romAdapter crypto)
        (RawCtxSourceOpen.openInput ⟨RawCtxFreshChainCut.concreteMaterial (key, nonce), sequence, context⟩))).run cache := by
  have exactCall := RawCtxSelectedOpenConsumer.call_cache 0 read expected key ⟨.hidden nonce, sequence, context⟩ crypto
    ⟨entry, fun _ => entry, cache⟩ nonempty decoded valid sequenceMatches slices parsed
  simp only [RawCtxUniversalOpening.call, dite_eq_left width, simulateQ_spec_query] at exactCall
  change (fun result => (result.1, result.2.cache)) <$> (do
    let result ← (simulateQ AdaptiveCtxSharedHash.hashImpl
      ((AdaptiveCtxSharedModes.localImpl true (RawCtxUniversalDecoder.decoder read) crypto key
        (.inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width)))).run entry)).run cache
    pure (result.1.1, { (⟨entry, fun _ => entry, cache⟩ : AdaptiveCtxDynamicKnownKeys.SourceState) with
      selected := result.1.2, cache := result.2 })) = _ at exactCall
  simpa only [map_bind, map_pure, bind_pure_comp, Functor.map_map, RawCtxInterpretedArguments.toOpenInput,
    RawCtxInterpretedArguments.mapInput, RawCtxSelectedMessageKey.interpret] using exactCall

/-- A hidden opening in the all-real CTX world is the bare chain world's native opening: the same optional reply, shared cache and pending writer log, for every admitted opening (malformed payloads and missing material included). -/
theorem opening_bare (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (admitted : PqxdhRecordLiftCtxOracle.Admitted codec.frameRead (.inr (.inl pending))) :
    Prod.map id ctxBare <$> (ctxInterpreter (fun _ => .real) replace setup codec (.opening pending)).run state =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec (fun _ => true) (.opening pending)).run
        (ctxBare state) := by
  obtain ⟨nonempty, decoded, valid, prepared⟩ := admitted
  change Prod.map id ctxBare <$> (simulateQ (keyed (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto) (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain pending)).run
      state = (do
    let result ← (PqxdhRecordLiftNativeAdapters.receiveOpen (PqxdhRecordLiftLoggedAdapters.receiveNative
      (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
      (PqxdhRecordLiftMaterialTable.eraseOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain
        pending)).run (state.base.primitive.2, state.base.pending)
    pure (result.1, { ctxBare state with cache := result.2.1, pending := result.2.2 }))
  rw [PqxdhRecordLiftCtxServices.receiveOpen_logged, PqxdhRecordLiftCtxServices.receiveOpen_native]
  cases parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload with
  | none =>
      rw [hiddenOpening_malformed _ _ _ parsed, PqxdhRecordLiftCtxServices.native_opening_malformed _ _ _ parsed]
      simp only [simulateQ_pure, StateT.run_pure, map_pure, pure_bind, Prod.map_def, id_eq]
      rfl
  | some slices =>
      rw [RawCtxSelectedOpenConsumer.native_service, RawCtxInterpretedArguments.openArguments_native,
        PqxdhRecordLiftMaterialTable.eraseOpening, RawCtxInterpretedArguments.openArguments_map]
      unfold hiddenOpening
      simp only [parsed]
      cases found : RawCtxInterpretedArguments.openArguments (RawCtxChainInterpretation.mapOpeningChains
          (PqxdhRecordLiftChainTable.chain (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain)
          (PqxdhRecordLiftChainTable.chain (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain)
          pending) with
      | none =>
          simp only [Option.map_none, simulateQ_pure, StateT.run_pure, map_pure, pure_bind, Prod.map_def, id_eq]
          rfl
      | some input =>
          obtain ⟨sequenceFact, contextFact⟩ := openArguments_facts _ input found
          have width : input.context.associatedData.length = 153 := contextFact ▸ valid.2.2
          simp only [Option.map_some, dite_eq_left width, simulateQ_map, simulateQ_spec_query, StateT.run_map,
            Functor.map_map]
          have sameContext : input.context = pending.context := contextFact
          have sequenceMatches : input.sequence = input.context.frame.sequence := by
            rw [RawCtxChainInterpretation.opening_sequence_chains, prepared] at sequenceFact
            rw [sameContext]
            exact (RustM.ok.inj sequenceFact).symm
          have romEq := real_open_cache codec.frameRead pending.context.frame.sender setup.source.crypto
            (materialAt state.base.chain input.material).1 (materialAt state.base.chain input.material).2
            input.sequence input.context (state.keys input.material) state.base.primitive.2 width
            (sameContext ▸ nonempty) (sameContext ▸ decoded) (sameContext ▸ valid) sequenceMatches slices
            (sameContext ▸ parsed)
          have lhs : (fun a => Prod.map id ctxBare
                (RawCtxSharedOpeningConsumer.apiReply input.sequence input.context a.1, a.2)) <$>
              (keyed (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
                (input.material, .inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
                  (materialAt state.base.chain input.material).2 input.context width)))).run state =
              (fun result => (RawCtxSharedOpeningConsumer.apiReply input.sequence input.context result.1,
                { ctxBare state with cache := result.2 })) <$>
              ((fun result => (result.1.1, result.2)) <$> (simulateQ AdaptiveCtxSharedHash.hashImpl
                ((AdaptiveCtxSharedModes.localImpl true (RawCtxUniversalDecoder.decoder codec.frameRead)
                  setup.source.crypto (materialAt state.base.chain input.material).1
                  (.inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
                    (materialAt state.base.chain input.material).2 input.context width)))).run
                  (state.keys input.material))).run state.base.primitive.2) := by
            have keyedEq := keyed_bare (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead)
              setup.source.crypto (input.material, .inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
                (materialAt state.base.chain input.material).2 input.context width))) state
            calc _ = (fun a => (RawCtxSharedOpeningConsumer.apiReply input.sequence input.context a.1, a.2)) <$>
                  (Prod.map id ctxBare <$> (keyed (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead)
                    setup.source.crypto (input.material, .inr (RawCtxUniversalDecoder.pack
                      (RawCtxUniversalDecoder.envelope (materialAt state.base.chain input.material).2 input.context
                        width)))).run state) := by
                  rw [Functor.map_map]; rfl
              _ = _ := by
                  rw [keyedEq, Functor.map_map, Functor.map_map]; rfl
          refine Eq.trans lhs ?_
          rw [romEq]
          simp only [bind_pure_comp, Functor.map_map]
          rfl

/-- `StateT.run_map` for a state transformer applied directly to its state. -/
theorem stateT_map_apply {σ α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (f : α → β)
    (x : StateT σ m α) (s : σ) : (f <$> x) s = (fun p => (f p.1, p.2)) <$> x s :=
  StateT.run_map f x s

/-- `StateT.run_bind` for a state transformer applied directly to its state. -/
theorem stateT_bind_apply {σ α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (x : StateT σ m α) (f : α → StateT σ m β) (s : σ) : (x >>= f) s = x s >>= fun p => f p.1 p.2 :=
  StateT.run_bind x f s

/-- A real one-key seal with a fresh nonce returns exactly the literal shared-ROM seal of its key and input. -/
theorem real_seal_cache (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey) (input : CtxSealInput)
    (entry : KeyEntry) (cache : CtxRO.QueryCache) (fresh : input.nonce ∉ entry.1.usedNonces) :
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ AdaptiveCtxSharedHash.hashImpl
        ((AdaptiveCtxSharedModes.localImpl true decode crypto key (.inl (.inr (.inr input)))).run entry)).run cache =
      (fun result => (some result.1, result.2)) <$> (simulateQ ctxRandomOracle (ctxSeal crypto key input)).run cache := by
  simp only [AdaptiveCtxSharedModes.localImpl, ite_true, AdaptiveCtxSharedHash.localImpl,
    AdaptiveCtxSharedHash.localSeal, fresh, ite_false, StateT.run, bind_pure_comp]
  simp only [ctxSeal, simulateQ_map, simulateQ_spec_query, Functor.map_map, bind_pure_comp,
    AdaptiveCtxSharedHash.hashImpl, QueryImpl.add_apply_inr]
  rw [stateT_map_apply, stateT_map_apply]
  simp only [Functor.map_map]
  rfl

/-- The literal native sealing callback of a labeled seal reads the coordinate's table material and the original sequence and context. -/
theorem eraseSeal_arguments (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (pending : PqxdhRecordLiftProtocol.Sealing n) :
    RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal
      (PqxdhRecordLiftMaterialTable.eraseSeal seeds table pending)) =
      ⟨PqxdhRecordLiftMaterialTable.material table pending.material, pending.sequence, pending.context⟩ := by
  simp only [RawCtxSourceSend.arguments, RawCtxInterpretedSend.nativeSeal, PqxdhRecordLiftMaterialTable.eraseSeal,
    RawCtxInterpretedSend.mapSeal, RawCtxChainSend.nativeSeal]

/-- The pure continuation of a hidden seal after its keyed reply: a refused seal returns none and logs nothing; a record is logged before the writer result. -/
def sealedReply (writer : RawCtxMixedShared.Writer) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) :
    Option CtxRomRecord → Option RawCtxSourceSend.Encrypted × PqxdhRecordLiftLoggedAdapters.Frames
  | none => (none, frames)
  | some record =>
      let frame : RawCtxReceive.DecodedFrame := ⟨pending.sequence, pending.context.senderId, record.encode⟩
      ((writer frame).map fun ciphertext => ⟨ciphertext, pending.context.targetId, pending.sequence⟩, frames ++ [frame])

/-- A hidden seal in the all-real CTX world with a fresh coordinate nonce is the bare chain world's native seal: the same optional reply, shared cache, logged frame (also on writer failure) and invalid-width rejection. -/
theorem sealing_bare (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (fresh : pending.context.associatedData.length = 153 →
      (materialAt state.base.chain pending.material).2 ∉ (state.keys pending.material).1.usedNonces) :
    Prod.map id ctxBare <$> (ctxInterpreter (fun _ => .real) id setup codec (.sealing pending)).run state =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec (fun _ => true) (.sealing pending)).run
        (ctxBare state) := by
  change Prod.map id ctxBare <$> (do
      let result ← (simulateQ (keyed (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto) ((hiddenSealing codec.frameWrite state.base.chain id pending).run state.base.pending)).run
          state
      pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } })) = (do
    let result ← (PqxdhRecordLiftNativeAdapters.sendSeal (PqxdhRecordLiftLoggedAdapters.sendNative
      (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
      (PqxdhRecordLiftMaterialTable.eraseSeal (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain
        pending)).run (state.base.primitive.2, state.base.pending)
    pure (result.1, { ctxBare state with cache := result.2.1, pending := result.2.2 }))
  rw [PqxdhRecordLiftCtxServices.sendSeal_inner, eraseSeal_arguments]
  by_cases width : pending.context.associatedData.length = 153
  · have keyEq : RawCtxCanonicalSeal.sourceKey
        ⟨PqxdhRecordLiftMaterialTable.material state.base.chain pending.material, pending.sequence, pending.context⟩ =
        (materialAt state.base.chain pending.material).1 :=
      (RawCtxSelectedMessageSealing.selected_input (materialAt state.base.chain pending.material).1
        (materialAt state.base.chain pending.material).2 pending.sequence pending.context width).1
    have inputEq : RawCtxCanonicalSeal.sourceInput
        ⟨PqxdhRecordLiftMaterialTable.material state.base.chain pending.material, pending.sequence, pending.context⟩
          width =
        RawCtxSelectedMessageSealing.selectedInput (materialAt state.base.chain pending.material).2 pending.sequence
          pending.context width :=
      (RawCtxSelectedMessageSealing.selected_input (materialAt state.base.chain pending.material).1
        (materialAt state.base.chain pending.material).2 pending.sequence pending.context width).2
    rw [PqxdhRecordLiftCtxServices.nativeSeal_typed _ _ _ width, keyEq, inputEq]
    have sealedEq := real_seal_cache (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (materialAt state.base.chain pending.material).1
      (RawCtxSelectedMessageSealing.selectedInput (materialAt state.base.chain pending.material).2 pending.sequence
        pending.context width) (state.keys pending.material) state.base.primitive.2 (fresh width)
    have keyedEq := keyed_bare (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (pending.material, .inl (.inr (.inr (RawCtxSelectedMessageSealing.selectedInput
        (materialAt state.base.chain pending.material).2 pending.sequence pending.context width)))) state
    have hidden : (hiddenSealing codec.frameWrite state.base.chain id pending).run state.base.pending =
        sealedReply codec.frameWrite pending state.base.pending <$>
          ((KeyedSpec n).query (pending.material, .inl (.inr (.inr (RawCtxSelectedMessageSealing.selectedInput
            (materialAt state.base.chain pending.material).2 pending.sequence pending.context width)))) :
            OracleComp (KeyedSpec n) (Option CtxRomRecord)) := by
      have width' : (replaceContext id pending.context).associatedData.length = 153 := width
      change (if width'' : (replaceContext id pending.context).associatedData.length = 153 then _ else _) = _
      rw [dite_eq_left_of_eq_true (eq_true width'), map_eq_bind_pure_comp]
      congr 1
      funext reply
      cases reply <;> rfl
    rw [hidden, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    calc _ = (fun result => ((sealedReply codec.frameWrite pending state.base.pending result.1).1,
          { result.2 with pending := (sealedReply codec.frameWrite pending state.base.pending result.1).2 })) <$>
          (Prod.map id ctxBare <$> (keyed (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead)
            setup.source.crypto (pending.material, .inl (.inr (.inr (RawCtxSelectedMessageSealing.selectedInput
              (materialAt state.base.chain pending.material).2 pending.sequence pending.context width))))).run
                state) := by
          simp only [bind_pure_comp, Functor.map_map]
          rfl
      _ = _ := by
          rw [keyedEq, Functor.map_map]
          have mapped := congrArg (fun work => (fun result : Option CtxRomRecord × CtxRO.QueryCache =>
              ((sealedReply codec.frameWrite pending state.base.pending result.1).1,
                { ({ ctxBare state with cache := result.2 } : PqxdhRecordLiftCtxProtocol.Bare n) with
                  pending := (sealedReply codec.frameWrite pending state.base.pending result.1).2 })) <$> work)
              sealedEq
          simp only [Functor.map_map] at mapped
          refine Eq.trans mapped ?_
          simp only [bind_pure_comp, Functor.map_map]
          rfl
  · rw [PqxdhRecordLiftCtxServices.nativeSeal_invalid _ _ _ width]
    have narrow := hiddenSealing_narrow codec.frameWrite state.base.chain id pending state.base.pending width
    simp only [narrow, simulateQ_pure, StateT.run_pure, map_pure, bind_pure_comp, Prod.map_def, id_eq]
    rfl

/-- Every service other than a hidden opening or sealing is the bare chain world's service, in every mode family. -/
theorem base_bare (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n)
    (notOpening : ∀ pending, query ≠ .opening pending) (notSealing : ∀ pending, query ≠ .sealing pending)
    (state : CtxPrivate n) :
    Prod.map id ctxBare <$> (ctxInterpreter modes replace setup codec query).run state =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec (fun _ => true) query).run (ctxBare state) := by
  rw [ctxInterpreter_base modes replace setup codec query notOpening notSealing state, Functor.map_map]
  exact PqxdhRecordLiftCtxProtocol.bare_query setup codec (fun _ => true) query state.base

/-- A keyed request changes the CTX state of its own coordinate only. -/
theorem keyed_other (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n)
    (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((keyed modes decode crypto query).run state))
    (label : Label n) (different : label ≠ query.1) : result.2.keys label = state.keys label := by
  simp only [keyed, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact Function.update_of_ne different _ _

/-- A supported shared-cache execution returns a supported result of the cache-free program. -/
theorem hash_support {α : Type} (work : OracleComp AdaptiveCtxSharedHash.HashSpec α) (cache : CtxRO.QueryCache)
    (result : α × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl work).run cache)) :
    result.1 ∈ support work := by
  apply support_simulateQ_run'_subset AdaptiveCtxSharedHash.hashImpl work cache
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- A real-mode non-seal one-key request keeps the coordinate's attempted-nonce history. -/
theorem real_nonseal_nonces (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (query : ReceiveSpec.Domain) (notSeal : ¬AdaptiveCtxQueryBounds.SourceSeal query) (entry : KeyEntry)
    (cache : CtxRO.QueryCache) (result : (ReceiveSpec.Range query × KeyEntry) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl
      ((AdaptiveCtxSharedModes.localImpl true decode crypto key query).run entry)).run cache)) :
    result.1.2.1.usedNonces = entry.1.usedNonces := by
  have reached := hash_support _ cache result supported
  rcases query with (coin | (hash | input)) | raw
  · simp only [AdaptiveCtxSharedModes.localImpl, ite_true, AdaptiveCtxSharedHash.localImpl, StateT.run,
      bind_pure_comp, support_map, Set.mem_image] at reached
    obtain ⟨_, ⟨_, _, rfl⟩, equal⟩ := reached
    rw [← equal]
  · simp only [AdaptiveCtxSharedModes.localImpl, ite_true, AdaptiveCtxSharedHash.localImpl, StateT.run,
      bind_pure_comp, support_map, Set.mem_image] at reached
    obtain ⟨_, ⟨_, _, rfl⟩, equal⟩ := reached
    rw [← equal]
  · exact absurd trivial notSeal
  · simp only [AdaptiveCtxSharedModes.localImpl, ite_true, AdaptiveCtxSharedHash.localImpl, StateT.run,
      bind_pure_comp, support_map, Set.mem_image] at reached
    obtain ⟨inner, member, equal⟩ := reached
    rw [← equal]
    unfold AdaptiveCtxSharedHash.localRaw at member
    split at member
    · simp only [support_pure, Set.mem_singleton_iff] at member
      rw [member]
    · simp only [bind_pure_comp, support_map, Set.mem_image] at member
      obtain ⟨_, _, equal⟩ := member
      rw [← equal]

/-- The coordinate's CTX state after a supported keyed request is the state of a supported one-key execution. -/
theorem keyed_self (modes : Label n → KeyMode) (decode : RawDecoder) (crypto : Pqxdh.Crypto)
    (query : (KeyedSpec n).Domain) (state : CtxPrivate n)
    (result : (KeyedSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((keyed modes decode crypto query).run state)) :
    ∃ inner ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl
      ((keyImpl decode crypto (materialAt state.base.chain query.1).1 (modes query.1) query.2).run
        (state.keys query.1))).run state.base.primitive.2),
      result.2.keys query.1 = inner.1.2 := by
  simp only [keyed, StateT.run, bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨sampledResult, member, rfl⟩ := supported
  refine ⟨sampledResult.1, ?_, Function.update_self _ _ _⟩
  simp only [PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp, support_map, Set.mem_image] at member
  obtain ⟨counted, member, rfl⟩ := member
  apply support_simulateQ_run'_subset PqxdhRecordLiftWorld.countCoin _ state.base.primitive.1.uniform
  rw [StateT.run'_eq, support_map]
  exact ⟨counted, member, rfl⟩

/-- A supported all-real hidden opening keeps every coordinate's attempted-nonce history. -/
theorem opening_nonces (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (pending : PqxdhRecordLiftProtocol.Opening n) (state : CtxPrivate n)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter (fun _ => .real) replace setup codec (.opening pending)).run state))
    (label : Label n) : (result.2.keys label).1.usedNonces = (state.keys label).1.usedNonces := by
  change result ∈ support ((simulateQ (keyed (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto) (hiddenOpening (PqxdhRecordLiftProtocol.cachedSeeds state.base) state.base.chain
      pending)).run state) at supported
  unfold hiddenOpening at supported
  split at supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
  · split at supported
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
    · rename_i input _
      split at supported
      · rename_i width
        simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map, Set.mem_image] at supported
        obtain ⟨keyedResult, member, rfl⟩ := supported
        change (keyedResult.2.keys label).1.usedNonces = _
        by_cases same : label = input.material
        · subst label
          obtain ⟨inner, innerMember, equal⟩ := keyed_self (fun _ => .real)
            (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
            (input.material, .inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
              (materialAt state.base.chain input.material).2 input.context width))) state keyedResult member
          rw [equal]
          exact real_nonseal_nonces _ _ _ (.inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
            (materialAt state.base.chain input.material).2 input.context width))) (fun hit => hit) _ _ inner innerMember
        · rw [keyed_other (fun _ => .real) (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
            (input.material, .inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope
              (materialAt state.base.chain input.material).2 input.context width))) state keyedResult member label
              same]
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        rw [supported]

/-- A supported hidden sealing in any mode changes no other coordinate's CTX state. -/
theorem sealing_other (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (state : CtxPrivate n)
    (result : Option RawCtxSourceSend.Encrypted × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec (.sealing pending)).run state))
    (label : Label n) (different : label ≠ pending.material) : result.2.keys label = state.keys label := by
  change result ∈ support (do
    let inner ← (simulateQ (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
      ((hiddenSealing codec.frameWrite state.base.chain replace pending).run state.base.pending)).run state
    pure (inner.1.1, { inner.2 with base := { inner.2.base with pending := inner.1.2 } })) at supported
  simp only [bind_pure_comp, support_map, Set.mem_image] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  change inner.2.keys label = state.keys label
  unfold hiddenSealing at member
  simp only [StateT.run] at member
  split at member
  · rename_i width
    simp only [simulateQ_bind, simulateQ_spec_query, stateT_bind_apply, mem_support_bind_iff] at member
    obtain ⟨keyedResult, keyedMember, rest⟩ := member
    have keysEq := keyed_other modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (pending.material, .inl (.inr (.inr (RawCtxSelectedMessageSealing.selectedInput
        (materialAt state.base.chain pending.material).2 pending.sequence (replaceContext replace pending.context)
          width)))) state keyedResult keyedMember label different
    split at rest <;>
    · simp only [simulateQ_pure] at rest
      rw [rest, keysEq]
  · simp only [simulateQ_pure] at member
    rw [member]

/-- Coordinates outside the attempted-seal history have never attempted a nonce in their CTX state. -/
def Unsealed (state : CtxPrivate n) (past : List (Label n)) : Prop :=
  ∀ label, label ∉ past → (state.keys label).1.usedNonces = []

/-- One admitted, fresh service of the all-real CTX world is the bare chain world's service. -/
theorem step_bare (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) (past : List (Label n)) (unsealed : Unsealed state past)
    (fresh : PqxdhRecordLiftProtocolHistory.Fresh (past, query))
    (admitted : PqxdhRecordLiftCtxProtocol.Admitted codec.frameRead query) :
    Prod.map id ctxBare <$> (ctxInterpreter (fun _ => .real) id setup codec query).run state =
      (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec (fun _ => true) query).run (ctxBare state) := by
  cases query with
  | opening pending => exact opening_bare setup codec id pending state admitted
  | sealing pending =>
      refine sealing_bare setup codec pending state (fun _ => ?_)
      rw [unsealed pending.material fresh]
      exact List.not_mem_nil
  | allocate _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | coin _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | hash _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | charge _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | lookup _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | knownSend _ _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | knownReceive _ _ _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state
  | publish _ => exact base_bare _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state

/-- Every service other than a hidden opening or sealing leaves every coordinate's CTX state unchanged. -/
theorem base_keys (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : PqxdhRecordLiftProtocol.Service n)
    (notOpening : ∀ pending, query ≠ .opening pending) (notSealing : ∀ pending, query ≠ .sealing pending)
    (state : CtxPrivate n) (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter modes replace setup codec query).run state)) :
    result.2.keys = state.keys := by
  rw [ctxInterpreter_base modes replace setup codec query notOpening notSealing state, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

/-- Every supported all-real service extends the unsealed invariant by exactly its own sealing coordinate. -/
theorem step_unsealed (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (query : PqxdhRecordLiftProtocol.Service n)
    (state : CtxPrivate n) (past : List (Label n)) (unsealed : Unsealed state past)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × CtxPrivate n)
    (supported : result ∈ support ((ctxInterpreter (fun _ => .real) id setup codec query).run state)) :
    Unsealed result.2 (past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query) := by
  intro label outside
  cases query with
  | opening pending =>
      rw [opening_nonces setup codec id pending state result supported label]
      exact unsealed label (by simpa [PqxdhRecordLiftWorldProvenance.sealingCoordinates] using outside)
  | sealing pending =>
      have parts : label ∉ past ∧ label ≠ pending.material := by
        simpa [PqxdhRecordLiftWorldProvenance.sealingCoordinates, not_or] using outside
      rw [sealing_other _ id setup codec pending state result supported label parts.2]
      exact unsealed label parts.1
  | allocate _ | coin _ | hash _ | charge _ | lookup _ | knownSend _ _ | knownReceive _ _ _ | publish _ =>
      rw [base_keys _ _ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) state result supported]
      exact unsealed label (by simpa [PqxdhRecordLiftWorldProvenance.sealingCoordinates] using outside)

/-- Every complete fresh, admitted adaptive source continuation of the all-real CTX world erases to the bare chain world's continuation, retaining the complete result. -/
theorem schedule_bare {Result : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (state : CtxPrivate n) (past : List (Label n)) (unsealed : Unsealed state past)
    (fresh : (PqxdhRecordLiftProtocolHistory.annotated client past).AllQueriesSatisfy
      PqxdhRecordLiftProtocolHistory.Fresh)
    (admitted : client.AllQueriesSatisfy (PqxdhRecordLiftCtxProtocol.Admitted codec.frameRead)) :
    Prod.map id ctxBare <$> (simulateQ (ctxInterpreter (fun _ => .real) id setup codec) client).run state =
      (simulateQ (PqxdhRecordLiftCtxProtocol.bareInterpreter setup codec (fun _ => true)) client).run
        (ctxBare state) := by
  induction client using OracleComp.inductionOn generalizing state past with
  | pure value => simp
  | query_bind query next ih =>
      rw [PqxdhRecordLiftProtocolHistory.annotated_query_bind, allQueriesSatisfy_query_bind_iff] at fresh
      rw [allQueriesSatisfy_query_bind_iff] at admitted
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← step_bare setup codec query state past unsealed fresh.1 admitted.1, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result member
      exact ih result.1 result.2 (past ++ PqxdhRecordLiftWorldProvenance.sealingCoordinates query)
        (step_unsealed setup codec query state past unsealed result member) (fresh.2 result.1) (admitted.2 result.1)

/-- The initial CTX states have attempted no nonce. -/
theorem initial_unsealed : Unsealed (CtxPrivate.initial : CtxPrivate n) [] := fun _ _ => rfl

/-- Source equality of X1: the all-real CTX world erases exactly to the chain-ideal world: the complete client result and the counter-erased private state (shared cache, effects, seeds, full table, tagged produced frames and pending log) have the same law. The nonce stop of the per-coordinate real CTX states never fires (each hidden coordinate is sealed at most once, `PqxdhRecordLiftProtocolHistory.program_fresh`), and every hidden opening is admitted by the source parser (`PqxdhRecordLiftCtxProtocol.program_admitted`). -/
theorem allReal_bare (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    Prod.map id ctxBare <$> ctxRun (fun _ => .real) id setup codec route env serverKid bounds mode adversary =
      Prod.map id PqxdhRecordLiftCtxProtocol.erasePrivate <$>
        idealChains setup codec route env serverKid bounds mode adversary := by
  rw [ctxRun, schedule_bare setup codec _ CtxPrivate.initial [] initial_unsealed
      (PqxdhRecordLiftProtocolHistory.program_fresh env setup.source.crypto codec route serverKid bounds mode adversary)
      (PqxdhRecordLiftCtxProtocol.program_admitted env setup.source.crypto codec route serverKid bounds mode adversary),
    idealChains, chains, PqxdhRecordLiftProtocol.run]
  exact (PqxdhRecordLiftCtxProtocol.bare_schedule setup codec (fun _ => true) _
    PqxdhRecordLiftProtocol.initialPrivate).symm

/-- The all-real CTX world and the chain-ideal world have the same law of the permitted view. -/
theorem allReal_view (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ctxView <$> ctxRun (fun _ => .real) id setup codec route env serverKid bounds mode adversary =
      chainView <$> idealChains setup codec route env serverKid bounds mode adversary := by
  have same := congrArg (fun work => (fun result => viewOf result.1 result.2.produced) <$> work)
    (allReal_bare setup codec route env serverKid bounds mode adversary)
  simp only [Functor.map_map] at same
  exact same

/-- The all-real CTX world and the chain-ideal world give the same law to every cache-free decision on the permitted view. -/
theorem allReal_decision (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (decision : View n E X → ProbComp Bool) :
    (ctxRun (fun _ => .real) id setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (ctxView result)) =
      (idealChains setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (chainView result)) := by
  rw [← bind_map_left ctxView, ← bind_map_left chainView, allReal_view]

/-! ### The key-indexed hybrid family -/

/-- The CTX mode family of the key-indexed hybrid with cut `cut`: replay mode on the bounded coordinates whose `PqxdhRecordLiftChainOrder` index is below `cut` (the same depth-major order as the chain hybrids), real mode on every other coordinate. -/
noncomputable def hybridModes (positions cut : Nat) (label : Label n) : KeyMode :=
  if PqxdhRecordLiftChainOrder.selected positions cut label then .replay else .real

/-- The key-indexed CTX hybrid with cut `cut`: the CTX world under `hybridModes`, without plaintext replacement. -/
noncomputable def hybrid (positions cut : Nat) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :=
  ctxRun (hybridModes positions cut) id setup codec route env serverKid bounds mode adversary

/-- The first hybrid is the all-real CTX world. -/
theorem hybridModes_zero (positions : Nat) : (hybridModes positions 0 : Label n → KeyMode) = fun _ => .real := by
  funext label
  simp only [hybridModes, PqxdhRecordLiftChainOrder.selected_zero, Bool.false_eq_true, ite_false]

/-- The first hybrid has the view law of the chain-ideal world. -/
theorem hybrid_zero_view (positions : Nat) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ctxView <$> hybrid positions 0 setup codec route env serverKid bounds mode adversary =
      chainView <$> idealChains setup codec route env serverKid bounds mode adversary := by
  rw [hybrid, hybridModes_zero]
  exact allReal_view setup codec route env serverKid bounds mode adversary

/-- After all `positions * (n * 2)` steps, exactly the bounded coordinates are in replay mode. -/
theorem hybridModes_last (positions : Nat) (label : Label n) :
    hybridModes positions (positions * (n * 2)) label = .replay ↔
      PqxdhRecordLiftChainOrder.Bounded positions label := by
  rw [← PqxdhRecordLiftChainOrder.selected_last (positions := positions) label, hybridModes]
  cases PqxdhRecordLiftChainOrder.selected positions (positions * (n * 2)) label <;> simp

/-- Advancing the hybrid by one step changes the mode of no coordinate other than the step's own coordinate. -/
theorem hybridModes_unchanged (positions : Nat) (step : Fin (positions * (n * 2))) (label : Label n)
    (different : label ≠ PqxdhRecordLiftChainOrder.entryAt step) :
    hybridModes positions (step.val + 1) label = hybridModes positions step.val label := by
  rw [hybridModes, hybridModes, PqxdhRecordLiftChainOrder.selected_unchanged step label different]

/-- The step's own coordinate is real before the step and in replay mode after it. -/
theorem hybridModes_step (positions : Nat) (step : Fin (positions * (n * 2))) :
    hybridModes positions step.val (PqxdhRecordLiftChainOrder.entryAt step) = .real ∧
      hybridModes positions (step.val + 1) (PqxdhRecordLiftChainOrder.entryAt step) = .replay := by
  obtain ⟨before, after⟩ := PqxdhRecordLiftChainOrder.selected_step step
  simp only [hybridModes, before, after, Bool.false_eq_true, ite_false, ite_true, and_self]

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.keyed_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.keyed_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.openArguments_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.openArguments_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.real_open_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.real_open_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.opening_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.opening_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.stateT_map_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.stateT_map_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.stateT_bind_apply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.stateT_bind_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.real_seal_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.real_seal_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.eraseSeal_arguments' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.eraseSeal_arguments

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.sealing_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.sealing_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.base_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.base_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.keyed_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.keyed_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hash_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hash_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.real_nonseal_nonces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.real_nonseal_nonces

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.keyed_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.keyed_self

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.opening_nonces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.opening_nonces

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.sealing_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.sealing_other

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.step_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.step_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.base_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.base_keys

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.step_unsealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.step_unsealed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.schedule_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.schedule_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.initial_unsealed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.initial_unsealed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.allReal_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.allReal_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.allReal_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.allReal_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.allReal_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.allReal_decision

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybrid_zero_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybrid_zero_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_last' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_last

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_unchanged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxHybrid.hybridModes_step

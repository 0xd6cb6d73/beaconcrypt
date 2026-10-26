-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.LazyOracleDiscard
import BeaconcryptCore.Computational.PqxdhRecordLiftSeed
import BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor
import BeaconcryptCore.Computational.RawCtxOwnerProvenance
import BeaconcryptCore.Computational.PqxdhServerAuthCtxMaterial

/-!
# Hidden-entry kernels and the local erasure of a discarded finish opening

The Beacon's hidden-entry finish runs the labelled finish-time receive of `PqxdhServerAuthBeaconFactor.factored` before its sequence-one gate. `reached` is the effect that receive reaches when every KDF request is answered by the selected step, and `reached_sequence` shows that a reached opening carries the decoded target as its sequence. `finish_erase_local` is the local part of C7: a raw whose decoded sequence is not one makes at most one primitive call, an opening whose reply is discarded, and the finish rejects. `discarded_native` shows that, with the native primitive interpreter, this discarded opening changes the shared state only by completing one point of the lazily sampled CTX cache, so the finish has the pointed form that `LazyOracleDiscard.discard_erase` erases.

`finish_erase_native` is the CTX-cache instance of the engine: against any adaptive client that triggers hidden finishes on chosen prepared registrations and slot factors and queries BLAKE2b on the same lazily sampled cache, the real finish and the erased finish (no opening on a non-sequence-one raw) have the same output law.

The labelled-kernel identities `resolve_after_send` and `resolve_after_receive` (critique M3) show that the labelled first Server send and the labelled sequence-one Beacon receive on a 76-byte reply end in exactly the record world's seed kernels `PqxdhRecordLiftSeed.serverKernel` and `beaconKernel` of (next32, right32), by transport to the extracted computations `PqxdhRecordLiftSeed.sendOne_from_counters` and `receiveOne_from_counters`.

These are equalities of programs over arbitrary primitive interpreters (and, for the native interpreter, equalities in law of the lazy CTX cache). They make no authentication, secrecy or independence claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels
open PqxdhServerAuthSendFactor (Kernel Factor resolve)
open RawCtxSelectedChain (Slot nativeKernel)
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf

/-- A labelled receive effect of the finish-time receive. -/
abbrev OpenEffect := RawCtxChainReceive.Effect Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext

/-- The effect a labelled receive reaches when every KDF request is answered by the selected step. -/
noncomputable def reached (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) :
    OpenEffect → OpenEffect
  | .kdfRequested pending => reached source challenge
      (RawCtxChainReceive.normalResume pending (RawCtxSelectedChain.step source challenge pending.request))
  | .rejected entry context => .rejected entry context
  | .openRequested opening => .openRequested opening
termination_by effect => RawCtxChainReceive.effectRank effect
decreasing_by exact RawCtxChainReceive.normalResume_rank _ _

section Program
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Under `primLabels` every KDF request is answered without effect, so the receive program equals the program of the reached effect. -/
theorem program_reached (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) (effect : OpenEffect) :
    simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source challenge)
        (RawCtxChainReceive.program (Plaintext := RawCtxWholeOwner.Decrypted) effect) =
      simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source challenge)
        (RawCtxChainReceive.program (Plaintext := RawCtxWholeOwner.Decrypted) (reached source challenge effect)) := by
  generalize ranked : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | kdfRequested pending =>
          rw [reached]
          simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query,
            PqxdhServerAuthBeaconFactor.primLabels, pure_bind]
          exact ih _ (ranked ▸ RawCtxChainReceive.normalResume_rank pending
            (RawCtxSelectedChain.step source challenge pending.request)) _ rfl
      | rejected entry context => rw [reached]
      | openRequested opening => rw [reached]

end Program

/-- A reached effect is a rejection or an opening request. -/
theorem reached_cases (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) (effect : OpenEffect) :
    (∃ entry context, reached source challenge effect = .rejected entry context) ∨
      ∃ opening, reached source challenge effect = .openRequested opening := by
  generalize ranked : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | kdfRequested pending =>
          rw [reached]
          exact ih _ (ranked ▸ RawCtxChainReceive.normalResume_rank pending
            (RawCtxSelectedChain.step source challenge pending.request)) _ rfl
      | rejected entry context =>
          rw [reached]
          exact Or.inl ⟨entry, context, rfl⟩
      | openRequested opening =>
          rw [reached]
          exact Or.inr ⟨opening, rfl⟩

/-- The primitive opening input of a labelled opening (none on missing material), as `primLabels` computes it. -/
noncomputable def openingInput
    (opening : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    Option RawCtxWholeOwner.OpenInput :=
  RawCtxWholeOwner.arguments (RawCtxInterpretedOpening.toNative
    (RawCtxChainInterpretation.mapOpeningChains (fun _ => RawCtxSelectedChain.unusedChain)
      (fun _ => RawCtxSelectedChain.unusedChain) opening))

/-- A labelled effect retains the decoded target and the immutable open context (the labelled form of `RawCtxOwnerProvenance.Scope`). -/
def Scope (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) : OpenEffect → Prop
  | .rejected _ actual => actual = context
  | .kdfRequested pending => pending.target = target ∧ pending.context = context
  | .openRequested opening => RawCtxInterpretedOpening.sequence opening = ok target ∧ opening.context = context

/-- Mapping chain labels does not change an opening's sequence. -/
theorem sequence_mapChains {SendValue ReceiveValue : Type} (send : Slot → SendValue) (receive : Slot → ReceiveValue)
    (opening : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext) :
    RawCtxInterpretedOpening.sequence (RawCtxChainInterpretation.mapOpeningChains send receive opening) =
      RawCtxInterpretedOpening.sequence opening := by
  rcases opening with ⟨entry, context, prepared⟩
  cases prepared <;> rfl

/-- The labelled scope is the native scope of the mapped effect. -/
theorem scope_native (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) (effect : OpenEffect) :
    RawCtxOwnerProvenance.Scope target context
        (RawCtxInterpretedReceive.nativeEffect (RawCtxChainReceive.nativeEffect
          (fun _ => RawCtxSelectedChain.unusedChain) (fun _ => RawCtxSelectedChain.unusedChain) effect)) ↔
      Scope target context effect := by
  cases effect with
  | rejected entry actual => exact Iff.rfl
  | kdfRequested pending => exact Iff.rfl
  | openRequested opening =>
      simp only [RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.nativeEffect,
        RawCtxOwnerProvenance.Scope, Scope, RawCtxInterpretedOpening.native_sequence, sequence_mapChains]
      exact Iff.rfl

/-- Labelled admission retains the decoded target and context on every path. -/
theorem begin_scope (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Scope target context (RawCtxChainReceive.normalBegin entry target context) := by
  have hscope := RawCtxOwnerProvenance.oracle_begin_scope
    (⟨RawCtxChainInterpretation.mapChains (fun _ => RawCtxSelectedChain.unusedChain)
      (fun _ => RawCtxSelectedChain.unusedChain) entry⟩ : ConcreteRatchetKernel) target context
  rw [RawCtxInterpretedReceive.normalBegin_native, RawCtxChainReceive.normalBegin_native] at hscope
  exact (scope_native target context _).1 hscope

/-- Every typed KDF reply preserves the pending target and context through the labelled continuation. -/
theorem resume_scope (pending : RawCtxChainReceive.Kdf Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : Slot × RatchetMaterial) :
    Scope pending.target pending.context (RawCtxChainReceive.normalResume pending reply) := by
  have resumed := RawCtxChainReceive.normalResume_exact pending reply
  simp only [RawCtxChainReceive.resume, RawCtxChainReceive.rejected, Bind.bind, Aeneas.Std.bind] at resumed
  repeat' split at resumed
  all_goals simp only [RustM.ok.injEq, reduceCtorEq] at resumed
  all_goals rw [← resumed]
  all_goals simp_all only [Scope, RawCtxInterpretedOpening.sequence, and_self]

/-- m3: a reached opening carries the requested target as its sequence and the original context. -/
theorem reached_scope (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) (effect : OpenEffect)
    (hscope : Scope target context effect) : Scope target context (reached source challenge effect) := by
  generalize ranked : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | kdfRequested pending =>
          rw [reached]
          obtain ⟨hTarget, hContext⟩ := hscope
          have next := resume_scope pending (RawCtxSelectedChain.step source challenge pending.request)
          rw [hTarget, hContext] at next
          exact ih _ (ranked ▸ RawCtxChainReceive.normalResume_rank pending
            (RawCtxSelectedChain.step source challenge pending.request)) _ next rfl
      | rejected entry actual =>
          rw [reached]
          exact hscope
      | openRequested opening =>
          rw [reached]
          exact hscope

/-- m3: the opening input reached from admission carries the decoded target as its sequence. -/
theorem reached_sequence (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse) (entry : Kernel)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (opening : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (input : RawCtxWholeOwner.OpenInput)
    (h : reached source challenge (RawCtxChainReceive.normalBegin entry target context) = .openRequested opening)
    (hin : openingInput opening = some input) : input.sequence = target ∧ input.context = context := by
  have hscope := reached_scope source challenge target context _ (begin_scope entry target context)
  rw [h] at hscope
  obtain ⟨hSequence, hContext⟩ := hscope
  obtain ⟨_, hInputSequence, hInputContext⟩ := RawCtxWholeOwner.arguments_some _ input hin
  rw [RawCtxInterpretedOpening.native_sequence, sequence_mapChains, hSequence] at hInputSequence
  exact ⟨(RustM.ok.inj hInputSequence).symm, hInputContext.trans hContext⟩

/-- A raw whose decoded frame has sequence one. -/
def SeqOne (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) : Bool :=
  match decode raw with
  | some frame => decide (frame.sequence = 1#u64)
  | none => false

/-- The reply component of a labelled finish is the given reply. -/
theorem normalFinish_reply {Plaintext : Type}
    (opening : RawCtxInterpretedOpening.Opening Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (reply : core.option.Option Plaintext) :
    (RawCtxChainReceive.normalFinish opening reply).2 = reply := by
  have finished := RawCtxChainReceive.normalFinish_exact opening reply
  simp only [RawCtxInterpretedOpening.finish, Bind.bind, Aeneas.Std.bind] at finished
  repeat' split at finished
  all_goals simp only [RustM.ok.injEq, reduceCtorEq] at finished
  all_goals rw [← finished]

section Finish
variable {m : Type → Type} [Monad m] {Response : Type}

/-- The `some raw` branch of `PqxdhServerAuthBeaconFactor.factored`. -/
noncomputable def factoredBody (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes) :
    m (Option PqxdhBeaconPhase2Publication.Staged) := do
  let candidate := PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate
  let result ← (RawCtxChainOwner.rawReceive (PqxdhServerAuthBeaconFactor.primCalls sendCall prim source value.1)
    decode raw).run (PqxdhServerAuthBeaconFactor.localState candidate (PqxdhServerAuthBeaconFactor.initial value.2))
  pure (PqxdhBeaconPhase2Publication.afterOpening candidate (resolve result.2.kernel) result.1)

/-- The hidden Beacon finish is the application getter followed by `factoredBody`. -/
theorem factored_body (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → m (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) :
    PqxdhServerAuthBeaconFactor.factored prim sendCall source application decode prepared value = (do
      let raw ← application prepared.response
      match raw with
      | none => pure none
      | some raw => factoredBody prim sendCall source decode prepared value raw) := rfl

/-- The opening input the finish-time receive reaches without any primitive call; none on every earlier rejection. -/
noncomputable def discardedInput (source : FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes) :
    Option RawCtxWholeOwner.OpenInput :=
  let state := PqxdhServerAuthBeaconFactor.localState
    (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate) (PqxdhServerAuthBeaconFactor.initial value.2)
  if raw.isEmpty then none else
  match decode raw with
  | none => none
  | some frame =>
      if RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame then
        match reached source value.1
            (RawCtxChainReceive.normalBegin state.kernel frame.sequence ⟨raw, frame, state.associatedData⟩) with
        | .openRequested opening => openingInput opening
        | _ => none
      else none

/-- The erased hidden finish tail (M4 form): a non-sequence-one raw rejects with no primitive call and reports the discarded opening input. -/
noncomputable def finishErased (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → m (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) : m (Option PqxdhBeaconPhase2Publication.Staged × Option RawCtxWholeOwner.OpenInput) := do
  let raw ← application prepared.response
  match raw with
  | none => pure (none, none)
  | some raw =>
      if SeqOne decode raw then (·, none) <$> factoredBody prim sendCall source decode prepared value raw
      else pure (none, discardedInput source decode prepared value raw)

/-- On a raw whose decoded sequence is not one, the finish body is at most one discarded opening call, and it rejects. -/
theorem body_discard [LawfulMonad m] (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes)
    (notOne : SeqOne decode raw = false) :
    factoredBody prim sendCall source decode prepared value raw =
      match discardedInput source decode prepared value raw with
      | none => pure none
      | some input => (fun _ => none) <$> prim (.inr input) := by
  simp only [factoredBody, discardedInput, RawCtxChainOwner.rawReceive, StateT.run]
  by_cases blank : raw.isEmpty = true
  · simp only [blank, ite_true, pure_bind, RawCtxChainOwner.publish, PqxdhBeaconPhase2Publication.afterOpening]
  · simp only [blank, Bool.false_eq_true, ite_false]
    cases decoded : decode raw with
    | none =>
        dsimp only
        simp only [pure_bind, RawCtxChainOwner.publish, PqxdhBeaconPhase2Publication.afterOpening]
    | some frame =>
        dsimp only
        have sequenceNe : frame.sequence ≠ 1#u64 := by
          simpa only [SeqOne, decoded, decide_eq_false_iff_not] using notOne
        by_cases valid : RawCtxReceive.ValidFrame
            (PqxdhServerAuthBeaconFactor.localState (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
              (PqxdhServerAuthBeaconFactor.initial value.2)).expectedSender
            (PqxdhServerAuthBeaconFactor.localState (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
              (PqxdhServerAuthBeaconFactor.initial value.2)).associatedData frame
        · simp only [valid, ite_true, bind_assoc, pure_bind, PqxdhServerAuthBeaconFactor.primCalls,
            RawCtxChainReceive.execute, RawCtxChainOwner.publish]
          rw [program_reached]
          rcases reached_cases source value.1 (RawCtxChainReceive.normalBegin
              (PqxdhServerAuthBeaconFactor.localState (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
                (PqxdhServerAuthBeaconFactor.initial value.2)).kernel frame.sequence
              ⟨raw, frame, (PqxdhServerAuthBeaconFactor.localState
                (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
                (PqxdhServerAuthBeaconFactor.initial value.2)).associatedData⟩) with
            ⟨entry, context, hreached⟩ | ⟨opening, hreached⟩
          · rw [hreached]
            simp only [RawCtxChainReceive.program, simulateQ_pure, pure_bind,
              PqxdhBeaconPhase2Publication.afterOpening]
          · rw [hreached]
            simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
              PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose, bind_assoc, pure_bind,
              normalFinish_reply]
            change simulateQ prim (RawCtxWholeOwner.adapter (.inr _)) >>= _ = match openingInput opening with
              | none => pure none
              | some input => (fun _ => none) <$> prim (.inr input)
            cases hin : openingInput opening with
            | none =>
                simp only [RawCtxWholeOwner.adapter]
                rw [show RawCtxWholeOwner.arguments _ = none from hin]
                simp only [simulateQ_pure, pure_bind, PqxdhBeaconPhase2Publication.afterOpening]
            | some input =>
                have hseq := (reached_sequence source value.1 _ _ _ opening input hreached hin).1
                rw [RawCtxWholeOwner.adapter_present _ input hin]
                simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bind_assoc, pure_bind]
                rw [map_eq_bind_pure_comp]
                refine bind_congr fun reply => ?_
                cases reply with
                | none => simp only [RawCtxOwnerResult.mapReply, PqxdhBeaconPhase2Publication.afterOpening,
                    Function.comp_apply]
                | some plaintext =>
                    simp only [RawCtxOwnerResult.mapReply, PqxdhBeaconPhase2Publication.afterOpening,
                      RawCtxWholeOwner.decrypted, hseq, ne_eq, sequenceNe, not_false_eq_true, ite_true,
                      Function.comp_apply]
        · simp only [valid, ite_false, pure_bind, RawCtxChainOwner.publish, PqxdhBeaconPhase2Publication.afterOpening]

/-- C7, local part (M4 form): the hidden finish is its erased form followed by the discarded opening call. -/
theorem finish_erase_local [LawfulMonad m] (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (sendCall : Kernel → RawCtxSourceSend.SealContext → m (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → m (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) :
    PqxdhServerAuthBeaconFactor.factored prim sendCall source application decode prepared value =
      (finishErased prim sendCall source application decode prepared value >>= fun r =>
        match r.2 with
        | none => pure r.1
        | some input => (fun _ => r.1) <$> prim (.inr input)) := by
  rw [factored_body]
  simp only [finishErased, bind_assoc]
  refine bind_congr fun raw => ?_
  cases raw with
  | none => simp only [pure_bind]
  | some raw =>
      dsimp only
      by_cases hone : SeqOne decode raw = true
      · simp only [hone, ↓reduceIte, bind_map_left, bind_pure]
      · simp only [hone, Bool.false_eq_true, ↓reduceIte, pure_bind]
        rw [body_discard prim sendCall source decode prepared value raw (by simpa only [Bool.not_eq_true] using hone)]

end Finish

/-! ### The discarded opening as one completion of the shared CTX cache -/

/-- The lens onto the CTX cache of the shared primitive state. -/
abbrev ctxLens : LazyOracleDiscard.CacheLens CtxRomAuth.CtxRO (RawCtxSharedPrimitive.SharedState Unit) :=
  LazyOracleDiscard.StateLens.snd Unit CtxRomAuth.CtxRO.QueryCache

/-- The BLAKE2b point of a primitive opening (none when the payload or AD width rejects first). -/
def openPoint (input : RawCtxWholeOwner.OpenInput) : Option CtxRomAuth.CtxRO.Domain :=
  match RawCtxFrameDecoding.fromPayload input.context.frame.payload with
  | none => none
  | some slices =>
      if input.context.associatedData.length = 281 then some ((), RawCtxSourceOpen.hashInput input slices)
      else none

/-- With the native primitive interpreter, a discarded opening changes the shared state only by completing its point of the CTX cache. -/
theorem discarded_native {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (input : RawCtxWholeOwner.OpenInput) (state : RawCtxSharedPrimitive.SharedState Unit) :
    Prod.snd <$> (PqxdhServerAuthBeaconFactor.nativePrim setup codec (.inr input)).run state =
      (LazyOracleDiscard.StateLens.snd Unit CtxRomAuth.CtxRO.QueryCache).completeOpt
        (spec := CtxRomAuth.CtxRO) (openPoint input) state := by
  obtain ⟨auxiliary, cache⟩ := state
  simp only [PqxdhServerAuthBeaconFactor.nativePrim, QueryImpl.apply_compose, RawCtxSourceOpen.nativeAdapter]
  rw [RawCtxSharedPrimitive.native_opening_complete]
  unfold openPoint RawCtxSourceOpen.openInput
  cases RawCtxFrameDecoding.fromPayload input.context.frame.payload with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure, LazyOracleDiscard.StateLens.completeOpt]
  | some slices =>
      by_cases width : input.context.associatedData.length = 281
      · simp only [width, ↓reduceIte]
        rw [RawCtxSourceOpen.openSlices_rom]
        simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
          map_bind, map_pure, LazyOracleDiscard.StateLens.completeOpt, LazyOracleDiscard.StateLens.complete,
          LazyOracleDiscard.complete, Functor.map_map]
        rw [map_eq_bind_pure_comp]
        rfl
      · simp only [width, ↓reduceIte, simulateQ_pure, StateT.run_pure, map_pure,
          LazyOracleDiscard.StateLens.completeOpt]

/-! ### Labelled-kernel identities (critique M3) -/

/-- The labelled initial Server kernel: hidden send slot, known receive chain. -/
def serverInitial (right : RootOutput) : Kernel :=
  { control := ⟨0#u64, 0#u64, ⟨Std.Array.repeat 50#usize 0#u64, 0#u8⟩⟩
    send_chain := .hidden
    receive_chain := .known (RawCtxFreshChainCut.concreteChain right)
    receive_slots := Std.Array.repeat 50#usize .None }

/-- This constructor is the complete extracted initial Server result, not a replacement state. -/
theorem serverInitial_exact (right : RootOutput) :
    RawCtxSelectedInitialConstructor.initial false right = ok (serverInitial right) := rfl

/-- With the hidden send slot read as the unused chain, the labelled initial Server kernel is the native zero-counter kernel. -/
theorem serverInitial_native (right : RootOutput) :
    ConcreteRatchetKernel.from_counters 0#u64 0#u64 RawCtxSelectedChain.unusedChain
        (RawCtxFreshChainCut.concreteChain right) = ok (resolve (serverInitial right)) :=
  (RawCtxSelectedInitialConstructor.new_map RawCtxSelectedChain.unusedChain RawCtxSelectedChain.Slot.hidden
    (.known (RawCtxFreshChainCut.concreteChain right))).trans
      (congrArg (fun result => nativeKernel RawCtxSelectedChain.unusedChain <$> result) (serverInitial_exact right))

/-- The extracted first send from the resolved initial Server kernel follows the labelled admission. -/
theorem send_native (right : RootOutput) (context : RawCtxSourceSend.SealContext) (response : RatchetKdfResponse) :
    PqxdhRecordLiftSeed.sendOne (resolve (serverInitial right)) response context
        (core.option.Option.None : core.option.Option Unit) =
      match RawCtxChainSend.normalBegin (serverInitial right) context with
      | .exhausted _ _ => ok none
      | .requested pending => ok (some (⟨(RawCtxInterpretedSend.ready
          (RawCtxChainSend.nativeKdf (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain)
            (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain) pending)
          (RawCtxInterpretedReceive.decodeResponse response)).advanced⟩, core.option.Option.None)) := by
  have begun : begin_send (resolve (serverInitial right)) context =
      ok (RawCtxInterpretedSend.nativeStart (RawCtxChainSend.nativeStart
        (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain)
        (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain)
        (RawCtxChainSend.normalBegin (serverInitial right) context))) := by
    rw [resolve, nativeKernel, RawCtxInterpretedSend.native_begin, RawCtxInterpretedSend.normalBegin_exact,
      RawCtxChainSend.normalBegin_native]
    rfl
  simp only [PqxdhRecordLiftSeed.sendOne, begun, bind_tc_ok]
  cases RawCtxChainSend.normalBegin (serverInitial right) context with
  | exhausted entry other => rfl
  | requested pending =>
      simp only [RawCtxChainSend.nativeStart, RawCtxInterpretedSend.nativeStart, RawCtxSourceSend.resumeSend_exact,
        RawCtxInterpretedSend.ready_native, bind_tc_ok, SendSeal.finish_returns_interpreter_result,
        RawCtxMaterialInterpretation.rust_map_ok]
      rfl

/-- The first labelled Server send requests the hidden slot. -/
theorem initial_send_requested (right : RootOutput) (context : RawCtxSourceSend.SealContext) :
    ∃ pending, RawCtxChainSend.normalBegin (serverInitial right) context = .requested pending ∧
      pending.request = .hidden := by
  rcases PqxdhServerAuthSendFactor.send_begin (serverInitial right) context with
    ⟨other, exhausted⟩ | ⟨pending, requested, _, request⟩
  · exfalso
    let output : FullOutput := List.Vector.replicate 76 0
    have computed := PqxdhRecordLiftSeed.sendOne_from_counters (Output := Unit) RawCtxSelectedChain.unusedChain
      (RawCtxFreshChainCut.concreteChain right) (RawCtxKdfRequestTable.fullResponse output) _
      (PqxdhRecordLiftSeed.response_step output) context .None
    rw [serverInitial_native, bind_tc_ok, send_native, exhausted] at computed
    obtain ⟨kernel, built⟩ := PqxdhRecordLiftSeed.serverKernel_total
      (PqxdhOrderedChainHybrids.nextChain output, right)
    rw [show ConcreteRatchetKernel.from_counters 1#u64 0#u64
        (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output))
        (RawCtxFreshChainCut.concreteChain right) = ok kernel from built,
      RawCtxMaterialInterpretation.rust_map_ok] at computed
    cases RustM.ok.inj computed
  · exact ⟨pending, requested, request⟩

/-- M3, Server: the resolved kernel after the first labelled send on a 76-byte reply is the world's Server seed kernel. -/
theorem resolve_after_send (source : FixedHkdfSha512NoSaltSource) (right : RootOutput) (output : FullOutput)
    (context : RawCtxSourceSend.SealContext)
    (pending : RawCtxChainSend.Kdf Slot Slot RatchetMaterial RawCtxSourceSend.SealContext)
    (begun : RawCtxChainSend.normalBegin (serverInitial right) context = .requested pending) :
    PqxdhRecordLiftSeed.serverKernel (PqxdhOrderedChainHybrids.nextChain output, right) =
      ok (resolve (RawCtxChainSend.ready pending
        (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) pending.request)).advanced) := by
  obtain ⟨other, otherBegun, otherRequest⟩ := initial_send_requested right context
  rw [begun] at otherBegun
  cases otherBegun
  have computed := PqxdhRecordLiftSeed.sendOne_from_counters (Output := Unit) RawCtxSelectedChain.unusedChain
    (RawCtxFreshChainCut.concreteChain right) (RawCtxKdfRequestTable.fullResponse output) _
    (PqxdhRecordLiftSeed.response_step output) context .None
  rw [serverInitial_native, bind_tc_ok, send_native, begun] at computed
  obtain ⟨kernel, built⟩ := PqxdhRecordLiftSeed.serverKernel_total (PqxdhOrderedChainHybrids.nextChain output, right)
  rw [show ConcreteRatchetKernel.from_counters 1#u64 0#u64
      (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain output))
      (RawCtxFreshChainCut.concreteChain right) = ok kernel from built,
    RawCtxMaterialInterpretation.rust_map_ok] at computed
  have same := congrArg (fun result => Option.map Prod.fst result) (RustM.ok.inj computed)
  simp only [Option.map_some] at same
  rw [built, ← Option.some.inj same, otherRequest]
  rfl

/-- The first labelled receive request is the kernel's receive slot. -/
theorem receive_begin_request (entry : Kernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (pending : RawCtxChainReceive.Kdf Slot Slot RatchetMaterial RawCtxWholeOwner.OpenContext)
    (begun : RawCtxChainReceive.normalBegin entry target context = .kdfRequested pending) :
    pending.request = entry.receive_chain := by
  have exact := RawCtxChainReceive.normalBegin_exact entry target context
  rw [begun] at exact
  simp only [RawCtxChainReceive.beginReceive, RawCtxChainReceive.rejected, Bind.bind, Aeneas.Std.bind] at exact
  repeat' split at exact
  all_goals simp only [RustM.ok.injEq, reduceCtorEq] at exact
  all_goals cases exact
  all_goals rfl

/-- With the hidden receive slot read as the unused chain, the labelled initial Beacon kernel is the native zero-counter kernel. -/
theorem beaconInitial_native (right : RootOutput) :
    ConcreteRatchetKernel.from_counters 0#u64 0#u64 (RawCtxFreshChainCut.concreteChain right)
        RawCtxSelectedChain.unusedChain = ok (resolve (PqxdhServerAuthBeaconFactor.initial right)) :=
  (RawCtxSelectedInitialConstructor.new_map RawCtxSelectedChain.unusedChain
    (.known (RawCtxFreshChainCut.concreteChain right)) RawCtxSelectedChain.Slot.hidden).trans
      (congrArg (fun result => nativeKernel RawCtxSelectedChain.unusedChain <$> result)
        (PqxdhServerAuthBeaconFactor.initial_exact right))

/-- The extracted sequence-one receive from the resolved initial Beacon kernel follows the labelled admission and resume. -/
theorem receive_native {Plaintext : Type} (source : FixedHkdfSha512NoSaltSource) (right : RootOutput)
    (response : RatchetKdfResponse) (context : RawCtxWholeOwner.OpenContext) (plaintext : Plaintext) :
    PqxdhRecordLiftSeed.receiveOne (resolve (PqxdhServerAuthBeaconFactor.initial right)) response context plaintext =
      match RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context with
      | .kdfRequested pending =>
          match RawCtxChainReceive.normalResume pending (RawCtxSelectedChain.step source response .hidden) with
          | .openRequested opening => ok (some (resolve (RawCtxChainReceive.normalFinish opening
              (core.option.Option.Some plaintext)).1, core.option.Option.Some plaintext))
          | _ => ok none
      | _ => ok none := by
  have begun : begin_receive (resolve (PqxdhServerAuthBeaconFactor.initial right)) 1#u64 context =
      ok (RawCtxInterpretedReceive.nativeEffect (RawCtxChainReceive.nativeEffect
        (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain)
        (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain)
        (RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context))) := by
    rw [RawCtxOwnerOracle.begin_exact, resolve, nativeKernel, RawCtxInterpretedReceive.normalBegin_native,
      RawCtxChainReceive.normalBegin_native]
  simp only [PqxdhRecordLiftSeed.receiveOne, begun, bind_tc_ok]
  cases RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context with
  | rejected entry actual => rfl
  | openRequested opening => rfl
  | kdfRequested pending =>
      simp only [RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.nativeEffect,
        RawCtxOwnerOracle.resume_exact, bind_tc_ok]
      have resumed := RawCtxInterpretedReceive.normalResume_native
        (RawCtxChainReceive.nativeKdf (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain)
          (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain) pending) response
      rw [show RawCtxInterpretedReceive.decodeResponse response =
          (RawCtxSelectedChain.interpret RawCtxSelectedChain.unusedChain
            (RawCtxSelectedChain.step source response .hidden).1,
            (RawCtxSelectedChain.step source response .hidden).2) from rfl,
        RawCtxChainReceive.normalResume_native] at resumed
      rw [resumed]
      cases RawCtxChainReceive.normalResume pending (RawCtxSelectedChain.step source response .hidden) with
      | rejected entry actual => rfl
      | kdfRequested next => rfl
      | openRequested opening =>
          simp only [RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.nativeEffect,
            RawCtxOwnerOracle.finish_exact, RawCtxInterpretedReceive.normalFinish_native,
            RawCtxChainReceive.normalFinish_native, normalFinish_reply,
            RawCtxMaterialInterpretation.rust_map_ok]
          rfl

/-- M3, Beacon: after the sequence-one labelled receive on a 76-byte reply, the resolved kernel is the world's Beacon seed kernel; a failed receive is observed independently of its kernel. -/
theorem resolve_after_receive {m : Type → Type} [Monad m] [LawfulMonad m] (prim : QueryImpl RawCtxWholeOwner.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (right : RootOutput) (output : FullOutput)
    (context : RawCtxWholeOwner.OpenContext) (kernel : ConcreteRatchetKernel) {Result : Type}
    (observe : ConcreteRatchetKernel → core.option.Option RawCtxWholeOwner.Decrypted → Result)
    (hk : PqxdhRecordLiftSeed.beaconKernel (PqxdhOrderedChainHybrids.nextChain output, right) = ok kernel)
    (failure : ∀ first second, observe first .None = observe second .None) :
    (fun result => observe (resolve result.1) result.2) <$>
        simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source (RawCtxKdfRequestTable.fullResponse output))
          (RawCtxChainReceive.execute (Plaintext := RawCtxWholeOwner.Decrypted)
            (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context) =
      (fun result => observe kernel result.2) <$>
        simulateQ (PqxdhServerAuthBeaconFactor.primLabels prim source (RawCtxKdfRequestTable.fullResponse output))
          (RawCtxChainReceive.execute (Plaintext := RawCtxWholeOwner.Decrypted)
            (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context) := by
  have computed : ∀ plaintext : RawCtxWholeOwner.Decrypted,
      PqxdhRecordLiftSeed.receiveOne (resolve (PqxdhServerAuthBeaconFactor.initial right))
          (RawCtxKdfRequestTable.fullResponse output) context plaintext =
        ok (some (kernel, core.option.Option.Some plaintext)) := by
    intro plaintext
    have counted := PqxdhRecordLiftSeed.receiveOne_from_counters RawCtxSelectedChain.unusedChain
      (RawCtxFreshChainCut.concreteChain right) (RawCtxKdfRequestTable.fullResponse output) _
      (PqxdhRecordLiftSeed.response_step output) context plaintext
    rw [beaconInitial_native, bind_tc_ok] at counted
    rw [counted]
    exact congrArg (fun built => (fun kernel => some (kernel, core.option.Option.Some plaintext)) <$> built) hk
  rw [RawCtxChainReceive.execute, program_reached]
  have shape := computed ⟨[], 0#u64, 0#u64⟩
  rw [receive_native source] at shape
  cases begun : RawCtxChainReceive.normalBegin (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context with
  | rejected entry actual => simp only [begun, RustM.ok.injEq, reduceCtorEq] at shape
  | openRequested opening => simp only [begun, RustM.ok.injEq, reduceCtorEq] at shape
  | kdfRequested pending =>
      have request : pending.request = .hidden :=
        receive_begin_request (PqxdhServerAuthBeaconFactor.initial right) 1#u64 context pending begun
      cases resumed : RawCtxChainReceive.normalResume pending
          (RawCtxSelectedChain.step source (RawCtxKdfRequestTable.fullResponse output) .hidden) with
      | rejected entry actual => simp only [begun, resumed, RustM.ok.injEq, reduceCtorEq] at shape
      | kdfRequested next => simp only [begun, resumed, RustM.ok.injEq, reduceCtorEq] at shape
      | openRequested opening =>
          rw [reached, request, resumed, reached]
          simp only [RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
            map_bind, map_pure]
          refine bind_congr fun reply => ?_
          cases reply with
          | none =>
              rw [normalFinish_reply]
              exact congrArg pure (failure _ _)
          | some plaintext =>
              have opened := computed plaintext
              rw [receive_native source, begun] at opened
              simp only [resumed] at opened
              have same := congrArg (fun result => Option.map Prod.fst result) (RustM.ok.inj opened)
              simp only [Option.map_some] at same
              rw [normalFinish_reply, Option.some.inj same]

/-! ### The CTX-cache instance of `LazyOracleDiscard.discard_erase` -/

/-- The state monad of the native primitive interpreter. -/
abbrev NativeM := StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp

/-- The CTX lazy oracle is the lazy query on the whole cache. -/
theorem ctxRandomOracle_query (point : CtxRomAuth.CtxRO.Domain) :
    CtxRomAuth.ctxRandomOracle point =
      (LazyOracleDiscard.StateLens.id CtxRomAuth.CtxRO.QueryCache).query (spec := CtxRomAuth.CtxRO) point := by
  apply StateT.ext
  intro cache
  simp only [LazyOracleDiscard.StateLens.query, LazyOracleDiscard.StateLens.id, StateT.run]
  rw [show (fun result : CtxRomAuth.CtxDigest × CtxRomAuth.CtxRO.QueryCache => (result.1, result.2)) = id from rfl,
    id_map]

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)

/-- The native opening query is the lazy BLAKE2b opening program lifted onto the CTX cache. -/
theorem nativePrim_open (input : RawCtxWholeOwner.OpenInput) :
    PqxdhServerAuthBeaconFactor.nativePrim setup codec (.inr input) =
      ctxLens.lift (simulateQ CtxRomAuth.ctxRandomOracle
        (simulateQ (RawCtxSourceOpen.romAdapter setup.source.crypto) (RawCtxSourceOpen.openInput input))) := by
  apply StateT.ext
  rintro ⟨auxiliary, cache⟩
  simp only [PqxdhServerAuthBeaconFactor.nativePrim, QueryImpl.apply_compose, RawCtxSourceOpen.nativeAdapter]
  rw [RawCtxSharedPrimitive.native_opening_complete]
  rfl

/-- Every native primitive query commutes with completions of the CTX cache. -/
theorem nativePrim_commutes (query : RawCtxWholeOwner.PrimitiveSpec.Domain) :
    LazyOracleDiscard.Commutes ctxLens (PqxdhServerAuthBeaconFactor.nativePrim setup codec query) := by
  cases query with
  | inl request =>
      rw [PqxdhServerAuthBeaconFactor.native_kdf]
      exact LazyOracleDiscard.commutes_pure ctxLens _
  | inr input =>
      rw [nativePrim_open]
      exact LazyOracleDiscard.commutes_lift ctxLens (LazyOracleDiscard.StateLens.id CtxRomAuth.CtxRO.QueryCache) _
        (LazyOracleDiscard.commutes_simulateQ _ _
          (fun point => by rw [ctxRandomOracle_query]; exact LazyOracleDiscard.commutes_query _ point) _)

/-- Every labelled receive query over the native interpreter commutes with completions of the CTX cache. -/
theorem primLabels_commutes (source : FixedHkdfSha512NoSaltSource) (challenge : RatchetKdfResponse)
    (query : (RawCtxChainReceive.ReceiveSpec Slot Slot RatchetMaterial
      RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted).Domain) :
    LazyOracleDiscard.Commutes ctxLens
      (PqxdhServerAuthBeaconFactor.primLabels (PqxdhServerAuthBeaconFactor.nativePrim setup codec) source challenge query) := by
  cases query with
  | inl slot => exact LazyOracleDiscard.commutes_pure ctxLens _
  | inr pending =>
      simp only [PqxdhServerAuthBeaconFactor.primLabels, QueryImpl.apply_compose]
      exact LazyOracleDiscard.commutes_simulateQ _ _ (nativePrim_commutes setup codec) _

/-- The finish body over the native interpreter commutes with completions of the CTX cache. -/
theorem factoredBody_commutes
    (sendCall : Kernel → RawCtxSourceSend.SealContext → NativeM (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (value : Factor) (raw : Pqxdh.Bytes) :
    LazyOracleDiscard.Commutes ctxLens
      (factoredBody (PqxdhServerAuthBeaconFactor.nativePrim setup codec) sendCall source decode prepared value raw) := by
  unfold factoredBody
  refine LazyOracleDiscard.commutes_bind ctxLens ?_ (fun _ => LazyOracleDiscard.commutes_pure ctxLens _)
  simp only [RawCtxChainOwner.rawReceive, StateT.run]
  split
  · exact LazyOracleDiscard.commutes_pure ctxLens _
  · split
    · exact LazyOracleDiscard.commutes_pure ctxLens _
    · split
      · exact LazyOracleDiscard.commutes_bind ctxLens
          (LazyOracleDiscard.commutes_simulateQ _ _ (primLabels_commutes setup codec source value.1) _)
          (fun _ => LazyOracleDiscard.commutes_pure ctxLens _)
      · exact LazyOracleDiscard.commutes_pure ctxLens _

/-- M5 for the spike: the erased hidden finish over the native interpreter commutes with completions of the CTX cache whenever its application getter does. -/
theorem finishErased_commutes
    (sendCall : Kernel → RawCtxSourceSend.SealContext → NativeM (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → NativeM (Option Pqxdh.Bytes))
    (applicationCommutes : ∀ response, LazyOracleDiscard.Commutes ctxLens (application response))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) :
    LazyOracleDiscard.Commutes ctxLens (Prod.fst <$>
      finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec) sendCall source application decode prepared value) := by
  apply LazyOracleDiscard.commutes_map
  unfold finishErased
  refine LazyOracleDiscard.commutes_bind ctxLens (applicationCommutes _) (fun raw => ?_)
  cases raw with
  | none => exact LazyOracleDiscard.commutes_pure ctxLens _
  | some raw =>
      dsimp only
      split
      · exact LazyOracleDiscard.commutes_map ctxLens _ (factoredBody_commutes setup codec sendCall source decode prepared value raw)
      · exact LazyOracleDiscard.commutes_pure ctxLens _

/-- C7 local part over the native interpreter, pointed form: the hidden finish is its erased form followed by the completion of the discarded opening's CTX point. -/
theorem finish_pointed_native
    (sendCall : Kernel → RawCtxSourceSend.SealContext → NativeM (Kernel × Option RawCtxSourceSend.Encrypted))
    (source : FixedHkdfSha512NoSaltSource) (application : Response → NativeM (Option Pqxdh.Bytes))
    (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response)
    (value : Factor) (state : RawCtxSharedPrimitive.SharedState Unit) :
    (PqxdhServerAuthBeaconFactor.factored (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
        sendCall source application decode prepared value).run state =
      (finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
          sendCall source application decode prepared value).run state >>= fun r =>
        (r.1.1, ·) <$> ctxLens.completeOpt (spec := CtxRomAuth.CtxRO) (r.1.2.bind openPoint) r.2 := by
  rw [finish_erase_local, StateT.run_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨⟨staged, _ | input⟩, current⟩
  · simp only [StateT.run_pure, Option.bind_none, LazyOracleDiscard.StateLens.completeOpt, map_pure]
  · simp only [Option.bind_some, StateT.run_map, ← discarded_native setup codec input current, Functor.map_map]

end Native

/-- A deployment-shaped interface for the instance: hidden Beacon finishes on chosen prepared registrations and slot factors, and BLAKE2b queries on the same lazily sampled CTX cache. -/
abbrev FinishSpec (Response : Type) :=
  ((PqxdhBeaconPhase2Preparation.Prepared Response × Factor) →ₒ Option PqxdhBeaconPhase2Publication.Staged) +
    CtxRomAuth.CtxRO

section Instance
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
  (sendCall : Kernel → RawCtxSourceSend.SealContext → NativeM (Kernel × Option RawCtxSourceSend.Encrypted))
  (application : Response → NativeM (Option Pqxdh.Bytes)) (decode : RawCtxReceive.FrameDecoder)

/-- The real interface: every hidden finish runs the factored Beacon tail, and BLAKE2b is the lazy CTX oracle. -/
noncomputable def finishOracle : QueryImpl (FinishSpec Response) NativeM
  | .inl query => PqxdhServerAuthBeaconFactor.factored (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      sendCall setup.source application decode query.1 query.2
  | .inr point => ctxLens.query point

/-- The erased interface: a non-sequence-one hidden finish makes no opening. -/
noncomputable def finishOracleErased : QueryImpl (FinishSpec Response) NativeM
  | .inl query => Prod.fst <$> finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
      sendCall setup.source application decode query.1 query.2
  | .inr point => ctxLens.query point

/-- The pointed interface: each step reports the CTX point the real interface completes after it. -/
noncomputable def finishOraclePointed (query : (FinishSpec Response).Domain) :
    NativeM ((FinishSpec Response).Range query × Option CtxRomAuth.CtxRO.Domain) :=
  match query with
  | .inl query => (fun r => (r.1, r.2.bind openPoint)) <$>
      finishErased (PqxdhServerAuthBeaconFactor.nativePrim setup codec)
        sendCall setup.source application decode query.1 query.2
  | .inr point => (·, none) <$> ctxLens.query point

/-- Forgetting the reported points of the pointed interface gives the erased interface. -/
theorem pointed_erased :
    (fun query => Prod.fst <$> finishOraclePointed setup codec sendCall application decode query :
      QueryImpl (FinishSpec Response) NativeM) =
      finishOracleErased setup codec sendCall application decode := by
  funext query
  cases query with
  | inl query =>
      simp only [finishOraclePointed, finishOracleErased, Functor.map_map]
      rfl
  | inr point => simp only [finishOraclePointed, finishOracleErased, Functor.map_map, id_map']

/-- C7 for the CTX-cache instance: against any adaptive client of hidden finishes and BLAKE2b queries, the real and erased interfaces have the same output law. -/
theorem finish_erase_native
    (applicationCommutes : ∀ response, LazyOracleDiscard.Commutes ctxLens (application response))
    {α : Type} (client : OracleComp (FinishSpec Response) α) (state : RawCtxSharedPrimitive.SharedState Unit) :
    LazyOracleDiscard.LawEq ((simulateQ (finishOracle setup codec sendCall application decode) client).run' state)
      ((simulateQ (finishOracleErased setup codec sendCall application decode) client).run' state) := by
  have erased := LazyOracleDiscard.discard_erase_proj ctxLens (finishOracle setup codec sendCall application decode)
    (finishOraclePointed setup codec sendCall application decode) ?factor ?oblivious
    (fun _ => ()) (fun _ _ => rfl) client state
  case factor =>
    intro query current
    apply LazyOracleDiscard.LawEq.of_eq
    cases query with
    | inl query =>
        simp only [finishOracle, finishOraclePointed, StateT.run_map, bind_map_left]
        exact finish_pointed_native setup codec sendCall setup.source application decode query.1 query.2 current
    | inr point =>
        simp only [finishOracle, finishOraclePointed, StateT.run_map, bind_map_left,
          LazyOracleDiscard.StateLens.completeOpt, map_pure, Prod.mk.eta, bind_pure]
  case oblivious =>
    intro query
    cases query with
    | inl query =>
        simp only [finishOraclePointed, Functor.map_map]
        exact finishErased_commutes setup codec sendCall setup.source application applicationCommutes decode query.1 query.2
    | inr point =>
        simp only [finishOraclePointed, Functor.map_map, id_map']
        exact LazyOracleDiscard.commutes_query ctxLens point
  rw [pointed_erased] at erased
  simpa only [StateT.run'_eq, Functor.map_map, Prod.map_fst, id_eq] using
    LazyOracleDiscard.LawEq.map Prod.fst erased

/-- The instance with the experiment codec's pure application getter and frame decoder: no premise remains. -/
theorem finish_erase_codec {α : Type} (client : OracleComp (FinishSpec Response) α)
    (state : RawCtxSharedPrimitive.SharedState Unit) :
    LazyOracleDiscard.LawEq
      ((simulateQ (finishOracle setup codec sendCall (fun response => pure (codec.application response))
        codec.frameRead) client).run' state)
      ((simulateQ (finishOracleErased setup codec sendCall (fun response => pure (codec.application response))
        codec.frameRead) client).run' state) :=
  finish_erase_native setup codec sendCall _ codec.frameRead
    (fun _ => LazyOracleDiscard.commutes_pure ctxLens _) client state

end Instance

end BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.program_reached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.program_reached

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.reached_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.reached_cases

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.sequence_mapChains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.sequence_mapChains

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.scope_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.scope_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.begin_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.begin_scope

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.resume_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.resume_scope

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.reached_scope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.reached_scope

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.reached_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.reached_sequence

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.normalFinish_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.normalFinish_reply

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.factored_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.factored_body

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.body_discard' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.body_discard

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_erase_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_erase_local

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.discarded_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.discarded_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.serverInitial_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.serverInitial_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.serverInitial_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.serverInitial_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.send_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.send_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.initial_send_requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.initial_send_requested

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.resolve_after_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.resolve_after_send

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.receive_begin_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.receive_begin_request

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.beaconInitial_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.beaconInitial_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.receive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.receive_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.resolve_after_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.resolve_after_receive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.ctxRandomOracle_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.ctxRandomOracle_query

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.nativePrim_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.nativePrim_open

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.nativePrim_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.nativePrim_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.primLabels_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.primLabels_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.factoredBody_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.factoredBody_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finishErased_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finishErased_commutes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_pointed_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_pointed_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.pointed_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.pointed_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_erase_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_erase_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_erase_codec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHiddenKernels.finish_erase_codec

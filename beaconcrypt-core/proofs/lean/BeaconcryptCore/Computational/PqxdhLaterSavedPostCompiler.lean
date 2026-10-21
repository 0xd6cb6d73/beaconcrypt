import BeaconcryptCore.Computational.PqxdhLaterSavedContext
import BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality

/-! The saved source request feeds the maintained complete instrumented Post compiler without resetting the ordinary CTX interpreter. No new record scheduler or nonce premise is introduced. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}

open PqxdhFirstRecordConfidentiality
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (monitor : Fin B)

section Record
variable
    (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (before : PqxdhInitialPostContext.NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Bool S B)
    (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (inner : RawCtxSelectedFamilyContext.Context M P I D K ((RawCtxProtocolReveals.SourceSpec S B).Range request) S B)
    (material : PqxdhOrderedChainHybrids.Material)
local notation "parent" => RawCtxSelectedPendingRoleCompiler.liveEntry inner material

noncomputable def record (quiet : PqxdhInitialPostCertificates.LiveQuiet inner) (localState : Local A N C) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Result × InsState M P I D K A N C S B) := do
  let result ← RawCtxSelectedPendingRoleCompiler.live source writer prior target nonce next read inner material quiet
  ((simulateQ (insImpl pre application initial selector aux source writer prior (some parent) target nonce next
    sender route read mark monitor) (outside result.1)).run).run
      ((PqxdhLaterSavedRecord.afterRecord before result.2, localState),
        (PqxdhInitialOriginPost.record trace request result.1, none, false))

/-- The actual saved record and complete executable Post share one component state throughout; the original optional outer stop remains in the result. -/
theorem record_evaluated (quiet : PqxdhInitialPostCertificates.LiveQuiet inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (record pre application initial selector aux source writer prior target nonce next mark sender route read monitor
          request before trace outside inner material quiet state.1)).run state.2 = (do
      let result ← (RawCtxSelectedReceiveCompiler.evaluated source key read
        (RawCtxSelectedPendingRoleCompiler.live source writer prior target nonce next read inner material quiet)).run state
      (simulateQ (insEvaluated pre application initial selector aux source writer prior (some parent) key target nonce next
        sender route read mark monitor) (RawCtxSelectedFamilyNonceCoupling.optionalClient (outside result.1.1))).run
        (((PqxdhLaterSavedRecord.afterRecord before result.1.2, result.2.1),
          (PqxdhInitialOriginPost.record trace request result.1.1, none, false)), result.2.2)) := by
  simp only [record, simulateQ_bind, StateT.run_bind, map_bind]
  simp only [RawCtxSelectedReceiveCompiler.evaluated, StateT.run, bind_map_left]
  apply bind_congr
  intro result
  have evaluated := congrArg (fun handler => handler.run
    (((PqxdhLaterSavedRecord.afterRecord before result.1.2, state.1),
      (PqxdhInitialOriginPost.record trace request result.1.1, none, false)), result.2))
    (insEvaluated_program pre application initial selector aux source writer prior (some parent) key target nonce next
      sender route read mark monitor (outside result.1.1))
  exact evaluated

/-- The complete source Post and its existing augmented component ledger assign the same mass to every actual event that retains hidden-disclosure freshness. This consumes the saved record's reached state, without assuming it is a first record. -/
theorem record_post_good
    (post : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (quiet : PqxdhInitialPostCertificates.LiveQuiet inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C))
    (event : Option Bool × Traced M P I D K A N C S B → Prop) :
    let pendingWork := (RawCtxSelectedReceiveCompiler.evaluated source key read
      (RawCtxSelectedPendingRoleCompiler.live source writer prior target nonce next read inner material quiet)).run state
    let sourceWork := do
      let result ← pendingWork
      (simulateQ (traced pre application initial selector aux source writer prior (some parent) key target nonce next
        sender route read mark) (RawCtxSelectedFamilyNonceCoupling.optionalClient (post result.1.1))).run
        ((PqxdhLaterSavedRecord.afterRecord before result.1.2, RawCtxSelectedReceiveCompiler.project result.2),
          PqxdhInitialOriginPost.record trace request result.1.1)
    let augmentedWork := do
      let result ← pendingWork
      (simulateQ (insAugmented pre application initial selector aux source writer prior (some parent) key target nonce next
        sender route read mark monitor) (RawCtxSelectedFamilyNonceCoupling.optionalClient (post result.1.1))).run
        (((PqxdhLaterSavedRecord.afterRecord before result.1.2, result.2.1),
          (PqxdhInitialOriginPost.record trace request result.1.1, none, false)), result.2.2)
    𝒟[(fun result => (by classical exact decide (event result ∧ PqxdhSelectedPostDisclosure.Good result.2.1))) <$> sourceWork] {true} =
      𝒟[(fun result => (by classical exact decide (event (result.1, insProject result.2) ∧
        PqxdhSelectedPostDisclosure.Good (insProject result.2).1))) <$> augmentedWork] {true} := by
  classical
  dsimp only
  simp only [map_bind, evalDist_apply_singleton, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro result
  congr 1
  have equality := post_source_augmented_vcvioLegacy pre application initial selector aux source writer prior (some parent) key target nonce next
    sender route read mark monitor (post result.1.1)
    (((PqxdhLaterSavedRecord.afterRecord before result.1.2, result.2.1),
      (PqxdhInitialOriginPost.record trace request result.1.1, none, false)), result.2.2) event
  rw [← true_mass_eq_vcvioLegacy, ← true_mass_eq_vcvioLegacy, evalDist_apply_singleton, evalDist_apply_singleton] at equality
  simpa only [insProject, RawCtxSelectedReceiveCompiler.project] using equality

end Record

section Finish
variable
    (index : Fin B) (before : PqxdhInitialPostContext.NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Bool S B) (origin : Option Bool)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (outside : Option Pqxdh.Bytes → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (inner : RawCtxSelectedFamilyContext.OwnerContext Unit (core.option.Option RawCtxWholeOwner.Decrypted))
    (material : PqxdhOrderedChainHybrids.Material)
local notation "parent" => RawCtxSelectedPendingOwnerCompiler.entry inner material

noncomputable def finish (quiet : RawCtxQuietOwnerTails.Quiet inner) (localState : Local A N C) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Result × InsState M P I D K A N C S B) := do
  let result ← RawCtxSelectedPendingOwnerCompiler.owner source writer prior target nonce next read inner material quiet
  let finished := PqxdhLaterSavedFinish.afterOwner index (initialFront before) control candidate result
  ((simulateQ (insImpl pre application initial selector aux source writer prior (some parent) target nonce next
    sender route read mark monitor) (outside finished.1)).run).run
      ((finished.2, localState), (PqxdhInitialOriginContext.finishedTrace trace origin index finished.1, none, false))

/-- A saved initial finish keeps the pending opening's full component state through original acceptance, publication and every later Post request. -/
theorem finish_evaluated (quiet : RawCtxQuietOwnerTails.Quiet inner)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (finish pre application initial selector aux source writer prior target nonce next mark sender route read monitor
          index before trace origin control candidate outside inner material quiet state.1)).run state.2 = (do
      let result ← (RawCtxSelectedReceiveCompiler.evaluated source key read
        (RawCtxSelectedPendingOwnerCompiler.owner source writer prior target nonce next read inner material quiet)).run state
      let finished := PqxdhLaterSavedFinish.afterOwner index (initialFront before) control candidate result.1
      (simulateQ (insEvaluated pre application initial selector aux source writer prior (some parent) key target nonce next
        sender route read mark monitor) (RawCtxSelectedFamilyNonceCoupling.optionalClient (outside finished.1))).run
        (((finished.2, result.2.1),
          (PqxdhInitialOriginContext.finishedTrace trace origin index finished.1, none, false)), result.2.2)) := by
  simp only [finish, simulateQ_bind, StateT.run_bind, map_bind]
  simp only [RawCtxSelectedReceiveCompiler.evaluated, StateT.run, bind_map_left]
  apply bind_congr
  intro result
  let finished := PqxdhLaterSavedFinish.afterOwner index (initialFront before) control candidate result.1
  have evaluated := congrArg (fun handler => handler.run
    (((finished.2, state.1),
      (PqxdhInitialOriginContext.finishedTrace trace origin index finished.1, none, false)), result.2))
    (insEvaluated_program pre application initial selector aux source writer prior (some parent) key target nonce next
      sender route read mark monitor (outside finished.1))
  exact evaluated

end Finish

section Builder
variable
    (trace : PqxdhInitialOriginPost.Trace Bool S B) (origin : Option Bool)
    (saved : PqxdhInitialBuilderContext.Builder extra M P I D K Result S B)
    (material : PqxdhOrderedChainHybrids.Material)
local notation "parent" => Entry.mk (RawCtxSelectedPendingCut.requestAddress saved.pending.request) material
local notation "ready" => RawCtxChainSend.ready saved.pending
  (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse (realize parent target)))

noncomputable def publication (sealed : Option RawCtxSourceSend.Encrypted) :
    StateT (Local A N C) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec)
      (Option PqxdhServerRegistrationPublication.Response ×
        PqxdhInitialGenericPublication.State (RefinedRatchet RatchetChain RatchetChain RatchetMaterial) M P (List Pqxdh.Bytes)) :=
  PqxdhInitialBuilderContext.afterSend
    (fun query => PqxdhSelectedCallbackCompiler.lower pre application initial selector aux
      (.inl (.inr (.inr (.inr (.inr query))))))
    saved.candidate saved.authenticated saved.metadata
    (PqxdhInitialPendingBuilder.selected sender saved.index saved.before) ((ready).advanced, sealed)

private theorem afterSend_simulate {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
    (sealed : Option RawCtxSourceSend.Encrypted) :
    simulateQ impl (PqxdhInitialBuilderContext.afterSend (fun query => PqxdhServerRegistrationPublication.AuxSpec.query query)
      saved.candidate saved.authenticated saved.metadata
      (PqxdhInitialPendingBuilder.selected sender saved.index saved.before) ((ready).advanced, sealed)) =
    PqxdhInitialBuilderContext.afterSend impl saved.candidate saved.authenticated saved.metadata
      (PqxdhInitialPendingBuilder.selected sender saved.index saved.before) ((ready).advanced, sealed) := by
  simp only [PqxdhInitialBuilderContext.afterSend, simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro erased
  cases sealed
  all_goals simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro serialized
  cases serialized <;> rfl

/-- Lowering the literal saved erase/write tail retains its optional result, complete source state and shared cache; the additional component ledger is only projected in this source equation. -/
theorem publication_source (sealed : Option RawCtxSourceSend.Encrypted)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    Prod.map id RawCtxSelectedReceiveCompiler.project <$>
      (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (publication pre application initial selector aux target sender saved material sealed)).run state =
      (PqxdhInitialBuilderContext.afterSend (serverAux pre application initial selector aux)
        saved.candidate saved.authenticated saved.metadata
        (PqxdhInitialPendingBuilder.selected sender saved.index saved.before) ((ready).advanced, sealed)).run
          (RawCtxSelectedReceiveCompiler.project state) := by
  unfold publication
  rw [← afterSend_simulate target sender saved material, PqxdhSelectedStateInterpreter.program]
  have projected := map_run_simulateQ_eq_of_query_map_eq
    (fun query => PqxdhSelectedStateInterpreter.evaluate
      (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (PqxdhSelectedCallbackCompiler.lower pre application initial selector aux
        (.inl (.inr (.inr (.inr (.inr query)))))))
    (serverAux pre application initial selector aux) RawCtxSelectedReceiveCompiler.project
    (fun query state => PqxdhSelectedInitialOwnerCompiler.external_project pre application initial selector aux
      source key read (.inr (.inr (.inr (.inr query)))) state)
    (PqxdhInitialBuilderContext.afterSend (fun query => PqxdhServerRegistrationPublication.AuxSpec.query query)
      saved.candidate saved.authenticated saved.metadata
      (PqxdhInitialPendingBuilder.selected sender saved.index saved.before) ((ready).advanced, sealed)) state
  simpa only [afterSend_simulate] using projected

noncomputable def builder (localState : Local A N C) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Result × InsState M P I D K A N C S B) := do
  let sealed ← RawCtxSelectedPendingSendCompiler.sealing source.crypto writer (RawCtxChainSend.nativeSeal id id ready)
  let published ← (publication pre application initial selector aux target sender saved material sealed).run localState
  let installed := PqxdhInitialPendingBuilder.reinstall saved.index saved.before (.ok published.1)
  ((simulateQ (insImpl pre application initial selector aux source writer prior (some parent) target nonce next
    sender route read mark monitor) (saved.outside installed.1)).run).run
      ((initialFront installed.2, published.2),
        (PqxdhInitialOriginContext.builtTrace trace origin installed.2 saved.index installed.1, none, false))

/-- The saved Server seal, original erasure and optional second writer, and the entire Post use one unchanged component interpreter. -/
theorem builder_evaluated (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (builder pre application initial selector aux source writer prior target nonce next mark sender route read monitor
          trace origin saved material state.1)).run state.2 = (do
      let sealed ← (RawCtxSelectedReceiveCompiler.evaluated source key read
        (RawCtxSelectedPendingSendCompiler.sealing source.crypto writer (RawCtxChainSend.nativeSeal id id ready))).run state
      let published ← (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (publication pre application initial selector aux target sender saved material sealed.1)).run sealed.2
      let installed := PqxdhInitialPendingBuilder.reinstall saved.index saved.before (.ok published.1)
      (simulateQ (insEvaluated pre application initial selector aux source writer prior (some parent) key target nonce next
        sender route read mark monitor) (RawCtxSelectedFamilyNonceCoupling.optionalClient (saved.outside installed.1))).run
        (((initialFront installed.2, published.2.1),
          (PqxdhInitialOriginContext.builtTrace trace origin installed.2 saved.index installed.1, none, false)), published.2.2)) := by
  simp only [builder, simulateQ_bind, StateT.run_bind, map_bind]
  simp only [RawCtxSelectedReceiveCompiler.evaluated, PqxdhSelectedStateInterpreter.evaluate,
    StateT.run, bind_map_left, PqxdhSelectedStateInterpreter.pair]
  apply bind_congr
  intro sealed
  apply bind_congr
  intro published
  let installed := PqxdhInitialPendingBuilder.reinstall saved.index saved.before (.ok published.1.1)
  have evaluated := congrArg (fun handler => handler.run
    (((initialFront installed.2, published.1.2),
      (PqxdhInitialOriginContext.builtTrace trace origin installed.2 saved.index installed.1, none, false)), published.2))
    (insEvaluated_program pre application initial selector aux source writer prior (some parent) key target nonce next
      sender route read mark monitor (saved.outside installed.1))
  exact evaluated

end Builder

section Complete
variable
    (qPost : Nat) (context : PqxdhInitialOriginContext.Context extra M P I D K Result Bool S B)
    (material : PqxdhOrderedChainHybrids.Material)
local notation "parent" => Entry.mk (PqxdhInitialBuilderContext.address context.original) material

/-- Execute the actual saved request and keep its original outside program alongside the complete instrumented state. -/
noncomputable def prepare (fits : PqxdhInitialOriginCertificates.Fits qPost context) (localState : Local A N C) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec
      (OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result × InsState M P I D K A N C S B) :=
  match context, fits with
  | ⟨.inl (.record request before outside inner), trace, _⟩, fits => do
      let result ← RawCtxSelectedPendingRoleCompiler.live source writer prior target nonce next read inner material fits.2
      pure (outside result.1, ((PqxdhLaterSavedRecord.afterRecord before result.2, localState),
        (PqxdhInitialOriginPost.record trace request result.1, none, false)))
  | ⟨.inl (.finish index before control candidate outside inner), trace, origin⟩, fits => do
      let result ← RawCtxSelectedPendingOwnerCompiler.owner source writer prior target nonce next read inner material fits.2
      let finished := PqxdhLaterSavedFinish.afterOwner index (initialFront before) control candidate result
      pure (outside finished.1, ((finished.2, localState),
        (PqxdhInitialOriginContext.finishedTrace trace origin index finished.1, none, false)))
  | ⟨.inr saved, trace, origin⟩, _ => do
      let ready := RawCtxChainSend.ready saved.pending (RawCtxInterpretedReceive.decodeResponse
        (RawCtxKdfRequestTable.fullResponse (realize parent target)))
      let sealed ← RawCtxSelectedPendingSendCompiler.sealing source.crypto writer (RawCtxChainSend.nativeSeal id id ready)
      let published ← (publication pre application initial selector aux target sender saved material sealed).run localState
      let installed := PqxdhInitialPendingBuilder.reinstall saved.index saved.before (.ok published.1)
      pure (saved.outside installed.1, ((initialFront installed.2, published.2),
        (PqxdhInitialOriginContext.builtTrace trace origin installed.2 saved.index installed.1, none, false)))

/-- The complete executable continuation has no explicit selected-key argument and never resets the component interpreter. -/
noncomputable def complete (fits : PqxdhInitialOriginCertificates.Fits qPost context) (localState : Local A N C) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Result × InsState M P I D K A N C S B) := do
  let prepared ← prepare pre application initial selector aux source writer prior target nonce next sender read qPost context material fits localState
  ((simulateQ (insImpl pre application initial selector aux source writer prior (some parent) target nonce next
    sender route read mark monitor) prepared.1).run).run prepared.2

/-- The complete actual saved request, including builder callbacks, hands its entire component poststate to the original adaptive Post compiler. -/
theorem complete_evaluated (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (complete pre application initial selector aux source writer prior target nonce next mark sender route read monitor
          qPost context material fits state.1)).run state.2 = (do
      let prepared ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (prepare pre application initial selector aux source writer prior target nonce next sender read
          qPost context material fits state.1)).run state.2
      (simulateQ (insEvaluated pre application initial selector aux source writer prior (some parent) key target nonce next
        sender route read mark monitor) (RawCtxSelectedFamilyNonceCoupling.optionalClient prepared.1.1)).run
        (prepared.1.2, prepared.2)) := by
  simp only [complete, simulateQ_bind, StateT.run_bind, map_bind]
  apply bind_congr
  intro prepared
  exact congrArg (fun handler => handler.run (prepared.1.2, prepared.2))
    (insEvaluated_program pre application initial selector aux source writer prior (some parent) key target nonce next
      sender route read mark monitor prepared.1.1)

/-- The compiled setup projects to the same complete saved-source continuation; every common source reply and publication outcome is retained. -/
theorem source_complete (fits : PqxdhInitialOriginCertificates.Fits qPost context)
    (state : RawCtxSelectedReceiveCompiler.State (Local A N C)) :
    (do
      let prepared ← (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (prepare pre application initial selector aux source writer prior target nonce next sender read
          qPost context material fits state.1)).run state.2
      Prod.map id (tracedProj key) <$>
        (simulateQ (tracedPlain pre application initial selector aux source writer prior (some parent) key target nonce next
          sender route read mark) prepared.1.1).run (insProject (prepared.1.2, prepared.2))) =
      PqxdhLaterSavedContext.complete pre application initial selector aux source writer prior key target nonce next mark
        sender route read qPost context material fits state := by
  rcases context with ⟨original, trace, origin⟩
  cases original with
  | inl original =>
      cases original with
      | record request before outside inner =>
          simp only [prepare, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
          simp only [PqxdhLaterSavedContext.complete, PqxdhLaterSavedRecord.selectedRecord,
            RawCtxSelectedReceiveCompiler.evaluated, StateT.run, bind_map_left,
            insProject, RawCtxSelectedReceiveCompiler.project]
          rfl
      | finish index before control candidate outside inner =>
          simp only [prepare, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
          simp only [PqxdhLaterSavedContext.complete, PqxdhLaterSavedFinish.selectedPendingFinish,
            RawCtxSelectedReceiveCompiler.evaluated, StateT.run, bind_map_left,
            insProject, RawCtxSelectedReceiveCompiler.project]
          rfl
  | inr saved =>
      simp only [prepare, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc]
      simp only [PqxdhLaterSavedContext.complete, PqxdhLaterSavedBuilder.selectedBuilder,
        RawCtxSelectedReceiveCompiler.evaluated, StateT.run, bind_map_left]
      apply bind_congr
      intro sealed
      have actual := publication_source pre application initial selector aux source key target sender read saved material
        sealed.1 (state.1, sealed.2)
      simp only [StateT.run] at actual
      rw [← actual]
      simp only [PqxdhSelectedStateInterpreter.evaluate, StateT.run, bind_map_left,
        PqxdhSelectedStateInterpreter.pair, Prod.map_def, id_eq, insProject, RawCtxSelectedReceiveCompiler.project]
      rfl

end Complete

end BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.record_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.record_evaluated
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.record_post_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.record_post_good
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.finish_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.finish_evaluated
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.publication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.publication_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.builder_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.builder_evaluated
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.complete_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.complete_evaluated
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.source_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterSavedPostCompiler.source_complete

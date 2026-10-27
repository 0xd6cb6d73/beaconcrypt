import BeaconcryptCore.Computational.PqxdhLaterChallengeInsidePublication
import BeaconcryptCore.Computational.PqxdhLaterChallengeInsideCache

/-! The real saved inside execution cannot yield the later marked target event at a still-missing predecessor input in the same initialized source cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded
open PqxdhInitialPostContext PqxdhRecordConfidentialityChallenge PqxdhFirstRecordConfidentiality
open PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhSecretInputKdf RawCtxSelectedParentTable RawCtxCursorLineage RawCtxSelectiveChainGame
variable {ι M P I D K X Response Shared : Type} {extra : OracleSpec ι} {S B : Nat}
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "Snapshot" => NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B

/-- Appending the original outside source schedule preserves the actual retained parent response and complete saved callback. -/
theorem parent_append {Value Result : Type}
    (next : Value → OracleComp (PostSpec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Bool S B) (output : FullOutput) :
    PqxdhInitialOriginContext.resume (X := X) (Response := Response) mark sender route decode
      (PqxdhLaterChallengeCapture.append next context)
      (PqxdhInitialParentBuilderContext.reply sender route decode
        (PqxdhLaterChallengeCapture.append next context).original output) =
    (PqxdhInitialOriginContext.resume mark sender route decode context
      (PqxdhInitialParentBuilderContext.reply sender route decode context.original output) >>=
        PqxdhLaterChallengeCapture.resumeOutside mark sender route decode next) := by
  rcases context with ⟨(⟨request, before, outside, inner⟩ | ⟨index, before, control, candidate, outside, inner⟩) | builder, trace, origin⟩
  all_goals simp only [PqxdhLaterChallengeCapture.append, PqxdhInitialOriginContext.resume,
    PqxdhInitialOriginContext.complete, PqxdhInitialParentBuilderContext.reply,
    simulateQ_bind, StateT.run_bind, bind_assoc]
  all_goals rfl

/-- Combining the actual source cache invariant, same cursor lineage and real retained callback counter excludes a complete true marked later-target event inside that callback. -/
theorem source_excluded {Local SourceA SourceN A N C : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))
    (ambient : Snapshot) (state reached : Local)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((handler owner number bit details.request.query).run details.request.before) ambient.1 ambient.2)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((handler owner number bit details.request.query).run details.request.before) ambient.1 ambient.2) state))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (atParent : PqxdhInitialBuilderContext.address details.callback.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState A N C)
    (result : (Bool × Snapshot) × PqxdhInitialNativeRetained.RetainedState A N C)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained source writer
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
      ((PqxdhInitialOriginContext.frame mark sender route decode details.callback).2
          (PqxdhInitialParentBuilderContext.reply sender route decode details.callback.original
            (RawCtxSelectedParentEntry.realize entry target)) >>=
        PqxdhLaterChallengeCapture.resumeOutside mark sender route decode
          (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next reply.1) reply.2))).run before))
    (root : RootOutput) (sourceState : PqxdhInitialOriginPostPath.State SourceA SourceN)
    (invariant : PqxdhInitialOriginPostPath.Invariant root owner ambient sourceState)
    (lineage : Lineage root sourceState.1.1.2)
    (missing : sourceState.1.1.2.1 (cursorAddress sourceState.1.1.2.2) = none)
    (position : number.val = sourceState.1.1.2.2.depth + 2)
    (accepted : result.1.1 = true) (published : ((owner, number), true) ∈ result.1.2.2.published) : False := by
  have absent : ((owner, number), true) ∉ ambient.2.published := by
    intro past
    exact PqxdhLaterCommonRisk.cached_beyond_cursor root number sourceState.1.1.2 lineage
      (invariant.2 number past) (by omega) missing
  obtain ⟨middle, callback, finalTarget, installed⟩ :=
    PqxdhLaterChallengeInsidePublication.inside_finish mark sender route decode owner number bit details classified
      selected selection impl ambient state reached cut
      (PqxdhInitialNativeRetained.retained source writer
        (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
      before _ result completed absent accepted published
  obtain ⟨record, returned, atNumber⟩ := finalTarget.2.1
  obtain ⟨kernel, present, counter⟩ := PqxdhLaterChallengeInsideRetained.resumed_kernel
    mark sender route decode owner number bit details classified selected selection impl
    ambient.1 ambient.2 state reached cut source writer prior entry target output external atParent before
    ((middle.1.1.2, middle.1.2), middle.2) middle.1.1.1 record returned (by simpa only [Prod.eta] using callback)
  have bound := PqxdhLaterChallengeInsideCache.marked_counter root owner ambient.1 ambient.2 sourceState
    invariant.1 lineage missing installed kernel present
  have sequence := congrArg (fun value : U64 => value.val) atNumber
  omega

/-- The actual complete captured source descriptor has the same inside-event exclusion; its original outside schedule and parent response are retained. -/
theorem frame_excluded {Local SourceA SourceN A N C : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → Local → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT Local ProbComp))
    (ambient : Snapshot) (state reached : Local)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((handler owner number bit details.request.query).run details.request.before) ambient.1 ambient.2)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((handler owner number bit details.request.query).run details.request.before) ambient.1 ambient.2) state))
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Bool S B)
    (joined : PqxdhLaterChallengeCapture.Joined owner number bit (context, details))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : RawCtxSelectedParentEntry.Entry) (target : RootOutput) (output : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (atParent : PqxdhInitialBuilderContext.address context.original = entry.address)
    (before : PqxdhInitialNativeRetained.RetainedState A N C)
    (result : (Bool × Snapshot) × PqxdhInitialNativeRetained.RetainedState A N C)
    (completed : result ∈ support ((simulateQ (PqxdhInitialNativeRetained.retained source writer
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
      (PqxdhInitialOriginContext.resume mark sender route decode context
        (PqxdhInitialParentBuilderContext.reply sender route decode context.original
          (RawCtxSelectedParentEntry.realize entry target)))).run before))
    (root : RootOutput) (sourceState : PqxdhInitialOriginPostPath.State SourceA SourceN)
    (invariant : PqxdhInitialOriginPostPath.Invariant root owner ambient sourceState)
    (lineage : Lineage root sourceState.1.1.2)
    (missing : sourceState.1.1.2.1 (cursorAddress sourceState.1.1.2.2) = none)
    (position : number.val = sourceState.1.1.2.2.depth + 2)
    (accepted : result.1.1 = true) (published : ((owner, number), true) ∈ result.1.2.2.published) : False := by
  change context = PqxdhLaterChallengeCapture.append
    (fun reply => PqxdhLaterChallengeCapture.wrapped owner number bit (details.request.next reply.1) reply.2)
    details.callback at joined
  subst context
  rw [PqxdhLaterChallengeSavedMonitor.append_address] at atParent
  rw [parent_append] at completed
  exact source_excluded mark sender route decode owner number bit details classified selected selection impl
    ambient state reached cut source writer prior entry target output external atParent before result completed
    root sourceState invariant lineage missing position accepted published

end BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded.parent_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded.parent_append

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded.source_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded.source_excluded

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded.frame_excluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideExcluded.frame_excluded

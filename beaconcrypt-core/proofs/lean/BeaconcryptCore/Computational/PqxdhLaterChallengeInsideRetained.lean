import BeaconcryptCore.Computational.PqxdhLaterChallengeInsideFirst
import BeaconcryptCore.Computational.PqxdhLaterChallengeRetainedSequence

/-! The complete actual inside-challenge source callback equals its saved continuation under the real retained interpreter, with the same native state and literal parent response. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeInsideRetained
open PqxdhInitialPostContext PqxdhFullSecretInputKdf PqxdhJointKdfGame
open PqxdhFirstRecordConfidentiality RawCtxSelectedParentTable
variable {ι M P I D K X Response Shared Result Origin A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The same syntactically reached original callback runs exactly as its full saved parent continuation; no state or response distribution is reconstructed. -/
theorem callback {State : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (front : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state reached : State)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace) state))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) (output : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (atParent : PqxdhInitialBuilderContext.address details.callback.original = entry.address)
    (backend : PqxdhInitialNativeRetained.RetainedState A N C) :
    (simulateQ (PqxdhInitialNativeRetained.retained source writer
      (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
      ((simulateQ (PqxdhInitialOriginPost.compiler (X := X) (Response := Response) mark sender route decode)
        ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before)).run
          (front, trace))).run backend =
      (simulateQ (PqxdhInitialNativeRetained.retained source writer
        (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
        ((PqxdhInitialOriginContext.frame mark sender route decode details.callback).2
          (PqxdhInitialParentBuilderContext.reply sender route decode details.callback.original
            (RawCtxSelectedParentEntry.realize entry target)))).run backend := by
  rw [(PqxdhLaterChallengeInsideFirst.cut_start mark sender route decode owner number bit details classified
    selected selection impl front trace state reached cut).2]
  exact PqxdhLaterChallengeRetainedHead.parent_execute source writer prior entry target output external
    mark sender route decode details.callback atParent backend

/-- A successful actual saved inside continuation returns the next record sequence of its literal pre-cut source kernel. -/
theorem resumed_kernel {State : Type} (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (sender : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Origin S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .inside)
    (selected : (Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (front : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B) (state reached : State)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route decode
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace) state))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (target : PqxdhSecretInputKdf.RootOutput) (output : FullOutput)
    (external : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response Shared)
      (PqxdhInitialBeaconAmbient.Ambient A N C))
    (atParent : PqxdhInitialBuilderContext.address details.callback.original = entry.address)
    (backend : PqxdhInitialNativeRetained.RetainedState A N C)
    (after : (PqxdhRecordConfidentialityChallenge.State ×
      (NativeFront M P I D K S B × PqxdhInitialOriginPost.Trace Origin S B)) ×
        PqxdhInitialNativeRetained.RetainedState A N C)
    (reply : (AdvSpec extra S B).Range details.request.query) (record : RawCtxSourceSend.Encrypted)
    (returned : after.1.1.reply = some (some record))
    (supported : (((reply, after.1.1), after.1.2), after.2) ∈ support
      ((simulateQ (PqxdhInitialNativeRetained.retained source writer
        (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external)
        ((PqxdhInitialOriginContext.frame mark sender route decode details.callback).2
          (PqxdhInitialParentBuilderContext.reply sender route decode details.callback.original
            (RawCtxSelectedParentEntry.realize entry target)))).run backend)) :
    ∃ kernel, RawCtxGenericRoleFamily.selectedKernel owner front.roles.1 = some kernel ∧
      record.sequence.val = kernel.control.send_sequence.val + 1 := by
  rw [← callback mark sender route decode owner number bit details classified selected selection impl
    front trace state reached cut source writer prior entry target output external atParent backend] at supported
  rcases details with ⟨⟨query, current, next⟩, context⟩
  cases used : current.pair with
  | some pair => simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
  | none =>
      rcases query with request | ⟨left, right⟩
      · simp only [PqxdhLaterChallengeSavedClassification.phase, used, reduceCtorEq] at classified
      · by_cases equal : left.length = right.length
        · exact PqxdhLaterChallengeRetainedSequence.challenge_kernel source writer
            (RawCtxSelectedMessageDriver.privateTable prior (some entry) target output) external mark sender route decode
            owner number bit left right equal current used front trace backend after reply record returned supported
        · simp only [PqxdhLaterChallengeSavedClassification.phase, used, equal, ite_false, reduceCtorEq] at classified

end BeaconcryptCore.Computational.PqxdhLaterChallengeInsideRetained

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideRetained.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideRetained.callback
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeInsideRetained.resumed_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeInsideRetained.resumed_kernel

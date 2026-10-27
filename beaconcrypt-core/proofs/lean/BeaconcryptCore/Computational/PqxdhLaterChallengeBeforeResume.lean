import BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification
import BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport

/-! Couple the same actual saved before-phase callback and its full monitored outside continuation, retaining optional refusal and explicit alias separation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResume
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared A N C Value Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (monitor : Fin B)

/-- Every all-reply result of an actual before-phase request leaves its challenge pair unused. This is source bookkeeping, without any crypto or state-origin premise. -/
theorem before_unused (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .before)
    (result : (AdvSpec extra S B).Range details.request.query × PqxdhRecordConfidentialityChallenge.State)
    (supported : result ∈ support ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before)) :
    result.2.pair = none := by
  rcases details with ⟨⟨query, current, outside⟩, callback⟩
  cases pair : current.pair with
  | none =>
      rcases query with request | ⟨left, right⟩
      · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run, mem_support_bind_iff,
          mem_support_pure_iff] at supported
        obtain ⟨reply, _, rfl⟩ := supported
        exact pair
      · by_cases equal : left.length = right.length
        · simp only [PqxdhLaterChallengeSavedClassification.phase, pair, equal, ite_true, reduceCtorEq] at classified
        · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run, ite_eq_left (Or.inr equal),
            mem_support_pure_iff] at supported
          simpa only [supported] using pair
  | some pair => simp only [PqxdhLaterChallengeSavedClassification.phase, pair, reduceCtorEq] at classified

/-- The same captured before-phase callback can be run in both challenge worlds with its whole optional mass. Every successful callback result is still unused, so the original carried continuation starts the existing monitored coupling from an unset marker. Parent/target separation remains explicit. -/
theorem resume_pre {Native : Type}
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (sourceBit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .before)
    (selected : (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B).Domain → Native → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B) (StateT Native ProbComp))
    (front : PqxdhInitialPostContext.NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Bool S B)
    (state reached : Native)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number sourceBit details.request.query).run details.request.before) front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number sourceBit details.request.query).run details.request.before) front trace) state))
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost details.callback) (localState : Local A N C)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠
      PqxdhInitialBuilderContext.address details.callback.original) :
    Pre (fun a b => a = b) (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux source writer prior target nonce next
        sender route read mark monitor owner number false details material qPost fits localState none)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux source writer prior target nonce next
        sender route read mark monitor owner number true details material qPost fits localState none) := by
  unfold PqxdhLaterChallengeSavedMonitor.resume
  apply pre_bind_refl
  intro callback supported
  rcases callback with ⟨_ | ⟨reply, current⟩, after⟩
  · exact Pre.pure rfl
  · have unused := before_unused owner number sourceBit details classified (reply, current)
      (PqxdhLaterSavedCompilerSupport.source_support pre application initial selector aux source writer prior target nonce next
        sender route read mark monitor selected selection impl
        ((PqxdhRecordConfidentialityChallenge.handler owner number sourceBit details.request.query).run details.request.before)
        front trace state reached qPost details.callback cut material fits localState (reply, current) after supported)
    exact pre_map (PqxdhLaterChallengeMonitor.program_pre pre application initial selector aux source writer prior
      ⟨PqxdhInitialBuilderContext.address details.callback.original, material⟩ target nonce next sender route read mark monitor
      owner number (details.request.next reply) current unused after separate)
      _ _ (fun _ _ same => by rw [same]) (fun _ dead => dead) (fun _ dead => dead)

end BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResume

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResume.before_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResume.before_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResume.resume_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeResume.resume_pre

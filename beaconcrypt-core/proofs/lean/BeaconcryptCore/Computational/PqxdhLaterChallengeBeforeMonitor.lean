import BeaconcryptCore.Computational.PqxdhLaterSavedCompilerSupport
import BeaconcryptCore.Computational.PqxdhLaterChallengeSavedClassification

/-! Before the admitted challenge, actual saved callbacks preserve the unused wrapper and enable the existing monitored two-world continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhFirstRecordConfidentiality
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Every ordinary or immediately rejected request before the chosen challenge returns an unused wrapper on every source reply path. -/
theorem callback_unused (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .before)
    (result : (AdvSpec extra S B).Range details.request.query × PqxdhRecordConfidentialityChallenge.State)
    (supported : result ∈ support ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run
      details.request.before)) : result.2.pair = none := by
  rcases details with ⟨⟨query, ⟨pair, reply, other⟩, next⟩, callback⟩
  rcases pair with _ | pair
  · rcases query with request | ⟨left, right⟩
    · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run, mem_support_bind_iff,
        mem_support_pure_iff] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
    · by_cases equal : left.length = right.length
      · simp only [PqxdhLaterChallengeSavedClassification.phase, equal, ite_true, reduceCtorEq] at classified
      · simp only [PqxdhRecordConfidentialityChallenge.handler, StateT.run] at supported
        rw [ite_eq_left (Or.inr equal), mem_support_pure_iff] at supported
        subst result
        rfl
  · simp only [PqxdhLaterChallengeSavedClassification.phase, reduceCtorEq] at classified

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

/-- An unused saved callback executes identically in both worlds, then runs its literal request continuation with an unset monitor. The only address inequality is the existing explicitly charged parent-alias event. -/
theorem resume_pre (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (material : PqxdhOrderedChainHybrids.Material) (qPost : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qPost details.callback)
    (unused : PqxdhLaterSavedOutsideSupport.Returns (fun result => result.2.pair = none) details.callback)
    (localState : Local A N C)
    (separate : RawCtxSelectedParentPrivatePatch.targetAddress target ≠
      PqxdhInitialBuilderContext.address details.callback.original) :
    Pre (fun a b => a = b) (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (fun result => PqxdhLaterChallengeMonitor.Dead result.2)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux source writer prior target nonce next sender route read
        mark monitor owner number false details material qPost fits localState none)
      (PqxdhLaterChallengeSavedMonitor.resume pre application initial selector aux source writer prior target nonce next sender route read
        mark monitor owner number true details material qPost fits localState none) := by
  unfold PqxdhLaterChallengeSavedMonitor.resume
  apply pre_bind_refl
  intro completed actual
  rcases completed with ⟨_ | ⟨reply, current⟩, after⟩
  · exact Pre.pure rfl
  · have stillUnused := PqxdhLaterSavedCompilerSupport.complete_returns pre application initial selector aux source writer prior target
      nonce next sender route read mark monitor (fun result => result.2.pair = none) qPost details.callback material fits unused
      localState (reply, current) after actual
    exact pre_map (PqxdhLaterChallengeMonitor.program_pre pre application initial selector aux source writer prior
      ⟨PqxdhInitialBuilderContext.address details.callback.original, material⟩ target nonce next sender route read mark monitor
      owner number (details.request.next reply) current stillUnused after separate)
      _ _ (fun _ _ same => by rw [same]) (fun _ dead => dead) (fun _ dead => dead)

/-- The actual supported before-phase callback cut supplies the unused-wrapper certificate consumed by `resume_pre`; it is proved from source syntax and is not an additional caller security premise. -/
theorem cut_unused {State : Type} (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (details : PqxdhLaterChallengeCapture.Details extra M P I D K Bool S B)
    (classified : PqxdhLaterChallengeSavedClassification.phase (some details) = .before)
    (selected : (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B).Domain → State → Bool)
    (selection : ∀ query state, selected query state = true → PqxdhInitialOriginForwardPost.selected query = true)
    (impl : QueryImpl (PqxdhInitialPostContext.Base extra RatchetChain I D K X Response Shared S B) (StateT State ProbComp))
    (front : PqxdhInitialPostContext.NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Bool S B)
    (state reached : State)
    (cut : RawCtxForwardScan.Cut.pending details.callback reached ∈ support
      (RawCtxForwardScan.scan PqxdhInitialOriginForwardPost.selected selected selection impl
        (PqxdhInitialOriginForwardPost.program mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace)
        (PqxdhInitialOriginForwardPost.program_covered mark sender route read
          ((PqxdhRecordConfidentialityChallenge.handler owner number bit details.request.query).run details.request.before) front trace) state)) :
    PqxdhLaterSavedOutsideSupport.Returns (fun result => result.2.pair = none) details.callback :=
  PqxdhLaterSavedOutsideSupport.scan_returns (fun result => result.2.pair = none) mark sender route read selected selection impl _
    (callback_unused owner number bit details classified) front trace state reached details.callback cut

end BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor.callback_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor.callback_unused
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor.resume_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor.resume_pre
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor.cut_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeMonitor.cut_unused

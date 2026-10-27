-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhLaterChallengeBeforeConsumer
import BeaconcryptCore.Computational.PqxdhLaterExecutableCertificates

/-! Derive both complete wrapper allowances from the original all-reply adversary budget at the actual source capture, before any cryptographic interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits
open PqxdhFirstRecordConfidentiality PqxdhInitialPostContext PqxdhInitialOriginForwardPost
open PqxdhLaterChallengeCapture RawCtxForwardTags PqxdhInitialBuilderContext
variable {ι M P I D K X Response Shared Origin Value Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Appending the literal complete outside program adds its all-reply budget and preserves every quiet inner certificate. -/
theorem append_fits (outside : Value → OracleComp (PostSpec extra S B) Result)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Value Origin S B)
    (qCallback qOutside : Nat)
    (fits : PqxdhInitialOriginCertificates.Fits qCallback context)
    (bounded : ∀ value, (outside value).IsTotalQueryBound qOutside) :
    PqxdhInitialOriginCertificates.Fits (qCallback + qOutside) (append outside context) := by
  rcases context with ⟨(⟨request, before, continuation, inner⟩ | ⟨index, before, control, candidate, continuation, inner⟩) | builder, trace, origin⟩
  case inr => exact fun reply => isTotalQueryBound_bind (fits reply) bounded
  all_goals exact ⟨fun reply => isTotalQueryBound_bind (fits.1 reply) bounded, fits.2⟩

/-- Either literal challenge world preserves the original all-reply adversary query cap from every actual wrapper state. -/
theorem wrapped_total (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (work : OracleComp (AdvSpec extra S B) Bool) (current : PqxdhRecordConfidentialityChallenge.State)
    (q : Nat) (bounded : work.IsTotalQueryBound q) :
    (wrapped owner number bit work current).IsTotalQueryBound q := by
  apply (isQueryBoundP_true_iff _ _).mp
  simp only [wrapped, isQueryBoundP_map_iff]
  apply PqxdhRecordConfidentialityChallenge.query_bound
  convert bounded.isQueryBoundP using 1

/-- One actual wrapper request makes at most one original Post request, including rejected challenge requests and both send directions. -/
theorem handler_total (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (query : (AdvSpec extra S B).Domain) (current : PqxdhRecordConfidentialityChallenge.State) :
    ((PqxdhRecordConfidentialityChallenge.handler owner number bit query).run current).IsTotalQueryBound 1 := by
  apply (isQueryBoundP_true_iff _ _).mp
  have bounded := PqxdhRecordConfidentialityChallenge.query_bound owner number bit (fun _ => True)
    ((AdvSpec extra S B).query query : OracleComp (AdvSpec extra S B) _) 1
    ((isQueryBoundP_query_iff _ _ _).mpr (fun _ => Nat.zero_lt_succ _)) current
  simpa only [simulateQ_spec_query] using bounded

/-- The original all-reply adversary allowance certifies both whole appended wrappers at every source-generated callback, without any probabilistic-support or successful-target premise. -/
theorem captured_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (sourceBit : Bool)
    (work : OracleComp (AdvSpec extra S B) Bool) (q : Nat) (bounded : work.IsTotalQueryBound q)
    (current : PqxdhRecordConfidentialityChallenge.State) (before : NativeFront M P I D K S B)
    (trace : PqxdhInitialOriginPost.Trace Origin S B) :
    All (fun capture => ∀ bit, PqxdhInitialOriginCertificates.Fits (1 + q)
      (PqxdhLaterChallengeScanCoupling.tagged owner number bit capture.2).1)
      (captured (X := X) (Response := Response) mark sender route read owner number sourceBit work current before trace) := by
  induction work using OracleComp.inductionOn generalizing current before trace with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    have nextBound : ∀ answer, (next answer).IsTotalQueryBound q :=
      fun answer => (bounded.2 answer).mono (Nat.sub_le q 1)
    change All _ (_ >>= _)
    refine bind_all _ _ _ ?_ (fun result => ih _ (nextBound _) _ _ _)
    refine map_all (PqxdhInitialOriginCertificates.Fits 1) _ _ ?_ _
      (PqxdhInitialOriginCertificates.post_fits mark sender route read _ 1
        (handler_total owner number sourceBit query current) before trace)
    intro context valid bit
    exact append_fits _ context 1 q valid (fun reply =>
      wrapped_total owner number bit (next reply.1) reply.2 q (nextBound reply.1))

/-- Both complete continuations at a later cut obey the same source allowance. Initial Builder cuts remain explicitly outside this predicate's claim. -/
noncomputable def BothFits (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (q : Nat)
    (tag : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B × Option (Details extra M P I D K Origin S B)) : Prop :=
  match tag.2 with
  | none => True
  | some details => ∀ bit, PqxdhInitialOriginCertificates.Fits (1 + q)
      (PqxdhLaterChallengeScanCoupling.tagged owner number bit details).1

/-- Every later callback in the literal initial Builder and adaptive continuation inherits the original all-reply adversary cap, for both wrapper bits. -/
theorem builder_fits (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (AdvSpec extra S B) Bool)
    (q : Nat) (bounded : ∀ reply, (adversary reply).IsTotalQueryBound q) :
    All (BothFits owner number q)
      (PqxdhLaterChallengeBuilderCapture.capturedBuilder (X := X) (Response := Response)
        mark origin sender route read index before trace source initial metadata ready owner number bit adversary) := by
  unfold PqxdhLaterChallengeBuilderCapture.capturedBuilder
  refine bind_all _ _ _ ?_ ?_
  · refine map_all (fun _ => True) (BothFits owner number q) _ ?_ _ (all_true _)
    intro context _
    trivial
  · intro result
    refine map_all _ (BothFits owner number q) _ ?_ _
      (captured_fits mark sender route read owner number bit (adversary result.1) q (bounded result.1)
        PqxdhRecordConfidentialityChallenge.initial result.2.1 result.2.2)
    intro context valid
    exact valid

/-- The actual shared source scanner inherits both complete wrapper caps at every supported later cut. -/
theorem shared_fits {A N C : Type}
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin) (origin : Origin)
    (sender : M → U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (index : Fin S) (before : NativeFront M P I D K S B) (trace : PqxdhInitialOriginPost.Trace Origin S B)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared)
      (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (application : Response → PqxdhNativeSharedPrefix.LocalCallback A N C (Option Pqxdh.Bytes))
    (initializer : PqxdhBeaconPhase2Shared.Secrets Shared →
      PqxdhNativeSharedPrefix.LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp))
    (initial : RustM (PqxdhInitialPendingPost.KernelOf RatchetChain)) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready)
    (owner : RawCtxProtocolReveals.Owner S B) (number : U64) (bit : Bool)
    (adversary : BuildResult → OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Bool)
    (q : Nat) (bounded : ∀ reply, (adversary reply).IsTotalQueryBound q)
    (depth : Nat) (state : PqxdhNativeSharedPrefix.Local A N C)
    (context : PqxdhInitialOriginContext.Context extra M P I D K Bool Origin S B)
    (details : Option (Details extra M P I D K Origin S B)) (reached : PqxdhNativeSharedPrefix.Local A N C)
    (supported : RawCtxForwardScan.Cut.pending (context, details) reached ∈ support
      (PqxdhLaterChallengeBuilderCapture.sharedCarried mark origin sender route read index before trace source writer stage pre application initializer selector aux
        initial metadata ready owner number bit adversary depth state)) :
    BothFits owner number q (context, details) := by
  exact shared_scan_all _ _ _ _ _ _ _
    (builder_fits mark origin sender route read index before trace source initial metadata ready owner number bit adversary q bounded)
    _ _ _ supported

end BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.append_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.append_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.wrapped_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.wrapped_total

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.handler_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.handler_total

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.captured_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.captured_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.builder_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.builder_fits

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.shared_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengeCapturedFits.shared_fits

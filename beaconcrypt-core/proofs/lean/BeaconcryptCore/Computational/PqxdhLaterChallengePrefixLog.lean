import BeaconcryptCore.Computational.PqxdhLaterChallengeSendLog

/-! Original adaptive wrapper prefixes retain the full chronological private-input log. Earlier challenge witnesses refer to that exact source execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog
open PqxdhJointKdf PqxdhJointKdfGame PqxdhInitialBeaconAmbient
variable {ι I D K X Response Shared A N C Result : Type} {extra : OracleSpec ι} {S B : Nat}
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C PqxdhInitialNativeAudit.InitialReply)
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))
local notation "Spec" => PqxdhInitialNativeAudit.Spec extra RatchetChain I D K X Response Shared S B
local notation "Backend" => PqxdhInitialNativeAudit.State A N C
local notation "impl" => PqxdhInitialNativeAudit.handler (S := S) (B := B) source writer stage pre application initial selector aux

variable {M P Origin : Type}
variable (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Origin)
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
local notation "Full" => (PqxdhInitialPendingPost.Front RatchetChain M P I D K S B ×
  PqxdhInitialOriginPost.Trace Origin S B) × Backend
local notation "postImpl" => PqxdhLaterChallengeCutChronology.postImpl mark sender route decode impl

/-- Every complete original Post callback retains all prior private inputs, including failed or repeated finish attempts. -/
theorem step_monotone (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (before : Full) (result : (PqxdhInitialGenericPost.Spec extra S B).Range query × Full)
    (supported : result ∈ support (((postImpl) query).run before)) :
    before.2.1.1.2 ⊆ result.2.2.1.1.2 := by
  simp only [PqxdhLaterChallengeCutChronology.postImpl, StateT.run, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  exact PqxdhLaterChallengeInputLog.program_monotone source writer stage pre application initial selector aux
    _ before.2 actual reached

/-- Arbitrary complete source Post programs preserve the same chronological log through every original callback and continuation. -/
theorem program_monotone (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (before : Full) (result : Result × Full)
    (supported : result ∈ support ((simulateQ postImpl work).run before)) :
    before.2.1.1.2 ⊆ result.2.2.1.1.2 := by
  rw [show before = (before.1, before.2) from rfl,
    PqxdhLaterChallengeCutChronology.post_program, support_map] at supported
  obtain ⟨actual, reached, rfl⟩ := supported
  exact PqxdhLaterChallengeInputLog.program_monotone source writer stage pre application initial selector aux
    _ before.2 actual reached

/-- Every reached prefix of the unchanged challenge wrapper retains earlier source inputs, including screened replies and refused challenges. -/
theorem reaches_monotone (owner : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (bit : Bool)
    (client rest : OracleComp (PqxdhFirstRecordConfidentiality.AdvSpec extra S B) Result)
    (current final : PqxdhRecordConfidentialityChallenge.State) (before after : Full)
    (reached : PqxdhRecordConfidentialityTrace.Reaches postImpl owner number bit
      client current before rest final after) :
    before.2.1.1.2 ⊆ after.2.1.1.2 := by
  induction reached with
  | here client current before =>
      exact List.Subset.refl _
  | later query next current before step rest final after actual tail ih =>
      exact List.Subset.trans
        (program_monotone source writer stage pre application initial selector aux mark sender route decode
          _ before step actual) ih

end BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog

/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog.step_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog.step_monotone
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog.program_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog.program_monotone
/-- info: 'BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog.reaches_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLaterChallengePrefixLog.reaches_monotone

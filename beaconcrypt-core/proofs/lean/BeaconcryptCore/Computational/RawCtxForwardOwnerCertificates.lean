import BeaconcryptCore.Computational.RawCtxForwardTags
import BeaconcryptCore.Computational.RawCtxForwardOwner
import BeaconcryptCore.Computational.RawCtxQuietOwnerTails

/-!
The source owner constructs quiet descriptors inside a single original request. Its saved outside source client is the actual zero-query continuation, and every remaining receive or send callback retains this fact. These are certificates of the carried data, not facts recovered by replacing that data with an equal-frame witness.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates
open RawCtxForwardOwner RawCtxForwardTags
open RawCtxQuietOwnerTails (Quiet)
variable {Metadata Result : Type}

/-- Every receive descriptor carries the original zero-query outside client, through all permitted skipped-key derivations. -/
theorem receive_quiet
    (before : Owner Metadata)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (later : ∀ result, All Quiet (after result))
    (effect : RawCtxChainReceive.Effect RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext) :
    All Quiet (receive before outside after effect) := by
  generalize depth : RawCtxChainReceive.effectRank effect = count
  induction count using Nat.strong_induction_on generalizing effect with
  | h count ih =>
    cases effect with
    | rejected entry context => simpa only [receive] using later (entry, .None)
    | openRequested pending =>
        rw [receive, query_all]
        exact ⟨(fun _ impossible => by cases impossible), fun _ => later _⟩
    | kdfRequested pending =>
        rw [receive, query_all]
        exact ⟨fun tag same => by cases same; exact quiet,
          fun reply => ih _ (depth ▸ RawCtxChainReceive.normalResume_rank pending reply) _ rfl⟩

/-- A send descriptor retains the original zero-query outside client before its seal callback and publication. -/
theorem send_quiet
    (before : Owner Metadata)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result)
    (after : (RawCtxPendingOwnerQueries.Kernel RatchetChain × Option RawCtxSourceSend.Encrypted) →
      OracleComp (Spec Metadata Result) (Result × Owner Metadata))
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (later : ∀ result, All Quiet (after result))
    (start : RawCtxChainSend.Start RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext) :
    All Quiet (send before outside after start) := by
  cases start with
  | exhausted entry context => exact later _
  | requested pending =>
      rw [send, query_all]
      refine ⟨fun tag same => by cases same; exact quiet, fun reply => ?_⟩
      rw [query_all]
      exact ⟨(fun _ impossible => by cases impossible), fun _ => later _⟩

/-- Zero source calls construct no descriptors, regardless of the local return value or full owner state. -/
theorem program_zero (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (bounded : client.IsTotalQueryBound 0)
    (state : Owner Metadata) (predicate : RawCtxSelectedFamilyContext.OwnerContext Metadata Result → Prop) :
    All predicate (program sender decode client state) := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client bounded
  trivial

/-- Every literal descriptor constructed inside one original owner request carries its actual zero-call outside continuation. -/
theorem program_quiet (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (bounded : client.IsTotalQueryBound 1)
    (state : Owner Metadata) : All Quiet (program sender decode client state) := by
  induction client using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query outside ih =>
      have quiet : ∀ reply, (outside reply).IsTotalQueryBound 0 := by
        simpa only [IsTotalQueryBound, isQueryBound_query_bind_iff, Nat.sub_self, zero_lt_one, true_and] using bounded
      have later : ∀ reply (updated : Owner Metadata), All Quiet (program sender decode (outside reply) updated) :=
        fun reply updated => program_zero sender decode _ (quiet reply) updated Quiet
      rw [program_query]
      rcases query with (plaintext | raw) | publicQuery
      all_goals dsimp only
      · split
        · exact later _ _
        · exact send_quiet _ _ _ quiet (fun result => later result.2 _) _
      · by_cases empty : raw.isEmpty = true
        · simp only [empty, if_true]
          exact later _ _
        · simp only [empty, Bool.false_eq_true, if_false]
          cases decoded : decode raw with
          | none => exact later _ _
          | some frame =>
            by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
            · simp only [valid, if_true]
              exact receive_quiet _ _ _ quiet (fun result => later (RawCtxChainOwner.publish state result).1 _) _
            · simp only [valid, if_false]
              exact later _ _
      · rw [query_all]
        exact ⟨(fun _ impossible => by cases impossible), fun _ => later _ _⟩

end BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.receive_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.receive_quiet
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.send_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.send_quiet

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.program_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.program_zero
/-- info: 'BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.program_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardOwnerCertificates.program_quiet

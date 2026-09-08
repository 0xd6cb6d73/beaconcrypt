import BeaconcryptCore.Computational.RawCtxChainReceive
import BeaconcryptCore.Computational.RawCtxKdfBudget

/-!
The opaque-chain receive driver retains the exact max(1,remaining) callback allowance. Zero/one phases cannot issue another KDF request, every typed reply decreases the allowance, and the complete adaptive driver preserves it. The existing actual source admission bound transports through checked chain/material/source interpretations, giving at most 51 KDF calls and one opening per receive.

Constant chain/material values occur only as proof witnesses for unchanged control/cost, not runtime values, callback restrictions, injectivity premises or a cryptographic distribution claim. Rejected and repeated attempts remain counted. These logical query bounds do not remove source control, copying, byte processing or deterministic primitive work, nor establish input freshness or live-reveal security. Snapshot, persistence and restoration services are excluded from this proof task.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxChainReceiveBounds
open RawCtxChainReceive

def kdfCost {Send Receive Material Context : Type} : Effect Send Receive Material Context → Nat
  | .kdfRequested pending => max 1 pending.remaining.val
  | _ => 0

/-- Actual zero/one source phases cannot issue another KDF request, for any typed chain/material reply. -/
theorem resume_small {Send Receive Material Context : Type}
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material)
    (small : pending.remaining.val ≤ 1) :
    ∃ next, resume pending (ok reply) = ok next ∧ kdfCost next = 0 := by
  by_cases hzero : pending.remaining = 0#u8
  · simp [resume, hzero, rejected, kdfCost]
  · have hone : pending.remaining = 1#u8 := by scalar_tac
    simp only [resume, hone, if_true, if_neg (by decide : (1#u8) ≠ 0#u8)]
    obtain ⟨advanced, hadvanced⟩ := control.advance_receive_target_total pending.working_control
    cases hseq : advanced.sequence <;> simp only [hadvanced, hseq, bind_tc_ok, rejected]
    all_goals first | exact ⟨_, rfl, rfl⟩ | skip
    rename_i targetSequence
    obtain ⟨valid, hvalid⟩ := refined.pending_receive_is_valid_ok pending.entry
      ⟨advanced.state, reply.1, pending.staged_slots, targetSequence, reply.2,
        pending.first_slot, pending.skipped⟩ pending.target
    simp only [hvalid, bind_tc_ok]
    repeat' first | exact ⟨_, rfl, rfl⟩ | split

/-- The actual callback allowance decreases by one for every typed reply, including malformed zero phases. -/
theorem resume_cost {Send Receive Material Context : Type}
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material) :
    kdfCost (normalResume pending reply) + 1 ≤ kdfCost (.kdfRequested pending) := by
  by_cases small : pending.remaining.val ≤ 1
  · obtain ⟨next, hnext, hcost⟩ := resume_small pending reply small
    have same := RustM.ok.inj ((normalResume_exact pending reply).symm.trans hnext)
    rw [same, hcost]
    simp only [kdfCost]
    omega
  · have decreasing := normalResume_rank pending reply
    cases hnext : normalResume pending reply with
    | rejected => simp [kdfCost]
    | openRequested => simp [kdfCost]
    | kdfRequested later =>
      simp only [hnext, effectRank] at decreasing
      simp only [kdfCost]
      omega

/-- Every complete adaptive continuation retains the refined KDF allowance. -/
theorem program_cost {Send Receive Material Context Plaintext : Type}
    (effect : Effect Send Receive Material Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP
      (fun request => request.isLeft = true) (kdfCost effect) := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [program]
    | openRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp [kdfCost]
    | kdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp only [Sum.isLeft, not_true_eq_false, false_or, if_true]
      refine ⟨by simp [kdfCost], fun reply => ?_⟩
      apply (ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl).mono
      have cost := resume_cost pending reply
      omega

/-- The original source window bound applies without any payload-validity or injectivity premise. -/
theorem begin_cost {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    kdfCost (normalBegin kernel target context) ≤ 51 := by
  let zero : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩
  let response : RatchetKdfResponse := ⟨⟨List.replicate 76 0#u8, by simp⟩⟩
  let material : Material → RatchetMaterial := fun _ => (RawCtxInterpretedReceive.decodeResponse response).2
  have bound := RawCtxKdfBudget.begin_cost ⟨RawCtxMaterialInterpretation.mapRefined material
    (RawCtxChainInterpretation.mapChains (fun _ : Send => zero) (fun _ : Receive => zero) kernel)⟩ target context
  rw [RawCtxInterpretedReceive.normalBegin_native, RawCtxInterpretedReceive.normalBegin_map,
    RawCtxChainReceive.normalBegin_native] at bound
  cases observed : normalBegin kernel target context
  all_goals simpa only [observed, kdfCost, RawCtxKdfBudget.kdfCost,
    RawCtxInterpretedReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect, nativeEffect,
    RawCtxInterpretedReceive.nativeKdf, RawCtxInterpretedReceive.mapKdf, nativeKdf] using bound

/-- Every original receive has at most 51 KDF calls under arbitrary typed replies and private chain values. -/
theorem receive_bound {Send Receive Material Context Plaintext : Type}
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    (execute (Plaintext := Plaintext) kernel target context).IsQueryBoundP
      (fun request => request.isLeft = true) 51 :=
  (program_cost _).mono (begin_cost kernel target context)

/-- The complete source skip driver makes at most one opening callback. -/
theorem program_open_bound {Send Receive Material Context Plaintext : Type}
    (effect : Effect Send Receive Material Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP (fun request => request.isRight = true) 1 := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [program]
    | openRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp
    | kdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp only [Sum.isRight, Bool.false_eq_true, not_false_eq_true, true_or, if_false, true_and]
      exact fun reply => ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl

end BeaconcryptCore.Computational.RawCtxChainReceiveBounds

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceiveBounds.resume_small' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceiveBounds.resume_small

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceiveBounds.resume_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceiveBounds.resume_cost

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceiveBounds.program_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceiveBounds.program_cost

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceiveBounds.begin_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceiveBounds.begin_cost

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceiveBounds.receive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceiveBounds.receive_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceiveBounds.program_open_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceiveBounds.program_open_bound

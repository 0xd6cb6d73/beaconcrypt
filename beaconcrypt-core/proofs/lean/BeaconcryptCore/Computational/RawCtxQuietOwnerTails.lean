import BeaconcryptCore.Computational.RawCtxSelectedFamilyContext
import BeaconcryptCore.Computational.RawCtxChainReceiveBounds

/-!
The actual singleton owner source request derives an original receive/send frame whose saved outside source client makes zero queries. All actual admission, parser, rejection and publication branches are retained. A private selected callback cannot arise in that quiet outside client. The exact frame and its resource evidence are produced together; no bound for an arbitrary Context is postulated. These statements are budget provenance for the actual source hierarchy, not a security assumption or a pending-completion cost bound.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxQuietOwnerTails
open RawCtxPendingOwnerTails RawCtxPendingOwnerQueries RawCtxQueryOccurrence RawCtxSelectedFamilyContext

/-- A source client with zero calls is an actual pure return; arbitrary local result values are retained. -/
theorem zero_pure {ι Result : Type} {spec : OracleSpec ι} (client : OracleComp spec Result)
    (bounded : client.IsTotalQueryBound 0) : ∃ result, client = pure result := by
  induction client using OracleComp.inductionOn with
  | pure result => exact ⟨result, rfl⟩
  | query_bind query next ih =>
      simp only [IsTotalQueryBound, isQueryBound_query_bind_iff] at bounded
      omega

def Quiet {Metadata Result : Type} : OwnerContext Metadata Result → Prop
  | .receive _ outside _ => ∀ reply, (outside reply).IsTotalQueryBound 0
  | .send _ outside _ => ∀ reply, (outside reply).IsTotalQueryBound 0

def QuietTail {Metadata Result : Type} (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query →
      OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain) (Result × Owner RatchetChain Metadata)) : Prop :=
  ∃ context : OwnerContext Metadata Result,
    (⟨query, next⟩ : OwnerFrame Metadata Result) = ownerFrame sender decode context ∧ Quiet context

private theorem no_occurrence {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxPendingOwnerTails.SourceSpec Result) (bounded : client.IsTotalQueryBound 0)
    (state : Owner RatchetChain Metadata)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query →
      OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain) (Result × Owner RatchetChain Metadata))
    (occurs : Occurs query next (program sender decode client state)) : False := by
  obtain ⟨value, rfl⟩ := zero_pure client bounded
  exact pure_impossible query next (value, state) occurs

set_option backward.isDefEq.respectTransparency false in
/-- A selected callback inside one original owner request captures only that request's actual zero-call outside continuation. -/
theorem step_tail {Metadata Result : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxPendingOwnerTails.SourceSpec.Domain)
    (outside : RawCtxPendingOwnerTails.SourceSpec.Range request → OracleComp RawCtxPendingOwnerTails.SourceSpec Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (state : Owner RatchetChain Metadata)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query →
      OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain) (Result × Owner RatchetChain Metadata))
    (occurs : Occurs query next (program sender decode
      ((RawCtxPendingOwnerTails.SourceSpec.query request : OracleComp RawCtxPendingOwnerTails.SourceSpec _) >>= outside) state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender decode query next := by
  rw [program_query] at occurs
  rcases request with (plaintext | raw) | externalRequest
  · simp only [compiler, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.sendOwner, StateT.run] at occurs
    by_cases empty : plaintext.isEmpty = true
    · simp only [empty, if_true, pure_bind] at occurs
      exact (no_occurrence sender decode _ (quiet none) _ query next occurs).elim
    · simp only [empty, Bool.false_eq_true, if_false, calls, bind_assoc, pure_bind] at occurs
      exact RawCtxPendingQueryTails.send_occurs (sendRest sender decode state outside)
        (QuietTail sender decode)
        (fun result innerQuery innerNext innerOccurs _ =>
          (no_occurrence sender decode _ (quiet result.2) _ innerQuery innerNext innerOccurs).elim)
        (fun pending => ⟨.send state outside pending, rfl, quiet⟩)
        (RawCtxChainSend.normalBegin state.kernel ⟨plaintext, state.expectedSender, sender, state.associatedData⟩)
        query next occurs selected
  · simp only [compiler, RawCtxChainOwner.ownerImpl, RawCtxChainOwner.rawReceive, StateT.run] at occurs
    by_cases empty : raw.isEmpty = true
    · simp only [empty, if_true, pure_bind] at occurs
      exact (no_occurrence sender decode _ (quiet .None) _ query next occurs).elim
    · simp only [empty, Bool.false_eq_true, if_false] at occurs
      cases decoded : decode raw with
      | none =>
          simp only [decoded, pure_bind] at occurs
          exact (no_occurrence sender decode _ (quiet .None) _ query next occurs).elim
      | some frame =>
          simp only [decoded] at occurs
          by_cases valid : RawCtxReceive.ValidFrame state.expectedSender state.associatedData frame
          · simp only [valid, if_true, calls, bind_assoc, pure_bind] at occurs
            exact RawCtxPendingQueryTails.receive_occurs (receiveRest sender decode state outside)
              (QuietTail sender decode)
              (fun result innerQuery innerNext innerOccurs _ =>
                (no_occurrence sender decode _ (quiet (RawCtxChainOwner.publish state result).1) _ innerQuery innerNext innerOccurs).elim)
              (fun pending => ⟨.receive state outside pending, rfl, quiet⟩)
              (RawCtxChainReceive.normalBegin state.kernel frame.sequence ⟨raw, frame, state.associatedData⟩)
              query next occurs selected
          · simp only [valid, if_false, pure_bind] at occurs
            exact (no_occurrence sender decode _ (quiet .None) _ query next occurs).elim
  · simp only [compiler, StateT.run, publicForward, bind_assoc, pure_bind] at occurs
    rcases query_cases query (.inr (.inr externalRequest)) next
      (fun reply => program sender decode (outside reply) state) occurs with same | ⟨reply, later⟩
    · have sameQuery := congrArg Sigma.fst same
      change query = .inr (.inr externalRequest) at sameQuery
      rw [sameQuery] at selected
      cases selected
    · exact (no_occurrence sender decode _ (quiet reply) state query next later).elim

/-- The exact singleton owner source request derives its captured zero-query continuation instead of assuming a bound for an arbitrary saved context. -/
theorem single_tail {Metadata : Type}
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxPendingOwnerTails.SourceSpec.Domain) (state : Owner RatchetChain Metadata)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query →
      OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
        (RawCtxPendingOwnerTails.SourceSpec.Range request × Owner RatchetChain Metadata))
    (occurs : Occurs query next (program sender decode (RawCtxPendingOwnerTails.SourceSpec.query request) state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender decode query next :=
  step_tail sender decode request (fun reply => pure reply) (fun _ => by trivial) state query next
    (by simpa only [bind_pure] using occurs) selected

end BeaconcryptCore.Computational.RawCtxQuietOwnerTails

/-- info: 'BeaconcryptCore.Computational.RawCtxQuietOwnerTails.zero_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietOwnerTails.zero_pure
/-- info: 'BeaconcryptCore.Computational.RawCtxQuietOwnerTails.step_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietOwnerTails.step_tail
/-- info: 'BeaconcryptCore.Computational.RawCtxQuietOwnerTails.single_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietOwnerTails.single_tail

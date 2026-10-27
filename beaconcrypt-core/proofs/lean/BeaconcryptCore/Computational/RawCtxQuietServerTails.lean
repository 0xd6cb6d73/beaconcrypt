import BeaconcryptCore.Computational.RawCtxQuietOwnerTails

/-!
An original singleton Server source request yields an exact owner/Server pending context whose captured source continuations make zero additional calls. The actual route lookup, peer lookup, associated-data choice and publication are retained. The owner witness comes from that original singleton owner request, not an arbitrary saved Tail. These statements provide source budget provenance for the later material-only completion and full family observer.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxQuietServerTails
open RawCtxPendingServerTails RawCtxPendingOwnerQueries RawCtxQueryOccurrence RawCtxSelectedFamilyContext
open RawCtxGenericRoleStorage RawCtxGenericServer

def Quiet {Metadata PeerMetadata Result : Type} : ServerContext Metadata PeerMetadata Result → Prop
  | .owner _ _ _ _ outside inner => (∀ reply, (outside reply).IsTotalQueryBound 0) ∧ RawCtxQuietOwnerTails.Quiet inner

def QuietTail {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata)) : Prop :=
  ∃ context : ServerContext Metadata PeerMetadata Result,
    (⟨query, next⟩ : ServerFrame Metadata PeerMetadata Result) = serverFrame sender route decode context ∧ Quiet context

private theorem no_occurrence {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxPendingServerTails.SourceSpec Result) (bounded : client.IsTotalQueryBound 0)
    (state : RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata))
    (occurs : Occurs query next (program sender route decode client state)) : False := by
  obtain ⟨value, rfl⟩ := RawCtxQuietOwnerTails.zero_pure client bounded
  exact pure_impossible query next (value, state) occurs

/-- The exact selected owner's singleton client and the actual Server installer retain zero-query source tails at both levels. -/
theorem owner_tail {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata)
    (kid : Std.U64) (peer : Peer (Kernel RatchetChain) PeerMetadata)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp RawCtxPendingServerTails.SourceSpec Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (owner : RawCtxPendingOwnerTails.Owner RatchetChain PeerMetadata)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata))
    (occurs : Occurs query next (liftOwner sender route decode before kid peer outside
      (RawCtxPendingOwnerTails.program (sender before.server.metadata) decode
        (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request)) owner)))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender route decode query next := by
  rcases RawCtxQueryOccurrenceComposition.bind_cases query next _ _ occurs with inside | continued
  · rcases inside with ⟨inner, innerOccurs, same⟩
    subst next
    obtain ⟨context, frame, quietContext⟩ := RawCtxQuietOwnerTails.single_tail (sender before.server.metadata) decode
      (.inl request) owner query inner innerOccurs selected
    refine ⟨.owner request before kid peer outside context, ?_, quiet, quietContext⟩
    exact congrArg (fun saved : OwnerFrame PeerMetadata (RawCtxMixedOwner.SourceSpec.Range request) =>
      (⟨saved.1, fun reply => liftOwner sender route decode before kid peer outside (saved.2 reply)⟩ :
        ServerFrame Metadata PeerMetadata Result)) frame
  · rcases continued with ⟨result, later⟩
    exact (no_occurrence sender route decode _ (quiet result.1) _ query next later).elim

/-- One original Server source request derives quiet captured owner and Server source tails while preserving the actual route and peer selection. -/
theorem step_tail {Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxPendingServerTails.SourceSpec.Domain)
    (outside : RawCtxPendingServerTails.SourceSpec.Range request → OracleComp RawCtxPendingServerTails.SourceSpec Result)
    (quiet : ∀ reply, (outside reply).IsTotalQueryBound 0)
    (state : RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (Result × RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata))
    (occurs : Occurs query next (program sender route decode
      ((RawCtxPendingServerTails.SourceSpec.query request : OracleComp RawCtxPendingServerTails.SourceSpec _) >>= outside) state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender route decode query next := by
  cases request with
  | inl request =>
    rcases request with ⟨plaintext, kid⟩
    cases found : state.server.peers kid with
    | some peer =>
      rw [send_selected sender route decode plaintext kid state peer found outside] at occurs
      exact owner_tail sender route decode (.inl plaintext) state kid peer outside quiet
        (selectedOwner kid (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer state.rawAttempts)
        query next occurs selected
    | none =>
      rw [program_query sender route decode (.inl (plaintext, kid)) outside state] at occurs
      simp only [StateT.run, serverImpl, sendServer, peerAssociatedData, found] at occurs
      exact (no_occurrence sender route decode _ (quiet none) _ query next occurs).elim
  | inr raw =>
    cases routed : route raw with
    | some kid =>
      cases found : state.server.peers kid with
      | some peer =>
        rw [raw_selected sender route decode raw kid state peer routed found outside] at occurs
        exact owner_tail sender route decode (.inr raw) state kid peer outside quiet
          (selectedOwner kid (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer state.rawAttempts)
          query next occurs selected
      | none =>
        rw [program_query sender route decode (.inr raw) outside state] at occurs
        simp only [StateT.run, serverImpl, rawServer, routed, peerAssociatedData, found] at occurs
        exact (no_occurrence sender route decode _ (quiet .None) _ query next occurs).elim
    | none =>
      rw [program_query sender route decode (.inr raw) outside state] at occurs
      simp only [StateT.run, serverImpl, rawServer, routed] at occurs
      exact (no_occurrence sender route decode _ (quiet .None) _ query next occurs).elim

/-- The literal singleton Server request discharges quiet owner and Server continuations from actual source syntax. -/
theorem single_tail {Metadata PeerMetadata : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxPendingServerTails.SourceSpec.Domain)
    (state : RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata)
    (query : (RawCtxPendingOwnerQueries.Spec RatchetChain).Domain)
    (next : (RawCtxPendingOwnerQueries.Spec RatchetChain).Range query → OracleComp (RawCtxPendingOwnerQueries.Spec RatchetChain)
      (RawCtxPendingServerTails.SourceSpec.Range request × RawCtxPendingServerTails.State RatchetChain Metadata PeerMetadata))
    (occurs : Occurs query next (program sender route decode (RawCtxPendingServerTails.SourceSpec.query request) state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : QuietTail sender route decode query next :=
  step_tail sender route decode request (fun reply => pure reply) (fun _ => by trivial) state query next
    (by simpa only [bind_pure] using occurs) selected

end BeaconcryptCore.Computational.RawCtxQuietServerTails

/-- info: 'BeaconcryptCore.Computational.RawCtxQuietServerTails.owner_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietServerTails.owner_tail
/-- info: 'BeaconcryptCore.Computational.RawCtxQuietServerTails.step_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietServerTails.step_tail
/-- info: 'BeaconcryptCore.Computational.RawCtxQuietServerTails.single_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxQuietServerTails.single_tail

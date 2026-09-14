import BeaconcryptCore.Computational.RawCtxGenericServer
import BeaconcryptCore.Computational.RawCtxPendingOwnerTails
import BeaconcryptCore.Computational.RawCtxQueryOccurrenceComposition

/-!
A selected pending KDF inside the actual Server frontend retains the complete pre-call Server, assigned peer and original outside Server client. Its inner continuation is derived from the actual single-owner source program. Publication changes the same selected peer before the external Server continuation resumes. These source provenance statements do not assume that arbitrary native functions can be retagged and do not establish freshness or secrecy.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingServerTails
open RawCtxGenericRoleStorage RawCtxGenericServer RawCtxPendingOwnerQueries
open RawCtxQueryOccurrence

abbrev State (Chain Metadata PeerMetadata : Type) := ServerState (Kernel Chain) Metadata PeerMetadata
abbrev SourceSpec := RawCtxServerMixed.SourceSpec

noncomputable def program {Chain Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State Chain Metadata PeerMetadata) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata) :=
  (simulateQ (serverImpl calls sender route decode) client).run state

noncomputable def afterOwner {Chain Metadata PeerMetadata Value Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (before : State Chain Metadata PeerMetadata) (kid : Std.U64) (peer : Peer (Kernel Chain) PeerMetadata)
    (outside : Value → OracleComp SourceSpec Result)
    (result : Value × RawCtxPendingOwnerTails.Owner Chain PeerMetadata) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata) :=
  program sender route decode (outside result.1)
    ⟨putPeer before.server kid peer result.2.kernel, result.2.rawAttempts⟩

noncomputable def liftOwner {Chain Metadata PeerMetadata Value Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (before : State Chain Metadata PeerMetadata) (kid : Std.U64) (peer : Peer (Kernel Chain) PeerMetadata)
    (outside : Value → OracleComp SourceSpec Result)
    (work : OracleComp (Spec Chain) (Value × RawCtxPendingOwnerTails.Owner Chain PeerMetadata)) :
    OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata) :=
  work >>= afterOwner sender route decode before kid peer outside

inductive Tail {Chain Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    (query : (Spec Chain).Domain) →
      ((Spec Chain).Range query → OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata)) → Prop where
  | original (request : RawCtxMixedOwner.SourceSpec.Domain)
      (before : State Chain Metadata PeerMetadata) (kid : Std.U64) (peer : Peer (Kernel Chain) PeerMetadata)
      (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp SourceSpec Result)
      (query : (Spec Chain).Domain)
      (inner : (Spec Chain).Range query → OracleComp (Spec Chain)
        (RawCtxMixedOwner.SourceSpec.Range request × RawCtxPendingOwnerTails.Owner Chain PeerMetadata))
      (origin : RawCtxPendingOwnerTails.Tail (sender before.server.metadata) decode query inner) :
      Tail sender route decode query
        (fun reply => liftOwner sender route decode before kid peer outside (inner reply))

private theorem owner_occurs {Chain Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State Chain Metadata PeerMetadata)
    (kid : Std.U64) (peer : Peer (Kernel Chain) PeerMetadata)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp SourceSpec Result)
    (owner : RawCtxPendingOwnerTails.Owner Chain PeerMetadata)
    (outsideGood : ∀ result query next, Occurs query next (afterOwner sender route decode before kid peer outside result) →
      RawCtxPendingMixedPrefix.ownerSelected query = true → Tail sender route decode query next)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata))
    (occurs : Occurs query next (liftOwner sender route decode before kid peer outside
      (RawCtxPendingOwnerTails.program (sender before.server.metadata) decode
        (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request)) owner)))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : Tail sender route decode query next := by
  rcases RawCtxQueryOccurrenceComposition.bind_cases query next _ _ occurs with inside | continued
  · rcases inside with ⟨inner, innerOccurs, same⟩
    subst next
    exact Tail.original request before kid peer outside query inner
      (RawCtxPendingOwnerTails.program_tail (sender before.server.metadata) decode _ owner query inner innerOccurs selected)
  · rcases continued with ⟨result, nextOccurs⟩
    exact outsideGood result query next nextOccurs selected

/-- The original Server operation completes before its original outside client receives the actual reply. -/
theorem program_query {Chain Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : SourceSpec.Domain) (outside : SourceSpec.Range request → OracleComp SourceSpec Result)
    (state : State Chain Metadata PeerMetadata) :
    program sender route decode (SourceSpec.query request >>= outside) state =
      (do let result ← (serverImpl calls sender route decode request).run state
          program sender route decode (outside result.1) result.2) := rfl

/-- A routed raw operation invokes the exact original selected-owner source program, then the same full Server publication and outside client. -/
theorem raw_selected {Chain Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (kid : Std.U64) (state : State Chain Metadata PeerMetadata)
    (peer : Peer (Kernel Chain) PeerMetadata) (routed : route raw = some kid)
    (found : state.server.peers kid = some peer)
    (outside : core.option.Option RawCtxWholeOwner.Decrypted → OracleComp SourceSpec Result) :
    program sender route decode (SourceSpec.query (.inr raw) >>= outside) state =
      liftOwner sender route decode state kid peer outside
        (RawCtxPendingOwnerTails.program (sender state.server.metadata) decode
          (RawCtxSelectedPublicTrace.SourceSpec.query (.inl (.inr raw)))
          (selectedOwner kid (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer state.rawAttempts)) := by
  rw [program_query sender route decode (.inr raw) outside state]
  simp [StateT.run, serverImpl, rawServer, routed, peerAssociatedData, found,
    liftOwner, RawCtxPendingOwnerTails.program, RawCtxPendingOwnerQueries.compiler,
    RawCtxChainOwner.ownerImpl]
  rfl

/-- A selected send completes its original owner operation before updating the same peer and continuing the original Server client. -/
theorem send_selected {Chain Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (kid : Std.U64) (state : State Chain Metadata PeerMetadata)
    (peer : Peer (Kernel Chain) PeerMetadata) (found : state.server.peers kid = some peer)
    (outside : Option RawCtxSourceSend.Encrypted → OracleComp SourceSpec Result) :
    program sender route decode (SourceSpec.query (.inl (plaintext, kid)) >>= outside) state =
      liftOwner sender route decode state kid peer outside
        (RawCtxPendingOwnerTails.program (sender state.server.metadata) decode
          (RawCtxSelectedPublicTrace.SourceSpec.query (.inl (.inl plaintext)))
          (selectedOwner kid (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer state.rawAttempts)) := by
  rw [program_query sender route decode (.inl (plaintext, kid)) outside state]
  simp [StateT.run, serverImpl, sendServer, peerAssociatedData, found,
    liftOwner, RawCtxPendingOwnerTails.program, RawCtxPendingOwnerQueries.compiler,
    RawCtxChainOwner.ownerImpl]
  rfl

/-- Every selected occurrence in the actual adaptive Server program derives an original owner tail, exact peer publication and original outside client. -/
theorem program_tail {Chain Metadata PeerMetadata Result : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State Chain Metadata PeerMetadata)
    (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata))
    (occurs : Occurs query next (program sender route decode client state))
    (selected : RawCtxPendingMixedPrefix.ownerSelected query = true) : Tail sender route decode query next := by
  induction client using OracleComp.inductionOn generalizing state query next with
  | pure value => exact (pure_impossible query next (value, state) occurs).elim
  | query_bind request outside ih =>
    cases request with
    | inl request =>
      rcases request with ⟨plaintext, kid⟩
      cases found : state.server.peers kid with
      | some peer =>
        rw [send_selected sender route decode plaintext kid state peer found outside] at occurs
        exact owner_occurs sender route decode (.inl plaintext) state kid peer outside
          (selectedOwner kid (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer state.rawAttempts)
          (fun result innerQuery innerNext innerOccurs innerSelected =>
            ih result.1 ⟨putPeer state.server kid peer result.2.kernel, result.2.rawAttempts⟩ innerQuery innerNext innerOccurs innerSelected)
          query next occurs selected
      | none =>
        rw [program_query sender route decode (.inl (plaintext, kid)) outside state] at occurs
        simp only [StateT.run, serverImpl, sendServer, peerAssociatedData, found] at occurs
        exact ih none state query next occurs selected
    | inr raw =>
      cases routed : route raw with
      | some kid =>
        cases found : state.server.peers kid with
        | some peer =>
          rw [raw_selected sender route decode raw kid state peer routed found outside] at occurs
          exact owner_occurs sender route decode (.inr raw) state kid peer outside
            (selectedOwner kid (RawCtxServerRouting.associatedBytes state.server.identity peer.identity) peer state.rawAttempts)
            (fun result innerQuery innerNext innerOccurs innerSelected =>
              ih result.1 ⟨putPeer state.server kid peer result.2.kernel, result.2.rawAttempts⟩ innerQuery innerNext innerOccurs innerSelected)
            query next occurs selected
        | none =>
          rw [program_query sender route decode (.inr raw) outside state] at occurs
          simp only [StateT.run, serverImpl, rawServer, routed, peerAssociatedData, found] at occurs
          exact ih .None {state with rawAttempts := state.rawAttempts + 1} query next occurs selected
      | none =>
        rw [program_query sender route decode (.inr raw) outside state] at occurs
        simp only [StateT.run, serverImpl, rawServer, routed] at occurs
        exact ih .None {state with rawAttempts := state.rawAttempts + 1} query next occurs selected

/-- A supported original Server cut derives its concrete tail from the same actual program and reached primitive state. -/
theorem reached_tail {Chain Metadata PeerMetadata Result PrimitiveState : Type}
    (sender : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (server : State Chain Metadata PeerMetadata)
    (impl : QueryImpl (Spec Chain) (StateT PrimitiveState ProbComp)) (index : Nat)
    (initial reached : PrimitiveState) (query : (Spec Chain).Domain)
    (next : (Spec Chain).Range query → OracleComp (Spec Chain) (Result × State Chain Metadata PeerMetadata))
    (supported : (RawCtxPendingMixedPrefix.Stopped.pending query next, reached) ∈
      support (RawCtxPendingMixedPrefix.scan RawCtxPendingMixedPrefix.ownerSelected impl
        (program sender route decode client server) index initial)) : Tail sender route decode query next := by
  exact program_tail sender route decode client server query next
    (RawCtxQueryOccurrence.scan_occurs _ impl _ index initial reached query next supported)
    (RawCtxPendingMixedPrefix.pending_selected _ impl _ index initial reached query next supported)

end BeaconcryptCore.Computational.RawCtxPendingServerTails

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingServerTails.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingServerTails.program_query

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingServerTails.raw_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingServerTails.raw_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingServerTails.send_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingServerTails.send_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingServerTails.program_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingServerTails.program_tail

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingServerTails.reached_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingServerTails.reached_tail

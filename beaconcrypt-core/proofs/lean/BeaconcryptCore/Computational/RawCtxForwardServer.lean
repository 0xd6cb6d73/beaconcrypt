import BeaconcryptCore.Computational.RawCtxForwardOwner
import BeaconcryptCore.Computational.RawCtxForwardAnnotationComposition

/-!
The Server compiler attaches the selected peer and original outside Server client to the descriptor carried by its actual owner operation. It performs the source routing and peer admission before compiling that owner, then reinstalls its complete returned kernel before the outside client resumes. Descriptor construction runs forward with the source program and uses no inverse of a saved continuation.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxForwardServer
open RawCtxSelectedFamilyContext RawCtxGenericServer RawCtxForwardAnnotation
open RawCtxGenericRoleStorage

abbrev Base := RawCtxPendingOwnerQueries.Spec RatchetChain
abbrev Spec (Metadata PeerMetadata Result : Type) :=
  RawCtxForwardAnnotation.Spec (ServerContext Metadata PeerMetadata Result) Base
abbrev State (Metadata PeerMetadata : Type) := NativeServer Metadata PeerMetadata
abbrev SourceSpec := RawCtxServerMixed.SourceSpec

noncomputable def owner {M P Result : Type}
    (sender : M → Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State M P) (kid : Std.U64)
    (peer : Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp SourceSpec Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P →
      OracleComp (Spec M P Result) (Result × State M P)) :
    OracleComp (Spec M P Result) (Result × State M P) := do
  let result ← mapTags (fun inner => ServerContext.owner request before kid peer outside inner)
    (RawCtxForwardOwner.program (sender before.server.metadata) decode
      (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
      (selectedOwner kid (RawCtxServerRouting.associatedBytes before.server.identity peer.identity) peer before.rawAttempts))
  after result.1 ⟨putPeer before.server kid peer result.2.kernel, result.2.rawAttempts⟩

noncomputable def program {M P Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) : State M P → OracleComp (Spec M P Result) (Result × State M P) :=
  OracleComp.recOn client (fun result state => pure (result, state))
    (fun request outside recurse state => match request with
      | .inl (plaintext, kid) => match state.server.peers kid with
        | none => recurse none state
        | some peer => owner sender decode (.inl plaintext) state kid peer outside recurse
      | .inr raw => match route raw with
        | none => recurse .None {state with rawAttempts := state.rawAttempts + 1}
        | some kid => match state.server.peers kid with
          | none => recurse .None {state with rawAttempts := state.rawAttempts + 1}
          | some peer => owner sender decode (.inr raw) state kid peer outside recurse)

/-- The forward compiler dispatches one actual Server request before recursively compiling the original outside client. -/
theorem program_query {M P Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : SourceSpec.Domain) (outside : SourceSpec.Range request → OracleComp SourceSpec Result)
    (state : State M P) :
    program sender route decode (SourceSpec.query request >>= outside) state =
      (match request with
      | .inl (plaintext, kid) => match state.server.peers kid with
        | none => program sender route decode (outside none) state
        | some peer => owner sender decode (.inl plaintext) state kid peer outside
            (fun reply updated => program sender route decode (outside reply) updated)
      | .inr raw => match route raw with
        | none => program sender route decode (outside .None) {state with rawAttempts := state.rawAttempts + 1}
        | some kid => match state.server.peers kid with
          | none => program sender route decode (outside .None) {state with rawAttempts := state.rawAttempts + 1}
          | some peer => owner sender decode (.inr raw) state kid peer outside
              (fun reply updated => program sender route decode (outside reply) updated)) := by
  rcases request with ⟨plaintext, kid⟩ | raw <;> rfl

/-- Erasing the concrete owner descriptor retains the full original owner operation, same-peer publication and exact original outside Server client. -/
theorem owner_erase {M P Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State M P) (kid : Std.U64)
    (peer : Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp SourceSpec Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P →
      OracleComp (Spec M P Result) (Result × State M P))
    (after_erase : ∀ reply updated, simulateQ erase (after reply updated) =
      RawCtxPendingServerTails.program sender route decode (outside reply) updated) :
    simulateQ erase (owner sender decode request before kid peer outside after) =
      RawCtxPendingServerTails.liftOwner sender route decode before kid peer outside
        (RawCtxPendingOwnerTails.program (sender before.server.metadata) decode
          (RawCtxSelectedPublicTrace.SourceSpec.query (.inl request))
          (selectedOwner kid (RawCtxServerRouting.associatedBytes before.server.identity peer.identity) peer before.rawAttempts)) := by
  simp only [owner, simulateQ_bind, erase_mapTags, RawCtxForwardOwner.program_erase, after_erase,
    RawCtxPendingServerTails.liftOwner]
  rfl

/-- The complete forward Server interpreter erases to the actual source routing, peer operations and all adaptive outside continuations. -/
theorem program_erase {M P Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State M P) :
    simulateQ erase (program sender route decode client state) =
      RawCtxPendingServerTails.program sender route decode client state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind request outside ih =>
    rw [program_query]
    rcases request with ⟨plaintext, kid⟩ | raw
    case inr =>
      cases routed : route raw with
      | some kid =>
        cases found : state.server.peers kid with
        | some peer =>
          simp only [routed, found]
          exact (owner_erase sender route decode (.inr raw) state kid peer outside _ ih).trans
            (RawCtxPendingServerTails.raw_selected sender route decode raw kid state peer routed found outside).symm
        | none =>
          rw [RawCtxPendingServerTails.program_query sender route decode (.inr raw) outside state]
          simp [routed, found, ih, serverImpl, rawServer,
            peerAssociatedData, StateT.run]
      | none =>
        rw [RawCtxPendingServerTails.program_query sender route decode (.inr raw) outside state]
        simp [routed, ih, serverImpl, rawServer, StateT.run]
    case inl =>
      cases found : state.server.peers kid with
      | some peer =>
        simp only [found]
        exact (owner_erase sender route decode (.inl plaintext) state kid peer outside _ ih).trans
          (RawCtxPendingServerTails.send_selected sender route decode plaintext kid state peer found outside).symm
      | none =>
        rw [RawCtxPendingServerTails.program_query sender route decode (.inl (plaintext, kid)) outside state]
        simp [found, ih, serverImpl, sendServer, peerAssociatedData, StateT.run]

/-- Every carried Server descriptor reconstructs the entire erased owner continuation, peer publication and adaptive outside client. -/
theorem owner_sound {M P Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State M P) (kid : Std.U64)
    (peer : Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp SourceSpec Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P →
      OracleComp (Spec M P Result) (Result × State M P))
    (after_erase : ∀ reply updated, simulateQ erase (after reply updated) =
      RawCtxPendingServerTails.program sender route decode (outside reply) updated)
    (after_sound : ∀ reply updated, Sound (serverFrame sender route decode) (after reply updated)) :
    Sound (serverFrame sender route decode) (owner sender decode request before kid peer outside after) := by
  apply RawCtxForwardAnnotationComposition.sound_map_bind
    (ownerFrame (sender before.server.metadata) decode) (serverFrame sender route decode)
    (fun inner => ServerContext.owner request before kid peer outside inner) _ _
    (RawCtxForwardOwner.program_sound _ _ _ _) (fun result => after_sound result.1 _)
  simp only [serverFrame, RawCtxForwardAnnotationComposition.appendFrame, after_erase, RawCtxPendingServerTails.liftOwner]
  intro tag; rfl

/-- The actual complete Server client carries exact source descriptors under every adaptive response. -/
theorem program_sound {M P Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State M P) :
    Sound (serverFrame sender route decode) (program sender route decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact sound_pure _ _
  | query_bind request outside ih =>
    rw [program_query]
    rcases request with ⟨plaintext, kid⟩ | raw
    all_goals dsimp only
    all_goals (repeat' first | split | exact ih _ _ | exact owner_sound sender route decode _ _ _ _ _ _ (fun reply updated => program_erase sender route decode (outside reply) updated) ih)

/-- Every owner derivation remains annotated through the Server's peer installation and complete outside continuation. -/
theorem owner_covered {M P Result : Type}
    (sender : M → Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (request : RawCtxMixedOwner.SourceSpec.Domain) (before : State M P) (kid : Std.U64)
    (peer : Peer (RawCtxPendingOwnerQueries.Kernel RatchetChain) P)
    (outside : RawCtxMixedOwner.SourceSpec.Range request → OracleComp SourceSpec Result)
    (after : RawCtxMixedOwner.SourceSpec.Range request → State M P →
      OracleComp (Spec M P Result) (Result × State M P))
    (after_covered : ∀ reply updated, RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (after reply updated)) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (owner sender decode request before kid peer outside after) := by
  exact RawCtxForwardAnnotationComposition.covered_map_bind _ _ _ _
    (RawCtxForwardOwner.program_covered _ _ _ _) (fun result => after_covered result.1 _)

/-- The entire actual Server client annotates exactly its private derivations for every adaptive reply and routing outcome. -/
theorem program_covered {M P Result : Type}
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp SourceSpec Result) (state : State M P) :
    RawCtxForwardCoverage.Covered RawCtxPendingMixedPrefix.ownerSelected (program sender route decode client state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => exact RawCtxForwardCoverage.covered_pure _ _
  | query_bind request outside ih =>
    rw [program_query]
    rcases request with ⟨plaintext, kid⟩ | raw
    all_goals dsimp only
    all_goals (repeat' first | split | exact ih _ _ | exact owner_covered sender decode _ _ _ _ _ _ ih)

end BeaconcryptCore.Computational.RawCtxForwardServer

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardServer.program_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardServer.program_query

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardServer.owner_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardServer.owner_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardServer.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardServer.program_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardServer.owner_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardServer.owner_sound

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardServer.program_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardServer.program_sound

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardServer.owner_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardServer.owner_covered

/-- info: 'BeaconcryptCore.Computational.RawCtxForwardServer.program_covered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxForwardServer.program_covered

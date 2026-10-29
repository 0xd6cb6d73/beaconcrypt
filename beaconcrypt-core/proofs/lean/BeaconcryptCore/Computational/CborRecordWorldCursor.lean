-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldClient
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocol
import BeaconcryptCore.Computational.RawCtxReceiveSendFields

/-!
Public sending cursors are projections of actual stored source control. Record advancement and receive stability below are derived from the complete native programs, including failed writers, failed authentication, malformed original kernels and exhausted counters. No invariant is imposed on arbitrary abstract knownReceive replies.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRecordWorldCursor
open PqxdhRecordLiftInterface
open CborRecordWorldClient (Cursor Shell advance)
variable {n : Nat} {Metadata Primitive ι : Type} {base : OracleSpec ι}

/-- The actual whole-owner send advances once on every nonempty, nonexhausted attempt, irrespective of its optional ciphertext. -/
theorem send_cursor
    (native : QueryImpl RawCtxSourceSend.PrimitiveSpec (StateT Primitive (OracleComp base)))
    (sender : Std.U64) (plaintext : Pqxdh.Bytes)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : Primitive)
    (result : (Option RawCtxSourceSend.Encrypted × RawCtxWholeOwner.OwnerState Metadata) × Primitive)
    (supported : result ∈ support (RawCtxSourceSend.sendGame native sender plaintext owner primitive)) :
    result.1.2.owner.kernel.refined.control.send_sequence.val =
      advance plaintext owner.owner.kernel.refined.control.send_sequence.val := by
  cases empty : plaintext.isEmpty with
  | true =>
      simp only [RawCtxSourceSend.sendGame, StateT.run, RawCtxSourceSend.sendOwner, empty, ite_true,
        simulateQ_pure, ] at supported
      subst result
      simp only [advance, empty, ite_true]
  | false =>
      by_cases top : owner.owner.kernel.refined.control.send_sequence = core.num.U64.MAX
      · simp only [RawCtxSourceSend.sendGame, StateT.run, RawCtxSourceSend.sendOwner, empty, Bool.false_eq_true,
          ite_false, RawCtxSourceSend.send_exhausted _ _ top,
          pure_bind, simulateQ_pure, ] at supported
        subst result
        simp [advance, empty, top]
      · have different : owner.owner.kernel.refined.control.send_sequence.val ≠ core.num.U64.MAX.val :=
          fun same => top (UScalar.eq_of_val_eq same)
        have below : owner.owner.kernel.refined.control.send_sequence.val < core.num.U64.MAX.val := by
          simp [core.num.U64.MAX, U64.rMax] at different ⊢
          scalar_tac
        have step := (RawCtxSourceSend.sendGame_active_state native sender plaintext owner primitive
          empty top result supported).1
        simpa only [advance, empty, Bool.false_eq_true, ite_false, below, ite_true] using step

/-- Every actual raw receive preserves the sending cursor, through all decoder, validation and optional opening outcomes. -/
theorem receive_cursor
    (native : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT Primitive (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : Primitive)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Metadata) × Primitive)
    (supported : result ∈ support (RawCtxWholeOwner.rawGame native decode raw owner primitive)) :
    result.1.2.owner.kernel.refined.control.send_sequence = owner.owner.kernel.refined.control.send_sequence := by
  simp only [RawCtxWholeOwner.rawGame, StateT.run, RawCtxWholeOwner.rawReceive] at supported
  split at supported
  · simp only [simulateQ_pure, ] at supported
    subst result
    rfl
  · split at supported
    · simp only [simulateQ_pure, ] at supported
      subst result
      rfl
    · rename_i frame decoded
      split at supported
      · simp only [simulateQ_bind, simulateQ_pure, ← QueryImpl.simulateQ_compose] at supported
        change result ∈ support (do
          let opened ← (simulateQ (native ∘ₛ RawCtxWholeOwner.adapter)
            (RawCtxOwnerOracle.receive owner.owner.kernel frame.sequence
              ⟨raw, frame, owner.owner.associatedData⟩)).run primitive
          pure (RawCtxWholeOwner.publish owner opened.1, opened.2)) at supported
        simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
        obtain ⟨opened, reached, same⟩ := supported
        subst result
        exact (RawCtxReceiveSendFields.receive_fields (native ∘ₛ RawCtxWholeOwner.adapter)
          primitive owner.owner.kernel frame.sequence ⟨raw, frame, owner.owner.associatedData⟩ opened reached).2
      · simp only [simulateQ_pure, ] at supported
        subst result
        rfl

/-- Native mixed dispatch keeps the same cursor law while forwarding all primitive effects unchanged. -/
theorem mixed_cursor
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp base)))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : RawCtxWholeOwner.OwnerState Metadata) (primitive : Primitive)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × RawCtxWholeOwner.OwnerState Metadata) × Primitive)
    (supported : result ∈ support ((simulateQ native
      ((RawCtxMixedOwner.ownerImpl sender decode query).run owner)).run primitive)) :
    result.1.2.owner.kernel.refined.control.send_sequence.val =
      match query with
      | .inl plaintext => advance plaintext owner.owner.kernel.refined.control.send_sequence.val
      | .inr _ => owner.owner.kernel.refined.control.send_sequence.val := by
  cases query with
  | inl plaintext =>
      apply send_cursor (native ∘ₛ RawCtxMixedOwner.sendAdapter) sender plaintext owner primitive result
      simpa only [RawCtxMixedOwner.ownerImpl, StateT.run, ← QueryImpl.simulateQ_compose,
        RawCtxSourceSend.sendGame] using supported
  | inr raw =>
      apply congrArg UScalar.val
      apply receive_cursor (native ∘ₛ RawCtxMixedOwner.receiveAdapter) decode raw owner primitive result
      simpa only [RawCtxMixedOwner.ownerImpl, StateT.run, ← QueryImpl.simulateQ_compose,
        RawCtxWholeOwner.rawGame] using supported

/-- Forgetting the private writer log retains the actual record result and primitive poststate. -/
theorem logged_support {Result : Type}
    (native : QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive (OracleComp base)))
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (primitive : Primitive)
    (result : (Result × List PqxdhDeploymentNative.Frame) × Primitive)
    (supported : result ∈ support ((simulateQ native (PqxdhDeploymentNative.logged work)).run primitive)) :
    (result.1.1, result.2) ∈ support ((simulateQ native work).run primitive) := by
  rw [← PqxdhDeploymentNative.logged_forget work []]
  simp only [PqxdhDeploymentNative.logged] at supported
  rw [simulateQ_map, StateT.run_map, support_map]
  exact ⟨result, supported, rfl⟩

/-- This projection reads only public metadata and actual source sending counters. -/
def worldShell (state : PqxdhRecordLiftWorld.State n) : Shell :=
  ⟨state.server.map fun server => ⟨server.sender, fun keyId =>
      (server.records.server.peers keyId).map fun peer => peer.kernel.refined.control.send_sequence.val⟩,
    fun owner => (state.owners[owner]?).bind fun phase => match phase with
      | .inactive _ => none
      | .established shell kernel => some ⟨shell.identityKeyId, kernel.refined.control.send_sequence.val⟩⟩

def storedSequence : PqxdhRecordLiftWorldCompiler.StoredKernel n → Nat
  | .known kernel => kernel.refined.control.send_sequence.val
  | .hidden _ kernel => kernel.control.send_sequence.val

/-- Hidden coordinates do not expose seed or key bytes when recovering a cursor from Protocol.Control. -/
def controlShell (state : PqxdhRecordLiftProtocol.Control n) : Shell :=
  ⟨state.server.map fun server => ⟨server.sender, fun keyId =>
      (server.peers keyId).map fun peer => storedSequence peer.kernel⟩,
    fun owner => (state.owners[owner]?).bind fun phase => match phase with
      | .inactive _ => none
      | .established shell kernel => some ⟨shell.identityKeyId, storedSequence kernel⟩⟩

/-- Concrete interpretation changes chain and material payloads, while retaining the exact source sending counter. -/
theorem stored_sequence_erasure
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n))
    (kernel : PqxdhRecordLiftWorldCompiler.StoredKernel n) :
    (kernel.erase (PqxdhRecordLiftWorldCompiler.interpret seeds table)).refined.control.send_sequence.val =
      storedSequence kernel := by
  cases kernel <;> rfl

private theorem shell_ext (left right : Shell)
    (server : left.server = right.server) (owners : left.owners = right.owners) : left = right := by
  cases left
  cases right
  cases server
  cases owners
  rfl

private theorem server_ext (left right : CborRecordWorldClient.Server)
    (sender : left.sender = right.sender) (peers : left.peers = right.peers) : left = right := by
  cases left
  cases right
  cases sender
  cases peers
  rfl

/-- The public cursor is already present in Protocol.Control; concrete cache/seed interpretation cannot alter it. -/
theorem world_control_shell (state : PqxdhRecordLiftWorldCompiler.State n) :
    worldShell (PqxdhRecordLiftWorldCompiler.world state) =
      controlShell (PqxdhRecordLiftProtocol.control state) := by
  apply shell_ext
  · simp only [worldShell, controlShell, PqxdhRecordLiftProtocol.control,
      PqxdhRecordLiftWorldCompiler.world, PqxdhRecordLiftWorldCompiler.project,
      PqxdhRecordLiftWorldCompiler.erase, Option.map_map, Function.comp_def]
    congr 1
    funext server
    apply server_ext
    · rfl
    · funext keyId
      simp only [PqxdhRecordLiftWorldCompiler.Server.erase, Option.map_map, PqxdhRecordLiftWorldCompiler.Peer.erase, Function.comp_def]
      congr 1
      funext peer
      exact stored_sequence_erasure _ _ peer.kernel
  · funext owner
    simp only [worldShell, controlShell, PqxdhRecordLiftProtocol.control,
      PqxdhRecordLiftWorldCompiler.world, PqxdhRecordLiftWorldCompiler.project,
      PqxdhRecordLiftWorldCompiler.erase, List.getElem?_map, Option.bind_map, Function.comp_def]
    congr 1
    funext phase
    cases phase with
    | inactive => rfl
    | established shell kernel =>
        simp only [PqxdhRecordLiftWorldCompiler.Phase.erase]
        rw [stored_sequence_erasure]

/-- Both source and concrete cursors start empty, without an initialization premise. -/
theorem initial_shell :
    worldShell (PqxdhRecordLiftWorld.initial : PqxdhRecordLiftWorld.State n) = CborRecordWorldClient.initial ∧
    controlShell (PqxdhRecordLiftProtocol.initialControl : PqxdhRecordLiftProtocol.Control n) = CborRecordWorldClient.initial :=
  ⟨rfl, rfl⟩

end BeaconcryptCore.Computational.CborRecordWorldCursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursor.send_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursor.send_cursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursor.receive_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursor.receive_cursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursor.mixed_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursor.mixed_cursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursor.logged_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursor.logged_support

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursor.stored_sequence_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursor.stored_sequence_erasure

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursor.world_control_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursor.world_control_shell

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursor.initial_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursor.initial_shell

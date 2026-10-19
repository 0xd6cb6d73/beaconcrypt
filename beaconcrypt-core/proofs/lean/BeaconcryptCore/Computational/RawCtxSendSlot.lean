import BeaconcryptCore.Computational.RawCtxSourceSeal
import BeaconcryptCore.Computational.RawCtxNativeSlot

/-!
This module connects the actual send driver to the already modeled synchronous Option slot. Empty input returns ordinary None before take, even for a diagnostic absent slot. Nonempty input takes the whole kernel and retains a distinct absent-slot assertion outcome. Every normal ready-slot result reinstalls the complete returned kernel before the actual API reply. The equality retains the entire stateful primitive interpreter, so active failed sealing publishes the advanced send kernel while retaining all receive state; it does not become receive-style rollback.

The seven statements use the exact existing source send/seal programs and ready representation. Their four one-call KDF/AEAD/hash/writer caps are preserved; native slot/byte work is not thereby free. These are functional source-order and normal-return equations, not native slot extraction, compiler correctness, callback losslessness, allocation/timing, unwind/crash recovery, CAS or durable publication. The diagnostic faults are proof markers, not extra public API replies. Serial ownership and a ready kernel remain explicit representation/deployment premises. No primitive security, independent-key or protocol authentication premise is introduced.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxSendSlot
open RawCtxNativeSlot

/-- Empty source requests reject before take; all nonempty requests run the owning send driver and reinstall before reply. -/
noncomputable def sendOwner {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : State Metadata) :
    OracleComp RawCtxSourceSend.PrimitiveSpec (Except Fault (Option RawCtxSourceSend.Encrypted) × State Metadata) :=
  if plaintext.isEmpty then pure (.ok none, state) else do
    let context : RawCtxSourceSend.SealContext :=
      ⟨plaintext, state.owner.expectedSender, senderId, state.owner.associatedData⟩
    let result ← run (fun entry => simulateQ RawCtxSourceSend.adapter
      (RawCtxSourceSend.send entry context)) state.owner.slot
    pure (result.1, { state with owner := { state.owner with slot := result.2 } })

/-- Ready-slot send is exactly the complete established-owner program, preserving its actual optional result. -/
theorem sendOwner_ready {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    sendOwner senderId plaintext (ready state) =
      (fun result => (.ok result.1, ready result.2)) <$>
        (RawCtxSourceSend.sendOwner senderId plaintext).run state := by
  unfold sendOwner RawCtxSourceSend.sendOwner StateT.run
  dsimp only [ready]
  split
  all_goals simp only [run_ready, map_pure, map_bind, bind_map_left]

/-- Empty input is ordinary rejection before slot access, including a diagnostic absent slot. -/
theorem sendOwner_empty {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : State Metadata) (hempty : plaintext.isEmpty = true) :
    sendOwner senderId plaintext state = pure (.ok none, state) := by
  simp only [sendOwner, hempty, ite_true]

/-- A nonempty request to an absent slot keeps its assertion diagnostic distinct from API None. -/
theorem sendOwner_absent {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : State Metadata) (hnonempty : plaintext.isEmpty = false) (hslot : state.owner.slot = none) :
    sendOwner senderId plaintext state = pure (.error .absent, state) := by
  simp only [sendOwner, hnonempty, Bool.false_eq_true, ite_false, hslot, run_absent, pure_bind]
  rw [← hslot]

/-- Concrete private sealing runs outside the local vacant slot and retains its full primitive state. -/
noncomputable def sendGame {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : State Metadata) (primitive : PrimitiveState) :
    OracleComp base ((Except Fault (Option RawCtxSourceSend.Encrypted) × State Metadata) × PrimitiveState) :=
  (simulateQ (impl ∘ₛ RawCtxSourceSeal.nativeAdapter) (sendOwner senderId plaintext state)).run primitive

/-- Ready native-slot sending preserves the complete concrete source game and all actual optional failure states. -/
theorem sendGame_ready {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    sendGame impl senderId plaintext (ready state) primitive =
      (fun result => ((.ok result.1.1, ready result.1.2), result.2)) <$>
        RawCtxSourceSend.sendGame (impl ∘ₛ RawCtxSourceSeal.nativeAdapter) senderId plaintext state primitive := by
  simp only [sendGame, sendOwner_ready, simulateQ_map, StateT.run_map, RawCtxSourceSend.sendGame]

/-- Every supported ready-slot result has a reinstalled complete kernel and the same final primitive state. -/
theorem sendGame_normal {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (result : (Except Fault (Option RawCtxSourceSend.Encrypted) × State Metadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext (ready state) primitive)) :
    ∃ sourceResult,
      sourceResult ∈ support (RawCtxSourceSend.sendGame (impl ∘ₛ RawCtxSourceSeal.nativeAdapter)
        senderId plaintext state primitive) ∧
      result = ((.ok sourceResult.1.1, ready sourceResult.1.2), sourceResult.2) := by
  rw [sendGame_ready] at hsupport
  simpa only [support_map, Set.mem_image, eq_comm] using hsupport

/-- Every active send reinstalls the advanced whole kernel even on None; receive chains/cache remain intact. -/
theorem sendGame_active {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxSourceSeal.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (hnonempty : plaintext.isEmpty = false)
    (hmax : state.owner.kernel.refined.control.send_sequence ≠ core.num.U64.MAX)
    (result : (Except Fault (Option RawCtxSourceSend.Encrypted) × State Metadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext (ready state) primitive)) :
    ∃ kernel, result.1.2.owner.slot = some kernel ∧
      kernel.refined.control.send_sequence.val = state.owner.kernel.refined.control.send_sequence.val + 1 ∧
      kernel.refined.control.receive_sequence = state.owner.kernel.refined.control.receive_sequence ∧
      kernel.refined.control.receive_cache = state.owner.kernel.refined.control.receive_cache ∧
      kernel.refined.receive_chain = state.owner.kernel.refined.receive_chain ∧
      kernel.refined.receive_slots = state.owner.kernel.refined.receive_slots := by
  obtain ⟨sourceResult, hsource, rfl⟩ := sendGame_normal impl senderId plaintext state primitive result hsupport
  exact ⟨_, rfl, RawCtxSourceSend.sendGame_active_state (impl ∘ₛ RawCtxSourceSeal.nativeAdapter)
    senderId plaintext state primitive hnonempty hmax sourceResult hsource⟩

/-- The ready-slot representation introduces no additional KDF, AEAD, hash or writer calls. -/
theorem sendOwner_bounds {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    let program := simulateQ RawCtxSourceSeal.nativeAdapter (sendOwner senderId plaintext (ready state))
    program.IsQueryBoundP (fun query => query.isLeft = true) 1 ∧
      ∀ kind, program.IsQueryBoundP (fun query => RawCtxSourceSeal.category kind query = true) 1 := by
  simp only [sendOwner_ready, simulateQ_map, isQueryBoundP_map_iff]
  exact RawCtxSourceSeal.nativeSend_bounds senderId plaintext state

end BeaconcryptCore.Computational.RawCtxSendSlot

/--
info: 'BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_ready

/--
info: 'BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_empty

/--
info: 'BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_absent

/--
info: 'BeaconcryptCore.Computational.RawCtxSendSlot.sendGame_ready' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendSlot.sendGame_ready

/--
info: 'BeaconcryptCore.Computational.RawCtxSendSlot.sendGame_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendSlot.sendGame_normal

/--
info: 'BeaconcryptCore.Computational.RawCtxSendSlot.sendGame_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendSlot.sendGame_active

/--
info: 'BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSendSlot.sendOwner_bounds

import BeaconcryptCore.Computational.RawCtxOwnerProvenance

/-!
This module formalizes the synchronous Option-slot choreography used by RatchetKernelSlot and the raw receive helper. Taking a kernel vacates the slot before the absent-kernel assertion; putting it checks vacancy before installing the returned whole kernel. Diagnostic Fault values model those panic points and remain distinct from ordinary optional rejection. They are proof outcomes, not new public API replies or assertions about panic recovery.

For a ready slot, the complete OracleComp program equals the existing one-owner raw source program under the displayed representation map. The equality survives arbitrary stateful primitive interpretation and preserves complete primitive state, actual optional reply, owner metadata and publication order. Empty, malformed and invalid input reject before take. The private driver receives only the owning extracted capability and cannot mutate the vacant local slot.

This is a checked model of source take/put order and a normal-return representation map. It does not prove Rust compiler correctness, native HashMap or Cap'n Proto implementation, native extraction of the slot, memory erasure, losslessness of independently aborting primitive callbacks, unwind/crash recovery, durable publication, CAS or concurrency. A ready entry and serial ownership are explicit source/deployment premises. No cryptographic authentication or plaintext secrecy conclusion is assumed.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxNativeSlot

/-- These marked failures represent native expect/assert panics, not a new public API reply. -/
inductive Fault where
  | absent
  | occupied
  deriving DecidableEq

abbrev Slot := Option ConcreteRatchetKernel

/-- Native Option.take vacates the slot before checking whether a kernel was present. -/
def take (slot : Slot) : Except Fault ConcreteRatchetKernel × Slot :=
  (match slot with | none => .error .absent | some kernel => .ok kernel, none)

/-- Native put asserts vacancy before installing the returned whole kernel. -/
def put (kernel : ConcreteRatchetKernel) (slot : Slot) : Except Fault Unit × Slot :=
  match slot with
  | none => (.ok (), some kernel)
  | some _ => (.error .occupied, slot)

/-- The private driver owns the taken kernel and cannot mutate the local vacant slot. -/
def run {Plaintext : Type} {ι : Type} {spec : OracleSpec ι}
    (driver : ConcreteRatchetKernel → OracleComp spec (ConcreteRatchetKernel × Plaintext))
    (slot : Slot) : OracleComp spec (Except Fault Plaintext × Slot) :=
  let (taken, vacant) := take slot
  match taken with
  | .error fault => pure (.error fault, vacant)
  | .ok entry => do
      let (kernel, reply) ← driver entry
      let (published, installed) := put kernel vacant
      match published with
      | .error fault => pure (.error fault, installed)
      | .ok () => pure (.ok reply, installed)

/-- An absent source slot fails before calling the driver and remains vacant. -/
theorem run_absent {Plaintext : Type} {ι : Type} {spec : OracleSpec ι}
    (driver : ConcreteRatchetKernel → OracleComp spec (ConcreteRatchetKernel × Plaintext)) :
    run driver none = pure (.error .absent, none) := rfl

/-- A ready slot executes the exact driver and reinstalls its whole returned kernel before exposing its reply. -/
theorem run_ready {Plaintext : Type} {ι : Type} {spec : OracleSpec ι}
    (driver : ConcreteRatchetKernel → OracleComp spec (ConcreteRatchetKernel × Plaintext))
    (entry : ConcreteRatchetKernel) :
    run driver (some entry) = (fun result => (.ok result.2, some result.1)) <$> driver entry := by
  simp only [run, take, put, map_eq_bind_pure_comp]
  rfl

/-- The native owner representation has one Option slot for its complete ratchet. -/
structure Owner (Metadata : Type) where
  slot : Slot
  expectedSender : Std.U64
  associatedData : Pqxdh.Bytes
  metadata : Metadata

structure State (Metadata : Type) where
  owner : Owner Metadata
  rawAttempts : Nat

/-- Outside an operation, a ready native owner represents exactly one whole modeled owner. -/
def ready {Metadata : Type} (state : RawCtxWholeOwner.OwnerState Metadata) : State Metadata :=
  ⟨⟨some state.owner.kernel, state.owner.expectedSender, state.owner.associatedData, state.owner.metadata⟩,
    state.rawAttempts⟩

/-- A diagnostic result preserves panic markers; it does not expose them as ordinary API rejection. -/
def publish {Metadata : Type} (state : State Metadata)
    (result : Except Fault (core.option.Option RawCtxWholeOwner.Decrypted) × Slot) :
    Except Fault (core.option.Option RawCtxWholeOwner.Decrypted) × State Metadata :=
  (result.1, ⟨{ state.owner with slot := result.2 }, state.rawAttempts + 1⟩)

/-- Source parsing precedes take; normal source completion puts the complete kernel before the reply. -/
noncomputable def rawReceive {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : State Metadata) :
    OracleComp RawCtxWholeOwner.PrimitiveSpec
      (Except Fault (core.option.Option RawCtxWholeOwner.Decrypted) × State Metadata) :=
  if raw.isEmpty then pure (publish state (.ok .None, state.owner.slot)) else
  match decode raw with
  | none => pure (publish state (.ok .None, state.owner.slot))
  | some frame =>
      if RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame then do
        let result ← run (fun entry => simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive entry frame.sequence ⟨raw, frame, state.owner.associatedData⟩)) state.owner.slot
        pure (publish state result)
      else pure (publish state (.ok .None, state.owner.slot))

/-- The diagnostic slot program is exactly the existing source raw program on every ready entry. -/
theorem rawReceive_ready {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata) :
    rawReceive decode raw (ready state) =
      (fun result => (.ok result.1, ready result.2)) <$> (RawCtxWholeOwner.rawReceive decode raw).run state := by
  unfold rawReceive RawCtxWholeOwner.rawReceive StateT.run
  dsimp only [ready]
  split
  all_goals simp only [map_pure, publish, RawCtxWholeOwner.publish]
  split
  all_goals simp_all only [map_pure]
  split
  all_goals simp_all only [run_ready, map_pure, map_bind, bind_map_left, ite_true, ite_false]

/-- Stateful private cryptographic effects stay outside the native slot and its publication. -/
noncomputable def rawGame {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : State Metadata) (primitive : PrimitiveState) :
    OracleComp base ((Except Fault (core.option.Option RawCtxWholeOwner.Decrypted) × State Metadata) × PrimitiveState) :=
  (simulateQ impl (rawReceive decode raw state)).run primitive

/-- Ready native-slot execution equals the entire source game, including actual primitive state. -/
theorem rawGame_ready {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    rawGame impl decode raw (ready state) primitive =
      (fun result => ((.ok result.1.1, ready result.1.2), result.2)) <$>
        RawCtxWholeOwner.rawGame impl decode raw state primitive := by
  simp only [rawGame, rawReceive_ready, simulateQ_map, StateT.run_map, RawCtxWholeOwner.rawGame]

/-- Every supported ready-slot result is a normal reply with the source game's complete final primitive state. -/
theorem rawGame_normal {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (result : (Except Fault (core.option.Option RawCtxWholeOwner.Decrypted) × State Metadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl decode raw (ready state) primitive)) :
    ∃ sourceResult, sourceResult ∈ support (RawCtxWholeOwner.rawGame impl decode raw state primitive) ∧
      result = ((.ok sourceResult.1.1, ready sourceResult.1.2), sourceResult.2) := by
  rw [rawGame_ready] at hsupport
  simpa only [support_map, Set.mem_image, eq_comm] using hsupport

/-- Ordinary failed opening restores a ready complete native owner without rolling back primitive state. -/
theorem rawGame_failure_owner {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (result : (Except Fault (core.option.Option RawCtxWholeOwner.Decrypted) × State Metadata) × PrimitiveState)
    (hsupport : result ∈ support (rawGame impl decode raw (ready state) primitive))
    (hfailure : result.1.1 = .ok .None) : result.1.2.owner = (ready state).owner := by
  obtain ⟨sourceResult, hsource, rfl⟩ := rawGame_normal impl decode raw state primitive result hsupport
  have howner := RawCtxWholeOwner.rawGame_failure_owner impl decode raw state primitive sourceResult hsource (Except.ok.inj hfailure)
  simp only [ready, howner]

/-- Empty raw input rejects before take even if the diagnostic slot is already vacant. -/
theorem rawReceive_empty {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : State Metadata) (hempty : raw.isEmpty = true) :
    rawReceive decode raw state = pure (publish state (.ok .None, state.owner.slot)) := by
  simp only [rawReceive, hempty, if_true]

/-- Malformed payload decoding rejects before the owner slot is taken. -/
theorem rawReceive_malformed {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : State Metadata) (hdecode : decode raw = none) :
    rawReceive decode raw state = pure (publish state (.ok .None, state.owner.slot)) := by
  simp only [rawReceive, hdecode, ite_self]

/-- Sender, shape and associated-data validation reject before take. -/
theorem rawReceive_invalid {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : State Metadata) (frame : RawCtxReceive.DecodedFrame)
    (hdecode : decode raw = some frame)
    (hinvalid : ¬RawCtxReceive.ValidFrame state.owner.expectedSender state.owner.associatedData frame) :
    rawReceive decode raw state = pure (publish state (.ok .None, state.owner.slot)) := by
  simp only [rawReceive, hdecode, hinvalid, if_false, ite_self]

end BeaconcryptCore.Computational.RawCtxNativeSlot

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.run_absent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.run_absent

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.run_ready' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.run_ready

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_ready

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.rawGame_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.rawGame_ready

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.rawGame_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.rawGame_normal

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.rawGame_failure_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.rawGame_failure_owner

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_empty

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_malformed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_malformed

/--
info: 'BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxNativeSlot.rawReceive_invalid

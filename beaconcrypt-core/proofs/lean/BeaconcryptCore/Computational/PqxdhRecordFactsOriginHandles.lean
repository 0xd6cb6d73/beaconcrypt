-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory

/-! Structural installed-slot and direction facts for record origin. These concern actual handle storage and add no cryptographic contract. -/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles
open PqxdhRecordLiftInterface PqxdhRecordLiftWorldCompiler PqxdhRecordLiftWorldProvenance
open PqxdhRecordLiftIdeal PqxdhRecordLiftProtocolHistory
open PqxdhDeploymentInterface (Handle)
variable {n : Nat}

/-- A handle's physical sending direction, independent of stored bytes. -/
def handleDirection : Handle → Bool
  | .peer _ => false
  | .owner _ => true

/-- Physical storage role selected by the public handle constructor. -/
def handleRole : Handle → Role
  | .peer _ => .server
  | .owner _ => .beacon

/-- Read the actual installed kernel, preserving absent Server peers and inactive Beacon owners. -/
def handleKernel (control : PqxdhRecordLiftProtocol.Control n) : Handle → Option (StoredKernel n)
  | .peer keyId => control.server.bind fun server => (server.peers keyId).map Peer.kernel
  | .owner owner => (control.owners[owner]?).bind fun phase => match phase with
      | .inactive _ => none
      | .established _ kernel => some kernel

/-- A stored hidden handle owns the slot and physical sending direction of a label. -/
def OwnsLabel (control : PqxdhRecordLiftProtocol.Control n) (label : Label n) (handle : Handle) : Prop :=
  handleSlot control handle = some label.slot ∧ label.direction = handleDirection handle

/-- Actual forward storage preserves every already installed hidden slot. -/
theorem storedAhead_origin (before after : StoredKernel n) (progress : StoredAhead before after)
    (slot : Slot n) (present : before.origin = some slot) : after.origin = some slot := by
  cases before with
  | known kernel => simp [StoredKernel.origin] at present
  | hidden old kernel =>
      obtain ⟨next, rfl, _⟩ := progress old kernel rfl
      exact present

/-- A protocol transition preserves the slot already installed on either physical handle role. -/
theorem handleSlot_step (before after : PqxdhRecordLiftProtocol.Control n)
    (progress : Step before after) (handle : Handle) (slot : Slot n)
    (present : handleSlot before handle = some slot) : handleSlot after handle = some slot := by
  cases handle with
  | peer keyId =>
      simp only [handleSlot, peerSlot, Option.bind_eq_some_iff] at present
      obtain ⟨server, existing, peer, found, origin⟩ := present
      obtain ⟨nextServer, nextPeer, installed, stored, advanced⟩ := progress.2.1 server existing keyId peer found
      simpa only [handleSlot, peerSlot, Option.bind_eq_some_iff] using
        (show ∃ server, after.server = some server ∧ ∃ peer, server.peers keyId = some peer ∧
          peer.kernel.origin = some slot from
          ⟨nextServer, installed, nextPeer, stored, storedAhead_origin _ _ advanced slot origin⟩)
  | owner owner =>
      simp only [handleSlot, ownerSlot, Option.bind_eq_some_iff] at present
      obtain ⟨phase, found, origin⟩ := present
      cases phase with
      | inactive phase => simp [Phase.origin] at origin
      | established shell kernel =>
          obtain ⟨nextShell, nextKernel, stored, advanced⟩ := progress.2.2 owner shell kernel found
          simpa only [handleSlot, ownerSlot, Option.bind_eq_some_iff] using
            (show ∃ phase, after.owners[owner]? = some phase ∧ phase.origin = some slot from
              ⟨.established nextShell nextKernel, stored, storedAhead_origin _ _ advanced slot origin⟩)

/-- Protocol evolution preserves every established slot-and-direction ownership witness. -/
theorem ownsLabel_step (before after : PqxdhRecordLiftProtocol.Control n)
    (progress : Step before after) (label : Label n) (handle : Handle)
    (owned : OwnsLabel before label handle) : OwnsLabel after label handle := by
  exact ⟨handleSlot_step before after progress handle label.slot owned.1, owned.2⟩

/-- Matching a label's stored sender to the opposite receiving direction gives the ideal counterpart relation. -/
theorem counterpart_of_opposite (control : PqxdhRecordLiftProtocol.Control n)
    (label : Label n) (sending receiving : Handle) (sender : OwnsLabel control label sending)
    (receivingDirection : label.direction = !handleDirection receiving) :
    Counterpart (handleSlot control) label.slot receiving sending := by
  cases sending <;> cases receiving <;> simp_all [OwnsLabel, handleDirection, Counterpart]

/-- The actual opening getter retains the installed hidden slot, physical receive direction and exact sequence for either cached or future material. -/
theorem opening_oriented {Context : Type} (role : Role) (slot : Slot n) (kernel : LabeledKernel n)
    (oriented : Oriented role (.hidden slot kernel))
    (pending : RawCtxInterpretedOpening.Opening (Label n) (Label n) (Label n) Context)
    (attributed : PqxdhRecordLiftMaterialTable.EffectAttributed kernel.receive_chain (.openRequested pending))
    (label : Label n) (material : RawCtxInterpretedOpening.material pending = .ok (.Some label)) :
    ∃ sequence, RawCtxInterpretedOpening.sequence pending = .ok sequence ∧
      label.slot = slot ∧ label.direction = !sendDirection role ∧ sequence.val = label.position + 1 := by
  obtain ⟨sequence, requested, origin⟩ :=
    PqxdhRecordLiftMaterialTable.opening_attributed kernel.receive_chain pending attributed label material
  exact ⟨sequence, requested, origin.1.trans oriented.2.1.2,
    origin.2.1.trans oriented.2.2.2, origin.2.2⟩

/-- The kernel selector reads exactly the installed-origin map exposed by the ideal view. -/
theorem handleKernel_origin (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle) :
    (handleKernel control handle).bind StoredKernel.origin = handleSlot control handle := by
  cases handle with
  | peer keyId => simp [handleKernel, handleSlot, peerSlot, Option.bind_assoc, Option.bind_map]
  | owner owner =>
      cases found : control.owners[owner]? with
      | none => simp [handleKernel, handleSlot, ownerSlot, found]
      | some phase => cases phase <;> simp [handleKernel, handleSlot, ownerSlot, found, Phase.origin]

/-- Source-reachable controls orient the actual selected kernel by its physical handle role. -/
theorem handleKernel_oriented (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (handle : Handle) (kernel : StoredKernel n) (stored : handleKernel control handle = some kernel) :
    Oriented (handleRole handle) kernel := by
  cases handle with
  | peer keyId =>
      simp only [handleKernel, Option.bind_eq_some_iff, Option.map_eq_some_iff] at stored
      obtain ⟨server, existing, peer, found, rfl⟩ := stored
      exact safe.1.1 server existing keyId peer found
  | owner owner =>
      simp only [handleKernel, Option.bind_eq_some_iff] at stored
      obtain ⟨phase, found, installed⟩ := stored
      cases phase with
      | inactive phase => cases installed
      | established shell actual =>
          cases installed
          exact safe.1.2 (.established shell kernel) (List.mem_iff_getElem?.mpr ⟨owner, found⟩)

/-- Reading an actual hidden kernel yields its installation slot at the same handle. -/
theorem handleKernel_slot (control : PqxdhRecordLiftProtocol.Control n) (handle : Handle)
    (slot : Slot n) (kernel : LabeledKernel n)
    (stored : handleKernel control handle = some (.hidden slot kernel)) :
    handleSlot control handle = some slot := by
  simp only [← handleKernel_origin, stored, Option.bind_some, StoredKernel.origin]

/-- The handle's sending direction is exactly the direction assigned by its source role. -/
theorem handleRole_direction (handle : Handle) : sendDirection (handleRole handle) = handleDirection handle := by
  cases handle <;> rfl

/-- Joining the actual control lookup to the exact opening getter gives the receiving handle's slot and opposite physical direction. -/
theorem handle_opening_oriented {Context : Type}
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control) (handle : Handle)
    (slot : Slot n) (kernel : LabeledKernel n)
    (stored : handleKernel control handle = some (.hidden slot kernel))
    (pending : RawCtxInterpretedOpening.Opening (Label n) (Label n) (Label n) Context)
    (attributed : PqxdhRecordLiftMaterialTable.EffectAttributed kernel.receive_chain (.openRequested pending))
    (label : Label n) (material : RawCtxInterpretedOpening.material pending = .ok (.Some label)) :
    ∃ sequence, RawCtxInterpretedOpening.sequence pending = .ok sequence ∧
      handleSlot control handle = some label.slot ∧ label.direction = !handleDirection handle ∧
      sequence.val = label.position + 1 := by
  obtain ⟨sequence, requested, origin, direction, position⟩ := opening_oriented
    (handleRole handle) slot kernel (handleKernel_oriented control safe handle _ stored)
    pending attributed label material
  exact ⟨sequence, requested, by simpa only [origin] using handleKernel_slot control handle slot kernel stored,
    by simpa only [handleRole_direction] using direction, position⟩

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.storedAhead_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.storedAhead_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleSlot_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleSlot_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.ownsLabel_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.ownsLabel_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.counterpart_of_opposite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.counterpart_of_opposite

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.opening_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.opening_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleKernel_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleKernel_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleKernel_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleKernel_oriented

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleKernel_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleKernel_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleRole_direction' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handleRole_direction

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handle_opening_oriented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginHandles.handle_opening_oriented

-- SPDX-License-Identifier: 0BSD
import Mathlib.Data.Nat.Basic

/-! Exact complete-message sizes from `beaconcrypt-core/src/transport.rs`, including CBOR headers and the inclusive 32 MiB limit. -/
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborSizing

def maxMessageSize : Nat := 33_554_432

def argumentLen (value : Nat) : Nat :=
  if value ≤ 23 then 1 else if value ≤ 255 then 2 else
    if value ≤ 65_535 then 3 else if value ≤ 4_294_967_295 then 5 else 9

def byteStringLen (length : Nat) : Nat := argumentLen length + length

def frameLen (sequence sender payload : Nat) : Nat :=
  3 + argumentLen sequence + argumentLen sender + byteStringLen payload

def initLen : Nat :=
  3 + byteStringLen 33 + byteStringLen 98 + byteStringLen 98 + byteStringLen 1249 +
    byteStringLen 1952 + byteStringLen 3309

def responseLen (payload assigned : Nat) : Nat :=
  3 + byteStringLen 32 + byteStringLen 32 + byteStringLen 1088 +
    byteStringLen payload + argumentLen assigned + byteStringLen 3309

def frameFits (plaintext sequence sender : Nat) : Prop :=
  frameLen sequence sender (plaintext + 80) ≤ maxMessageSize

def responseFits (application assigned : Nat) : Prop :=
  responseLen (application + 88) assigned ≤ maxMessageSize

theorem argumentLen_bounds (value : Nat) : 1 ≤ argumentLen value ∧ argumentLen value ≤ 9 := by
  unfold argumentLen
  split_ifs <;> omega

/-- A complete response has more overhead than its sequence-one virtual frame, even for a full-width sender identifier. -/
theorem registration_frame_le_response (payload assigned sender : Nat) :
    frameLen 1 sender payload ≤ responseLen payload assigned := by
  have senderWidth := (argumentLen_bounds sender).2
  change 4 + argumentLen sender + byteStringLen payload ≤
    1162 + byteStringLen payload + argumentLen assigned + 3312
  omega

/-- Virtual framing cannot add a size rejection to an admitted native response. -/
theorem registration_frame_fits (payload assigned sender : Nat)
    (admitted : responseLen payload assigned ≤ maxMessageSize) :
    frameLen 1 sender payload ≤ maxMessageSize :=
  Nat.le_trans (registration_frame_le_response payload assigned sender) admitted

/-- The fixed-size signed registration bundle has the same size at every session. -/
theorem init_size : initLen = 6757 := by
  decide

/-- The inclusive limit and the next rejected byte agree with both native size-boundary tests. -/
theorem inclusive_boundaries :
    frameLen 1 0 (maxMessageSize - 10) = maxMessageSize ∧
    maxMessageSize < frameLen 1 0 (maxMessageSize - 9) ∧
    responseLen (maxMessageSize - 4480) 1 = maxMessageSize ∧
    maxMessageSize < responseLen (maxMessageSize - 4479) 1 := by
  decide

end BeaconcryptCore.Computational.CborSizing

/-- info: 'BeaconcryptCore.Computational.CborSizing.argumentLen_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSizing.argumentLen_bounds
/-- info: 'BeaconcryptCore.Computational.CborSizing.registration_frame_le_response' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSizing.registration_frame_le_response
/-- info: 'BeaconcryptCore.Computational.CborSizing.registration_frame_fits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSizing.registration_frame_fits
/-- info: 'BeaconcryptCore.Computational.CborSizing.init_size' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSizing.init_size
/-- info: 'BeaconcryptCore.Computational.CborSizing.inclusive_boundaries' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSizing.inclusive_boundaries

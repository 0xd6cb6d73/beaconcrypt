-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceRestore
import BeaconcryptCore.Computational.RegistrationServerNativeSource

/-! The native Server's SDK fields are separated from its primitive auxiliary state only for provider-source reconstruction. Public root references restore the exact consumed native tokens. Replay insertion and its returned handle are the actual SDK operation, including failures and repeated identifiers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields

structure Fields where
  control : pqxdh.ServerState
  pin : session.ServerAuthenticationPin
  consumed : RegistrationReplaySchedule.State
  sessions : List (Option peer.ConsumedRegistration)

def ofNative {n : Nat} (before : RegistrationServerFrontendCompiler.State n) : Fields :=
  ⟨before.control, before.pin, before.consumed, before.sessions⟩

def restore (roots : RegistrationServerReferenceRestore.Roots) (before : RegistrationServerMaterialFrontend.State) : Fields :=
  ⟨before.control, before.pin, before.consumed, RegistrationServerReferenceRestore.sessions roots before⟩

def retain (accepted : agreement.ServerAgreement) (before : Fields) : RustM (Option Nat × Fields) :=
  match RegistrationReplaySchedule.consume accepted before.consumed with
  | .fail error => .fail error
  | .div => .div
  | .ok (.None, history) => .ok (none, { before with consumed := history })
  | .ok (.Some consumed, history) => .ok (some before.sessions.length,
      { before with consumed := history, sessions := before.sessions ++ [some consumed] })

/-- Token reconstruction retains every SDK field while replacing only the opaque source root in each one-use capability. -/
theorem restore_native {n : Nat} (roots : RegistrationServerReferenceRestore.Roots)
    (before : RegistrationServerMaterialFrontend.State) (localState : RegistrationServerRootCompiler.Local n) :
    ofNative (RegistrationServerReferenceRestore.restore roots before localState) = restore roots before := rfl

/-- Actual replay insertion commutes with restoration for every retained root reference. -/
theorem retain_restore (roots : RegistrationServerReferenceRestore.Roots) (ready : RegistrationServerReferenceRoot.Ready)
    (before : RegistrationServerMaterialFrontend.State) :
    (fun result => (result.1, restore roots result.2)) <$> RegistrationServerMaterialFrontend.retain ready before =
      retain (RegistrationServerReferenceRoot.atRoot ready (roots ready.reference)) (restore roots before) := by
  unfold RegistrationServerMaterialFrontend.retain retain
  rw [show (restore roots before).consumed = before.consumed from rfl]
  by_cases present : before.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) = true
  · rw [
      RegistrationReplaySchedule.consume_replayed (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.consumed present,
      RegistrationReplaySchedule.consume_replayed (RegistrationServerReferenceRoot.atRoot ready (roots ready.reference)) before.consumed present]
    rfl
  · have absent : before.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) = false := Bool.eq_false_iff.mpr present
    rw [
      RegistrationReplaySchedule.consume_fresh (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.consumed absent,
      RegistrationReplaySchedule.consume_fresh (RegistrationServerReferenceRoot.atRoot ready (roots ready.reference)) before.consumed absent]
    change RustM.ok (some before.sessions.length, restore roots
      { before with
        consumed := before.consumed ++ [absBytes ready.agreement.pending.registration_id.bytes]
        sessions := before.sessions ++ [some ready] }) = _
    simp only [restore, RegistrationServerReferenceRestore.sessions, List.map_append, List.map_cons, List.map_nil,
      Option.map_some, List.length_map, RegistrationServerReferenceRestore.token]
    rfl

/-- This field operation is the literal native SDK retention, with its complete primitive state kept outside the pure field lens. -/
theorem sdk_retain {n : Nat} (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (accepted : agreement.ServerAgreement) (before : RegistrationServerFrontendCompiler.State n) :
    (fun result => (result.1, ofNative result.2)) <$>
      (RegistrationServerNativeSource.retain created accepted).run before =
      match retain accepted (ofNative before) with
      | .fail error => pure (.fail error, ofNative before)
      | .div => pure (.div, ofNative before)
      | .ok (reply, after) => pure (.ok reply, after) := by
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore,
    StateT.run, retain, ofNative]
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error => simp only [map_pure]; rfl
  | div => simp only [map_pure]; rfl
  | ok result => rcases result with ⟨reply, history⟩; cases reply <;> simp only [map_pure] <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields.restore_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields.restore_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields.retain_restore' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields.retain_restore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields.sdk_retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptFields.sdk_retain

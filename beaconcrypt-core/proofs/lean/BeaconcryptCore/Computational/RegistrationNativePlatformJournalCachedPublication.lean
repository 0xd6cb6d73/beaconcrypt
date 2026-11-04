-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformJournalSafe
/-! Actual stateful Beacon and Server publication preserve cached ML signing receipts through every source continuation and failed writer. The proof derives preceding-hash alignment internally and retains the exact auxiliary platform poststate; only the literal per-source Ed/writer frame is required. A caller-supplied whole-publication Cached law is not used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication
open RegistrationNativePlatformSigningJournal (State source)
open RegistrationNativePlatformJournalErasure (liftWorld)
open RegistrationNativePlatformJournalPublication (extended)
open RegistrationNativePlatformJournalSafe (Safe Frame)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {Encoded Auxiliary : Type}
variable (primitive : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
abbrev WorldM (n : Nat) (Auxiliary : Type) := StateT (RegistrationWorldSigning.State n) (StateT Auxiliary ProbComp)

private def side
    (ed : registration.Ed25519SigningRequest → WorldM n Auxiliary RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → WorldM n Auxiliary (RustM (core.option.Option Encoded))) :
    QueryImpl (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded) (WorldM n Auxiliary)
  | .inl request => ed request
  | .inr view => encode view

private def free : QueryImpl RegistrationBeaconInitExecutor.Spec
    (OracleComp (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)))
  | .inl query => (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)).query (.inl query)
  | .inr request => (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)).query (.inr (.inl request))

private def freeEncode (view : registration.SignedInitView) :
    OracleComp (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)) (RustM (core.option.Option Encoded)) :=
  (RegistrationNativePlatformJournalErasure.Spec (RegistrationNativePlatformJournalWorld.BeaconSideSpec Encoded)).query (.inr (.inr view))

theorem source_beacon
    (ed : registration.Ed25519SigningRequest → WorldM n Auxiliary RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → WorldM n Auxiliary (RustM (core.option.Option Encoded)))
    (edFrame : ∀ request before previous result, result ∈ support (((ed request).run before).run previous) → Frame before result.1.2)
    (encodeFrame : ∀ view before previous result, result ∈ support (((encode view).run before).run previous) → Frame before result.1.2)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (before : State n) (safe : Safe before) (previous : Auxiliary)
    (result : (RustM (RegistrationBeaconInitExecutor.Result Encoded) × State n) × Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformBeaconPublication.begin
      (extended (source coins primitive) (fun request => liftWorld (ed request)))
      (fun view => liftWorld (encode view)) control inputs scalar pin mldsa).run before).run previous)) : Safe result.1.2 := by
  have frames : ∀ query before previous result, result ∈ support ((((side ed encode) query).run before).run previous) → Frame before result.1.2 := by
    intro query before previous result reached
    cases query with
    | inl request => exact edFrame request before previous result reached
    | inr view => exact encodeFrame view before previous result reached
  have interpreted := RegistrationNativePlatformBeaconPublication.begin_interpret
    (RegistrationNativePlatformJournalSafe.handler primitive (side ed encode)) free freeEncode control inputs scalar pin mldsa
  have callbacks : (fun query => simulateQ (RegistrationNativePlatformJournalSafe.handler primitive (side ed encode))
      (free (Encoded := Encoded) query)) = extended (source coins primitive) (fun request => liftWorld (ed request)) := by
    funext query
    cases query <;> simp only [free, simulateQ_spec_query, RegistrationNativePlatformJournalSafe.handler, side, extended]
  rw [callbacks] at interpreted
  have possible : result ∈ support (((simulateQ (RegistrationNativePlatformJournalSafe.handler primitive (side ed encode))
      (RegistrationNativePlatformBeaconPublication.begin free freeEncode control inputs scalar pin mldsa)).run before).run previous) := by
    rw [interpreted]
    simpa only [freeEncode, simulateQ_spec_query, RegistrationNativePlatformJournalSafe.handler, side] using supported
  exact RegistrationNativePlatformJournalSafe.program primitive (side ed encode) frames _ before safe previous result possible

theorem source_server
    (encode : registration.SignedResponseView → WorldM n Auxiliary (RustM (core.option.Option Encoded)))
    (encodeFrame : ∀ view before previous result, result ∈ support (((encode view).run before).run previous) → Frame before result.1.2)
    (pending : registration.ServerResponseHash) (before : State n) (safe : Safe before) (previous : Auxiliary)
    (result : (RustM (RegistrationWorldServerPublication.Result Encoded) × State n) × Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformServerPublication.program (source coins primitive)
      (fun view => liftWorld (encode view)) pending).run before).run previous)) : Safe result.1.2 := by
  let spec := RegistrationNativePlatformJournalErasure.Spec (registration.SignedResponseView →ₒ RustM (core.option.Option Encoded))
  apply RegistrationNativePlatformJournalSafe.program primitive encode encodeFrame
    (RegistrationNativePlatformServerPublication.program (fun query => spec.query (.inl query)) (fun view => spec.query (.inr view)) pending)
    before safe previous result
  rw [RegistrationNativePlatformServerPublication.program_interpret]
  simpa only [spec, simulateQ_spec_query, RegistrationNativePlatformJournalSafe.handler] using supported

theorem beacon
    (ed : registration.Ed25519SigningRequest → WorldM n Auxiliary RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → WorldM n Auxiliary (RustM (core.option.Option Encoded)))
    (edFrame : ∀ request before previous result, result ∈ support (((ed request).run before).run previous) → Frame before result.1.2)
    (encodeFrame : ∀ view before previous result, result ∈ support (((encode view).run before).run previous) → Frame before result.1.2)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize)
    (before : RegistrationWorldSigning.State n) (cached : RegistrationSigningShared.Cached (RegistrationWorldSigning.project before))
    (previous : Auxiliary) (result : (RustM (RegistrationBeaconInitExecutor.Result Encoded) × RegistrationWorldSigning.State n) × Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformBeaconPublication.begin
      (RegistrationNativePlatformJournalWorld.beaconOutgoing coins primitive ed) encode control inputs scalar pin mldsa).run before).run previous)) :
    RegistrationSigningShared.Cached (RegistrationWorldSigning.project result.1.2) := by
  have law := congrArg (fun work => (work : StateT Auxiliary ProbComp _).run previous)
    (RegistrationNativePlatformJournalWorld.beacon coins primitive ed encode control inputs scalar pin mldsa (before, none))
  rw [StateT.run_map] at law
  rw [← law, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  have safe : Safe (before, none) := ⟨cached, by intro cut impossible; cases impossible⟩
  have after := source_beacon primitive ed encode edFrame encodeFrame control inputs scalar pin mldsa (before, none) safe previous inner reached
  cases same
  exact after.1

theorem server
    (encode : registration.SignedResponseView → WorldM n Auxiliary (RustM (core.option.Option Encoded)))
    (encodeFrame : ∀ view before previous result, result ∈ support (((encode view).run before).run previous) → Frame before result.1.2)
    (pending : registration.ServerResponseHash) (before : RegistrationWorldSigning.State n)
    (cached : RegistrationSigningShared.Cached (RegistrationWorldSigning.project before)) (previous : Auxiliary)
    (result : (RustM (RegistrationWorldServerPublication.Result Encoded) × RegistrationWorldSigning.State n) × Auxiliary)
    (supported : result ∈ support (((RegistrationNativePlatformServerPublication.program
      (fun query => RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing primitive query)) encode pending).run before).run previous)) :
    RegistrationSigningShared.Cached (RegistrationWorldSigning.project result.1.2) := by
  have law := congrArg (fun work => (work : StateT Auxiliary ProbComp _).run previous)
    (RegistrationNativePlatformJournalWorld.server coins primitive encode pending (before, none))
  rw [StateT.run_map] at law
  rw [← law, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  have safe : Safe (before, none) := ⟨cached, by intro cut impossible; cases impossible⟩
  have after := source_server primitive encode encodeFrame pending (before, none) safe previous inner reached
  cases same
  exact after.1
end BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.source_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.source_beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.source_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.source_server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalCachedPublication.server

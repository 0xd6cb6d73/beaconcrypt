-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityBundlePhase
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
/-! Actual logged source paths retain one-use bundle phases, so a second successful publication at the same owner index is impossible. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxKeyJournal (Whole drop owners)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeIdentityBundlePhase (Keeps Closed)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend


/-- The actual signing-log interpreter retains the source phase policy at every callback. -/
theorem query_keeps (query : TypedSpec.Domain) (before : Whole n KemSK Platform source)
    (result : TypedSpec.Range query × Whole n KemSK Platform source)
    (supported : result ∈ support ((actual query).run before)) : Keeps (owners before) (owners result.2) := by
  exact RegistrationNativeIdentityBundlePhase.handler setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query (drop before) (result.1,drop result.2)
    (RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before result supported)

/-- Every intervening original source callback keeps an earlier published owner's position closed. -/
theorem path_keeps {before after : Whole n KemSK Platform source}
    {calls : List (Call TypedSpec (Whole n KemSK Platform source))} (path : Path actual before calls after) :
    Keeps (owners before) (owners after) := by
  induction path with
  | nil state => exact Keeps.refl _
  | cons call called rest last following ih =>
      exact ih.trans (query_keeps setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer call.query call.before (call.reply,call.after) called)

/-- Successful original logged bundle publication closes this owner to any future bundle. -/
theorem bundle_closed (index : Nat) (before : Whole n KemSK Platform source)
    (result : RustM (Option Pqxdh.Bytes) × Whole n KemSK Platform source) (bytes : Pqxdh.Bytes)
    (returned : result.1=.ok (some bytes))
    (supported : result ∈ support ((actual (.inr (.bundle index))).run before)) : Closed index (owners result.2) := by
  exact RegistrationNativeIdentityBundlePhase.source_bundle_closed setup checks representation created writer index (drop before) (result.1,drop result.2) bytes returned
    (RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle index)) before result supported)

/-- A later original logged bundle cannot return bytes from an earlier published owner. -/
theorem bundle_declines (index : Nat) (before : Whole n KemSK Platform source)
    (result : RustM (Option Pqxdh.Bytes) × Whole n KemSK Platform source) (bytes : Pqxdh.Bytes)
    (closed : Closed index (owners before))
    (supported : result ∈ support ((actual (.inr (.bundle index))).run before)) : result.1≠.ok (some bytes) := by
  exact RegistrationNativeIdentityBundlePhase.source_bundle_declines setup checks representation created writer index (drop before) (result.1,drop result.2) bytes closed
    (RegistrationNativePlatformIdentityCtxKeyJournal.query_support setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle index)) before result supported)

/-- A literal original successful-publication marker carries its own source after-state closedness. -/
theorem call_closed (call : Call TypedSpec (Whole n KemSK Platform source))
    (called : Executed actual call) (index : Nat) (bytes : Pqxdh.Bytes)
    (marked : RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply=some (.bundle index (some bytes))) :
    Closed index (owners call.after) := by
  rcases call with ⟨query,before,reply,after⟩
  cases query with
  | inl coin => cases marked
  | inr command =>
      cases command <;> simp_all [RegistrationNativeRawRegistrationJournal.typedMark]
      obtain ⟨rfl,decoded⟩ := marked
      cases reply with
      | fail error | div => cases decoded
      | ok optional =>
          change optional=some bytes at decoded
          subst optional
          exact bundle_closed setup checks wire route representation created credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer _ before (.ok (some bytes),after) bytes rfl called

/-- A source owner already closed at this callback cannot contribute another successful publication marker. -/
theorem call_declines (call : Call TypedSpec (Whole n KemSK Platform source))
    (called : Executed actual call) (index : Nat) (bytes : Pqxdh.Bytes)
    (closed : Closed index (owners call.before)) :
    RegistrationNativeRawRegistrationJournal.typedMark call.query call.reply≠some (.bundle index (some bytes)) := by
  intro marked
  rcases call with ⟨query,before,reply,after⟩
  cases query with
  | inl coin => cases marked
  | inr command =>
      cases command <;> simp_all [RegistrationNativeRawRegistrationJournal.typedMark]
      obtain ⟨rfl,decoded⟩ := marked
      cases reply with
      | fail error | div => cases decoded
      | ok optional =>
          change optional=some bytes at decoded
          subst optional
          exact bundle_declines setup checks wire route representation created credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer _ before (.ok (some bytes),after) bytes closed called rfl

/-- Two distinct chronological original source callbacks at the same owner index cannot both publish bytes, retaining every intervening failure and later callback. -/
theorem no_second (first second : Call TypedSpec (Whole n KemSK Platform source))
    (earlier : Executed actual first) (later : Executed actual second)
    (middle : List (Call TypedSpec (Whole n KemSK Platform source)))
    (following : Path actual first.after middle second.before)
    (index : Nat) (firstBytes secondBytes : Pqxdh.Bytes)
    (firstMark : RegistrationNativeRawRegistrationJournal.typedMark first.query first.reply=some (.bundle index (some firstBytes)))
    (secondMark : RegistrationNativeRawRegistrationJournal.typedMark second.query second.reply=some (.bundle index (some secondBytes))) : False := by
  have closed := call_closed setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer first earlier index firstBytes firstMark
  have kept := path_keeps setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer following
  exact call_declines setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer second later index secondBytes (kept.closed index closed) secondMark

end BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.query_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.path_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.path_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.bundle_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.bundle_closed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.bundle_declines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.bundle_declines
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.call_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.call_closed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.call_declines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.call_declines
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.no_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityBundleOnce.no_second

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOwnerInvariants

/-! The selected single runtime retains actual generated recipient ownership and the prekey/scalar equation across all dynamic writer outcomes and every initialized native path. Record routing leaves the native owner metadata and pool literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin

open RegistrationNativePlatformOwnerInvariants (Holds)

/-- Each actual runtime callback preserves the generated-row and scalar/prekey invariants. -/
theorem handler (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : Native) (previous next : Platform) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (prior : Holds setup before)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before).run previous)) : Holds setup after := by
  have ordinary (same : RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query =
      RegistrationNativePlatformExperiment.handler (n := n) RegistrationNativePlatformMldsaProgram.coins setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential view failure allocation
          reserveRegistration reservePeer erased helper writer query) : Holds setup after := by
    rw [same] at supported
    exact RegistrationNativePlatformOwnerInvariants.handler RegistrationNativePlatformMldsaProgram.coins setup checks
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query before after previous next reply prior supported
  have routed (query : PqxdhRecordLiftInterface.RecordQuery) (reply : (PqxdhRecordLiftInterface.RecordSpec .O).Range query)
      (called : ((reply, after), next) ∈ support
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route query source).run before).run previous)) : Holds setup after := by
    have fixed := RegistrationNativePlatformOrdinaryTokenFrames.record setup wire reserveFrame route query before after previous next reply called
    have poolEq : after.pool = before.pool := congrArg (fun value => value.2.1) fixed
    have ownersEq : after.beacons = before.beacons := congrArg (fun value => value.2.2) fixed
    simpa only [Holds, ownersEq, poolEq] using prior
  cases query with
  | inl coin => exact ordinary rfl
  | inr command =>
      cases command with
      | serverSend keyId plaintext => exact routed (.inl (.inl (plaintext, keyId))) _ supported
      | serverRaw raw => exact routed (.inl (.inr raw)) _ supported
      | beaconSend owner plaintext => exact routed (.inr (owner, .inl plaintext)) _ supported
      | beaconRaw owner raw => exact routed (.inr (owner, .inr raw)) _ supported
      | _ => exact ordinary rfl

/-- The exact packed source callback retains these operational owner invariants. -/
theorem callback (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (called : Executed impl call)
    (prior : Holds setup call.before.1) : Holds setup call.after.1 := by
  simp only [Executed, RegistrationNativePlatformOrdinaryKemClientJournal.actual, RegistrationNativePlatformPackedState.pack,
    StateT.run, support_map] at called
  obtain ⟨⟨⟨value, native⟩, platform⟩, supported, same⟩ := called
  have replyEq : value = call.reply := congrArg Prod.fst same
  have nativeEq : native = call.after.1 := congrArg (fun result => result.2.1) same
  have platformEq : platform = call.after.2 := congrArg (fun result => result.2.2) same
  rw [replyEq, nativeEq, platformEq] at supported
  exact handler setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer call.query call.before.1 call.after.1 call.before.2 call.after.2 call.reply prior supported

/-- One actual same-run path preserves the owner invariants at its final state. -/
theorem path {before after : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl before calls after) (prior : Holds setup before.1) : Holds setup after.1 := by
  induction reached with
  | nil => exact prior
  | cons call called rest last following ih =>
      exact ih (callback setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer call called prior)

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerInvariants.path

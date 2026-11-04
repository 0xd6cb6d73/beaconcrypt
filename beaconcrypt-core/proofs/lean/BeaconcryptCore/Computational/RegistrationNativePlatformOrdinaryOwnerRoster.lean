-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames
/-! All actual dynamic ordinary routes preserve the complete earlier immutable owner prefix. The corrected registration branches use their literal metadata receipts, while ongoing source records retain the owner list exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerRoster
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

private theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before after : Native) (previous next : Platform) (reply : (PqxdhRecordLiftInterface.RecordSpec .O).Range query)
    (supported : ((reply,after),next) ∈ support (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route query source).run before).run previous)) :
    RegistrationNativeOwnerRoster.Prefix before.beacons after.beacons := by
  have retained := RegistrationNativePlatformOrdinaryTokenFrames.record setup wire reserveFrame route query before after previous next reply supported
  have owners : after.beacons = before.beacons := congrArg (fun fields => fields.2.2) retained
  exact ⟨[],by rw [owners]; simp only [List.append_nil]⟩

/-- Every current source callback retains all prior immutable native owner fields at the same indices. -/
theorem handler [primitive : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : TypedSpec.Domain) (before after : Native) (previous next : Platform) (reply : TypedSpec.Range query)
    (supported : ((reply,after),next) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before).run previous)) :
    RegistrationNativeOwnerRoster.Prefix before.beacons after.beacons := by
  have ordinary (same : RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query =
      RegistrationNativePlatformExperiment.handler RegistrationNativePlatformMldsaProgram.coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential view failure allocation reserveRegistration reservePeer erased helper writer query) :
      RegistrationNativeOwnerRoster.Prefix before.beacons after.beacons := by
    rw [same] at supported
    exact RegistrationNativePlatformOwnerRoster.handler RegistrationNativePlatformMldsaProgram.coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query before after previous next reply supported
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | serverSend keyId plaintext => exact record setup wire reserveFrame route (.inl (.inl (plaintext,keyId))) before after previous next reply supported
    | serverRaw raw => exact record setup wire reserveFrame route (.inl (.inr raw)) before after previous next reply supported
    | beaconSend owner plaintext => exact record setup wire reserveFrame route (.inr (owner,.inl plaintext)) before after previous next reply supported
    | beaconRaw owner raw => exact record setup wire reserveFrame route (.inr (owner,.inr raw)) before after previous next reply supported
    | create _ _ _ | bundle _ | accept _ | build _ _ | finish _ _ | hmac _ _ | hash _ => exact ordinary rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerRoster
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerRoster.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryOwnerRoster.handler

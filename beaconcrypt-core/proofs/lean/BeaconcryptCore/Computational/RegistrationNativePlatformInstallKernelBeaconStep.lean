-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallStep
import BeaconcryptCore.Computational.RegistrationNativeInstallTypedHandles
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallBeaconRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconRuntimeDictionary
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconPreparationRuntime
/-! The actual corrected shared-platform typed finish pairs its own concrete descriptor with its actual returned owner handle. Physical hiddenness follows from that same prepared descriptor and complete runtime. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeaconStep
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativePlatformInstallRuntimeTrace (runtime)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativePlatformInstallKernelStorage (Valid events slots Selected)
open RegistrationNativeInstallStep (RoleStep)
open RegistrationNativeInstallTypedEntry (entry)
open BeaconcryptCore.Refinement
variable {n : Nat} {I KemSK ProviderState Platform E Reader Response Secret : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "sign" => RegistrationNativeMldsa.owned source credential
local notation "callback" => RegistrationNativeInstallRuntimeTrace.callback setup canonical sign seed scalar candidate provider service codec route
local notation "actual" => RegistrationNativePlatformSelectiveInstallKernel.typed setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route


private theorem finish_failed (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual (.inr (.finish index packet))).run before))
    (failed : RegistrationNativeInstallBeaconComplete.present result.1 = false) :
    RoleStep role (events before) (events result.2) (entry (.inr (.finish index packet)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  have original := RegistrationNativePlatformSelectiveInstallKernel.open_support setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route (.inr (.finish index packet)) before result supported
  obtain ⟨added,observed,count⟩ := RegistrationNativePlatformInstallBeaconTyped.finish setup canonical role index packet
    before.2.1.1.1.1 before.1 ((result.1,result.2.2.1.1.1.1),result.2.1)
    (by simpa only [RegistrationNativePlatformPublicFrontend.handler] using original)
  have empty : added = [] := List.eq_nil_of_length_eq_zero (by simpa only [failed, Bool.false_eq_true, and_false, ite_false] using count)
  apply RegistrationNativeInstallStep.of_quiet
  · simpa only [empty, List.append_nil, events] using observed
  · apply List.eq_nil_of_length_eq_zero
    rw [RegistrationNativeInstallTypedHandles.finish_length, failed]
    simp only [Bool.false_eq_true, and_false, ite_false]

private theorem finish_succeeded (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK ProviderState Platform Secret source) (valid : Valid before)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.2.1.1.1.1.1.beacons[index]? = some owner)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual (.inr (.finish index packet))).run before))
    (application : Pqxdh.Bytes) (successful : result.1 = .ok (some application)) :
    RoleStep role (events before) (events result.2) (entry (.inr (.finish index packet)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  obtain ⟨reference, observed, installed⟩ := RegistrationNativePlatformInstallKernelBeacon.finish_success
    setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route index packet before owner found valid.1 result supported application successful
  refine ⟨if role = .beacon then [reference] else [], observed role, ?_, ?_⟩
  · rw [RegistrationNativeInstallTypedHandles.finish_length, successful]
    cases role <;> simp [RegistrationNativeInstallBeaconComplete.present]
  · intro position message publicHandle messageAt handleAt selected
    have member := List.mem_of_getElem? messageAt
    split at member
    · simp only [List.mem_singleton] at member
      subst message
      have same := RegistrationNativeInstallTypedHandles.finish_handle role index packet result.1 position publicHandle handleAt
      subst publicHandle
      obtain ⟨slot, hidden⟩ := installed selected
      exact Option.isSome_iff_exists.mpr ⟨slot, hidden⟩
    · cases member

/-- The literal actual typed owner finish supplies its complete new-handle ordinal receipt for every owner and result. -/
theorem finish (role : PqxdhRecordLiftInterface.Role) (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK ProviderState Platform Secret source) (valid : Valid before)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual (.inr (.finish index packet))).run before)) :
    RoleStep role (events before) (events result.2) (entry (.inr (.finish index packet)) result.1)
      (slots result.2) (Selected setup seed scalar candidate) := by
  have unsuccessful (failed : RegistrationNativeInstallBeaconComplete.present result.1 = false) :=
    finish_failed setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route role index packet before result supported failed
  cases reply : result.1 with
  | fail error | div => simpa only [reply] using unsuccessful (by rw [reply]; rfl)
  | ok replyValue => cases replyValue with
    | none => simpa only [reply] using unsuccessful (by rw [reply]; rfl)
    | some application =>
        cases found : before.2.1.1.1.1.1.beacons[index]? with
        | none =>
            have original := RegistrationNativePlatformSelectiveInstallKernel.open_support setup wire seed scalar candidate provider checks credential selectedOwner selectedAccept
              view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route (.inr (.finish index packet)) before result supported
            simp only [RegistrationNativePlatformPublicFrontend.handler,RegistrationNativePlatformPublicFrontend.executeLocal,
              RegistrationNativePlatformPublicFrontend.beacon,RegistrationNativePlatformPublicFrontend.finish,found,StateT.run] at original
            have absent : result.1 = .ok none := congrArg (fun value => value.1.1) original
            rw [reply] at absent
            cases absent
        | some owner =>
            simpa only [reply] using finish_succeeded setup checks wire credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer service codec route role index packet before valid owner found result supported application reply

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeaconStep
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeaconStep.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeaconStep.finish

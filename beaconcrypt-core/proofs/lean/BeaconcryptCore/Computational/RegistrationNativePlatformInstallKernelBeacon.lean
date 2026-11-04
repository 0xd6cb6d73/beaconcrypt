-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallRuntimeTrace
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeacon
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativePlatformSelectiveInstallKernel (State)
open RegistrationNativePlatformInstallRuntimeTrace (runtime)
open RegistrationNativeInstallOrdinals (messages)
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

/-- A supported successful literal finish records its own descriptor once and derives that selected descriptor's hidden physical owner in the same final state. -/
theorem finish_success (index : Nat) (packet : Option registration.ResponsePacket)
    (before : State n KemSK ProviderState Platform Secret source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.2.1.1.1.1.1.beacons[index]? = some owner)
    (valid : RegistrationNativePlatformHiddenAllocationCore.Holds before.2)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Platform Secret source)
    (supported : result ∈ support ((actual (.inr (.finish index packet))).run before))
    (application : Pqxdh.Bytes) (successful : result.1 = .ok (some application)) :
    ∃ reference : RegistrationNativeRelatedFamily.Message,
      (∀ role, messages role result.2.1.events = messages role before.1.events ++ if role = .beacon then [reference] else []) ∧
      ((∀ bytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar reference = some bytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate bytes = true) →
        ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 (.owner index) = some slot) := by
  rw [RegistrationNativePlatformInstallRuntimeTrace.typed_source,support_map] at supported
  obtain ⟨native,called,returned⟩ := supported
  have reply : native.1.1 = .ok (some application) := (congrArg Prod.fst returned).trans successful
  have closed : ((.ok (some application),native.1.2),native.2) ∈ support
      ((simulateQ (callback ∘ₛ RegistrationNativePlatformPublicCoinEmbedding.embed)
        ((RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.beacon
            (RegistrationNativePlatformPublicFrontend.finish setup canonical source index packet))).run before.2.1.1.1.1)).run (runtime before)) := by
    have same : native = ((.ok (some application),native.1.2),native.2) := Prod.ext (Prod.ext reply rfl) rfl
    rw [← same]
    simpa only [QueryImpl.simulateQ_compose,RegistrationNativePlatformPublicFrontend.handler] using called
  obtain ⟨ready,current,middle,afterOwner,afterEnv,prepared,completed⟩ :=
    RegistrationNativePlatformTypedBeaconCut.finish (callback ∘ₛ RegistrationNativePlatformPublicCoinEmbedding.embed)
      setup canonical index packet before.2.1.1.1.1 native.1.2 owner found (runtime before) native.2 application closed
  rw [RegistrationNativePlatformBeaconRuntimeDictionary.interpreter] at prepared
  rw [RegistrationNativePlatformBeaconRuntimeDictionary.complete] at completed
  have traceEq : native.2.1 = result.2.1 := congrArg (fun value => value.2.1) returned
  have controlEq : native.2.2.1.2 = result.2.2.1.2 := congrArg (fun value => value.2.2.1.2) returned
  have physical : owner.view.worldOwner = index := valid.indexed index owner found
  refine ⟨ready.reference,?_,?_⟩
  · intro role
    have leading := RegistrationNativeInstallBeaconPreparationRuntime.preparation_count setup canonical sign seed scalar candidate provider service codec route
      role owner.scalar owner.view before.2.1.1.1.1.1.environment packet (runtime before) ((.ok (some ready),current),middle) prepared
    have last := RegistrationNativePlatformInstallBeaconRuntime.complete_count setup canonical sign seed scalar candidate provider service codec route
      role owner.view current ready middle.1 middle.2 ((.ok (some application),afterOwner),(afterEnv,native.2)) completed
    rw [traceEq,leading] at last
    simpa only [RegistrationNativeInstallBeaconComplete.present,and_true,runtime] using last
  · intro selected
    have installed := RegistrationNativePlatformInstallBeaconRuntime.complete_traced setup canonical sign seed scalar candidate provider service codec route
      owner.view current ready middle.1 middle.2 ((.ok (some application),afterOwner),(afterEnv,native.2)) completed application rfl selected
    rw [controlEq,physical] at installed
    exact installed

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeacon.finish_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallKernelBeacon.finish_success

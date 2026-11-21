-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallBeaconPreparationRuntime
import BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController

/-! An actual guarded successful typed owner finish records exactly its own same-run Ready descriptor and installs that selected descriptor's physical hidden origin. The complete chronological runtime is retained through its real preparation and completion cuts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallKernelBeacon
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State typed)
open RegistrationNativeInstallRuntimeTrace (callback runtime)
open RegistrationNativeInstallOrdinals (messages)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Every actual successful typed owner finish pairs its own descriptor suffix with its actual returned public owner handle. -/
theorem finish_success (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (selectedOwner selectedAccept : Nat)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State n KemSK ProviderState Secret source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.2.1.1.1.1.beacons[index]? = some owner)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds before.2)
    (result : RustM (Option Pqxdh.Bytes) × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((typed setup checks wire sign seed scalar candidate provider service codec route selectedOwner selectedAccept
      (.inr (.finish index packet))).run before))
    (application : Pqxdh.Bytes) (successful : result.1 = .ok (some application)) :
    ∃ reference : RegistrationNativeRelatedFamily.Message,
      (∀ role, messages role result.2.1.events = messages role before.1.events ++ if role = .beacon then [reference] else []) ∧
      ((∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar reference = some realizedBytes →
        RegistrationNativeSelectiveHiddenService.selected
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) →
        ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.2.2.1.2 (.owner index) = some slot) := by
  rw [RegistrationNativeInstallRuntimeTrace.typed_source, support_map] at supported
  obtain ⟨native, called, returned⟩ := supported
  have reply : native.1.1 = .ok (some application) := (congrArg Prod.fst returned).trans successful
  have actual : ((.ok (some application), native.1.2), native.2) ∈ support
      ((simulateQ (callback setup wire sign seed scalar candidate provider service codec route)
        ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar)
          (.inr (.finish index packet))).run before.2.1.1.1.1)).run (runtime before)) := by
    have same : native = ((.ok (some application), native.1.2), native.2) := Prod.ext (Prod.ext reply rfl) rfl
    rw [← same]
    exact called
  obtain ⟨ready, current, middle, afterOwner, afterEnv, prepared, completed⟩ :=
    RegistrationNativeTypedBeaconAllController.finish (callback setup wire sign seed scalar candidate provider service codec route)
      setup checks wire sign selectedOwner selectedAccept (setup.dh.publicKey scalar) index packet before.2.1.1.1.1 native.1.2 owner found
      (runtime before) native.2 application actual
  have traceEq : native.2.1 = result.2.1 := congrArg (fun value => value.2.1) returned
  have controlEq : native.2.2.1.2 = result.2.2.1.2 := congrArg (fun value => value.2.2.1.2) returned
  have physical : owner.view.worldOwner = index := valid.indexed index owner found
  refine ⟨ready.reference, ?_, ?_⟩
  · intro role
    have leading := RegistrationNativeInstallBeaconPreparationRuntime.preparation_count setup wire sign seed scalar candidate provider service codec route
      role owner.scalar owner.view before.2.1.1.1.1.environment packet (runtime before) ((.ok (some ready), current), middle) prepared
    have last := RegistrationNativeInstallBeaconRuntime.complete_count setup wire sign seed scalar candidate provider service codec route
      role owner.view current ready middle.1 middle.2 ((.ok (some application), afterOwner), (afterEnv, native.2))
      (by simpa only [RegistrationNativeTypedBeaconAllController.interpreter] using completed)
    rw [traceEq, leading] at last
    simpa only [RegistrationNativeInstallBeaconComplete.present, and_true, RegistrationNativeInstallRuntimeTrace.runtime] using last
  · intro selected
    have installed := RegistrationNativeInstallBeaconRuntime.complete_traced setup wire sign seed scalar candidate provider service codec route
      owner.view current ready middle.1 middle.2 ((.ok (some application), afterOwner), (afterEnv, native.2))
      (by simpa only [RegistrationNativeTypedBeaconAllController.interpreter] using completed) application rfl selected
    rw [controlEq, physical] at installed
    exact installed

end BeaconcryptCore.Computational.RegistrationNativeInstallKernelBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallKernelBeacon.finish_success' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallKernelBeacon.finish_success

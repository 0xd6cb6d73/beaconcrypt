-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinary
import BeaconcryptCore.Refinement.AdapterPublicOrdinarySendGate
open CoreModels Aeneas OracleComp OracleSpec beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformExtractedSdkOrdinary (M operations beaconSend beaconReceive)
variable {Platform E I KemSK Reader Response : Type} {base : OracleSpec I}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [PublicWrapperPlatform.Allocator] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [AdapterPublicOrdinaryPlatform.LookupOperations]
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations]

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations]
  [PublicWrapperPlatform.ContainerOperations] [AdapterPublicOrdinaryPlatform.LookupOperations]
  primitives [FrameDispatchFallback.Operations] in
private theorem returned_run {A : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (work : M Platform (RustM (ratchet.concrete.ConcreteRatchetKernel ×A))) :
    (do
      let result ← (⟨work⟩ : RustT (M Platform) _)
      pure (result.2,{self with state:=.Established control binding (AdapterPublicOrdinaryEnvelope.manager result.1)})).run =
      AdapterPublicOrdinaryKernel.returned self control binding <$> work := by
  rw [RustT.run_bind]
  simp only [RustT.run_pure]
  rw [← bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

noncomputable def send (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) :
    M Platform (RustM (Option beaconcrypt_record_send.shared.Encrypted ×beaconcrypt_public_wrapper.beacon.Beacon)) :=
  match AdapterPublicOrdinaryEnvelope.prepareSend bytes control.server_binding.identity_key_id
    self.identity_key_kid binding.associated_data kernel with
  | .ok none=>pure (.ok (none,self))
  | .ok (some context)=>AdapterPublicOrdinaryKernel.returned self control binding <$>
      RegistrationNativePlatformExtractedSdkOrdinaryDriver.send setup codec reserve view failure erased kernel context
  | .fail error=>pure (.fail error)
  | .div=>pure .div

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem send_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel)) (bytes : Slice U8) :
    beaconSend setup codec reserve view failure erased self bytes=
      send setup codec reserve view failure erased self control binding kernel bytes := by
  let := operations setup codec reserve view failure erased
  unfold beaconSend
  rw [AdapterPublicOrdinaryBeacon.send self control binding kernel stored bytes]
  simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
  unfold send
  cases prepared : AdapterPublicOrdinaryEnvelope.prepareSend bytes control.server_binding.identity_key_id
    self.identity_key_kid binding.associated_data kernel with
  | fail error=>rfl
  | div=>rfl
  | ok option=>
      cases option with
      | none=>rfl
      | some context=>exact returned_run self control binding _

noncomputable def receive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased : Array U8 357#usize) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (bytes : Slice U8) :
    M Platform (RustM (Option beaconcrypt.shared.Decrypted ×beaconcrypt_public_wrapper.beacon.Beacon)) :=
  match AdapterPublicOrdinaryEnvelope.prepareReceive bytes control.server_binding.identity_key_id with
  | .ok none=>pure (.ok (none,self))
  | .ok (some frame)=>AdapterPublicOrdinaryKernel.returned self control binding <$>
      RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.received setup codec erased kernel frame.sequence frame.ciphertext binding.associated_data frame.sender
  | .fail error=>pure (.fail error)
  | .div=>pure .div

omit [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem receive_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat →StateT Platform ProbComp (core.result.Result Unit E))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
    (erased : commitment.CommitmentTranscript) (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconEstablished) (binding : session.SessionBinding)
    (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (stored : self.state=.Established control binding (AdapterPublicOrdinaryEnvelope.manager kernel)) (bytes : Slice U8) :
    beaconReceive setup codec reserve view failure erased self bytes=
      receive setup codec erased.bytes self control binding kernel bytes := by
  let := operations setup codec reserve view failure erased
  unfold beaconReceive
  rw [AdapterPublicOrdinaryBeacon.receive self control binding kernel stored bytes]
  unfold receive
  simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
  cases prepared : AdapterPublicOrdinaryEnvelope.prepareReceive bytes control.server_binding.identity_key_id with
  | fail error=>rfl
  | div=>rfl
  | ok option=>
      cases option with
      | none=>rfl
      | some frame=>
          dsimp only
          rw [RegistrationNativePlatformExtractedSdkOrdinaryReceiveDriver.begin_effect]
          rw [← returned_run self control binding]
          simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
          obtain ⟨pending,admitted⟩ := BeaconcryptCore.PanicFreedom.RecordEffects.begin_record_receive_total
            kernel frame.sequence frame.ciphertext binding.associated_data frame.sender
          simp only [admitted]
          rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon.send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon.send_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon.receive_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkOrdinaryBeacon.receive_source

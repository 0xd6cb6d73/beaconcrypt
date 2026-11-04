-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocation
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentOrdinary
/-! The actual corrected raw frontend closes over its literal selective World backend. Registration callbacks retain their restricted source effects; ordinary routes keep their actual post-send allocator and full shared platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyQuery
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


local notation "sourceHandler" => RegistrationNativePlatformSelectiveEntropyNative.handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

noncomputable def environment
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState Platform source))) :
    RegistrationNativeEntropyInterface.Environment n (State n KemSK ProviderState Platform source) :=
  RegistrationNativePlatformSelectiveEntropyEnvironment.environment setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup

noncomputable def reference
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState Platform source))) :=
  RegistrationNativePlatformGatedNativeEntropy.native
    (environment setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup)
    (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount))

/-- Every registration, coin, hash and Server record callback has the actual gated native environment execution before World lowering. -/
theorem ordinary_source
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState Platform source)))
    (query : RegistrationNativeInterface.Spec.Domain)
    (ordinary : RegistrationNativeHiddenEnvironmentOrdinary.Ordinary query)
    (before : State n KemSK ProviderState Platform source) :
    (sourceHandler query).run before = (reference setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup query).run before := by
  cases query with
  | inl coin =>
    rw [RegistrationNativePlatformSelectiveEntropyNative.coin_source]
    simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native,
      RegistrationNativePlatformGatedNativeEntropy.post, bind_pure,
      RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
    rfl
  | inr command => cases command with
    | create edPin mlPin keyId =>
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native, RegistrationNativePlatformGatedNativeEntropy.post, bind_pure, RegistrationNativeEntropyWorld.native]
      convert (RegistrationNativePlatformSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ⟨.create edPin mlPin keyId, trivial⟩ before) using 1; rfl
    | bundle owner =>
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native, RegistrationNativePlatformGatedNativeEntropy.post, bind_pure, RegistrationNativeEntropyWorld.native]
      convert (RegistrationNativePlatformSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ⟨.bundle owner, trivial⟩ before) using 1; rfl
    | accept raw =>
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native, RegistrationNativePlatformGatedNativeEntropy.post, bind_pure, RegistrationNativeEntropyWorld.native]
      convert (RegistrationNativePlatformSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ⟨.accept raw, trivial⟩ before) using 1; rfl
    | build handle application =>
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native, RegistrationNativePlatformGatedNativeEntropy.post, bind_pure, RegistrationNativeEntropyWorld.native]
      convert (RegistrationNativePlatformSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ⟨.build handle application, trivial⟩ before) using 1; rfl
    | finish owner raw =>
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native, RegistrationNativePlatformGatedNativeEntropy.post, bind_pure, RegistrationNativeEntropyWorld.native]
      convert (RegistrationNativePlatformSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ⟨.finish owner raw, trivial⟩ before) using 1; rfl
    | hmac key bytes =>
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native, RegistrationNativePlatformGatedNativeEntropy.post, bind_pure, RegistrationNativeEntropyWorld.native]
      convert (RegistrationNativePlatformSelectiveEntropyNative.environment_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ⟨.hmac key bytes, trivial⟩ before) using 1; rfl
    | hash bytes =>
      rw [RegistrationNativePlatformSelectiveEntropyNative.hash_source]
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native,
        RegistrationNativePlatformGatedNativeEntropy.post, bind_pure,
        RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
      rfl
    | serverSend keyId plaintext =>
      rw [RegistrationNativePlatformSelectiveEntropyNative.server_send_source]
      rfl
    | serverRaw raw =>
      rw [RegistrationNativePlatformSelectiveEntropyNative.server_raw_source]
      simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native,
        RegistrationNativePlatformGatedNativeEntropy.post, bind_pure,
        RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
      rfl
    | beaconSend owner plaintext | beaconRaw owner raw => exact ordinary.elim

variable {Secret Reader Response : Type}
open RegistrationNativeHiddenEnvironmentWorld (lower lower_run lower_lift lower_bind)

/-- The actual complete raw callback has the same gated environment execution at every reached physical allocation state. -/
theorem query_source
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState Platform source)))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RegistrationNativeInterface.Spec.Domain)
    (before : RegistrationNativePlatformHiddenAllocationCore.State n Platform
      (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret source)
    (valid : RegistrationNativePlatformHiddenAllocationCore.Holds before) :
    (lower service codec route (sourceHandler query)).run before =
      (lower service codec route (reference setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup query)).run before := by
  by_cases ordinary : RegistrationNativeHiddenEnvironmentOrdinary.Ordinary query
  · rw [lower_run, lower_run, ordinary_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup query ordinary before.1.1.1]
  · cases query with
    | inl coin => exact (ordinary trivial).elim
    | inr command => cases command with
      | beaconSend index plaintext =>
        cases found : before.1.1.1.1.1.beacons[index]? with
        | some owner =>
          have sourceRun : (sourceHandler (.inr (.beaconSend index plaintext))).run before.1.1.1 =
              (reference setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup (.inr (.beaconSend index plaintext))).run before.1.1.1 := by
            rw [RegistrationNativePlatformSelectiveEntropyNative.beacon_send_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index plaintext owner before.1.1.1 found,
              valid.indexed index owner found]
            rfl
          rw [lower_run, lower_run, sourceRun]
        | none =>
          rw [lower_run, RegistrationNativePlatformSelectiveEntropyNative.send_missing setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index plaintext before.1.1.1 found,
            CborRawRecordOriginFlatten.interpret_pure, map_pure]
          change pure (none,before) = (lower service codec route
            ((StateT.lift ((WorldSpec n).query (.inr (.inr (.inr (index,.inl plaintext)))) : OracleComp (WorldSpec n) _) :
              StateT (State n KemSK ProviderState Platform source) (OracleComp (WorldSpec n)) (Option RawCtxSourceSend.Encrypted)) >>= fun output =>
              RegistrationNativePlatformGatedRecordInterface.closed
                (RegistrationNativePlatformOrdinaryGate.gate
                  (fun amount => RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount))
                  (fun value => value.ciphertext.length) output))).run before
          rw [lower_bind]
          simp only [StateT.run_bind, lower_lift]
          have absent := RegistrationNativePlatformHiddenAllocationCore.missing before valid index found
          rw [RegistrationNativeHiddenMissingRecord.send_missing service codec route index plaintext _ _ _ absent.1 absent.2]
          simp only [map_pure, pure_bind]
          rfl
      | beaconRaw index raw =>
        cases found : before.1.1.1.1.1.beacons[index]? with
        | some owner =>
          have sourceRun : (sourceHandler (.inr (.beaconRaw index raw))).run before.1.1.1 =
              (reference setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer startup (.inr (.beaconRaw index raw))).run before.1.1.1 := by
            rw [RegistrationNativePlatformSelectiveEntropyNative.beacon_raw_source setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index raw owner before.1.1.1 found,
              valid.indexed index owner found]
            simp only [reference, RegistrationNativePlatformGatedNativeEntropy.native,
              RegistrationNativePlatformGatedNativeEntropy.post, bind_pure,
              RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
            rfl
          rw [lower_run, lower_run, sourceRun]
        | none =>
          rw [lower_run, RegistrationNativePlatformSelectiveEntropyNative.raw_missing setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index raw before.1.1.1 found,
            CborRawRecordOriginFlatten.interpret_pure, map_pure]
          change pure (.None,before) = (lower service codec route (StateT.lift
            ((WorldSpec n).query (.inr (.inr (.inr (index,.inr raw)))) : OracleComp (WorldSpec n) _))).run before
          rw [lower_lift]
          have absent := RegistrationNativePlatformHiddenAllocationCore.missing before valid index found
          rw [RegistrationNativeHiddenMissingRecord.raw_missing service codec route index raw _ _ _ absent.1, map_pure]
      | _ => exact (ordinary trivial).elim

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyQuery

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyQuery.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyQuery.ordinary_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyQuery.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyQuery.query_source

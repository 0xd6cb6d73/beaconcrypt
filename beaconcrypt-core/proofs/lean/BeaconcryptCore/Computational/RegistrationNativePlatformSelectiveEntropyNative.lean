-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyRecords
/-! The actual corrected raw frontend closes over its literal selective World backend. Registration callbacks retain their restricted source effects; ordinary routes keep their actual post-send allocator and full shared platform state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative
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

noncomputable def handler : QueryImpl RegistrationNativeInterface.Spec
    (StateT (State n KemSK ProviderState Platform source) (OracleComp (WorldSpec n))) := fun query =>
  close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (RegistrationNativePlatformPublicFrontendCaps.raw setup checks wire source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)

/-- The literal corrected raw registration body is exactly its restricted environment effect tree. -/
theorem environment_source
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : State n KemSK ProviderState Platform source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr query.val)).run before =
      simulateQ effectLift ((RegistrationNativePlatformSelectiveEntropyEnvironment.step setup checks wire source credential seed scalar candidate provider
        selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before) :=
  (RegistrationNativePlatformSelectiveEntropyEnvironment.step_source setup checks wire source credential seed scalar candidate provider
    selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before).symm

/-- Actual source coins use the one shared World coin surface. -/
theorem coin_source (query : unifSpec.Domain) (before : State n KemSK ProviderState Platform source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inl query)).run before =
      (fun reply => (reply,before)) <$> coinLift query := by
  change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (RegistrationNativePlatformPublicFrontend.executeLocal (StateT.lift (RegistrationNativePlatformPublicFrontend.effect (.inl query))))).run before = _
  exact effect_source setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider (.inl query) before

/-- The literal public hash reaches the same shared CTX effect without changing either local state. -/
theorem hash_source (bytes : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes))).run before =
      (fun reply => (reply,before)) <$> effectLift (.inr (.hash bytes)) := by
  change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (RegistrationNativePlatformPublicFrontend.executeLocal (StateT.lift (RegistrationNativePlatformPublicFrontend.effect (.inr (.hash bytes)))))).run before = _
  exact effect_source setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider (.inr (.hash bytes)) before

/-- Literal raw Server send retains the complete source post-send gate. -/
theorem server_send_source (keyId : U64) (plaintext : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext))).run before =
      (RegistrationNativePlatformSelectiveEntropyRecords.worldSend reserveFrame (.inl keyId) plaintext).run before := by
  simp only [handler, RegistrationNativePlatformPublicFrontendCaps.raw, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.handler]
  exact congrArg (fun action => action.run before)
    (RegistrationNativePlatformSelectiveEntropyRecords.server_send (source := source) setup wire (RegistrationNativeMldsa.owned source credential)
      seed scalar candidate provider reserveFrame keyId plaintext)

/-- Literal raw Server receive preserves the actual bytes and the complete common local state. -/
theorem server_raw_source (raw : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw))).run before =
      (fun reply => (reply,before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inl (.inr raw)))) : OracleComp (WorldSpec n) _) := by
  exact RegistrationNativePlatformSelectiveEntropyRecords.server_raw setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider reserveFrame raw before

/-- Existing raw Beacon sends use the retained physical owner and the same actual gate. -/
theorem beacon_send_source (index : Nat) (plaintext : Pqxdh.Bytes) (owner : RegistrationNativePublicOwners.Owner source)
    (before : State n KemSK ProviderState Platform source) (found : before.1.1.beacons[index]? = some owner) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext))).run before =
      (RegistrationNativePlatformSelectiveEntropyRecords.worldSend reserveFrame (.inr owner.view.worldOwner) plaintext).run before := by
  simp only [handler, RegistrationNativePlatformPublicFrontendCaps.raw, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.handler]
  exact RegistrationNativePlatformSelectiveEntropyRecords.beacon_send setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider reserveFrame index plaintext owner before found

/-- Existing raw Beacon receives keep the literal stored owner and source bytes. -/
theorem beacon_raw_source (index : Nat) (raw : Pqxdh.Bytes) (owner : RegistrationNativePublicOwners.Owner source)
    (before : State n KemSK ProviderState Platform source) (found : before.1.1.beacons[index]? = some owner) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw))).run before =
      (fun reply => (reply,before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inr (owner.view.worldOwner,.inr raw)))) : OracleComp (WorldSpec n) _) := by
  simp only [handler, RegistrationNativePlatformPublicFrontendCaps.raw, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.handler]
  exact RegistrationNativePlatformSelectiveEntropyRecords.beacon_raw setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider reserveFrame index raw owner before found

/-- A missing raw Beacon send has no actual source or platform effect. -/
theorem send_missing (index : Nat) (plaintext : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source)
    (missing : before.1.1.beacons[index]? = none) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext))).run before = pure (none,before) := by
  simp only [handler, RegistrationNativePlatformPublicFrontendCaps.raw, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.handler]
  exact RegistrationNativePlatformSelectiveEntropyRecords.send_missing setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider reserveFrame index plaintext before missing

/-- A missing raw Beacon receive retains the complete source and platform state. -/
theorem raw_missing (index : Nat) (raw : Pqxdh.Bytes) (before : State n KemSK ProviderState Platform source)
    (missing : before.1.1.beacons[index]? = none) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw))).run before = pure (.None,before) := by
  simp only [handler, RegistrationNativePlatformPublicFrontendCaps.raw, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePlatformPublicFrontend.handler]
  exact RegistrationNativePlatformSelectiveEntropyRecords.raw_missing setup wire (RegistrationNativeMldsa.owned source credential)
    seed scalar candidate provider reserveFrame index raw before missing

end BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.environment_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.environment_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.coin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.coin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.hash_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.server_send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.server_send_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.server_raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.server_raw_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.beacon_send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.beacon_send_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.beacon_raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.beacon_raw_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.send_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.send_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.raw_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyNative.raw_missing

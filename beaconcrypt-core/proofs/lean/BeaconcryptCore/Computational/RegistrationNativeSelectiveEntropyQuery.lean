-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationJoint
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyOrdinary

/-! Actual source-to-entropy query equality follows from concrete reached allocation metadata. Existing Beacon handles use their stored physical handle; missing indices stutter in both actual interpreters with no dummy request effect. The whole-game proof must derive and preserve this allocation invariant from actual startup. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyQuery
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State environment)
open RegistrationNativeSelectiveEntropyNative (handler)
open RegistrationNativeSelectiveEntropyEffects (close)
open RegistrationNativeHiddenEnvironmentWorld (lower lower_run lower_lift)
variable {n : Nat} {ι KemSK ProviderState Secret Reader Response : Type} {base : OracleSpec ι}

/-- Every literal native query agrees with the original entropy environment at its actual reached allocation state. -/
theorem query_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (startup : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × State n KemSK ProviderState source)))
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RegistrationNativeInterface.Spec.Domain)
    (before : RegistrationNativeSelectiveAllocationJoint.State n KemSK ProviderState Secret source)
    (valid : RegistrationNativeSelectiveAllocationJoint.Holds before) :
    (lower service codec route (handler setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept query)).run before =
      (lower service codec route (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar candidate provider
        selectedOwner selectedAccept startup) query)).run before := by
  by_cases ordinary : RegistrationNativeSelectiveEntropyOrdinary.Ordinary query
  · rw [lower_run, lower_run, RegistrationNativeSelectiveEntropyOrdinary.query_source setup checks wire source credential
      seed scalar candidate provider selectedOwner selectedAccept startup query ordinary before.1.1.1]
  · cases query with
    | inl coin => exact (ordinary trivial).elim
    | inr command => cases command with
      | beaconSend index plaintext =>
          cases found : before.1.1.1.1.beacons[index]? with
          | some owner =>
              have sourceRun : (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
                  (.inr (.beaconSend index plaintext))).run before.1.1.1 =
                  (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar candidate provider
                    selectedOwner selectedAccept startup) (.inr (.beaconSend index plaintext))).run before.1.1.1 := by
                simp only [handler, RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose,
                  RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePublicFrontend.handler]
                change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
                  (RegistrationNativePublicFrontend.record (.inr (index, .inl plaintext)))).run before.1.1.1 = _
                rw [RegistrationNativeSelectiveEntropyRecords.beacon_send_present setup wire
                  (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider index plaintext owner before.1.1.1 found,
                  valid.indexed index owner found]
                simp only [RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
                rfl
              rw [lower_run, lower_run, sourceRun]
          | none =>
              have sourceRun : (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
                  (.inr (.beaconSend index plaintext))).run before.1.1.1 = pure (none, before.1.1.1) := by
                simpa only [handler, RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose,
                  RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePublicFrontend.handler,
                  PqxdhDeploymentNative.absent] using
                RegistrationNativeSelectiveEntropyRecords.beacon_send_absent setup wire
                  (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider index plaintext before.1.1.1 found
              rw [lower_run, sourceRun, CborRawRecordOriginFlatten.interpret_pure, map_pure]
              change pure (none, before) = (lower service codec route (StateT.lift
                ((PqxdhRecordLiftInterface.WorldSpec n).query (.inr (.inr (.inr (index, .inl plaintext)))) :
                  OracleComp (PqxdhRecordLiftInterface.WorldSpec n) _))).run before
              rw [lower_lift, RegistrationNativeHiddenMissingRecord.send_missing service codec route index plaintext _ _ _
                (RegistrationNativeSelectiveAllocationJoint.world_missing before valid index found)
                (RegistrationNativeSelectiveAllocationJoint.cursor_missing before valid index found), map_pure]
      | beaconRaw index raw =>
          cases found : before.1.1.1.1.beacons[index]? with
          | some owner =>
              have sourceRun : (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
                  (.inr (.beaconRaw index raw))).run before.1.1.1 =
                  (RegistrationNativeEntropyWorld.native (environment setup checks wire source credential seed scalar candidate provider
                    selectedOwner selectedAccept startup) (.inr (.beaconRaw index raw))).run before.1.1.1 := by
                simp only [handler, RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose,
                  RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePublicFrontend.handler]
                change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
                  (RegistrationNativePublicFrontend.record (.inr (index, .inr raw)))).run before.1.1.1 = _
                rw [RegistrationNativeSelectiveEntropyRecords.beacon_raw_present setup wire
                  (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider index raw owner before.1.1.1 found,
                  valid.indexed index owner found]
                simp only [RegistrationNativeEntropyWorld.native, StateT.run_lift, bind_pure_comp]
                rfl
              rw [lower_run, lower_run, sourceRun]
          | none =>
              have sourceRun : (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept
                  (.inr (.beaconRaw index raw))).run before.1.1.1 = pure (.None, before.1.1.1) := by
                simpa only [handler, RegistrationNativeHiddenEnvironmentRaw.frontend, QueryImpl.apply_compose,
                  RegistrationNativeRawAdapter.adapter, simulateQ_spec_query, RegistrationNativePublicFrontend.handler,
                  PqxdhDeploymentNative.absent] using
                RegistrationNativeSelectiveEntropyRecords.beacon_raw_absent setup wire
                  (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider index raw before.1.1.1 found
              rw [lower_run, sourceRun, CborRawRecordOriginFlatten.interpret_pure, map_pure]
              change pure (.None, before) = (lower service codec route (StateT.lift
                ((PqxdhRecordLiftInterface.WorldSpec n).query (.inr (.inr (.inr (index, .inr raw)))) :
                  OracleComp (PqxdhRecordLiftInterface.WorldSpec n) _))).run before
              rw [lower_lift, RegistrationNativeHiddenMissingRecord.raw_missing service codec route index raw _ _ _
                (RegistrationNativeSelectiveAllocationJoint.world_missing before valid index found), map_pure]
      | _ => exact (ordinary trivial).elim

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyQuery

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyQuery.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyQuery.query_source

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyRecords

/-! The closed actual raw native frontend has the literal entropy-interface World effects for coins, hashing and Server records. Registration callbacks use the separately proved restricted environment compiler. Beacon routing continues to use its retained physical owner handle until allocation correspondence is proved. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec effectLift coinLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveEntropyEnvironment (State)
open RegistrationNativeSelectiveEntropyEffects (close effect_source server_record_source)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

noncomputable def handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) :
    QueryImpl RegistrationNativeInterface.Spec (StateT (State n KemSK ProviderState source) (OracleComp (WorldSpec n))) := fun query =>
  close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (RegistrationNativeHiddenEnvironmentRaw.frontend setup checks wire source (RegistrationNativeMldsa.owned source credential)
      selectedOwner selectedAccept (setup.dh.publicKey scalar) query)

/-- Every literal registration environment callback agrees with the actual restricted entropy-interface callback. -/
theorem environment_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (query : RegistrationNativeEntropyInterface.EnvQuery) (before : State n KemSK ProviderState source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (.inr query.val)).run before =
      simulateQ effectLift ((RegistrationNativeSelectiveEntropyEnvironment.step setup checks wire source credential seed scalar candidate provider
        selectedOwner selectedAccept query).run before) :=
  (RegistrationNativeSelectiveEntropyEnvironment.step_source setup checks wire source credential seed scalar candidate provider
    selectedOwner selectedAccept query before).symm

/-- The actual raw native coin callback reaches the same shared World coin. -/
theorem coin_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (query : unifSpec.Domain)
    (before : State n KemSK ProviderState source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (.inl query)).run before =
      (fun reply => (reply, before)) <$> coinLift query := by
  change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (StateT.lift (RegistrationNativePublicFrontend.effect (.inl query)))).run before = _
  exact effect_source setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider (.inl query) before

/-- The actual public hash callback uses the one shared CTX cache and retains both actual local states. -/
theorem hash_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (bytes : Pqxdh.Bytes)
    (before : State n KemSK ProviderState source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (.inr (.hash bytes))).run before =
      (fun reply => (reply, before)) <$> effectLift (.inr (.hash bytes)) := by
  change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (StateT.lift (RegistrationNativePublicFrontend.effect (.inr (.hash bytes))))).run before = _
  exact effect_source setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider (.inr (.hash bytes)) before

/-- Native Server sends retain the literal original key identifier and plaintext. -/
theorem server_send_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (keyId : U64) (plaintext : Pqxdh.Bytes)
    (before : State n KemSK ProviderState source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (.inr (.serverSend keyId plaintext))).run before =
      (fun reply => (reply, before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inl (.inl (plaintext, keyId))))) : OracleComp (WorldSpec n) _) := by
  change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (RegistrationNativePublicFrontend.record (.inl (.inl (plaintext, keyId))))).run before = _
  exact server_record_source setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider (.inl (plaintext, keyId)) before

/-- Native Server raw receives retain every literal byte and the same source reply. -/
theorem server_raw_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat) (raw : Pqxdh.Bytes)
    (before : State n KemSK ProviderState source) :
    (handler setup checks wire source credential seed scalar candidate provider selectedOwner selectedAccept (.inr (.serverRaw raw))).run before =
      (fun reply => (reply, before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inl (.inr raw)))) : OracleComp (WorldSpec n) _) := by
  change (close setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider
    (RegistrationNativePublicFrontend.record (.inl (.inr raw)))).run before = _
  exact server_record_source setup wire (RegistrationNativeMldsa.owned source credential) seed scalar candidate provider (.inr raw) before

end BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.environment_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.environment_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.coin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.coin_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.hash_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.server_send_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.server_send_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.server_raw_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNative.server_raw_source

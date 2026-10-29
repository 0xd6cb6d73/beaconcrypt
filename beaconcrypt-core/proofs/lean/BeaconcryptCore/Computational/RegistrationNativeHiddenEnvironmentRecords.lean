-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects

/-! Actual ongoing Beacon record commands use the stored World owner handle. Existing and absent local handles retain their distinct source branches; index coincidence is not inferred from key equality or private KEM handles. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironment (State)
open RegistrationNativeHiddenEnvironmentEffects (close close_run)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Existing native local owner handles route to the literal retained World owner handle and retain both local states. -/
theorem beacon_send_present (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (index : Nat) (plaintext : Pqxdh.Bytes)
    (owner : RegistrationNativePublicOwners.Owner source) (before : State n KemSK ProviderState source)
    (found : before.1.beacons[index]? = some owner) :
    (close setup wire sign seed scalar provider (RegistrationNativePublicFrontend.record (.inr (index, .inl plaintext)))).run before =
      (fun reply => (reply, before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inr (owner.view.worldOwner, .inl plaintext)))) : OracleComp (WorldSpec n) _) := by
  have actual : (RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) (.inr (index, .inl plaintext))).run before.1 =
      (fun reply => (reply, before.1)) <$>
        ((RegistrationNativePublicFrontend.Spec n KemSK).query (.inr (.inr (owner.view.worldOwner, .inl plaintext))) :
          OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) := by
    simp only [RegistrationNativePublicFrontend.record, StateT.run, found]
    rfl
  rw [close_run, actual]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map,
    RegistrationNativeHiddenInterpreter.handler, StateT.run_lift, bind_pure_comp, Functor.map_map]
  rfl


/-- A missing local owner causes the actual frontend to make no ongoing record query. -/
theorem beacon_send_absent (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (index : Nat) (plaintext : Pqxdh.Bytes)
    (before : State n KemSK ProviderState source) (missing : before.1.beacons[index]? = none) :
    (close setup wire sign seed scalar provider (RegistrationNativePublicFrontend.record (.inr (index, .inl plaintext)))).run before =
      pure (PqxdhDeploymentNative.absent (.inl plaintext), before) := by
  have actual : (RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) (.inr (index, .inl plaintext))).run before.1 =
      pure (PqxdhDeploymentNative.absent (.inl plaintext), before.1) := by
    simp only [RegistrationNativePublicFrontend.record, StateT.run, missing, PqxdhDeploymentNative.absent]
  rw [close_run, actual]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]


/-- Existing native local owner handles route to the literal retained World owner handle and retain both local states. -/
theorem beacon_raw_present (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (index : Nat) (raw : Pqxdh.Bytes)
    (owner : RegistrationNativePublicOwners.Owner source) (before : State n KemSK ProviderState source)
    (found : before.1.beacons[index]? = some owner) :
    (close setup wire sign seed scalar provider (RegistrationNativePublicFrontend.record (.inr (index, .inr raw)))).run before =
      (fun reply => (reply, before)) <$>
        ((WorldSpec n).query (.inr (.inr (.inr (owner.view.worldOwner, .inr raw)))) : OracleComp (WorldSpec n) _) := by
  have actual : (RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) (.inr (index, .inr raw))).run before.1 =
      (fun reply => (reply, before.1)) <$>
        ((RegistrationNativePublicFrontend.Spec n KemSK).query (.inr (.inr (owner.view.worldOwner, .inr raw))) :
          OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) := by
    simp only [RegistrationNativePublicFrontend.record, StateT.run, found]
    rfl
  rw [close_run, actual]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map,
    RegistrationNativeHiddenInterpreter.handler, StateT.run_lift, bind_pure_comp, Functor.map_map]
  rfl


/-- A missing local owner causes the actual frontend to make no ongoing record query. -/
theorem beacon_raw_absent (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (index : Nat) (raw : Pqxdh.Bytes)
    (before : State n KemSK ProviderState source) (missing : before.1.beacons[index]? = none) :
    (close setup wire sign seed scalar provider (RegistrationNativePublicFrontend.record (.inr (index, .inr raw)))).run before =
      pure (PqxdhDeploymentNative.absent (.inr raw), before) := by
  have actual : (RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) (.inr (index, .inr raw))).run before.1 =
      pure (PqxdhDeploymentNative.absent (.inr raw), before.1) := by
    simp only [RegistrationNativePublicFrontend.record, StateT.run, missing, PqxdhDeploymentNative.absent]
  rw [close_run, actual]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]


end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_send_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_send_present
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_send_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_send_absent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_raw_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_raw_present
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_raw_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentRecords.beacon_raw_absent

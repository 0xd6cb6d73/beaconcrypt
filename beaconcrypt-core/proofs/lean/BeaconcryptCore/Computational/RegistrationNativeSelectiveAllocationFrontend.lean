-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationService
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyNoDemand
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationStartup

/-! The actual selective frontend preserves physical owner allocation. Allocation-free commands use their literal source footprints and universal local owner receipts. Creation has a derived zero-demand cap, so its complete execution is exactly the existing actual constructor with the extra cache retained. No caller-owned allocation or semantic-simulation condition is introduced at a security endpoint. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationFrontend
attribute [local irreducible] RegistrationNativePublicOwners.create
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeSelectiveAllocationJoint (State Holds drop dropLocal)
open RegistrationNativeHiddenEnvironmentWorld (lower lower_run)
open RegistrationNativeHiddenAllocationCore (Allowed WorldAllowed mapped)
open RegistrationNativeHiddenAllocationOwners (Indexed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem local_supported (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (supported : result ∈ support ((lower service codec route
      (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider work)).run before)) :
    (result.1, result.2.1.1.1.1) ∈ support (work.run before.1.1.1.1) := by
  rw [lower_run, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have possible := RegistrationNativeHiddenAllocationStartup.interpreted_support service codec route
    ((RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider work).run before.1.1.1)
    before.1.1.2 before.1.2 before.2 inner reached
  rw [RegistrationNativeSelectiveEntropyEffects.close_run, support_map] at possible
  obtain ⟨backend, backendReached, actual⟩ := possible
  have original : backend.1 ∈ support (work.run before.1.1.1.1) := by
    apply support_simulateQ_run'_subset
      (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) _ before.1.1.1.2
    rw [StateT.run'_eq, support_map]
    exact ⟨backend, backendReached, rfl⟩
  cases returned
  have same := congrArg (fun observed : Value × RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source =>
    (observed.1, observed.2.1)) actual
  change backend.1 = (inner.1.1.1.1, inner.1.1.1.2.1) at same
  rw [← same]
  exact original

private theorem completed (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT (RegistrationNativeSelectiveEntropyEnvironment.State n KemSK ProviderState source)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (valid : Holds before) (supported : result ∈ support ((lower service codec route work).run before))
    (length : result.2.1.2.owners.length = result.2.1.1.1.1.beacons.length)
    (indexed : Indexed result.2.1.1.1.1.beacons) : Holds result.2 := by
  refine ⟨length, indexed, ?_⟩
  exact RegistrationNativeHiddenJointCursor.absent _ _
    (RegistrationNativeHiddenJointCursorWorld.lower_domain service codec route work before result supported
      (RegistrationNativeHiddenJointCursor.of_absent _ _ valid.cursor))

/-- Every actual allocation-free selective command preserves joint physical allocation using its unchanged local controller receipts. -/
theorem quiet (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (valid : Holds before) (safe : AllQueriesSatisfy (work.run before.1.1.1.1) Allowed)
    (localReceipt : ∀ output, output ∈ support (work.run before.1.1.1.1) →
      output.2.beacons.length = before.1.1.1.1.beacons.length ∧ Indexed output.2.beacons)
    (supported : result ∈ support ((lower service codec route
      (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider work)).run before)) : Holds result.2 := by
  have footprint : AllQueriesSatisfy
      ((RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider work).run before.1.1.1) WorldAllowed := by
    rw [RegistrationNativeSelectiveEntropyEffects.close_run]
    exact mapped _ _ WorldAllowed
      (RegistrationNativeSelectiveAllocationService.program_safe setup wire sign seed scalar candidate provider _ before.1.1.1.2 safe)
  have physical := RegistrationNativeHiddenAllocationWorld.noappend service codec route _ before result footprint supported
  have fields := localReceipt (result.1, result.2.1.1.1.1)
    (local_supported setup wire sign seed scalar candidate provider service codec route work before result supported)
  exact completed service codec route _ before result valid supported
    (physical.trans (valid.length.trans fields.1.symm)) fields.2

/-- The genuine optional constructor preserves joint allocation and the untouched nonselected table on every source outcome. -/
theorem create (setup : Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK ProviderState Secret source) (result : RustM (Option Nat) × State n KemSK ProviderState Secret source)
    (valid : Holds before)
    (supported : result ∈ support ((lower service codec route
      (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider
        (RegistrationNativePublicFrontend.beacon
          (RegistrationNativePublicOwners.create setup source selected publicPrekey edPin mlPin keyId)))).run before)) : Holds result.2 := by
  have bounded := RegistrationNativePublicCaps.handler_bound (n := n) setup checks wire source sign selected selectedAccept publicPrekey
    (.inr (.create edPin mlPin keyId)) before.1.1.1.1
  change ((RegistrationNativePublicFrontend.beacon
    (RegistrationNativePublicOwners.create setup source selected publicPrekey edPin mlPin keyId)).run before.1.1.1.1).IsQueryBoundP
      (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) 0 at bounded
  have projected := RegistrationNativeSelectiveEntropyNoDemand.lower_base setup wire sign seed scalar candidate provider service codec route
    (RegistrationNativePublicFrontend.beacon (RegistrationNativePublicOwners.create setup source selected publicPrekey edPin mlPin keyId)) before bounded
  have oldSupport : (result.1, drop result.2) ∈ support ((lower service codec route
      (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider
        (RegistrationNativePublicFrontend.beacon
          (RegistrationNativePublicOwners.create setup source selected publicPrekey edPin mlPin keyId)))).run (drop before)) := by
    rw [← projected, support_map]
    exact ⟨result, supported, rfl⟩
  exact RegistrationNativeHiddenAllocationFrontend.create setup wire sign seed scalar provider service codec route selected publicPrekey
    edPin mlPin keyId (drop before) (result.1, drop result.2) valid oldSupport

end BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationFrontend.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationFrontend.quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationFrontend.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveAllocationFrontend.create

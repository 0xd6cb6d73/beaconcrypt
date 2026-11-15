-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationBirth
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationExecution
import BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld

/-! Actual local creation extends both rosters with the allocator's literal old length. Other allocation-free frontend programs preserve that correspondence whenever their verified local controller preserves owner addresses. The cursor-domain component is derived from the actual World execution under arbitrary private services. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFrontend
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
open RegistrationNativeHiddenEnvironmentJoint (State Holds)
open RegistrationNativeHiddenAllocationOwners (Indexed)
open RegistrationNativeHiddenAllocationCore (Allowed WorldAllowed)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem completed (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT (RegistrationNativeHiddenEnvironment.State n KemSK ProviderState source)
      (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)) Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (valid : Holds before)
    (supported : result ∈ support ((lower service codec route work).run before))
    (length : result.2.1.2.owners.length = result.2.1.1.1.1.beacons.length)
    (indexed : Indexed result.2.1.1.1.1.beacons) : Holds result.2 := by
  refine ⟨length, indexed, ?_⟩
  exact RegistrationNativeHiddenJointCursor.absent _ _
    (RegistrationNativeHiddenJointCursorWorld.lower_domain service codec route work before result supported
      (RegistrationNativeHiddenJointCursor.of_absent _ _ valid.cursor))

/-- Actual allocation-free frontend work retains the joint physical address invariant, using its actual local output receipts. -/
theorem quiet (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (valid : Holds before) (safe : AllQueriesSatisfy (work.run before.1.1.1.1) Allowed)
    (localReceipt : ∀ output, output ∈ support (work.run before.1.1.1.1) →
      output.2.beacons.length = before.1.1.1.1.beacons.length ∧ Indexed output.2.beacons)
    (supported : result ∈ support ((lower service codec route
      (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider work)).run before)) : Holds result.2 := by
  have footprint : AllQueriesSatisfy
      ((RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider work).run before.1.1.1) WorldAllowed := by
    rw [RegistrationNativeHiddenEnvironmentEffects.close_run]
    exact RegistrationNativeHiddenAllocationCore.mapped _ _ WorldAllowed
      (RegistrationNativeHiddenAllocationService.program setup wire sign seed scalar provider _ before.1.1.1.2 safe)
  have physical := RegistrationNativeHiddenAllocationWorld.noappend service codec route _ before result footprint supported
  apply completed service codec route _ before result valid supported
  · have sourceResult := supported
    rw [RegistrationNativeHiddenAllocationExecution.frontend, support_map] at sourceResult
    obtain ⟨inner, reached, returned⟩ := sourceResult
    have possible : inner.1 ∈ support (work.run before.1.1.1.1) := by
      apply support_simulateQ_run'_subset
        (RegistrationNativeHiddenAllocationExecution.publicCallback setup wire sign seed scalar provider service codec route) _
        (RegistrationNativeHiddenAllocationExecution.runtime before)
      rw [StateT.run'_eq, support_map]
      exact ⟨inner, reached, rfl⟩
    have localFields := localReceipt inner.1 possible
    cases returned
    exact physical.trans (valid.length.trans localFields.1.symm)
  · have sourceResult := supported
    rw [RegistrationNativeHiddenAllocationExecution.frontend, support_map] at sourceResult
    obtain ⟨inner, reached, returned⟩ := sourceResult
    have possible : inner.1 ∈ support (work.run before.1.1.1.1) := by
      apply support_simulateQ_run'_subset
        (RegistrationNativeHiddenAllocationExecution.publicCallback setup wire sign seed scalar provider service codec route) _
        (RegistrationNativeHiddenAllocationExecution.runtime before)
      rw [StateT.run'_eq, support_map]
      exact ⟨inner, reached, rfl⟩
    cases returned
    exact (localReceipt inner.1 possible).2

private theorem native_completed (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : State n KemSK ProviderState Secret source) (result : Value × State n KemSK ProviderState Secret source)
    (valid : Holds before)
    (receipt : ∀ inner, inner ∈ support ((simulateQ
      (RegistrationNativeHiddenAllocationRuntime.callback setup wire sign seed scalar provider service codec route)
      ((work.run (before.1.1.1.1.beacons.map RegistrationNativePublicOwners.restore)).run
        before.1.1.1.1.environment)).run (RegistrationNativeHiddenAllocationExecution.runtime before)) →
      inner.2.1.2.owners.length = inner.1.1.2.length ∧
        RegistrationNativeHiddenAllocationOwners.NativeIndexed inner.1.1.2)
    (supported : result ∈ support ((lower service codec route
      (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider
        (RegistrationNativePublicFrontend.beacon
          (RegistrationNativePublicOwners.executeLocal selected publicPrekey work)))).run before)) : Holds result.2 := by
  apply completed service codec route _ before result valid supported
  all_goals
    have native := supported
    rw [RegistrationNativeHiddenAllocationExecution.native, support_map] at native
    obtain ⟨inner, reached, returned⟩ := native
    have fields := receipt inner reached
    cases returned
  · exact fields.1.trans (RegistrationNativeHiddenAllocationOwners.pack_length selected publicPrekey inner.1.1.2).symm
  · exact RegistrationNativeHiddenAllocationOwners.pack selected publicPrekey inner.1.1.2 fields.2

/-- Actual public creation preserves joint allocation on every optional constructor outcome. -/
theorem create (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK ProviderState Secret source) (result : RustM (Option Nat) × State n KemSK ProviderState Secret source)
    (valid : Holds before)
    (supported : result ∈ support ((lower service codec route
      (RegistrationNativeHiddenEnvironmentEffects.close setup wire sign seed scalar provider
        (RegistrationNativePublicFrontend.beacon
          (RegistrationNativePublicOwners.create setup source selected publicPrekey edPin mlPin keyId)))).run before)) : Holds result.2 := by
  simp only [RegistrationNativePublicOwners.create] at supported
  generalize workEq : (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId :
    RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State (RustM (Option Nat))) = work at supported
  apply native_completed setup wire sign seed scalar provider service codec route selected publicPrekey
    work before result valid _ supported
  intro inner reached
  rw [← workEq] at reached
  exact RegistrationNativeHiddenAllocationBirth.create setup wire sign seed scalar provider service codec route
    edPin mlPin keyId (before.1.1.1.1.beacons.map RegistrationNativePublicOwners.restore) before.1.1.1.1.environment
    (RegistrationNativeHiddenAllocationExecution.runtime before) inner
    (by simpa only [List.length_map, RegistrationNativeHiddenAllocationExecution.runtime] using valid.length)
    (RegistrationNativeHiddenAllocationOwners.restore _ valid.indexed) reached

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFrontend.quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFrontend.quiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFrontend.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationFrontend.create

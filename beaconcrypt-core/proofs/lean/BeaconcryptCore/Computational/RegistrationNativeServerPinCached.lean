-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerPinRecompute
import BeaconcryptCore.Computational.RegistrationNativeServerPinStartup

/-! The historical fingerprint-cache startup invariant is retired: current pin selection performs no hash request. The remaining receipt relates immutable configured Server fields at actual native execution cuts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPinCached
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- The complete configured public fields, independent of any hash cache or fingerprint. -/
def Configured (pin : session.ServerAuthenticationPin) (binding : pqxdh.ServerBinding)
    (publicKey : Std.Array U8 1952#usize) : Prop :=
  pin.binding = binding ∧ pin.public_key = publicKey

/-- Every actual callback program retains the configured binding and full ML public key. -/
theorem program_fields (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (configured : Configured before.server.pin ⟨created.server.server.identity, created.server.server.metadata.sender⟩ credential.publicKey)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before)) :
    Configured result.2.server.pin ⟨created.server.server.identity, created.server.server.metadata.sender⟩ credential.publicKey := by
  rw [RegistrationNativeServerPinTrace.program_pin setup checks wire route representation created credential work before result supported]
  exact configured

/-- Actual constructor startup supplies both configured fields without a fingerprint query. -/
theorem start_fields (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Configured initial.state.server.pin ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ initial.credential.publicKey :=
  RegistrationNativeServerPinStartup.start_pin setup source ensureInit identityIndex serverKeyId initial started

/-- Actual initialization and immutable Server-pin fields identify the recomputed binding and displayed ML public key at every reached original cut. -/
theorem initialized_fields (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (initialized : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work).run initial.state)) :
    result.2.server.pin.binding = ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ ∧
      result.2.server.pin.public_key = initial.credential.publicKey := by
  rw [RegistrationNativeServerPinTrace.program_pin setup checks wire route representation initial.created initial.credential work initial.state result supported]
  exact RegistrationNativeServerPinStartup.start_pin setup source ensureInit identityIndex serverKeyId initial initialized

/-- Selection at an actual reached cut returns the configured pin with no state change. -/
theorem initialized_selection (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (initialized : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) work).run initial.state)) :
    (RegistrationNativeServerPinRecompute.native
      ⟨initial.created.server.server.identity, initial.created.server.server.metadata.sender⟩ initial.credential.publicKey).run
        result.2.server.world.world.1 = pure (.ok (.Some result.2.server.pin), result.2.server.world.world.1) := by
  obtain ⟨binding, key⟩ := initialized_fields setup checks wire route representation ensureInit identityIndex serverKeyId initial initialized work result supported
  simpa only [binding, key] using
    RegistrationNativeServerPinRecompute.native_exact result.2.server.pin result.2.server.world.world.1

end BeaconcryptCore.Computational.RegistrationNativeServerPinCached

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_selection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.initialized_selection

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.program_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.program_fields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinCached.start_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinCached.start_fields

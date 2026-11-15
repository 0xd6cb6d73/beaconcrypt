-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthRun
import BeaconcryptCore.Computational.RegistrationNativeStageTrace

/-! Actual initialized native paths retain the originating generated private KEM row for every reached owner. This supplies honest-recipient provenance without identifying public-key aliases or creation/session indices. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeGeneratedPath
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativeKemBirthInvariant (Holds)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)

/-- Every same-run typed source path preserves genuine generated key ownership, including all failed callbacks. -/
theorem path {before after : State n KemSK source} {calls : List (Call TypedSpec (State n KemSK source))}
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) before calls after)
    (prior : Holds setup before.beacons before.pool) : Holds setup after.beacons after.pool := by
  induction actual with
  | nil => exact prior
  | cons call called rest last following ih =>
    exact ih (RegistrationNativeKemBirthRun.handler_keeps setup checks wire route representation created credential
      call.query call.before call.after call.reply prior called)

/-- The generated-key ownership invariant is derived from actual startup and the reached prefix alone. -/
theorem initialized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (after : State n KemSK source) (calls : List (Call TypedSpec (State n KemSK source)))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls after) : Holds setup after.beacons after.pool :=
  path setup checks wire route representation initial.created initial.credential actual
    (RegistrationNativeKemBirthRun.start_holds setup source ensureInit identityIndex serverKeyId initial started)

/-- A reached owner has an actual key-generation witness at its exact private handle, even when other public keys alias it. -/
theorem owner (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (after : State n KemSK source) (calls : List (Call TypedSpec (State n KemSK source)))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls after) (index : Nat) (selected : RegistrationNativeBeaconFrontend.Owner source)
    (found : after.beacons[index]? = some selected) :
    ∃ pair, after.pool.keys[selected.kemHandle]? = some pair ∧ pair.1 = selected.kemPublic ∧
      pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) := by
  have reached := initialized setup checks wire route representation ensureInit identityIndex serverKeyId initial started after calls actual
  obtain ⟨pair, row, publicKey⟩ := reached.2 selected (List.mem_of_getElem? found)
  exact ⟨pair, row, publicKey, reached.1 pair (List.mem_of_getElem? row)⟩

end BeaconcryptCore.Computational.RegistrationNativeGeneratedPath

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeGeneratedPath.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeGeneratedPath.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeGeneratedPath.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeGeneratedPath.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeGeneratedPath.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeGeneratedPath.owner

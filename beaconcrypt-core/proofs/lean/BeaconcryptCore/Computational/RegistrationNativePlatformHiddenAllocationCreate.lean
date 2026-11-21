-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCore
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBirth
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCreate
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironmentWorld (lower)
open RegistrationNativePlatformHiddenAllocationCore (Holds close)
variable {n : Nat} {I KemSK ProviderState Platform Reader Response Secret A : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}
abbrev State (n : Nat) (KemSK ProviderState Platform Secret : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePlatformHiddenAllocationCore.State n Platform
    (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) Secret source

def runtime (before : State n KemSK ProviderState Platform Secret source) :
    RegistrationNativePlatformHiddenAllocationRuntime.State n KemSK ProviderState Secret :=
  (((before.1.1.1.2, before.1.1.2), before.1.2), before.2)

def attach (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (result : ((A × RegistrationNativeBeaconFrontend.State source) × RegistrationServerReferenceCompiler.Environment) ×
      RegistrationNativePlatformHiddenAllocationRuntime.State n KemSK ProviderState Secret) : A × State n KemSK ProviderState Platform Secret source :=
  (result.1.1.1, ((((({ before.1 with beacons := RegistrationNativePublicOwners.pack selected publicPrekey result.1.1.2, environment := result.1.2 }, before.2), result.2.1.1.1), result.2.1.1.2), result.2.1.2), result.2.2))

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
local notation "backend" => RegistrationNativePlatformSelectiveEntropyBackend.handler setup wire sign seed scalar candidate provider
local notation "native" => RegistrationNativePlatformHiddenAllocationRuntime.closed setup wire sign seed scalar candidate provider
local notation "callback" => RegistrationNativePlatformHiddenAllocationRuntime.callback setup wire sign seed scalar candidate provider service codec route

/-- The actual public constructor closes the genuine native AST through the same allocator before packing its public source state. -/
theorem source_run (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (before : State n KemSK ProviderState Platform Secret source) :
    (lower service codec route (close backend
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
        (RegistrationNativePlatformPublicOwners.executeLocal selected publicPrekey
          (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformPublicFrontend.trusted work)))))).run before =
    attach selected publicPrekey before.1.1.1.1 <$>
      (simulateQ callback ((work.run (before.1.1.1.1.1.beacons.map RegistrationNativePublicOwners.restore)).run
        before.1.1.1.1.1.environment)).run (runtime before) := by
  let tree := ((work.run (before.1.1.1.1.1.beacons.map RegistrationNativePublicOwners.restore)).run
    before.1.1.1.1.1.environment)
  have represented := congrArg (fun action => action.run (runtime before))
    (RegistrationNativeHiddenEnvironmentWorld.program_lower service codec route native tree)
  change (lower service codec route (simulateQ native tree)).run (runtime before) =
    (simulateQ callback tree).run (runtime before) at represented
  rw [← represented]
  unfold lower
  simp only [close,
    RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.beacon,
    RegistrationNativePlatformPublicOwners.executeLocal, RegistrationNativePlatformGenericBundle.liftLegacy,
    StateT.run, map_apply, simulateQ_map, Functor.map_map]
  have factored := RegistrationNativePlatformHiddenAllocationRuntime.native_world setup wire sign seed scalar candidate provider
    tree before.1.1.1.1.2 before.1.1.1.2
  dsimp only [tree, StateT.run] at factored
  rw [factored]
  rw [RegistrationNativeHiddenEnvironmentWorld.interpret_map]
  simp only [RegistrationNativeHiddenEnvironmentWorld.interpret_map, Functor.map_map, attach, runtime, tree, Prod.map_def, id_eq]
  rfl

/-- Literal public creation preserves physical/local roster length and addresses under every genuine constructor outcome. -/
theorem create (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK ProviderState Platform Secret source)
    (result : RustM (Option Nat) × State n KemSK ProviderState Platform Secret source)
    (valid : Holds before)
    (supported : result ∈ support ((lower service codec route (close backend
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
        (RegistrationNativePlatformPublicOwners.create RegistrationNativePlatformPublicFrontend.trusted setup source
          selected publicPrekey edPin mlPin keyId))))).run before)) : Holds result.2 := by
  apply RegistrationNativePlatformHiddenAllocationCore.completed service codec route _ before result valid supported
  all_goals
    change result ∈ support ((lower service codec route (close backend
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
        (RegistrationNativePlatformPublicOwners.executeLocal selected publicPrekey
          (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformPublicFrontend.trusted
            (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId))))))).run before) at supported
    rw [source_run, support_map] at supported
    obtain ⟨inner, reached, equal⟩ := supported
    have fields := RegistrationNativePlatformHiddenAllocationBirth.create callback (fun current => current.1.2.owners.length)
      (RegistrationNativePlatformHiddenAllocationRuntime.query_noappend setup wire sign seed scalar candidate provider service codec route)
      setup (RegistrationNativePlatformHiddenAllocationRuntime.query_append setup wire sign seed scalar candidate provider service codec route)
      edPin mlPin keyId (before.1.1.1.1.1.beacons.map RegistrationNativePublicOwners.restore) before.1.1.1.1.1.environment
      (runtime before) inner
      (by simpa only [List.length_map, runtime] using valid.length)
      (RegistrationNativeHiddenAllocationOwners.restore _ valid.indexed) reached
    cases equal
  · exact fields.1.trans (RegistrationNativeHiddenAllocationOwners.pack_length selected publicPrekey inner.1.1.2).symm
  · exact RegistrationNativeHiddenAllocationOwners.pack selected publicPrekey inner.1.1.2 fields.2
end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCreate.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCreate.source_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCreate.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCreate.create

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationNativeKemBirthInvariant

/-! Actual effectful Platform bundle generation preserves the genuinely generated private KEM rows of every prior owner, even across byte aliases and failed writer prefixes. Metadata transport preserves exact private handles and public bytes without a public-key injectivity assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKnownOwners
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativeKemBirthInvariant (Holds)
variable {n : Nat} {E Platform ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

/-- Complete immutable owner metadata transports literal private table ownership and generator receipts. -/
theorem metadata (setup : Setup base KemSK) (before after : List (Owner source)) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prior : Holds setup before pool) (same : after.map RegistrationNativeOwnerFields.metadata = before.map RegistrationNativeOwnerFields.metadata) :
    Holds setup after pool := by
  have projected := congrArg (List.map fun owner : Owner source => (owner.kemHandle, owner.kemPublic)) same
  have keys : after.map RegistrationNativeKemBirthInvariant.metadata = before.map RegistrationNativeKemBirthInvariant.metadata := by
    change after.map (fun owner : Owner source => (owner.kemHandle, owner.kemPublic)) =
      before.map (fun owner : Owner source => (owner.kemHandle, owner.kemPublic))
    simpa only [List.map_map, Function.comp_def, RegistrationNativeOwnerFields.metadata] using projected
  exact ⟨prior.1, RegistrationNativeKemBirthInvariant.metadata_transport before after pool prior.2 keys⟩

private theorem trusted (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owners : List (Owner source))
    (query : (Trusted n KemSK).Domain) (before after : Native) (previous next : Platform)
    (reply : (Trusted n KemSK).Range query) (prior : Holds setup owners before.pool)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.trusted coins setup checks representation created source query).run before).run previous)) :
    Holds setup owners after.pool := by
  have actual : (reply, after) ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before) :=
    RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
  apply RegistrationNativeKemBirthInvariant.trusted_program setup checks representation created source owners
    (liftM ((Trusted n KemSK).query query)) before after reply prior
  simpa only [simulateQ_spec_query] using actual

private theorem step (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owners : List (Owner source))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain)
    (before after : Native) (previous next : Platform)
    (reply : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Range query) (prior : Holds setup owners before.pool)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer query).run before).run previous)) :
    Holds setup owners after.pool := by
  cases query with
  | inl query => exact trusted coins setup checks representation created owners query before after previous next reply prior supported
  | inr query =>
    simp only [RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.writer,
      StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
    obtain ⟨⟨value, platform⟩, _called, same⟩ := supported
    have stateEq : after = before := (congrArg (fun result => result.1.2) same).symm
    exact stateEq ▸ prior

private theorem program (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owners : List (Owner source))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) V)
    (before after : Native) (previous next : Platform) (value : V) (prior : Holds setup owners before.pool)
    (supported : ((value, after), next) ∈ support
      (((simulateQ (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before).run previous)) :
    Holds setup owners after.pool := by
  induction work using OracleComp.inductionOn generalizing before after previous next with
  | pure input =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    exact supported.1.2 ▸ prior
  | query_bind query continuation ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨reply, middle⟩, platform⟩, called, continued⟩ := supported
    exact ih reply middle after platform next
      (step coins setup checks representation created owners writer query before middle previous platform reply prior called) continued

private theorem map_apply {S X Y : Type} (f : X → Y) (work : StateT S ProbComp X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual Platform bundle execution preserves genuine generated rows for every prior and final owner on all source writer outcomes. -/
theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before after : Native) (previous next : Platform) (reply : RustM (Option Pqxdh.Bytes))
    (prior : Holds setup before.beacons before.pool)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    Holds setup after.beacons after.pool := by
  have sameMetadata := RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer
    index before after previous next reply supported
  simp only [RegistrationNativePlatformExperiment.bundle, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨raw, platform⟩, called, same⟩ := supported
  have poolEq : after.pool = raw.2.pool := (congrArg (fun result => result.1.2.pool) same).symm
  have valid := program coins setup checks representation created before.beacons writer _ before raw.2 previous platform raw.1 prior called
  apply metadata setup before.beacons after.beacons after.pool _ sameMetadata
  exact poolEq ▸ valid

end BeaconcryptCore.Computational.RegistrationNativePlatformKnownOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKnownOwners.metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKnownOwners.metadata

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKnownOwners.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKnownOwners.bundle

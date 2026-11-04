-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBundleHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityBirthHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFrontendHashBounds
/-! The actual full Main owner create and dynamic-writer bundle callbacks inherit one and two physical shared hashes. Public alias reporting remains protocol-only and adds no shared hash. Full source joins retain all fields and all failed prefixes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformIdentityCtxHashBoundsCore (Bounded)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- Actual owner birth carries its one pin hash into Main without another physical shared hash. -/
theorem create_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) :
    Bounded (RegistrationNativePlatformIdentityCtxLifecycle.create (n := n) (source := source) (Platform := Platform)
      setup edPin mlPin keyId checks representation created) 1 :=
  RegistrationNativePlatformIdentityCtxFrontendHashBounds.beacon_bound setup checks representation created _ 1
    (RegistrationNativePlatformIdentitySourceHashBounds.native_bound _ 1
      (RegistrationNativePlatformIdentityBirthHashBounds.create_bound setup source edPin mlPin keyId))

/-- Literal source bundle lookup, signing, mutable writing and public reply conversion retain their two-hash bill. -/
theorem bundle_bound (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat) :
    Bounded (RegistrationNativePlatformIdentityCtxLifecycle.bundle (n := n) (source := source) setup checks representation created writer index) 2 := by
  intro before
  rw [RegistrationNativePlatformIdentityCtxLifecycle.bundle, StateT.run_map, isQueryBoundP_map_iff]
  exact RegistrationNativePlatformIdentityCtxFrontendHashBounds.beacon_bound setup checks representation created _ 2
    (RegistrationNativePlatformIdentityBundleHashBounds.bundle_bound setup index writer) before

/-- Reporting all public aliases preserves every source state and never calls the shared hash branch. -/
theorem report_bound (packet : registration.InitPacket) :
    Bounded (RegistrationNativePlatformIdentityCtxOrdinary.report (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) packet) 0 := by
  intro before
  simp only [RegistrationNativePlatformIdentityCtxOrdinary.report, StateT.run, isQueryBoundP_map_iff]
  apply (isQueryBoundP_false _ 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp [RegistrationNativePlatformIdentityCtxCompiler.protocol, RegistrationNativePlatformIdentityCtxBackend.IsHash]
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds.create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds.bundle_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds.report_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxLifecycleHashBounds.report_bound

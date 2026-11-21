-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
/-! The current public bundle closes the actual publication and extracted writer request programs in one persistent primitive/platform monad. This equality exposes the source body rather than replacing it by a static encoder. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I}
variable {m : Type →Type} [Monad m] [LawfulMonad m]
variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)

noncomputable def localBody (index : Nat) :
    RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformExperiment.M n KemSK source m) (RustM (Option (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformGenericBundle.bundle
    (RegistrationNativePlatformExperiment.trusted (n:=n) coins setup checks representation created source)
    setup source
    (RegistrationNativePlatformGenericBundle.encoderWith (RegistrationNativePlatformExperiment.writer writer)) index

/-- The actual source publication and stateful writer are interpreted before their owner/environment result is committed. -/
theorem local_source (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    (simulateQ (RegistrationNativePlatformExperiment.bundleHandler (n:=n) coins setup checks representation created source writer)
      (((RegistrationNativePlatformGenericBundle.program (n:=n) E setup source index).run owners).run env)) =
    ((localBody (n:=n) coins setup checks representation created source writer index).run owners).run env := by
  exact congrFun (congrFun (RegistrationNativePlatformGenericBundle.program_evaluate
    (RegistrationNativePlatformExperiment.bundleHandler (n:=n) coins setup checks representation created source writer)
    setup source index) owners) env

noncomputable def bundle (index : Nat) :
    RegistrationNativePlatformExperiment.M n KemSK source m (RustM (Option Pqxdh.Bytes)) := fun before=>do
  let result←(((localBody (n:=n) coins setup checks representation created source writer index).run before.beacons).run
    (RegistrationWorldAgreementCompiler.erase before.server.world)).run before
  pure ((do let optional←result.1.1.1; .ok (optional.map TranscriptAuthParts.absSlice)),
    { result.2 with
      beacons := result.1.1.2
      server := { result.2.server with world :=
        RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })

/-- All fresh, supplied-coin, consumed, writer-failure and absent-owner cases have the exact current callback result and poststate. -/
theorem bundle_source (index : Nat) :
    bundle (n:=n) coins setup checks representation created source writer index =
      RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index := by
  funext before
  unfold bundle RegistrationNativePlatformExperiment.bundle
  rw [local_source]

/-- The same bundle source law keeps the arbitrary persistent platform poststate jointly with every primitive and owner field. -/
theorem joint {Platform : Type} (publicCoins : QueryImpl unifSpec (StateT Platform ProbComp))
    (publicWriter : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    ((bundle publicCoins setup checks representation created source publicWriter index).run before).run previous=
      ((RegistrationNativePlatformExperiment.bundle publicCoins setup checks representation created source publicWriter index).run before).run previous := by
  rw [bundle_source]
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle.local_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle.local_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle.bundle_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle.joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedBundle.joint

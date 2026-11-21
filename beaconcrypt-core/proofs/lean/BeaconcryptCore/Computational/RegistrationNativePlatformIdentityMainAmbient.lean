-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityAmbient
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainOrdinary

/-! The executable indexed identity client runs all current-runtime non-Beacon callbacks using only seed-free owner World handles. Private source realization recovers the literal same native/platform callback, including every source allocator/writer failure and ongoing record route. No full-handler source equality or security conclusion is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainAmbient
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project)
open RegistrationNativeIdentityMainOrdinary (attach)
open RegistrationNativeIdentityWorld (Context)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def dummyOwners (owners : RegistrationNativeIdentityFrontend.State source) :=
  owners.map (RegistrationNativeIdentityFrontend.restore RegistrationNativeIdentityFrontend.dummyIdentity)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

variable [primitives : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

noncomputable def command (query : TypedSpec.Domain) (owners : RegistrationNativeIdentityFrontend.State source) :
    StateT (Context n KemSK × Platform) ProbComp (TypedSpec.Range query) := fun before =>
  (fun result => (result.1.1, (RegistrationNativeIdentityWorld.project result.1.2, result.2))) <$>
    ((callback query).run (attach (dummyOwners owners) before.1)).run before.2

noncomputable def step (query : TypedSpec.Domain) : M n KemSK Platform source (TypedSpec.Range query) := fun before =>
  (RegistrationNativePlatformIdentityMainOrdinary.ordinary
    (command setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before.1.beacons)).run before

/-- The current-runtime callback is recovered from an executable seed-free command using only public World owner handles; the entire P/private native result is retained. -/
theorem step_source (query : TypedSpec.Domain) (allowed : RegistrationNativePlatformIdentityAmbient.nonBeacon query)
    (before : (State n KemSK source × Platform) × SourceState) :
    Prod.map id project <$>
      (interpret setup.joint (step setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((callback query).run (project before).1).run (project before).2 := by
  let owners := RegistrationNativeIdentityRealization.owners before.2 before.1.1.beacons
  let context := before.1.1.context
  have handles : (attach (dummyOwners before.1.1.beacons) context).beacons.map RegistrationNativeBeaconFrontend.Owner.worldOwner =
      owners.map RegistrationNativeBeaconFrontend.Owner.worldOwner := by
    simp only [attach, dummyOwners, owners, RegistrationNativeIdentityRealization.owners, List.map_map, Function.comp_def,
      RegistrationNativeIdentityRealization.owner, RegistrationNativeIdentityFrontend.restore]
  have actual := RegistrationNativePlatformIdentityAmbient.handler setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query allowed
    (attach (dummyOwners before.1.1.beacons) context) owners handles
  have law := congrArg (fun program =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$> program.run before.1.2) actual
  change Prod.map id project <$>
    (interpret setup.joint (RegistrationNativePlatformIdentityMainOrdinary.ordinary
      (command setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query before.1.1.beacons))).run before = _
  rw [RegistrationNativePlatformIdentityMainOrdinary.ordinary_source]
  simp only [command, StateT.run, map_apply, Functor.map_map, Prod.map, id_eq,
    RegistrationNativeIdentityWorld.project, RegistrationNativeIdentityMainOrdinary.attach,
    RegistrationNativePlatformIdentityAmbient.replace, owners, context,
    project, RegistrationNativeIdentityMainSource.project] at law ⊢
  exact law

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainAmbient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainAmbient.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainAmbient.step_source

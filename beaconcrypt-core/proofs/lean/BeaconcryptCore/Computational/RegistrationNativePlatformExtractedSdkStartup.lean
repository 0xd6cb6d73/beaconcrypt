-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterServerConstructorReady
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier
import BeaconcryptCore.Refinement.AdapterServerConstructorRetained
import BeaconcryptCore.Refinement.AdapterServerConstructorKeyFrame
import BeaconcryptCore.Refinement.AdapterServerConstructorMaterial
import BeaconcryptCore.Refinement.AdapterServerConstructorGeneration
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The source initializer executes the actual checked caller-RNG constructor and actual Server authentication_pin continuation. The receipt retains even constructor errors and the same returned source Self/RNG. Native initialization is its proved projection, with no caller startup/profile equation. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkStartup
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperState AdapterPublicWrapperStorage
open BeaconcryptCore.Computational
variable {n : Nat} {I KemSK R Error : Type} {base : OracleSpec I}
variable {mlSource : RegistrationNativeMldsa.Source}
variable [storage : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [AdapterServerConstructorPrimitive.Standard]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [localOps : LocalOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
variable [children : ChildOperations (RustT (StateT (PqxdhRecordLiftWorld.State n) ProbComp))]
local notation "World"   =>   PqxdhRecordLiftWorld.State n
local notation "M"   =>   StateT World ProbComp

open AdapterServerConstructorRunner
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (generator : rand_core.TryCryptoRng R Error) (view : MaterialView mlSource KemSK)
variable (views : Views) (objects : AdapterServerConstructorObjects.Leaves views)
variable (ensureInit : StateT Unit ProbComp Bool)
local notation "edSample"   =>   PqxdhRecordLiftWorld.sampled (n:=n) (AdapterServerConstructorStartup.edCore ensureInit)
local notation "mlSample"   =>   PqxdhRecordLiftWorld.sampled (n:=n) (RegistrationNativeMldsa.generate mlSource)
variable (ed : AdapterServerConstructorJoint.EdContract generator view setup.joint
  (PqxdhRecordLiftWorld.sampled (n:=n) (AdapterServerConstructorStartup.edCore ensureInit)))
variable (ml : AdapterServerConstructorGeneration.MldsaContract generator view
  (PqxdhRecordLiftWorld.sampled (n:=n) (RegistrationNativeMldsa.generate mlSource)))
include views objects ed ml

variable (edGetter : ∀key,(crypto.edPublicBytes key).run=pure (.ok (view.edPublic key)))
variable (mlGetter : ∀identity,(localOps.auth_MldsaIdentity_public_key identity).run=pure (.ok (view.mldsa identity).publicKey))
include edGetter mlGetter

variable {Platform : Type}

noncomputable def carrier (identityIndex : Nat) (identifier : U64) (rng : R)
    (receipt : Receipt n KemSK R mlSource)
    (ready : AdapterServerConstructorInitialized.Ready n KemSK R mlSource)
    (previous : Platform)
    (supported : receipt∈support (game setup view identityIndex identifier generator rng))
    (returned : receipt.ready=some ready) :
    RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint ready.initial.created ready.initial.credential
      (ready.initial.state,previous) := by
  have derived:=AdapterServerConstructorReady.material setup generator view views objects ensureInit ed ml edGetter mlGetter
    identityIndex identifier rng receipt ready supported returned
  exact RegistrationNativePlatformExtractedSdkInitialCarrier.ready view views setup.joint ready previous
    derived.1 derived.2.1 derived.2.2.1 derived.2.2.2

omit children in
theorem source_fields (identityIndex : Nat) (identifier : U64) (rng : R)
    (receipt : Receipt n KemSK R mlSource)
    (ready : AdapterServerConstructorInitialized.Ready n KemSK R mlSource)
    (previous : Platform)
    (supported : receipt∈support (game setup view identityIndex identifier generator rng))
    (returned : receipt.ready=some ready) :
    let objects:=carrier setup generator view views objects ensureInit ed ml edGetter mlGetter identityIndex identifier rng receipt ready previous supported returned
    objects.objects.server=ready.stored ∧objects.objects.rng=ready.rng ∧
    objects.objects.beacons=(fun _ =>none) ∧objects.objects.tokens=(fun _ =>none) ∧
    objects.objects.nextOwner=0 ∧objects.objects.nextSession=0 ∧
    objects.objects.snapshot=.direct (ready.initial.state,previous) := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkStartup
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkStartup.carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkStartup.carrier
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkStartup.source_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkStartup.source_fields

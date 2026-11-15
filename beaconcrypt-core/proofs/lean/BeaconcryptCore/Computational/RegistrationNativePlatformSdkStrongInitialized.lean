import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized
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
    RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views ready.initial.created ready.initial.credential
      (ready.initial.state,previous) := by
  let original:=RegistrationNativePlatformExtractedSdkStartup.carrier setup generator view views objects ensureInit ed ml edGetter mlGetter identityIndex identifier rng receipt ready previous supported returned
  have derived:=AdapterServerConstructorReady.material setup generator view views objects ensureInit ed ml edGetter mlGetter
    identityIndex identifier rng receipt ready supported returned
  exact RegistrationNativePlatformSdkStrongCarrier.empty setup view views ready.initial.created ready.initial.credential
    (ready.initial.state,previous) original derived.2.1

omit children in
theorem base_carrier (identityIndex : Nat) (identifier : U64) (rng : R)
    (receipt : Receipt n KemSK R mlSource) (ready : AdapterServerConstructorInitialized.Ready n KemSK R mlSource)
    (previous : Platform) (supported : receipt∈support (game setup view identityIndex identifier generator rng))
    (returned : receipt.ready=some ready) :
    (carrier setup generator view views objects ensureInit ed ml edGetter mlGetter identityIndex identifier rng receipt ready previous supported returned).base=
      RegistrationNativePlatformExtractedSdkStartup.carrier setup generator view views objects ensureInit ed ml edGetter mlGetter identityIndex identifier rng receipt ready previous supported returned := rfl

noncomputable def store (identityIndex : Nat) (identifier : U64) (rng : R) (previous : Platform)
    (packet : {receipt //receipt∈support (game (n:=n) setup view identityIndex identifier generator rng)}) :
    match packet.val.ready with
    | none=>PUnit
    | some ready=>RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view views ready.initial.created ready.initial.credential (ready.initial.state,previous) := by
  cases returned:packet.val.ready with
  | none=>exact PUnit.unit
  | some ready=>
    exact carrier setup generator view views objects ensureInit ed ml edGetter mlGetter
      identityIndex identifier rng packet.val ready previous packet.property returned
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized.carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized.carrier

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized.base_carrier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized.base_carrier

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized.store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongInitialized.store

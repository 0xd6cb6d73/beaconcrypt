-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkStartup
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized
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

noncomputable def sample (identityIndex : Nat) (identifier : U64) (rng : R) :=
  PFunctor.FreeM.attachSupp (game (n:=n) setup view identityIndex identifier generator rng)

omit children views objects ensureInit ed ml edGetter mlGetter in
theorem source (identityIndex : Nat) (identifier : U64) (rng : R) :
    Subtype.val <$>sample (n:=n) setup generator view identityIndex identifier rng=
      game (n:=n) setup view identityIndex identifier generator rng :=
  PFunctor.FreeM.map_attachSupp _

omit children in
theorem native (identityIndex : Nat) (identifier : U64) (rng : R) :
    (fun packet=>nativeView packet.val) <$>sample (n:=n) setup generator view identityIndex identifier rng=
      RegistrationNativeExperiment.start (n:=n) setup mlSource ensureInit identityIndex identifier := by
  have erased := congrArg (fun work =>nativeView <$>work) (source (n:=n) setup generator view identityIndex identifier rng)
  have native := AdapterServerConstructorRunner.native setup generator view views objects ensureInit ed ml edGetter mlGetter identityIndex identifier rng
  simpa only [Functor.map_map,Function.comp_def] using erased.trans native

noncomputable def store (identityIndex : Nat) (identifier : U64) (rng : R) (previous : Platform)
    (packet : {receipt // receipt∈support (game (n:=n) setup view identityIndex identifier generator rng)}) :
    match packet.val.ready with
    | none => PUnit
    | some ready => RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view views setup.joint ready.initial.created ready.initial.credential
        (ready.initial.state,previous) := by
  cases returned : packet.val.ready with
  | none => exact PUnit.unit
  | some ready =>
      exact RegistrationNativePlatformExtractedSdkStartup.carrier setup generator view views objects ensureInit ed ml
        edGetter mlGetter identityIndex identifier rng packet.val ready previous packet.property returned

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized.source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized.native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized.store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialized.store

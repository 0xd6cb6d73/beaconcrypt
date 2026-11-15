-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPinParsing
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
/-! The raw physical constructor commits only actual returned Self/RNG and its actual primitive/platform poststate. Normal key-generation error retains its returned RNG; enclosing Rust failure/divergence exposes no replacement source object. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R Platform : Type}

def finish (before : Store n KemSK R Platform) (outcome : RustM (AdapterBeaconConstructorBody.Outcome R))
    (after : Backend n KemSK ×Platform) :
    RustM (Option Nat ×Store n KemSK R Platform) ×(Backend n KemSK ×Platform) :=
  (match outcome with
  | .fail error=>.fail error
  | .div=>.div
  | .ok returned=>.ok ((match returned.1 with | .Err _=>none | .Ok _=>some before.nextOwner),
      RegistrationNativePlatformPublicAdapterStore.create before returned after),after)

def run (work : RustT (StateT (Backend n KemSK) (StateT Platform ProbComp)) (AdapterBeaconConstructorBody.Outcome R))
    (before : Store n KemSK R Platform) :=
  (fun result=>finish before result.1.1 (result.1.2,result.2)) <$>
    ((work.run.run before.backend.1).run before.backend.2)

theorem run_pure (outcome : AdapterBeaconConstructorBody.Outcome R) (before : Store n KemSK R Platform) :
    run (pure outcome) before=pure (finish before (.ok outcome) before.backend) := by
  simp only [run,RustT.run_pure,StateT.run_pure,map_pure]

theorem rejected (before : Store n KemSK R Platform) :
    finish before (.ok (.Err (),before.rng)) before.backend=(.ok (none,before),before.backend) := rfl

variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (RustT (StateT (Backend n KemSK) (StateT Platform ProbComp)))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations
  (RustT (StateT (Backend n KemSK) (StateT Platform ProbComp)))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations
  (RustT (StateT (Backend n KemSK) (StateT Platform ProbComp)))]
variable {mlSource : RegistrationNativeMldsa.Source}

def source {Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (keyId : U64) (identityKey mlKey : Slice U8) (before : Store n KemSK R Platform) :=
  run (beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng
    (m:=RustT (StateT (Backend n KemSK) (StateT Platform ProbComp))) generator keyId identityKey mlKey before.rng) before

theorem invalid {Error : Type} (view : AdapterPublicWrapperState.MaterialView mlSource KemSK)
    (parsing : RegistrationNativePlatformPublicAdapterPinParsing.EdContract view)
    (generator : rand_core.TryCryptoRng R Error) (keyId : U64) (identityKey mlKey : Slice U8)
    (before : Store n KemSK R Platform)
    (bad : PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey)=none ∨
      RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey)=none) :
    source generator keyId identityKey mlKey before=pure (.ok (none,before),before.backend) := by
  have _children := children
  unfold source
  rw [RegistrationNativePlatformPublicAdapterPinParsing.rejected view parsing generator keyId identityKey mlKey before.rng bad,
    run_pure,rejected]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore.run_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore.rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore.rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore.invalid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateStore.invalid

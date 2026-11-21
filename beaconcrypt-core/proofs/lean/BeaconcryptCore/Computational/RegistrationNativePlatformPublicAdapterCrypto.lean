-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkCountedReification
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter
/-! The public adapter's actual source cryptographic operations run directly on the physical backend. No protocol-owner representation is available to this interpreter. The actual agreement request program and its private capture have the same joint law after erasure. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n : Nat} {KemSK A B : Type} {source : RegistrationNativeMldsa.Source}
local notation "WorldM" => StateT (PqxdhRecordLiftWorld.State n) ProbComp
local notation "BackendM" => StateT (Backend n KemSK) ProbComp

def world (work : WorldM A) : BackendM A := fun before =>
  (fun result =>(result.1,{before with world:=result.2})) <$>work.run before.world

private theorem world_pure (value : A) : world (KemSK:=KemSK) (pure value : WorldM A)=pure value := by
  funext before
  change (fun result : A ×PqxdhRecordLiftWorld.State n =>(result.1,{before with world:=result.2})) <$>
    (pure (value,before.world) : ProbComp _) = pure (value,before)
  rw [map_pure]

private theorem world_bind (work : WorldM A) (next : A →WorldM B) :
    world (KemSK:=KemSK) (work >>=next)=(world work >>=fun value=>world (next value)) := by
  funext before
  change (fun result : B ×PqxdhRecordLiftWorld.State n =>(result.1,{before with world:=result.2})) <$>
    (work >>=next).run before.world =
    (do let result ← (fun result : A ×PqxdhRecordLiftWorld.State n =>(result.1,{before with world:=result.2})) <$>work.run before.world
        world (next result.1) result.2)
  rw [StateT.run_bind,map_bind,bind_map_left]
  rfl

noncomputable def transform (work : RustT ProbComp A) : RustT BackendM A :=
  ⟨world (AdapterPublicAgreementCountedRust.counted work).run⟩

private theorem transform_pure (value : A) : transform (n:=n) (KemSK:=KemSK) (pure value)=pure value := by
  apply RustT.ext
  rw [transform,AdapterPublicAgreementCountedRust.counted_pure]
  exact world_pure (RustM.ok value)

private theorem transform_liftRust (result : RustM A) :
    transform (n:=n) (KemSK:=KemSK) (AdapterRecordRequestMonad.liftRust result)=AdapterRecordRequestMonad.liftRust result := by
  apply RustT.ext
  rw [transform,AdapterPublicAgreementCountedRust.counted_liftRust]
  exact world_pure result

private theorem transform_bind (work : RustT ProbComp A) (next : A →RustT ProbComp B) :
    transform (n:=n) (KemSK:=KemSK) (work >>=next)=(transform work >>=fun value=>transform (next value)) := by
  apply RustT.ext
  simp only [transform,AdapterPublicAgreementCountedRust.counted_bind,RustT.run_bind,world_bind]
  apply bind_congr
  intro result
  cases result <;> simp only [world_pure]

@[instance_reducible] noncomputable def translation : AdapterPublicAgreementMonadMap.Transformation ProbComp BackendM where
  transform:=transform
  lawful:=Cslib.IsMonadHom.mk' transform_pure transform_bind
  lift:=transform_liftRust

theorem transform_backend (work : RustT ProbComp A) (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$> (RegistrationNativePlatformSdkCountedReification.native work).run.run before=
      (transform work).run.run (backend before) := by
  simp only [RegistrationNativePlatformSdkCountedReification.native,
    AdapterPublicAgreementNativeWorldMap.transform,AdapterPublicAgreementCountedRust.counted,
    RegistrationNativeExperiment.world,RegistrationNativeExperiment.server,transform,world,
    PqxdhRecordLiftWorld.sampled,RegistrationNativePlatformSdkReification.backend,
    RegistrationNativePlatformSdkReification.worldBackend,StateT.run,bind_pure_comp,Functor.map_map]
  rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]

@[instance_reducible] noncomputable def operations (original : CryptoOperations (RustT ProbComp)) : CryptoOperations (RustT BackendM) :=
  let : AdapterPublicAgreementMonadMap.Transformation ProbComp BackendM:=translation
  AdapterPublicAgreementMonadCrypto.operations original

noncomputable def captured {R E Value : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : AdapterPublicAgreementFields.Keys) (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R) :=
  letI : CryptoOperations (RustT BackendM):=operations original
  (simulateQ (AdapterPublicAgreementInterpreter.handler (m:=BackendM) generator keys)
    (RegistrationAgreementQueryTrace.trace work [])).run ⟨rng,.None,.None⟩

theorem captured_source {R E Value : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : AdapterPublicAgreementFields.Keys) (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R) :
    captured (n:=n) (KemSK:=KemSK) generator keys work rng=
      transform ((simulateQ (AdapterPublicAgreementInterpreter.handler (m:=ProbComp) generator keys)
        (RegistrationAgreementQueryTrace.trace work [])).run ⟨rng,.None,.None⟩) := by
  let : AdapterPublicAgreementMonadMap.Transformation ProbComp BackendM:=translation
  exact AdapterPublicAgreementMonadInterpreter.program generator keys (RegistrationAgreementQueryTrace.trace work []) ⟨rng,.None,.None⟩

theorem captured_backend {R E Value : Type} (generator : rand_core.TryCryptoRng R E)
    (keys : AdapterPublicAgreementFields.Keys) (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id backend <$>
      (AdapterPublicAgreementNativeWorldInterpreter.captured generator keys work rng).run.run before=
      (captured generator keys work rng).run.run (backend before) := by
  rw [AdapterPublicAgreementNativeWorldInterpreter.captured_eq]
  unfold AdapterPublicAgreementCountedNative.captured
  rw [AdapterPublicAgreementCountedInterpreter.program,captured_source]
  exact transform_backend _ before

theorem captured_platform {R E Value Platform : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : AdapterPublicAgreementFields.Keys)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : Platform) :
    Prod.map (Prod.map id backend) id <$>
      ((AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run.run before).run previous =
      (simulateQ coins ((captured generator keys work rng).run.run (backend before))).run previous := by
  rw [AdapterPublicAgreementNativePlatformInterpreter.captured_run,←captured_backend generator keys work rng before,
    simulateQ_map,StateT.run_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.captured_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.captured_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.transform_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.transform_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.captured_backend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.captured_backend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.captured_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCrypto.captured_platform

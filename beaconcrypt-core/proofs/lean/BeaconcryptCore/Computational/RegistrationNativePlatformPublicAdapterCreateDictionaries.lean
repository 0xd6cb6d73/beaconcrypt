-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateGeneration
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreatePrimitives
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateKemPhysical
/-! Constructor dictionaries execute the original probabilistic per-key source methods through paired physical observers. Only the actual returned KEM pair causes a source pool birth. The selected native leaves are derived from the original primitive contracts, rather than supplied as a whole constructor correspondence premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDictionaries
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
private theorem lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value,before)) <$> work := by
  change (StateT.lift work : StateT S m A).run before = _
  rw [StateT.run_lift,bind_pure_comp]
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1,result.2)) <$> work before := by
  exact StateT.run_map f work before

variable {n : Nat} {I KemSK R Error P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [original : AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto : CryptoOperations (RustT ProbComp)]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
local notation "SourceM" => AdapterBeaconConstructorNative.M n KemSK source RegistrationServerRoleBackend.State (StateT P ProbComp)
local notation "PhysicalM" => StateT (Backend n KemSK) (StateT P ProbComp)

noncomputable def sourceKem {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (rng : R) :
    RustT SourceM (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair ed.Error × R) :=
  ⟨StateT.lift (StateT.lift (RegistrationNativePlatformPublicAdapterCreateKem.native view coins generator rng).run)⟩

@[instance_reducible] noncomputable def sourceGenerators : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) :=
  RegistrationNativePlatformPublicAdapterCreateGeneration.operations
    (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created) original
    (sourceKem coins view)

@[instance_reducible] noncomputable def physicalGenerators : AdapterBeaconConstructorRequestMonad.Operations (RustT PhysicalM) :=
  RegistrationNativePlatformPublicAdapterCreateGeneration.operations
    (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform coins setup checks representation created) original
    (RegistrationNativePlatformPublicAdapterCreateKem.physical view coins)

variable {m : Type → Type} [Monad m] [LawfulMonad m]
@[instance_reducible] def crypto (uniform : QueryImpl unifSpec m) : CryptoOperations (RustT m) :=
  {RegistrationNativePlatformPublicAdapterUniformObserver.operations uniform originalCrypto with
    edPublicBytes := fun key => pure (view.edPublic key)}

@[instance_reducible] def children (previous : ChildOperations (RustT m))
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest) : ChildOperations (RustT m) :=
  {previous with executeHash := fun request => ⟨(fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request⟩}

noncomputable def prekeyContract (uniform : QueryImpl unifSpec m)
    (generator : rand_core.TryCryptoRng R Error)
    (contract : AdapterBeaconConstructorGeneration.KxContract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar) :
    let : CryptoOperations (RustT m) := crypto view uniform
    AdapterBeaconConstructorGeneration.KxContract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (simulateQ uniform PqxdhJointGapDh.sampleScalar) := by
  let : CryptoOperations (RustT m) := crypto view uniform
  refine {joint := fun rng => simulateQ uniform (contract.joint rng), nativeMarginal := ?_, realize := contract.realize, privateView := contract.privateView, publicView := contract.publicView, operation := ?_}
  · intro rng
    rw [← simulateQ_map,contract.nativeMarginal]
  · intro rng
    change RegistrationNativePlatformPublicAdapterUniformObserver.observe uniform (originalCrypto.kxGenerate generator rng) = _
    rw [contract.operation,RegistrationNativePlatformPublicAdapterUniformObserver.lift_observe,simulateQ_map]

omit [Monad m] [LawfulMonad m] in
noncomputable def sourceLeaves
    (previous : ChildOperations (RustT SourceM)) (generator : rand_core.TryCryptoRng R Error)
    (kem : AdapterBeaconConstructorKem.Representation view R)
    (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view (RegistrationNativeMldsa.generate source))
    (signing : AdapterBeaconConstructorGeneration.EdContract generator view setup.joint PqxdhJointIdentity.sampleSeed)
    (prekey : AdapterBeaconConstructorGeneration.KxContract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)) PqxdhJointGapDh.sampleScalar)
    (kemContract : RegistrationNativePlatformPublicAdapterCreateKem.Contract view setup kem generator) :
    let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := sourceGenerators coins setup checks representation created view
    let : CryptoOperations (RustT SourceM) := crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
    let : ChildOperations (RustT SourceM) := children previous (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
    AdapterBeaconConstructorNative.Leaves (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State) coins setup checks representation created generator view kem := by
  let : AdapterBeaconConstructorRequestMonad.Operations (RustT SourceM) := sourceGenerators coins setup checks representation created view
  let : CryptoOperations (RustT SourceM) := crypto view (RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform coins setup checks representation created)
  let : ChildOperations (RustT SourceM) := children previous (RegistrationNativePlatformPublicAdapterCreatePrimitives.hash coins setup checks representation created)
  let uniform := RegistrationNativePlatformPublicAdapterCreatePrimitives.uniform (n:=n) (source:=source) coins setup checks representation created
  let mappedMl := RegistrationNativePlatformPublicAdapterCreateGeneration.mldsa uniform (sourceKem coins view) generator view _ ml
  let mappedEd := RegistrationNativePlatformPublicAdapterCreateGeneration.signing uniform (sourceKem coins view) generator view setup.joint _ signing
  let mappedKx := prekeyContract setup view uniform generator prekey
  refine {ml := ?_, ed := ?_, kx := ?_, getter := fun _ => rfl, hash := fun _ => rfl, kemOperation := ?_}
  · refine {joint := mappedMl.joint, nativeMarginal := ?_, realize := mappedMl.realize, privateView := mappedMl.privateView, operation := mappedMl.operation}
    intro rng
    exact (mappedMl.nativeMarginal rng).trans (RegistrationNativePlatformPublicAdapterCreatePrimitives.sample coins setup checks representation created _)
  · refine {joint := mappedEd.joint, nativeMarginal := ?_, realize := mappedEd.realize, privateView := mappedEd.privateView, publicView := mappedEd.publicView, operation := mappedEd.operation}
    intro rng
    exact (mappedEd.nativeMarginal rng).trans (RegistrationNativePlatformPublicAdapterCreatePrimitives.sample coins setup checks representation created _)
  · refine {joint := mappedKx.joint, nativeMarginal := ?_, realize := mappedKx.realize, privateView := mappedKx.privateView, publicView := mappedKx.publicView, operation := mappedKx.operation}
    intro rng
    exact (mappedKx.nativeMarginal rng).trans (RegistrationNativePlatformPublicAdapterCreatePrimitives.sample coins setup checks representation created _)
  · intro rng
    apply RustT.ext
    change StateT.lift (StateT.lift (RegistrationNativePlatformPublicAdapterCreateKem.native view coins generator rng).run) = _
    rw [RegistrationNativePlatformPublicAdapterCreateKem.native_operation view coins setup kem generator kemContract rng]
    funext owners environment before
    simp only [RustT.run_lift,AdapterBeaconConstructorKemLift.joint,lift_apply,map_apply,Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDictionaries
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDictionaries.prekeyContract' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDictionaries.prekeyContract
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceLeaves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDictionaries.sourceLeaves

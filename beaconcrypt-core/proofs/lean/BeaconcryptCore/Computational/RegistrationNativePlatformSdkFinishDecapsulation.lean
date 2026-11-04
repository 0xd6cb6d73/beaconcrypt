-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishSampleFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalBackend
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCommonModel
/-! A reached indexed decapsulation reads the actual private key row. Only the model's indexed query log is erased; every key, source primitive draw, counter, cache and optional reply remains in the same computation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformSdkFinishSampling (sample uniform)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open PqxdhRootTableInitialization (rootArray)
variable {n : Nat} {I KemSK P : Type} {base : OracleSpec I}

 theorem indexed (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (handle : Nat) (pair : MlKem768PublicKey × KemSK) (present : before.pool.keys[handle]?=some pair)
    (ciphertext : MlKem768Ciphertext) :
    Prod.map id erase <$>
      (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created
        (.inr (.inr (.inl (.decapsulate handle ciphertext))))).run before =
      (sample (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.decaps pair.2 ciphertext))).run (erase before) := by
  simp only [RegistrationNativePlatformSdkFinishBackend.handler,
    RegistrationNativePlatformSdkReification.backendLeaf, RegistrationNativeKemInterface.source,
    PqxdhLiveKemBirth.poolImpl, present, StateT.run]
  simp only [PqxdhRecordLiftWorld.sampled, simulateQ_map, StateT.run_map, bind_pure_comp,
    Functor.map_map, sample, RegistrationNativePlatformPublicAdapterCrypto.world,
    erase, PqxdhLiveKemBirth.record, worldBackend]
  simp only [PqxdhRecordLiftWorld.sampled,StateT.run,bind_pure_comp,Functor.map_map]
  have owners : before.world.owners=[] := (congrArg PqxdhRecordLiftWorld.State.owners canonical).symm
  have admin : Function.update before.world.primitive.1.effects .administrative 0 = before.world.primitive.1.effects :=
    congrArg (fun world=>world.primitive.1.effects) canonical
  congr 1
  funext result
  simp only [Prod.map,id_eq,erase,admin]
  congr 2
  rw [owners]

 theorem mapped (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (handle : Nat) (pair : MlKem768PublicKey × KemSK) (present : before.pool.keys[handle]?=some pair)
    (ciphertext : MlKem768Ciphertext) :
    Prod.map (fun reply=>RegistrationAgreementRoot.nativeOption (reply.map rootArray)) erase <$>
      (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created
        (.inr (.inr (.inl (.decapsulate handle ciphertext))))).run before =
      (sample ((fun reply=>RegistrationAgreementRoot.nativeOption (reply.map rootArray)) <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
          (setup.kem.decaps pair.2 ciphertext))).run (erase before) := by
  have core:=congrArg (fun work=>Prod.map (fun reply=>RegistrationAgreementRoot.nativeOption (reply.map rootArray)) id <$>work)
    (indexed setup checks representation created before canonical handle pair present ciphertext)
  simp only [Functor.map_map] at core
  refine core.trans ?_
  exact (RegistrationNativePlatformSdkFinishSampleFrame.map _ _ (erase before)).symm

/-- The primitive's original sampling contract, before any protocol execution or private row selection. -/
def Aligned (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (decapsulate : AdapterPublicAgreementFields.CipherArray → KemSK → ProbComp (core.option.Option AdapterPublicAgreementFields.Array32)) : Prop :=
  ∀ ciphertext secret, decapsulate ciphertext secret =
    (fun reply=>RegistrationAgreementRoot.nativeOption (reply.map rootArray)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.decaps secret (PqxdhPhase2InputBytes.ciphertext ciphertext))

 theorem source_leaf (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (decapsulate : AdapterPublicAgreementFields.CipherArray → KemSK → ProbComp (core.option.Option AdapterPublicAgreementFields.Array32))
    (aligned : Aligned setup decapsulate)
    (before : Backend n KemSK) (canonical : worldBackend before.world=before.world)
    (handle : Nat) (pair : MlKem768PublicKey × KemSK) (present : before.pool.keys[handle]?=some pair)
    (ciphertext : AdapterPublicAgreementFields.CipherArray) :
    Prod.map (fun reply=>RegistrationAgreementRoot.nativeOption (reply.map rootArray)) erase <$>
      (RegistrationNativePlatformSdkFinishBackend.handler setup checks representation created
        (.inr (.inr (.inl (.decapsulate handle (PqxdhPhase2InputBytes.ciphertext ciphertext)))))).run before =
      (simulateQ (uniform (n:=n)) (decapsulate ciphertext pair.2)).run (erase before) := by
  rw [RegistrationNativePlatformSdkFinishSampling.program,aligned ciphertext pair.2]
  exact mapped setup checks representation created before canonical handle pair present _

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation.indexed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation.indexed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation.mapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation.mapped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation.source_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDecapsulation.source_leaf

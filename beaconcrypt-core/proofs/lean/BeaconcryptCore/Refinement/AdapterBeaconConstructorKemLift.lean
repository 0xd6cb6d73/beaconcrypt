-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorKem
import BeaconcryptCore.Computational.RegistrationNativePlatformGenericBundle
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The same private generated KEM pair is lifted through the native owner/environment stack. Its public projection is the actual indexed create callback, with every native and common interpreter poststate retained. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorKemLift
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Trusted)
variable {n : Nat} {ι KemSK R Auxiliary : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]

noncomputable def implementation (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl (Trusted n KemSK) (StateT (AdapterBeaconConstructorKem.Native n KemSK source) m) :=
  fun query => RegistrationNativePlatformInterpret.state coins
    (RegistrationNativeExperiment.trusted setup checks representation created source query)

noncomputable def joint (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : AdapterBeaconConstructorKem.Representation view R) (rng : R) :
    RegistrationNativePlatformGenericBundle.M source Auxiliary
      (StateT (AdapterBeaconConstructorKem.Native n KemSK source) m) (AdapterBeaconConstructorKem.Receipt R) :=
  StateT.lift (StateT.lift (AdapterBeaconConstructorKem.joint coins setup view model rng))

theorem native (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (model : AdapterBeaconConstructorKem.Representation view R) (rng : R) :
    AdapterBeaconConstructorKem.Receipt.born <$> joint (n := n) (Auxiliary := Auxiliary) coins setup view model rng =
      RegistrationNativePlatformGenericBundle.liftLegacy (implementation coins setup checks representation created)
        (RegistrationNativeBeaconFrontend.kem (.inr (.inl .create))) := by
  funext owners env before
  change (((AdapterBeaconConstructorKem.Receipt.born <$> joint (n := n) (Auxiliary := Auxiliary) coins setup view model rng).run owners).run env).run before =
    (simulateQ (implementation coins setup checks representation created)
      (((RegistrationNativeBeaconFrontend.kem (.inr (.inl .create)) : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary _).run owners).run env)).run before
  unfold joint
  simp only [RegistrationNativeBeaconFrontend.kem, StateT.run_lift, StateT.run_map,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    Functor.map_map]
  have same := AdapterBeaconConstructorKem.native coins setup checks representation created view model rng before
  apply congrArg (fun work => (fun result => (((result.1, owners), env), result.2)) <$> work) at same
  simp only [Functor.map_map, Prod.map_def, id_eq] at same
  convert same using 1; rfl

end BeaconcryptCore.Refinement.AdapterBeaconConstructorKemLift

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorKemLift.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorKemLift.native

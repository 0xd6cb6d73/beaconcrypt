-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleSigning
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle
/-! The complete source Bundle publication and literal extracted Init writer factor through the physical backend. Private signing journals and owner histories are erased only after retaining the same public result and persistent source effects. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend backend)
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

noncomputable def handler (identity : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E) (StateT (Backend n KemSK) (StateT P ProbComp))
  | .inl query=>RegistrationNativePlatformPublicAdapterBundleSigning.outgoing coins setup checks representation created identity query
  | .inr query=>StateT.lift (writer query)

private noncomputable def nativeHandler (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E) (StateT Native (StateT P ProbComp))
  | .inl query=>RegistrationNativeBundleInterpretation.outgoing coins setup checks representation created writer index owner query
  | .inr query=>StateT.lift (writer query)

private theorem native_tree (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) :
    simulateQ (nativeHandler coins setup checks representation created writer index owner)
      (RegistrationNativePlatformWriter.begin E ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin)=
      RegistrationNativeBundleLifetime.tree (n:=n) coins setup checks representation created writer index owner scalar := by
  rw [RegistrationNativePlatformWriter.begin_interpret,RegistrationNativeBundleLifetime.tree_lower]
  congr 1
  funext signed
  change simulateQ (fun query=>StateT.lift (writer query)) _=_
  rw [RegistrationNativeBundleInterpretation.encoder_source]
  exact simulateQ_liftTarget writer _

noncomputable def program (identity : PqxdhJointIdentity.IdentitySeed)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (oneTime : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :=
  simulateQ (handler (n:=n) coins setup checks representation created writer identity)
    (RegistrationNativePlatformWriter.begin E control inputs oneTime pin)

theorem tree_source (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativeBundleLifetime.tree coins setup checks representation created writer index owner scalar).run before=
      (program coins setup checks representation created writer owner.identitySeed
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin).run (backend before) := by
  rw [←native_tree]
  unfold program
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  cases query with
  | inl query=>exact RegistrationNativePlatformPublicAdapterBundleSigning.outgoing_platform coins setup checks representation created writer index owner query current
  | inr query=>
    simp only [nativeHandler,handler,StateT.run_lift,bind_pure_comp,Functor.map_map]
    rfl

theorem tree_platform (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : Native) (previous : P) :
    Prod.map (Prod.map id backend) id <$>
      ((RegistrationNativeBundleLifetime.tree coins setup checks representation created writer index owner scalar).run before).run previous=
      ((program coins setup checks representation created writer owner.identitySeed
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin).run (backend before)).run previous := by
  rw [←tree_source coins setup checks representation created writer index owner scalar before,StateT.run_map]
  rfl

noncomputable def freshProgram (identity : PqxdhJointIdentity.IdentitySeed)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs)
    (pin : session.ServerAuthenticationPin) :=do
  let scalar←RegistrationNativePlatformPublicAdapterBundleSigning.sample (n:=n) coins setup checks representation created PqxdhJointGapDh.sampleScalar
  let published←program coins setup checks representation created writer identity control inputs
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ pin
  pure (scalar,published)

theorem fresh_tree_source (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (before : Native) :
    Prod.map id backend <$>
      (RegistrationNativeBundleLifetime.fresh_tree coins setup checks representation created writer index owner).run before=
      (freshProgram coins setup checks representation created writer owner.identitySeed
        ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner) owner.pin).run (backend before) := by
  have first:=RegistrationNativePlatformPublicAdapterBundleSigning.sample_source (source:=source)
    coins setup checks representation created PqxdhJointGapDh.sampleScalar before
  unfold RegistrationNativeBundleLifetime.fresh_tree RegistrationNativeBundleLifetime.sample freshProgram
  rw [RegistrationNativeBundleInterpretation.legacy]
  simp only [StateT.run_bind,StateT.run_pure,map_bind]
  rw [←first,bind_map_left]
  apply bind_congr
  rintro ⟨scalar,current⟩
  have same:=congrArg (fun work=>(fun result=>((scalar,result.1),result.2)) <$>work)
    (tree_source coins setup checks representation created writer index owner scalar current)
  simp only [bind_pure_comp,Functor.map_map] at same ⊢
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication.tree_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication.tree_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication.tree_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication.tree_platform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication.fresh_tree_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePublication.fresh_tree_source

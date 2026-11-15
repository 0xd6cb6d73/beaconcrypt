-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleGeneration
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backendLeaf worldBackend)
open RegistrationNativePlatformPublicAdapterPhysicalBackend (erase)
open RegistrationNativePlatformPublicAdapterPhysicalFrame
variable {n : Nat} {I KemSK E P A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))

theorem coin (request : unifSpec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterBundleGeneration.backendUniform (n:=n) coins setup checks representation created request) :=by
  apply interpret_frame
  intro before
  simp only [backendLeaf,StateT.run,Functor.map_map,erase]
  rfl

theorem sample (work : ProbComp A) :
    Compatible (RegistrationNativePlatformPublicAdapterBundleSigning.sample (n:=n) coins setup checks representation created work) :=by
  rw [←RegistrationNativePlatformPublicAdapterBundleGeneration.backend_program]
  exact program_frame _ (coin coins setup checks representation created) work

theorem hash (bytes : Pqxdh.Bytes) :
    Compatible (fun before=>simulateQ coins ((RegistrationNativePlatformPublicAdapterAuthentication.hash (n:=n) setup checks representation created bytes).run before)) :=by
  apply interpret_frame
  intro before
  simp only [RegistrationNativePlatformPublicAdapterAuthentication.hash,backendLeaf,StateT.run,Functor.map_map,erase]
  rfl

theorem outgoing (identity : PqxdhJointIdentity.IdentitySeed)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Compatible (RegistrationNativePlatformPublicAdapterBundleSigning.outgoing (n:=n) coins setup checks representation created identity query) :=by
  apply interpret_frame
  cases query with
  | inl query=>cases query with
    | hash request=>
      intro before
      simp only [RegistrationNativePlatformPublicAdapterBundleSigning.rawOutgoing,RegistrationNativePlatformPublicAdapterAuthentication.hash,backendLeaf,StateT.run,Functor.map_map,erase]
      rfl
    | sign request payload digest=>
      simp only [RegistrationNativePlatformPublicAdapterBundleSigning.rawOutgoing]
      exact pure_frame _
  | inr request=>
    simp only [RegistrationNativePlatformPublicAdapterBundleSigning.rawOutgoing]
    split <;> exact pure_frame _

theorem publication (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
    (identity : PqxdhJointIdentity.IdentitySeed)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (oneTime : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    Compatible (RegistrationNativePlatformPublicAdapterBundlePublication.program (n:=n) coins setup checks representation created writer identity control inputs oneTime pin) :=by
  apply program_frame
  intro query
  cases query with
  | inl query=>exact outgoing coins setup checks representation created identity query
  | inr query=>exact lift_frame _

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.coin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.sample' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.sample

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleFrame.publication

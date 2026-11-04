-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconBirth
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
/-! Successful creation returns the old local owner count. This derives the public SDK owner ordinal from the literal source control flow, independent of primitive replies and private key aliases. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCreateHandle
open RegistrationNativeBeaconFrontend
variable {n : Nat} {I KemSK Private Platform : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

theorem literal (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (implementation : QueryImpl (Trusted n KemSK) (StateT Private ProbComp))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners ownersAfter : State source)
    (environment environmentAfter : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (before after : Private) (index : Nat)
    (supported : (((.ok (some index),ownersAfter),environmentAfter),after)∈support
      ((simulateQ implementation (((create setup source edPin mlPin keyId).run owners).run environment)).run before)) :
    index=owners.length := by
  obtain ⟨prepared,leadingOwners,leadingEnv,middle,earlier,appended⟩ :=
    RegistrationNativeBeaconBirth.create_supported setup source implementation edPin mlPin keyId owners environment before index ownersAfter environmentAfter after supported
  have reached : ((.ok (some prepared),leadingOwners),leadingEnv)∈support
      (((prepare (n:=n) (KemSK:=KemSK) source edPin mlPin keyId).run owners).run environment) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ before
    rw [StateT.run'_eq,support_map]
    exact ⟨(((.ok (some prepared),leadingOwners),leadingEnv),middle),earlier,rfl⟩
  have unchanged:=RegistrationNativeKemBirthOwners.prepare_owners edPin mlPin keyId owners environment _ reached
  obtain ⟨born,afterBorn,worldOwner,final,_generated,_allocated,returned⟩ :=
    RegistrationNativeBeaconBirth.append_supported setup source implementation edPin keyId prepared.pin prepared.credentials
      prepared.identity prepared.prekey leadingOwners leadingEnv middle _ appended
  have same : index=leadingOwners.length := Option.some.inj (RustM.ok.inj (congrArg (fun result=>result.1.1.1) returned))
  exact same.trans (congrArg List.length unchanged)

theorem native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : RegistrationNativeExperiment.State n KemSK source) (index : Nat)
    (supported : (.ok (some index),after)∈support
      ((RegistrationNativeExperiment.beacon setup checks representation created (create setup source edPin mlPin keyId)).run before)) :
    index=before.beacons.length := by
  simp only [RegistrationNativeExperiment.beacon,StateT.run,mem_support_bind_iff,
    support_pure,Set.mem_singleton_iff] at supported
  obtain ⟨⟨⟨⟨reply,ownersAfter⟩,environmentAfter⟩,rawAfter⟩,called,returned⟩ := supported
  have same : reply=.ok (some index) := congrArg Prod.fst returned.symm
  subst reply
  exact literal setup (RegistrationNativeExperiment.trusted setup checks representation created source) edPin mlPin keyId
    before.beacons ownersAfter (RegistrationWorldAgreementCompiler.erase before.server.world) environmentAfter before rawAfter index called

theorem platform (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before after : RegistrationNativeExperiment.State n KemSK source) (previous next : Platform) (index : Nat)
    (supported : ((.ok (some index),after),next)∈support
      (((RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created (create setup source edPin mlPin keyId))).run before).run previous)) :
    index=before.beacons.length := by
  apply native setup checks representation created edPin mlPin keyId before after index
  exact RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported

end BeaconcryptCore.Computational.RegistrationNativeCreateHandle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateHandle.literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateHandle.literal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateHandle.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateHandle.native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCreateHandle.platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCreateHandle.platform

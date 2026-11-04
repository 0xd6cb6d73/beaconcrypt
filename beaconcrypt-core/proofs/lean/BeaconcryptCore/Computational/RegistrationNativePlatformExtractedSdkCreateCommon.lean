-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateReceipt
/-! The retained constructor receipt exposes the actual pre-registration source state and the full native owner-registration marginal of one common run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformExtractedSdkCreateReceipt (SourceM Packet Result)
variable {n : Nat} {I KemSK R Error Platform A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S V W : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (observe : V →W) (work : StateT S m V) (before : S) :
    (observe <$>work) before=(fun result =>(observe result.1,result.2)) <$>work before := by
  change (observe <$>work).run before=_
  rw [StateT.run_map]
  rfl

private theorem bind_apply {S V W : Type} {m : Type →Type} [Monad m]
    (work : StateT S m V) (next : V →StateT S m W) (before : S) :
    (work >>=next) before=(work before >>=fun result =>next result.1 result.2) := rfl

private theorem close_map (observe : A →B) (work : SourceM n KemSK source Platform A) :
    RegistrationNativePlatformExtractedSdkCreate.close (observe <$>work)=
      observe <$>RegistrationNativePlatformExtractedSdkCreate.close work := by
  funext before
  change (RegistrationNativePlatformExtractedSdkCreate.close (observe <$>work)).run before=
    (observe <$>RegistrationNativePlatformExtractedSdkCreate.close work).run before
  unfold RegistrationNativePlatformExtractedSdkCreate.close
  dsimp only [StateT.run]
  simp only [map_apply,Functor.map_map]

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (SourceM n KemSK source Platform))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (SourceM n KemSK source Platform))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (SourceM n KemSK source Platform))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (kem : AdapterBeaconConstructorKem.Representation view R)

noncomputable def runner
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    StateT Platform ProbComp (Result n KemSK R source) :=
  ((RegistrationNativePlatformExtractedSdkCreateReceipt.program coins setup checks representation created generator view kem leaves keyId serverId mlPin rng).run
    before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world) |>.run before

def nativeProjection (result : Result n KemSK R source) : RustM (Option Nat) ×RegistrationNativeExperiment.State n KemSK source :=
  (result.1.1.1.reply,RegistrationNativeFinishTerminalTree.assemble result.1.1.2 result.1.2 result.2)

theorem native
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    nativeProjection <$>runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before=
      (RegistrationNativePlatformExperiment.liftNative coins
        (RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativeBeaconFrontend.create setup source (view.edPublic serverId) mlPin keyId))).run before := by
  have erased := congrArg (fun work =>RegistrationNativePlatformExtractedSdkCreate.close work)
    (RegistrationNativePlatformExtractedSdkCreateReceipt.erases coins setup checks representation created generator view kem leaves keyId serverId mlPin rng)
  rw [close_map] at erased
  have source := RegistrationNativePlatformExtractedSdkCreate.native_entry coins setup checks representation created generator view kem leaves keyId serverId mlPin rng
  rw [←erased,←Functor.map_map] at source
  have equation := congrArg (fun work =>work.run before) source
  unfold RegistrationNativePlatformExtractedSdkCreate.close at equation
  dsimp only [StateT.run] at equation
  simp only [RegistrationNativePlatformExtractedSdkCreateReceipt.forget,map_apply,Functor.map_map] at equation
  exact equation


def sourceProjection (result : Result n KemSK R source) :
    RustM (AdapterBeaconConstructorBody.Outcome R) ×RegistrationNativeExperiment.State n KemSK source :=
  (.ok result.1.1.1.outcome,result.1.1.1.sourceAfter)

theorem source_body
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    sourceProjection <$>runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before=
      (RegistrationNativePlatformExtractedSdkCreate.close
        (AdapterBeaconConstructorBody.withInputs (m := SourceM n KemSK source Platform) generator keyId serverId mlPin rng).run).run before := by
  rw [AdapterBeaconConstructorNative.source_body coins setup checks representation created generator view kem leaves]
  simp only [RustT.run_lift]
  unfold runner RegistrationNativePlatformExtractedSdkCreateReceipt.program
    RegistrationNativePlatformExtractedSdkCreate.close
  dsimp only [StateT.run]
  simp only [map_apply,Functor.map_map,bind_apply,map_bind]
  conv_rhs => rw [←bind_pure_comp]
  apply bind_congr
  rintro ⟨⟨⟨captured,owners⟩,environment⟩,current⟩
  have same := RegistrationNativePlatformExtractedSdkCreateReceipt.commit_source
    coins setup checks representation created generator view kem leaves keyId serverId captured owners environment current
  have mapped := congrArg (fun work => (fun pair => (RustM.ok pair.1,pair.2)) <$>work) same
  simp only [Functor.map_map,map_pure,RegistrationNativePlatformExtractedSdkCreateReceipt.sourceWord] at mapped
  exact mapped

theorem typed_source
    (leaves : AdapterBeaconConstructorNative.Leaves (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
      coins setup checks representation created generator view kem)
    (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey) (mlPin : Std.Array U8 1952#usize) (rng : R)
    (identityBytes mldsaBytes : Slice U8)
    (parsed : beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityBytes=.ok (.Ok serverId))
    (parsedMl : core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mldsaBytes=.ok (.Ok mlPin))
    (before : RegistrationNativeExperiment.State n KemSK source) :
    sourceProjection <$>runner coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before=
      (RegistrationNativePlatformExtractedSdkCreate.close
        (beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m := RustT (SourceM n KemSK source Platform))
          generator keyId identityBytes mldsaBytes rng).run).run before := by
  rw [RegistrationNativePlatformExtractedSdkCreate.typed_source coins setup checks representation created generator view kem leaves
    keyId serverId mlPin rng identityBytes mldsaBytes parsed parsedMl,
    ←AdapterBeaconConstructorNative.source_body coins setup checks representation created generator view kem leaves]
  exact source_body coins setup checks representation created generator view kem leaves keyId serverId mlPin rng before

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon.source_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon.source_body

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateCommon.typed_source

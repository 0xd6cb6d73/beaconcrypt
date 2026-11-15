-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorNativeRegister
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Reached constructor receipts obtain their pin binding and private KEM row from the actual same run, before owner registration. These facts hold for every supported result and retain all four shared state layers. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorReached
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup Checks)
open AdapterBeaconConstructorNative (M Leaves)
variable {n : Nat} {ι KemSK R Error Auxiliary P : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (M n KemSK source Auxiliary (StateT P ProbComp)))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (M n KemSK source Auxiliary (StateT P ProbComp)))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (M n KemSK source Auxiliary (StateT P ProbComp)))]
variable (coins : QueryImpl unifSpec (StateT P ProbComp)) (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : Leaves (n := n) (Auxiliary := Auxiliary) coins setup checks representation created generator view kem)

omit children in
theorem binding (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng afterRng : R)
    (owners ownersAfter : RegistrationNativeBeaconFrontend.State source)
    (env envAfter : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before after : AdapterBeaconConstructorKem.Native n KemSK source) (platform platformAfter : P)
    (ready : RegistrationNativeBeaconFrontend.Prepared source) (receipt : AdapterBeaconConstructorKem.Receipt R)
    (supported : (((((some (ready, receipt), afterRng), ownersAfter), envAfter), after), platformAfter) ∈ support
      (((((AdapterBeaconConstructorNative.joint coins setup checks representation created generator view kem leaves
        (view.edPublic serverId) mlPin keyId rng).run owners).run env).run before).run platform)) :
    ready.pin.binding = ⟨view.edPublic serverId, keyId⟩ := by
  have normalized : AdapterBeaconConstructorJoint.normalize (view.edPublic serverId) keyId <$>
      AdapterBeaconConstructorNative.joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng =
      AdapterBeaconConstructorNative.joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng :=
    AdapterBeaconConstructorJoint.normalized generator view setup.joint _ leaves.ed _ _ leaves.kx _ (view.edPublic serverId) mlPin keyId rng
  rw [← normalized] at supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨raw, _, same⟩ := supported
  have selected := congrArg (fun result => result.1.1.1.1.1) same
  change raw.1.1.1.1.1.map (fun captured => (AdapterBeaconConstructorPrepare.normalizeReady (view.edPublic serverId) keyId captured.1, captured.2)) = some (ready, receipt) at selected
  cases choice : raw.1.1.1.1.1 with
  | none => simp only [choice, Option.map_none] at selected; cases selected
  | some captured =>
    simp only [choice, Option.map_some, Option.some.injEq] at selected
    have exactBinding := congrArg (fun value : AdapterBeaconConstructorJoint.Capture source R => value.1.pin.binding) selected
    exact exactBinding.symm

omit children in
theorem kem_row (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng afterRng : R)
    (owners ownersAfter : RegistrationNativeBeaconFrontend.State source)
    (env envAfter : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before after : AdapterBeaconConstructorKem.Native n KemSK source) (platform platformAfter : P)
    (ready : RegistrationNativeBeaconFrontend.Prepared source) (receipt : AdapterBeaconConstructorKem.Receipt R)
    (supported : (((((some (ready, receipt), afterRng), ownersAfter), envAfter), after), platformAfter) ∈ support
      (((((AdapterBeaconConstructorNative.joint coins setup checks representation created generator view kem leaves
        (view.edPublic serverId) mlPin keyId rng).run owners).run env).run before).run platform)) :
    AdapterPublicWrapperState.KemPair view after.pool receipt.pair receipt.born.1 receipt.born.2 := by
  simp only [AdapterBeaconConstructorNative.joint, AdapterBeaconConstructorJoint.joint,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨⟨⟨prepared, middleOwners⟩, middleEnv⟩, middleNative⟩, middleP⟩, _, continued⟩ := supported
  cases chosen : prepared.1 with
  | none =>
    simp only [chosen, StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    cases continued
  | some selected =>
    simp only [chosen, StateT.run_bind, mem_support_bind_iff] at continued
    obtain ⟨⟨⟨⟨⟨generated, lastOwners⟩, lastEnv⟩, lastNative⟩, lastP⟩, generatedSupport, done⟩ := continued
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at done
    cases done
    exact (AdapterBeaconConstructorKemSupport.lifted_supported coins setup view kem prepared.2 middleOwners ownersAfter
      middleEnv envAfter middleNative middleP receipt after platformAfter generatedSupport).2.2

omit children in
theorem entry_material (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng afterRng : R)
    (owners ownersAfter : RegistrationNativeBeaconFrontend.State source)
    (env envAfter : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before after : AdapterBeaconConstructorKem.Native n KemSK source) (platform platformAfter : P)
    (index : Nat) (stored : beaconcrypt_public_wrapper.beacon.Beacon)
    (supported : (((((.ok (some index), (.Ok stored, afterRng)), ownersAfter), envAfter), after), platformAfter) ∈ support
      (((((AdapterBeaconConstructorNative.entry coins setup checks representation created generator view kem leaves
        keyId serverId mlPin rng).run owners).run env).run before).run platform)) :
    ∃ owner, ownersAfter[index]? = some owner ∧
      AdapterPublicWrapperState.Beacon view setup.joint after.pool stored owner
        after.server.world.world.1.owners[owner.worldOwner]? := by
  simp only [AdapterBeaconConstructorNative.entry, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨⟨⟨⟨captured, middleOwners⟩, middleEnv⟩, middleNative⟩, middleP⟩, jointly, continued⟩ := supported
  rcases captured with ⟨selected, finalRng⟩
  cases selected with
  | none =>
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at continued
    cases continued
  | some captured =>
    rcases captured with ⟨ready, receipt⟩
    have pinBinding := binding coins setup checks representation created generator view kem leaves keyId serverId mlPin rng finalRng
      owners middleOwners env middleEnv before middleNative platform middleP ready receipt jointly
    have keyRow := kem_row coins setup checks representation created generator view kem leaves keyId serverId mlPin rng finalRng
      owners middleOwners env middleEnv before middleNative platform middleP ready receipt jointly
    simp only [StateT.run_bind] at continued
    rw [AdapterBeaconConstructorNativeRegister.register_exact] at continued
    simp only [StateT.run_pure, pure_bind, support_pure, Set.mem_singleton_iff,
      AdapterBeaconConstructorNative.sourceResult, AdapterBeaconConstructorJoint.sourceResult] at continued
    cases continued
    let owner := RegistrationNativeBeaconBirth.owner setup source ready.pin ready.identity ready.prekey receipt.born middleNative.server.world.world.1.owners.length
    refine ⟨owner, ?_, ?_⟩
    · simp [owner]
    · have slot : (AdapterBeaconConstructorMaterial.appendNative keyId (view.edPublic serverId) middleNative).server.world.world.1.owners[owner.worldOwner]? = some (.inactive .fresh) := by
        simp [AdapterBeaconConstructorMaterial.appendNative, AdapterBeaconConstructorMaterial.appendWorld,
          PqxdhRecordLiftWorld.chargeEffect, owner, RegistrationNativeBeaconBirth.owner]
      rw [slot]
      exact AdapterBeaconConstructorNativeRegister.object_related coins setup checks representation created generator view kem leaves keyId serverId ready receipt middleNative.pool middleNative.server.world.world.1.owners.length pinBinding keyRow

end BeaconcryptCore.Refinement.AdapterBeaconConstructorReached

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorReached.binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorReached.binding

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorReached.kem_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorReached.kem_row

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorReached.entry_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorReached.entry_material

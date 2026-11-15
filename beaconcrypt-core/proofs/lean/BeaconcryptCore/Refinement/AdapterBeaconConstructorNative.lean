-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint
import BeaconcryptCore.Refinement.AdapterBeaconConstructorKemLift
import BeaconcryptCore.Computational.RegistrationNativeBeaconCreateLift
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Actual SDK constructor and Native.create are projections of one joint key-generation execution under individual primitive sampling/object-view contracts. The typed source entry adds native owner registration as explicit proof administration after the SDK result. Every native/private/platform poststate and the exact source caller RNG are retained. Ed/X25519/KEM availability is the explicitly selected infallible native entropy profile; generic failing RNGs are covered only by the unconditional raw source factor. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorNative
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Trusted)
variable {n : Nat} {ι KemSK R Error Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]

abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Auxiliary : Type)
    (m : Type → Type) (Value : Type) := RegistrationNativePlatformGenericBundle.M source Auxiliary
      (StateT (AdapterBeaconConstructorKem.Native n KemSK source) m) Value

variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT (M n KemSK source Auxiliary m))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT (M n KemSK source Auxiliary m))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT (M n KemSK source Auxiliary m))]

noncomputable def lift (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    {Value : Type} (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : M n KemSK source Auxiliary m Value :=
  RegistrationNativePlatformGenericBundle.liftLegacy (AdapterBeaconConstructorKemLift.implementation coins setup checks representation created) work

structure Leaves (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (kem : AdapterBeaconConstructorKem.Representation view R) where
  ed : AdapterBeaconConstructorGeneration.EdContract (m := M n KemSK source Auxiliary m) generator view setup.joint
    (lift coins setup checks representation created (RegistrationNativeBeaconFrontend.sample PqxdhJointIdentity.sampleSeed))
  kx : AdapterBeaconConstructorGeneration.KxContract (m := M n KemSK source Auxiliary m) generator view
    (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
    (lift coins setup checks representation created (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar))
  getter : ∀ key, crypto.edPublicBytes key = pure (view.edPublic key)
  kemOperation : ∀ rng, generators.kemGenerate generator rng = RustT.lift
    ((fun receipt : AdapterBeaconConstructorKem.Receipt R => (.Ok receipt.pair, receipt.rng)) <$>
      AdapterBeaconConstructorKemLift.joint (n := n) (Auxiliary := Auxiliary) coins setup view kem rng)

variable (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (generator : rand_core.TryCryptoRng R Error) (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : Leaves (n := n) (Auxiliary := Auxiliary) coins setup checks representation created generator view kem)

noncomputable def joint (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    M n KemSK source Auxiliary m (Option (AdapterBeaconConstructorJoint.Capture source R) × R) :=
  AdapterBeaconConstructorJoint.joint generator view setup.joint _ leaves.ed _ _ leaves.kx
    (AdapterBeaconConstructorKemLift.joint coins setup view kem) edPin mlPin keyId rng

noncomputable def sourceResult (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (result : Option (AdapterBeaconConstructorJoint.Capture source R) × R) : AdapterBeaconConstructorBody.Outcome R :=
  AdapterBeaconConstructorJoint.sourceResult generator view setup.joint _ leaves.ed _ _ leaves.kx keyId serverId result

noncomputable def entry (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R) : M n KemSK source Auxiliary m (RustM (Option Nat) × AdapterBeaconConstructorBody.Outcome R) := do
  let captured ← joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng
  let sourceResult := sourceResult coins setup checks representation created generator view kem leaves keyId serverId captured
  match captured.1 with
  | none => pure (.ok none, sourceResult)
  | some (ready, generated) =>
    let registered ← lift coins setup checks representation created
      (RegistrationNativeBeaconCreateEntry.register setup (view.edPublic serverId) keyId ready generated.born)
    pure (registered, sourceResult)

omit children in
theorem source_body (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R) :
    AdapterBeaconConstructorBody.withInputs (m := M n KemSK source Auxiliary m) generator keyId serverId mlPin rng =
      RustT.lift (sourceResult coins setup checks representation created generator view kem leaves keyId serverId <$>
        joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng) := by
  exact AdapterBeaconConstructorJoint.source_program generator view setup.joint _ leaves.ed _ _ leaves.kx _
    keyId serverId mlPin rng (leaves.getter serverId) leaves.kemOperation

omit children in
theorem native_entry (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R) :
    Prod.fst <$> entry coins setup checks representation created generator view kem leaves keyId serverId mlPin rng =
      lift coins setup checks representation created
        (RegistrationNativeBeaconFrontend.create setup source (view.edPublic serverId) mlPin keyId) := by
  have marginal := AdapterBeaconConstructorJoint.native generator view setup.joint _ leaves.ed _ _ leaves.kx
    (AdapterBeaconConstructorKemLift.joint coins setup view kem)
    (lift coins setup checks representation created (RegistrationNativeBeaconFrontend.kem (.inr (.inl .create))))
    (AdapterBeaconConstructorKemLift.native coins setup checks representation created view kem)
    (view.edPublic serverId) mlPin keyId rng
  let next : Option (RegistrationNativeBeaconFrontend.Prepared source × (Nat × PqxdhKemIndCca.MlKem768PublicKey)) → M n KemSK source Auxiliary m (RustM (Option Nat)) := fun selected =>
    match selected with
    | none => pure (.ok none)
    | some (ready, born) => lift coins setup checks representation created (RegistrationNativeBeaconCreateEntry.register setup (view.edPublic serverId) keyId ready born)
  calc
    _ = ((AdapterBeaconConstructorJoint.nativeResult <$>
        joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) mlPin keyId rng) >>= next) := by
        simp only [entry, map_bind, bind_map_left]
        apply bind_congr
        rintro ⟨selected, nextRng⟩
        cases selected with
        | none => simp only [map_pure, AdapterBeaconConstructorJoint.nativeResult, Option.map_none, next]
        | some captured =>
          rcases captured with ⟨ready, generated⟩
          simp only [bind_pure_comp, AdapterBeaconConstructorJoint.nativeResult, Option.map_some, next, Functor.map_map]
          exact id_map (lift coins setup checks representation created (RegistrationNativeBeaconCreateEntry.register setup (view.edPublic serverId) keyId ready generated.born) : M n KemSK source Auxiliary m (RustM (Option Nat)))
    _ = _ := by
      change ((AdapterBeaconConstructorJoint.nativeResult <$> AdapterBeaconConstructorJoint.joint generator view setup.joint _ leaves.ed _ _ leaves.kx _ (view.edPublic serverId) mlPin keyId rng) >>= next) = _
      rw [marginal]
      refine Eq.trans ?_ (RegistrationNativeBeaconCreateLift.create
        (AdapterBeaconConstructorKemLift.implementation coins setup checks representation created) setup (view.edPublic serverId) mlPin keyId).symm
      change ((do
        let prepared ← RegistrationNativeBeaconCreateLift.prepared (AdapterBeaconConstructorKemLift.implementation coins setup checks representation created) (view.edPublic serverId) mlPin keyId
        match prepared with
        | none => pure none
        | some ready => do
          let born ← lift coins setup checks representation created (RegistrationNativeBeaconFrontend.kem (.inr (.inl .create)))
          pure (some (ready, born))) >>= next) = _
      simp only [bind_assoc]
      apply bind_congr
      intro selected
      cases selected with
      | none => simp only [pure_bind, next]
      | some ready => simp only [bind_assoc, pure_bind, next]; rfl

noncomputable def sourceAll (keyId : U64) (identityKey mldsaKey : Slice U8) (rng : R) : RustT (M n KemSK source Auxiliary m) (AdapterBeaconConstructorBody.Outcome R) := do
  let parsed ← AdapterRecordRequestMonad.liftRust (beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey)
  match parsed with
  | .Err _ => AdapterBeaconConstructorBody.reject rng
  | .Ok serverId =>
    let key : core.result.Result (Std.Array U8 1952#usize) core.array.TryFromSliceError ← AdapterRecordRequestMonad.liftRust
      (core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from 1952#usize core.U8.Insts.CoreMarkerCopy mldsaKey)
    core.result.Result.casesOn (motive := fun _ => RustT (M n KemSK source Auxiliary m) (AdapterBeaconConstructorBody.Outcome R)) key
      (fun key => RustT.lift (sourceResult coins setup checks representation created generator view kem leaves keyId serverId <$>
        joint coins setup checks representation created generator view kem leaves (view.edPublic serverId) key keyId rng))
      (fun _ => AdapterBeaconConstructorBody.reject rng)

omit children in
theorem source_all (keyId : U64) (identityKey mldsaKey : Slice U8) (rng : R) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m := RustT (M n KemSK source Auxiliary m)) generator keyId identityKey mldsaKey rng =
      sourceAll coins setup checks representation created generator view kem leaves keyId identityKey mldsaKey rng := by
  rw [AdapterBeaconConstructorBody.body]
  unfold AdapterBeaconConstructorBody.source sourceAll
  apply bind_congr
  intro parsed
  cases parsed with
  | Err error => rfl
  | Ok serverId =>
    apply bind_congr
    intro width
    cases width with
    | Err error => rfl
    | Ok mlPin => exact source_body coins setup checks representation created generator view kem leaves keyId serverId mlPin rng

end BeaconcryptCore.Refinement.AdapterBeaconConstructorNative

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorNative.source_body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorNative.source_body

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorNative.native_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorNative.native_entry

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorNative.source_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorNative.source_all

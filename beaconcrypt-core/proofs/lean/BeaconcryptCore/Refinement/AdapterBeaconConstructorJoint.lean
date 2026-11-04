-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare
import BeaconcryptCore.Refinement.AdapterBeaconConstructorKem
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! One joint constructor run returns the source object, private native preparation, indexed KEM receipt and exact caller RNG. Native erasure follows from individual sampler marginals. SDK correspondence uses an explicit individual KEM generation/availability contract; the unconditional raw source theorem separately retains all seven errors. Owner registration is a later proof-administration step. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Prepared)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT m)]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK R Error : Type}
variable (generator : rand_core.TryCryptoRng R Error)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (mlSample : m (Option (RegistrationNativeMldsa.Credential source)))
variable (ml : AdapterBeaconConstructorGeneration.MldsaContract generator view mlSample)
variable (jointKeys : PqxdhJointIdentity.Primitives) (edSample : m PqxdhJointIdentity.IdentitySeed)
variable (ed : AdapterBeaconConstructorGeneration.EdContract generator view jointKeys edSample)
variable (kxPublic : PqxdhJointGapDh.ScalarBytes → Std.Array U8 32#usize)
variable (kxSample : m PqxdhJointGapDh.ScalarBytes)
variable (kx : AdapterBeaconConstructorGeneration.KxContract generator view kxPublic kxSample)
variable (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
variable (kemJoint : R → m (AdapterBeaconConstructorKem.Receipt R))

abbrev Capture (source : RegistrationNativeMldsa.Source) (R : Type) := Prepared source × AdapterBeaconConstructorKem.Receipt R

noncomputable def object (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (captured : Capture source R) : beaconcrypt_public_wrapper.beacon.Beacon :=
  ⟨ed.realize captured.1.identity, keyId,
    .Fresh ⟨captured.1.pin.binding⟩ (kx.realize captured.1.prekey) captured.2.pair,
    serverId, ⟨ml.realize captured.1.credentials, captured.1.pin⟩⟩

noncomputable def joint (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    m (Option (Capture source R) × R) := do
  let prepared ← AdapterBeaconConstructorPrepare.joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash edPin mlPin keyId rng
  match prepared.1 with
  | none => pure (none, prepared.2)
  | some ready =>
    let kem ← kemJoint prepared.2
    pure (some (ready, kem), kem.rng)

noncomputable def sourceResult (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (result : Option (Capture source R) × R) : AdapterBeaconConstructorBody.Outcome R :=
  (match result.1 with
   | none => .Err ()
   | some captured => .Ok (object generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx keyId serverId captured), result.2)

def nativeResult (result : Option (Capture source R) × R) : Option (Prepared source × (Nat × PqxdhKemIndCca.MlKem768PublicKey)) :=
  result.1.map (fun captured => (captured.1, captured.2.born))

omit material primitive generators crypto children in
private theorem marginal_bind {A B C : Type} (work : m A) (observe : A → B) (sample : m B)
    (marginal : observe <$> work = sample) (next : A → m C) (target : B → m C)
    (step : ∀ value, next value = target (observe value)) :
    (do let value ← work; next value) = (do let value ← sample; target value) := by
  have same : next = target ∘ observe := funext step
  rw [same]
  calc
    _ = ((observe <$> work) >>= target) := by simp only [bind_map_left, Function.comp_def]
    _ = _ := by rw [marginal]

omit children in
theorem native (kemSample : m (Nat × PqxdhKemIndCca.MlKem768PublicKey))
    (kemMarginal : ∀ rng, AdapterBeaconConstructorKem.Receipt.born <$> kemJoint rng = kemSample)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    nativeResult <$> joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash kemJoint edPin mlPin keyId rng = (do
      let prepared ← (do
        let generated ← mlSample
        match generated with
        | none => pure none
        | some credentials =>
          let digest ← hash (.Single (Std.Array.to_slice mlPin))
          let identity ← edSample
          let prekey ← kxSample
          pure (some (⟨credentials, RegistrationNativeBeaconCreateProgram.pin edPin mlPin keyId digest, identity, prekey⟩ : Prepared source)))
      match prepared with
      | none => pure none
      | some ready =>
        let born ← kemSample
        pure (some (ready, born))) := by
  simp only [joint, map_bind]
  apply marginal_bind _ Prod.fst _ (AdapterBeaconConstructorPrepare.native generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash edPin mlPin keyId rng)
  rintro ⟨prepared, nextRng⟩
  cases prepared with
  | none => simp only [map_pure, nativeResult, Option.map_none]
  | some ready =>
    simp only [bind_pure_comp, Functor.map_map]
    change (fun receipt : AdapterBeaconConstructorKem.Receipt R => some (ready, receipt.born)) <$> kemJoint nextRng = _
    calc
      _ = (fun born => some (ready, born)) <$> (AdapterBeaconConstructorKem.Receipt.born <$> kemJoint nextRng) := by rw [Functor.map_map]
      _ = _ := by rw [kemMarginal]

theorem source_program (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R)
    (getter : crypto.edPublicBytes serverId = pure (view.edPublic serverId))
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request)
    (kemOperation : ∀ rng, generators.kemGenerate generator rng = RustT.lift
      ((fun receipt : AdapterBeaconConstructorKem.Receipt R => (.Ok receipt.pair, receipt.rng)) <$> kemJoint rng)) :
    AdapterBeaconConstructorBody.withInputs generator keyId serverId mlPin rng =
      RustT.lift (sourceResult generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx keyId serverId <$>
        joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash kemJoint (view.edPublic serverId) mlPin keyId rng) := by
  rw [AdapterBeaconConstructorPrepare.source_program generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash keyId serverId mlPin rng getter hashLeaf]
  apply RustT.ext
  simp only [joint, RustT.run_bind, RustT.run_lift, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨prepared, nextRng⟩
  cases prepared with
  | none => simp only [AdapterBeaconConstructorBody.reject, RustT.run_pure, map_pure, sourceResult]
  | some ready =>
    simp only [AdapterBeaconConstructorPrepare.finish]
    rw [kemOperation]
    simp only [RustT.run_bind, RustT.run_lift, Functor.map_map, bind_map_left,
      RustT.run_pure, sourceResult, object, bind_pure_comp]

omit material primitive generators crypto children in
def normalize (edPin : Std.Array U8 32#usize) (keyId : U64) (result : Option (Capture source R) × R) : Option (Capture source R) × R :=
  (result.1.map (fun captured => (AdapterBeaconConstructorPrepare.normalizeReady edPin keyId captured.1, captured.2)), result.2)

omit children in
theorem normalized (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    normalize edPin keyId <$> joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash kemJoint edPin mlPin keyId rng =
      joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash kemJoint edPin mlPin keyId rng := by
  calc
    _ = (do
      let prepared ← AdapterBeaconConstructorPrepare.normalize edPin keyId <$>
        AdapterBeaconConstructorPrepare.joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash edPin mlPin keyId rng
      match prepared.1 with
      | none => pure (none, prepared.2)
      | some ready => do
        let kem ← kemJoint prepared.2
        pure (some (ready, kem), kem.rng)) := by
      simp only [joint, map_bind, bind_map_left]
      apply bind_congr
      rintro ⟨prepared, nextRng⟩
      cases prepared with
      | none => simp only [map_pure, normalize, AdapterBeaconConstructorPrepare.normalize, Option.map_none]
      | some ready =>
        simp only [AdapterBeaconConstructorPrepare.normalize, Option.map_some, map_bind, map_pure, normalize]
    _ = _ := by rw [AdapterBeaconConstructorPrepare.normalized]; rfl

end BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint.native

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint.source_program

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorJoint.normalized

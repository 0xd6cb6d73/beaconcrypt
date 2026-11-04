-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration
import BeaconcryptCore.Refinement.AdapterBeaconConstructorPin
import BeaconcryptCore.Computational.RegistrationNativeBeaconCreateProgram
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! A joint preparation run keeps the caller RNG with the actual private key material. Its native projection is derived by erasing that RNG after each individual sampler. Its source projection continues into the unchanged KEM call, including every KEM error and returned RNG. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare
open AdapterPublicWrapperRustT (RustT)
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (Prepared)
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (RustT m)]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK R Error : Type}

omit material primitive generators crypto children in
private theorem lift_map {A B : Type} (observe : A → B) (work : m A) :
    RustT.lift (observe <$> work) = observe <$> RustT.lift work := by
  simp only [map_eq_bind_pure_comp, RustT.lift_bind, Function.comp_apply, RustT.lift_pure]
  rfl

omit material primitive generators crypto children [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl

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

noncomputable def joint (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    m (Option (Prepared source) × R) := do
  let generated ← ml.joint rng
  match generated.1 with
  | none => pure (none, generated.2)
  | some credentials =>
    let digest ← hash (.Single (Std.Array.to_slice mlPin))
    let identity ← ed.joint generated.2
    let prekey ← kx.joint identity.2
    pure (some ⟨credentials, RegistrationNativeBeaconCreateProgram.pin edPin mlPin keyId digest, identity.1, prekey.1⟩, prekey.2)

omit material primitive generators crypto children in
private theorem marginal_bind {A B : Type} (work : m (A × R)) (sample : m A)
    (marginal : Prod.fst <$> work = sample) (next : A × R → m B) (target : A → m B)
    (step : ∀ value rng, next (value, rng) = target value) :
    (do let reply ← work; next reply) = (do let value ← sample; target value) := by
  have same : next = fun reply => target reply.1 := by
    funext reply
    exact step reply.1 reply.2
  rw [same, ← bind_map_left, marginal]

omit children in
theorem native (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    Prod.fst <$> joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash edPin mlPin keyId rng = (do
      let generated ← mlSample
      match generated with
      | none => pure none
      | some credentials =>
        let digest ← hash (.Single (Std.Array.to_slice mlPin))
        let identity ← edSample
        let prekey ← kxSample
        pure (some ⟨credentials, RegistrationNativeBeaconCreateProgram.pin edPin mlPin keyId digest, identity, prekey⟩)) := by
  simp only [joint, map_bind]
  apply marginal_bind _ _ (ml.nativeMarginal rng)
  intro generated nextRng
  cases generated with
  | none => simp only [map_pure]
  | some credential =>
    simp only [map_bind]
    apply bind_congr
    intro digest
    apply marginal_bind _ _ (ed.nativeMarginal nextRng)
    intro identity afterSigning
    apply marginal_bind _ _ (kx.nativeMarginal afterSigning)
    intro prekey afterPrekey
    simp only [map_pure]

noncomputable def finish (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (ready : Prepared source) (rng : R) : RustT m (AdapterBeaconConstructorBody.Outcome R) := do
  let (kem, nextRng) ← generators.kemGenerate generator rng
  match kem with
  | .Err _ => AdapterBeaconConstructorBody.reject nextRng
  | .Ok kem => pure (.Ok ⟨ed.realize ready.identity, keyId,
      .Fresh ⟨ready.pin.binding⟩ (kx.realize ready.prekey) kem, serverId,
      ⟨ml.realize ready.credentials, ready.pin⟩⟩, nextRng)

theorem source_program (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (rng : R)
    (getter : crypto.edPublicBytes serverId = pure (view.edPublic serverId))
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => RustM.ok (core.option.Option.Some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request) :
    AdapterBeaconConstructorBody.withInputs generator keyId serverId mlPin rng = (do
      let prepared ← RustT.lift (joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash (view.edPublic serverId) mlPin keyId rng)
      match prepared.1 with
      | none => AdapterBeaconConstructorBody.reject prepared.2
      | some ready => finish generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx keyId serverId ready prepared.2) := by
  rw [AdapterBeaconConstructorGeneration.with_inputs generator view mlSample ml keyId serverId mlPin rng getter]
  simp only [joint, RustT.lift_bind, bind_assoc]
  apply bind_congr
  rintro ⟨generated, afterMl⟩
  cases generated with
  | none => simp only [RustT.lift_pure, pure_bind]
  | some credentials =>
    have fingerprint : beaconcrypt_public_request.auth.fingerprint_pin (m := RustT m)
        ⟨view.edPublic serverId, keyId⟩ mlPin =
        RustT.lift ((fun digest => core.option.Option.Some
          (RegistrationNativeBeaconCreateProgram.pin (view.edPublic serverId) mlPin keyId digest)) <$>
            hash (.Single (Std.Array.to_slice mlPin))) := by
      apply RustT.ext
      rw [AdapterBeaconConstructorPin.source _ _ hash hashLeaf]
      simp only [RustT.run_lift, Functor.map_map]
      rfl
    rw [fingerprint, lift_map]
    simp only [bind_map_left, RustT.lift_bind, bind_assoc]
    apply bind_congr
    intro digest
    rw [AdapterBeaconConstructorGeneration.with_keys generator view jointKeys edSample ed kxPublic kxSample kx]
    apply bind_congr
    rintro ⟨identity, afterSigning⟩
    simp only [pqxdh.BeaconFresh.new, lift_ok, pure_bind]
    apply bind_congr
    rintro ⟨prekey, afterPrekey⟩
    simp only [RustT.lift_pure, pure_bind, finish]
    rfl

omit material primitive generators crypto children in
def normalizeReady (edPin : Std.Array U8 32#usize) (keyId : U64) (ready : Prepared source) : Prepared source :=
  { ready with pin := { ready.pin with binding := ⟨edPin, keyId⟩ } }

omit material primitive generators crypto children in
def normalize (edPin : Std.Array U8 32#usize) (keyId : U64) (result : Option (Prepared source) × R) : Option (Prepared source) × R :=
  (result.1.map (normalizeReady edPin keyId), result.2)

omit children in
theorem normalized (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (rng : R) :
    normalize edPin keyId <$> joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash edPin mlPin keyId rng =
      joint generator view mlSample ml jointKeys edSample ed kxPublic kxSample kx hash edPin mlPin keyId rng := by
  simp only [joint, map_bind]
  apply bind_congr
  rintro ⟨generated, nextRng⟩
  cases generated with
  | none => simp only [map_pure, normalize, Option.map_none]
  | some credential =>
    simp only [map_bind]
    apply bind_congr
    intro digest
    apply bind_congr
    intro identity
    apply bind_congr
    intro prekey
    simp only [map_pure, normalize, Option.map_some, normalizeReady, RegistrationNativeBeaconCreateProgram.pin]

end BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare.native

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare.source_program

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare.normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorPrepare.normalized

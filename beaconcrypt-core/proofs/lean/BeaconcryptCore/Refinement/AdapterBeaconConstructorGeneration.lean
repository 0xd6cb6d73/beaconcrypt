-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterBeaconConstructorBody
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Selected per-key sampling and object-view contracts retain the actual returned caller RNG jointly with each native secret. ML failure retains its reached RNG. The Ed and X25519 contracts explicitly select the infallible native sampling profile; they do not cover arbitrary failing TryCryptoRng implementations. Generic constructor factoring remains valid on every error path without these contracts. No controller or initial-material conclusion is a contract field. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem lift_map {A B : Type} (observe : A → B) (work : m A) :
    RustT.lift (observe <$> work) = observe <$> RustT.lift work := by
  simp only [map_eq_bind_pure_comp, RustT.lift_bind, Function.comp_apply, RustT.lift_pure]
  rfl

variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
variable [crypto : CryptoOperations (RustT m)] [children : ChildOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK R Error : Type}

structure MldsaContract (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (sample : m (Option (RegistrationNativeMldsa.Credential source))) where
  joint : R → m (Option (RegistrationNativeMldsa.Credential source) × R)
  nativeMarginal : ∀ rng, Prod.fst <$> joint rng = sample
  realize : RegistrationNativeMldsa.Credential source → beaconcrypt_public_wrapper.auth.MldsaIdentity
  privateView : ∀ credential, view.mldsa (realize credential) = credential
  operation : ∀ rng, generators.mldsaGenerate generator rng = RustT.lift
    ((fun reply => (match reply.1 with | none => .Err () | some credential => .Ok (realize credential), reply.2)) <$> joint rng)

structure EdContract (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (jointKeys : PqxdhJointIdentity.Primitives)
    (sample : m PqxdhJointIdentity.IdentitySeed) where
  joint : R → m (PqxdhJointIdentity.IdentitySeed × R)
  nativeMarginal : ∀ rng, Prod.fst <$> joint rng = sample
  realize : PqxdhJointIdentity.IdentitySeed → beaconcrypt_crypto.crypto_sign.KeyPair
  privateView : ∀ seed, view.edSecret (realize seed).secret_key = seed
  publicView : ∀ seed, view.edPublic (realize seed).public_key =
    PqxdhRootTableInitialization.rootArray (jointKeys.publicKeys seed).ed25519
  operation : ∀ rng, generators.edGenerate generator rng = RustT.lift
    ((fun reply => (.Ok (realize reply.1), reply.2)) <$> joint rng)

structure KxContract (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (publicKey : PqxdhJointGapDh.ScalarBytes → Std.Array U8 32#usize)
    (sample : m PqxdhJointGapDh.ScalarBytes) where
  joint : R → m (PqxdhJointGapDh.ScalarBytes × R)
  nativeMarginal : ∀ rng, Prod.fst <$> joint rng = sample
  realize : PqxdhJointGapDh.ScalarBytes → beaconcrypt_crypto.crypto_kx.KeyPair
  privateView : ∀ scalar, view.kxSecret (realize scalar).secret_key = scalar
  publicView : ∀ scalar, view.kxPublic (realize scalar).public_key = publicKey scalar
  operation : ∀ rng, crypto.kxGenerate generator rng = RustT.lift
    ((fun reply => (.Ok (realize reply.1), reply.2)) <$> joint rng)

theorem with_inputs (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (sample : m (Option (RegistrationNativeMldsa.Credential source))) (model : MldsaContract generator view sample)
    (identifier : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mldsa : Std.Array U8 1952#usize) (rng : R)
    (getter : crypto.edPublicBytes serverId = pure (view.edPublic serverId)) :
    AdapterBeaconConstructorBody.withInputs generator identifier serverId mldsa rng = (do
      let reply ← RustT.lift (model.joint rng)
      match reply.1 with
      | none => AdapterBeaconConstructorBody.reject reply.2
      | some credential =>
        let binding : pqxdh.ServerBinding := ⟨view.edPublic serverId, identifier⟩
        let pin ← beaconcrypt_public_request.auth.fingerprint_pin (m := RustT m) binding mldsa
        match pin with
        | .None => AdapterBeaconConstructorBody.reject reply.2
        | .Some pin => AdapterBeaconConstructorBody.withKeys generator identifier serverId binding pin (model.realize credential) reply.2) := by
  unfold AdapterBeaconConstructorBody.withInputs
  rw [getter]
  simp only [pure_bind]
  rw [model.operation, lift_map]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨selected, nextRng⟩
  cases selected <;> rfl

omit children in
theorem with_keys (generator : rand_core.TryCryptoRng R Error)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (jointKeys : PqxdhJointIdentity.Primitives)
    (edSample : m PqxdhJointIdentity.IdentitySeed) (ed : EdContract generator view jointKeys edSample)
    (kxPublic : PqxdhJointGapDh.ScalarBytes → Std.Array U8 32#usize)
    (kxSample : m PqxdhJointGapDh.ScalarBytes) (kx : KxContract generator view kxPublic kxSample)
    (identifier : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (binding : pqxdh.ServerBinding) (pin : session.ServerAuthenticationPin)
    (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) (rng : R) :
    AdapterBeaconConstructorBody.withKeys generator identifier serverId binding pin identity rng = (do
      let signing ← RustT.lift (ed.joint rng)
      let control ← AdapterRecordRequestMonad.liftRust (pqxdh.BeaconFresh.new binding)
      let prekey ← RustT.lift (kx.joint signing.2)
      let (kem, nextRng) ← generators.kemGenerate generator prekey.2
      match kem with
      | .Err _ => AdapterBeaconConstructorBody.reject nextRng
      | .Ok kem => pure (.Ok ⟨ed.realize signing.1, identifier, .Fresh control (kx.realize prekey.1) kem, serverId, ⟨identity, pin⟩⟩, nextRng)) := by
  unfold AdapterBeaconConstructorBody.withKeys
  rw [ed.operation, lift_map]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨seed, afterSigning⟩
  apply bind_congr
  intro control
  rw [kx.operation, lift_map]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨scalar, afterPrekey⟩
  rfl

end BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration.with_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration.with_inputs

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration.with_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorGeneration.with_keys

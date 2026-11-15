-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleBody
/-! Actual source bundle serialization and object installation compose with the complete stateful publication program. Ordered immutable field-getter contracts and actual Ed/hash/ML leaf contracts are explicit; the encoder is the actual source child effect in the same monad, so allocation failure and every reached poststate are retained. Fresh key generation and the relation to native owner storage are separate correspondences. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundlePublication
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
open AdapterPublicInitPublication
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

omit localOps crypto children [Monad m] [LawfulMonad m] in
def install {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (rng : R) (published : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :
    RustM (core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon × R) :=
  match published with
  | .fail error => .fail error
  | .div => .div
  | .ok (.Err _) => .ok (.None, self, rng)
  | .ok (.Ok finished) => .ok (.Some finished.encoded,
      { self with state := .InitSent finished.pending prekey oneTime kem }, rng)

omit platform localOps crypto in
private theorem publish_ready {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (rng : R) (control : pqxdh.BeaconFresh) (selected : core.option.Option registration.BeaconInitReady) :
    (AdapterPublicBundleBody.publish (m := m) self prekey oneTime kem rng selected).run = (do
      let published ← publication control (fun view => (children.encodeInit (AdapterPublicBundleBody.packet view)).run)
        (pure selected : RustT m _)
      pure (install self prekey oneTime kem rng published)) := by
  cases selected with
  | none => simp only [AdapterPublicBundleBody.publish, RustT.run_pure, publication, pure_bind, install]
  | some ready =>
      simp only [AdapterPublicBundleBody.publish, RustT.run_bind, RustT.run_liftRust,
        publication, RustT.run_pure, pure_bind, RegistrationNativePlatformBeaconPublication.ready]
      cases message : ready.message with
      | fail error | div => simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith, install]
      | ok view =>
          simp only [RegistrationNativePlatformBeaconPublication.continueWith, bind_assoc, pure_bind]
          apply bind_congr
          intro encoded
          cases encoded with
          | fail error | div => rfl
          | ok buffer =>
              simp only [bind_tc_ok]
              cases published : ready.publish buffer with
              | fail error | div => rfl
              | ok result => cases result with
                | Err previous => rfl
                | Ok finished => simp only [RustT.run_pure, RustT.run_bind,
                    RustT.run_liftRust, registration.PublishedBeaconInit.into_parts, pure_bind, install]

omit platform localOps crypto in
theorem publish {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (rng : R) (control : pqxdh.BeaconFresh)
    (work : RustT m (core.option.Option registration.BeaconInitReady)) :
    (do let selected ← work; AdapterPublicBundleBody.publish self prekey oneTime kem rng selected).run = (do
      let published ← publication control (fun view => (children.encodeInit (AdapterPublicBundleBody.packet view)).run) work
      pure (install self prekey oneTime kem rng published)) := by
  simp only [RustT.run_bind, publication, bind_assoc]
  apply bind_congr
  intro selected
  cases selected with
  | fail error | div => simp only [pure_bind, install]
  | ok selected =>
      have result := publish_ready (m := m) self prekey oneTime kem rng control selected
      simpa only [publication, RustT.run_pure, pure_bind] using result

omit platform localOps in
theorem withKeys {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (control : pqxdh.BeaconFresh)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R)
    (prekeyPublic oneTimePublic identity : Std.Array U8 32#usize)
    (kemPublic : Std.Array U8 1184#usize)
    (edSign : Slice U8 → m (core.result.Result (alloc.vec.Vec U8) primitive.Error))
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (prekeyGetter : (crypto.kxPublicBytes prekey.public_key).run = pure (.ok prekeyPublic))
    (oneTimeGetter : (crypto.kxPublicBytes oneTime.public_key).run = pure (.ok oneTimePublic))
    (kemGetter : (crypto.kemPublicBytes kem.public_key).run = pure (.ok kemPublic))
    (identityGetter : (crypto.edPublicBytes self.identity_key.public_key).run = pure (.ok identity))
    (edSignLeaf : ∀ message, (crypto.edSign message self.identity_key.secret_key).run = RustM.ok <$> edSign message)
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request)
 :
    (AdapterPublicBundleBody.withKeys (m := m) self control prekey oneTime kem rng).run = (do
      let published ← RegistrationNativePlatformBeaconPublication.begin (outgoing hash (edMethod identity edSign))
        (fun view => (children.encodeInit (AdapterPublicBundleBody.packet view)).run)
        control ⟨identity, prekeyPublic, kemPublic⟩ ⟨oneTimePublic⟩ self.authentication.server_pin
      pure (install self prekey oneTime kem rng published)) := by
  have getters : AdapterPublicBundleBody.withKeys (m := m) self control prekey oneTime kem rng = (do
      let effect ← liftRust (registration.begin_beacon_init control ⟨identity, prekeyPublic, kemPublic⟩
        ⟨oneTimePublic⟩ self.authentication.server_pin)
      let ready ← beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) effect self
      AdapterPublicBundleBody.publish self prekey oneTime kem rng ready) := by
    apply RustT.ext
    simp only [AdapterPublicBundleBody.withKeys, RustT.run_bind, prekeyGetter, oneTimeGetter,
      kemGetter, identityGetter, pure_bind]
  rw [getters, ← bind_assoc, publish]
  rw [AdapterPublicInitEdPublication.begin_source self control _ _ _ identity edSign hash _
    identityGetter edSignLeaf hashLeaf]
end BeaconcryptCore.Refinement.AdapterPublicBundlePublication

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundlePublication.publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundlePublication.publish

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundlePublication.withKeys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundlePublication.withKeys

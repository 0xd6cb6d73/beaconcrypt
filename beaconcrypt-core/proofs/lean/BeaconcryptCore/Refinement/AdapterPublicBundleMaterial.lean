-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundlePublication
import BeaconcryptCore.Refinement.AdapterPublicAgreementGeneration
/-! Actual source bundle generation and publication use the native owner inputs under individual opaque-object public-view and primitive contracts. The Fresh endpoint retains generated private key objects and updated caller RNG. Existing stored coins require their actual public-key view; it is not inferred from public equality or selected from another owner. Source serialization and every shared-state failure remain inside the common monad. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundleMaterial
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source} {KemSK : Type}

/-- Read-only public views of the individual opaque cryptographic objects. -/
structure Getters (view : AdapterPublicWrapperState.MaterialView source KemSK) : Prop where
  ed : ∀ key, (crypto.edPublicBytes key).run = pure (.ok (view.edPublic key))
  kx : ∀ key, (crypto.kxPublicBytes key).run = pure (.ok (view.kxPublic key))
  kem : ∀ key, (crypto.kemPublicBytes key).run = pure (.ok (RegistrationNativeBeaconFrontend.pqArray (view.kemPublic key)))

/-- Per-primitive functional effects, without a source controller or security conclusion premise. -/
structure PublicationLeaves {self : beaconcrypt_public_wrapper.beacon.Beacon} where
  edSign : Slice U8 → m (core.result.Result (alloc.vec.Vec U8) ed.Error)
  hash : registration.HashRequest → m CtxRomAuth.CtxDigest
  edLaw : ∀ message, (crypto.edSign message self.identity_key.secret_key).run = RustM.ok <$> edSign message
  hashLaw : ∀ request, (children.executeHash request).run =
    (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request

def withMaterial (joint : PqxdhJointIdentity.Primitives) (dh : PqxdhJointGapDh.DhInterface joint)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (leaves : PublicationLeaves (m := m) (self := self)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    {R : Type} (rng : R) : m (RustM (core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon × R)) := (do
      let published ← RegistrationNativePlatformBeaconPublication.begin
        (AdapterPublicInitPublication.outgoing (PublicationLeaves.hash (self := self) leaves)
          (AdapterPublicInitPublication.edMethod (PqxdhRootTableInitialization.rootArray (joint.publicKeys owner.identitySeed).ed25519) (PublicationLeaves.edSign (self := self) leaves)))
        (fun signed => (children.encodeInit (AdapterPublicBundleBody.packet signed)).run)
        ⟨owner.pin.binding⟩
        ⟨PqxdhRootTableInitialization.rootArray (joint.publicKeys owner.identitySeed).ed25519, owner.prekeyPublic, RegistrationNativeBeaconFrontend.pqArray owner.kemPublic⟩
        ⟨PqxdhRootTableInitialization.rootArray (dh.publicKey scalar)⟩ owner.pin
      pure (AdapterPublicBundlePublication.install self prekey oneTime kem rng published))

omit platform localOps in
theorem withKeys (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : Getters (m := m) view) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (dh : PqxdhJointGapDh.DhInterface joint)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (leaves : PublicationLeaves (m := m) (self := self))
    (control : pqxdh.BeaconFresh) (controlView : control.expected_server_binding = owner.pin.binding)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekeyView : AdapterPublicWrapperState.KxPair view prekey owner.prekeyScalar owner.prekeyPublic)
    (oneTimeView : AdapterPublicWrapperState.KxPair view oneTime scalar (PqxdhRootTableInitialization.rootArray (dh.publicKey scalar)))
    (kemView : AdapterPublicWrapperState.KemPair view pool kem owner.kemHandle owner.kemPublic)
    {R : Type} (rng : R) :
    (AdapterPublicBundleBody.withKeys (m := m) self control prekey oneTime kem rng).run = withMaterial joint dh self owner leaves scalar prekey oneTime kem rng := by
  unfold withMaterial
  have controlSame : control = ⟨owner.pin.binding⟩ := by
    cases control
    exact congrArg pqxdh.BeaconFresh.mk controlView
  rw [AdapterPublicBundlePublication.withKeys self control prekey oneTime kem rng
    owner.prekeyPublic (PqxdhRootTableInitialization.rootArray (dh.publicKey scalar))
    (PqxdhRootTableInitialization.rootArray (joint.publicKeys owner.identitySeed).ed25519)
    (RegistrationNativeBeaconFrontend.pqArray owner.kemPublic)
    (PublicationLeaves.edSign (self := self) leaves) (PublicationLeaves.hash (self := self) leaves)]
  · rw [controlSame, related.pin]
  · simpa only [prekeyView.2] using getters.kx prekey.public_key
  · simpa only [oneTimeView.2] using getters.kx oneTime.public_key
  · simpa only [kemView.1] using getters.kem kem.public_key
  · simpa only [related.identityPublic] using getters.ed self.identity_key.public_key
  · exact (PublicationLeaves.edLaw (self := self) leaves)
  · exact (PublicationLeaves.hashLaw (self := self) leaves)

omit platform localOps in
theorem fresh (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : Getters (m := m) view) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (dh : PqxdhJointGapDh.DhInterface joint)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (leaves : PublicationLeaves (m := m) (self := self))
    (control : pqxdh.BeaconFresh) (controlView : control.expected_server_binding = owner.pin.binding)
    (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (prekeyView : AdapterPublicWrapperState.KxPair view prekey owner.prekeyScalar owner.prekeyPublic)
    (kemView : AdapterPublicWrapperState.KemPair view pool kem owner.kemHandle owner.kemPublic)
    {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (sample : m PqxdhJointGapDh.ScalarBytes)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (dh.publicKey scalar)) sample)
    (state : self.state = .Fresh control prekey kem) :
    (beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT m) generator self rng).run = (do
      let scalar ← sample
      let realized := generation.realize scalar rng
      withMaterial joint dh self owner leaves scalar prekey realized.1 kem realized.2) := by
  rw [AdapterPublicBundleBody.fresh generator self rng control prekey kem state]
  simp only [AdapterPublicBundleBody.generated, AdapterPublicWrapperRustT.RustT.run_bind,
    generation.operation, RustT.run_lift, bind_map_left]
  apply bind_congr
  intro scalar
  apply withKeys view getters joint pool dh self owner world related leaves control controlView prekey
    (generation.realize scalar rng).1 kem scalar prekeyView _ kemView (generation.realize scalar rng).2
  exact ⟨generation.privateView scalar rng, generation.publicView scalar rng⟩


omit platform localOps in
theorem fresh_related (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : Getters (m := m) view) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (dh : PqxdhJointGapDh.DhInterface joint)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (leaves : PublicationLeaves (m := m) (self := self))
    (control : pqxdh.BeaconFresh)
    (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (sample : m PqxdhJointGapDh.ScalarBytes)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (dh.publicKey scalar)) sample)
    (state : self.state = .Fresh control prekey kem) (ownerPhase : owner.phase = .fresh) :
    (beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT m) generator self rng).run = (do
      let scalar ← sample
      let realized := generation.realize scalar rng
      withMaterial joint dh self owner leaves scalar prekey realized.1 kem realized.2) := by
  have phase := related.phase
  simp only [state, ownerPhase, AdapterPublicWrapperState.Phase] at phase
  exact fresh view getters joint pool dh self owner world related leaves control phase.1 prekey kem
    phase.2.1 phase.2.2.1 generator rng sample generation state

omit platform localOps in
theorem with_coins_related (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : Getters (m := m) view) (joint : PqxdhJointIdentity.Primitives)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (dh : PqxdhJointGapDh.DhInterface joint)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (leaves : PublicationLeaves (m := m) (self := self))
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (state : self.state = .FreshWithCoins control prekey oneTime kem) (ownerPhase : owner.phase = .freshWithCoins scalar)
    (publicView : view.kxPublic oneTime.public_key = PqxdhRootTableInitialization.rootArray (dh.publicKey scalar)) :
    (beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT m) generator self rng).run =
      withMaterial joint dh self owner leaves scalar prekey oneTime kem rng := by
  have phase := related.phase
  simp only [state, ownerPhase, AdapterPublicWrapperState.Phase] at phase
  rw [AdapterPublicBundleBody.with_coins generator self rng control prekey oneTime kem state]
  exact withKeys view getters joint pool dh self owner world related leaves control phase.1 prekey oneTime kem
    scalar phase.2.1 ⟨phase.2.2.1, publicView⟩ phase.2.2.2.1 rng

omit platform localOps crypto children [Monad m] [LawfulMonad m] in
theorem installed_related (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint pool self owner world)
    (identifier : AdapterPublicWrapperState.currentId owner = owner.pin.binding.identity_key_id)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekeyView : AdapterPublicWrapperState.KxPair view prekey owner.prekeyScalar owner.prekeyPublic)
    (oneTimeView : view.kxSecret oneTime.secret_key = scalar)
    (kemView : AdapterPublicWrapperState.KemPair view pool kem owner.kemHandle owner.kemPublic)
    (finished : registration.PublishedBeaconInit (alloc.vec.Vec U8)) :
    AdapterPublicWrapperState.Beacon view joint pool
      { self with state := .InitSent finished.pending prekey oneTime kem }
      { owner with phase := .initSent finished.pending scalar } (some (.inactive .initSent)) := by
  exact AdapterPublicWrapperState.pending view joint pool self owner world related identifier
    finished.pending prekey oneTime kem scalar prekeyView oneTimeView kemView

end BeaconcryptCore.Refinement.AdapterPublicBundleMaterial

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.withKeys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.withKeys

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.fresh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.fresh_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.fresh_related

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.with_coins_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.with_coins_related

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.installed_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleMaterial.installed_related

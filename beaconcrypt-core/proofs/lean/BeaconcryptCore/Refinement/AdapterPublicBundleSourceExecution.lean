-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundlePrimitives
import BeaconcryptCore.Refinement.AdapterPublicWrapperCutChildren
/-! The complete extracted SDK Fresh and FreshWithCoins bundle calls are projections of the actual native cryptographic publication and literal extracted writer on one common state. Per-opaque getter, Ed/ML signing and key-generation contracts are explicit. Generated private objects, the updated caller RNG and the complete returned source Self are retained on every result; only the private last-hash annotation is erased. Native lifecycle finalization is composed separately. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution
open BeaconcryptCore.Computational
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformCutErasure (liftWorld)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "CutM" => StateT (RegistrationNativePlatformCutJournal.State Native) m
variable [localOps : LocalOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) m))]
variable [crypto : CryptoOperations (RustT (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) m))]
variable (coins : QueryImpl unifSpec m) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
variable (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (failure : ed.Error)

noncomputable def authentication (other : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec CutM) :
    QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec CutM
  | .hash request => (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$>
      RegistrationNativePlatformCutJournal.hash (AdapterPublicBundlePrimitives.signing coins setup checks representation created writer index owner) request
  | query => other query

variable (other : QueryImpl AdapterPublicWrapperChildren.AuthenticationSpec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) m))
variable (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT (RegistrationNativePlatformCutJournal.State (RegistrationNativeExperiment.State n KemSK source)) m))
@[instance_reducible] noncomputable def children : ChildOperations (RustT CutM) := AdapterPublicWrapperChildren.children
  (authentication coins setup checks representation created writer index owner other) recording
  (AdapterPublicWrapperCutChildren.lifted (fun query => (StateT.lift (writer query) : StateT Native m _)))

structure Leaves (self : beaconcrypt_public_wrapper.beacon.Beacon) : Prop where
  edLaw : ∀ message, (crypto.edSign message self.identity_key.secret_key).run = RustM.ok <$>
    liftWorld (AdapterPublicBundlePrimitives.sign coins setup checks representation created writer index owner failure message)

noncomputable def leaves (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (law : Leaves (n := n) coins setup checks representation created writer index owner failure self) :
    letI : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
    AdapterPublicBundleMaterial.PublicationLeaves (m := CutM) (self := self) := by
  let : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
  exact {
    edSign message := liftWorld (AdapterPublicBundlePrimitives.sign coins setup checks representation created writer index owner failure message)
    hash := RegistrationNativePlatformCutJournal.hash (AdapterPublicBundlePrimitives.signing coins setup checks representation created writer index owner)
    edLaw := Leaves.edLaw (self := self) law
    hashLaw := fun _ => rfl }

omit material platform localOps crypto in
theorem encoder_source (signed : registration.InitView) :
    letI : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
    (ChildOperations.encodeInit (m := RustT CutM) (AdapterPublicBundleBody.packet signed)).run =
      liftWorld (RegistrationNativeBundleInterpretation.encoder (n := n) (source := source) coins setup checks representation created writer signed) := by
  let : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
  rw [AdapterPublicWrapperCutChildren.init, RegistrationNativeBundleInterpretation.encoder_source]
  congr 1
  exact simulateQ_liftTarget writer _

noncomputable def tree (scalar : PqxdhJointGapDh.ScalarBytes) :
    RegistrationNativePlatformExperiment.M n KemSK source m (RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformFrontend.interpret
          (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
          (RegistrationNativePlatformBeaconPublication.begin
            (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
              (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
            (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩
            (RegistrationNativeBeaconFrontend.inputs setup owner)
            ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin)

omit platform localOps in
theorem with_material {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (law : Leaves (n := n) coins setup checks representation created writer index owner failure self)
    (scalar : PqxdhJointGapDh.ScalarBytes) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R)
    (before : RegistrationNativePlatformCutJournal.State Native) :
    letI : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
    Prod.map id Prod.fst <$>
      (AdapterPublicBundleMaterial.withMaterial setup.joint setup.dh self owner
        (leaves coins setup checks representation created writer index owner failure other recording self law)
        scalar prekey oneTime kem rng).run before =
      (fun result => (AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1, result.2)) <$>
        (tree coins setup checks representation created writer index owner scalar).run before.1 := by
  let : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
  unfold tree AdapterPublicBundleMaterial.withMaterial
  simp only [bind_pure_comp, StateT.run_map, Functor.map_map]
  have encoders : (fun signed => (ChildOperations.encodeInit (m := RustT CutM) (AdapterPublicBundleBody.packet signed)).run) =
      (fun signed => liftWorld (RegistrationNativeBundleInterpretation.encoder (n := n) (source := source) coins setup checks representation created writer signed)) := by
    funext signed
    exact encoder_source coins setup checks representation created writer index owner other recording signed
  rw [encoders]
  have actual := congrArg (fun distribution => (fun result =>
    (AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1, result.2)) <$> distribution)
    (AdapterPublicBundlePrimitives.publication coins setup checks representation created writer index owner failure
      ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin before)
  simpa only [leaves, AdapterPublicBundleNative.outgoing, RegistrationNativeBeaconFrontend.inputs, Functor.map_map, Prod.map, id_eq] using actual


omit platform localOps in
theorem with_keys {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view setup.joint pool self owner world)
    (law : Leaves (n := n) coins setup checks representation created writer index owner failure self)
    (control : pqxdh.BeaconFresh) (controlView : control.expected_server_binding = owner.pin.binding)
    (scalar : PqxdhJointGapDh.ScalarBytes) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R)
    (prekeyView : AdapterPublicWrapperState.KxPair view prekey owner.prekeyScalar owner.prekeyPublic)
    (oneTimeView : AdapterPublicWrapperState.KxPair view oneTime scalar (PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)))
    (kemView : AdapterPublicWrapperState.KemPair view pool kem owner.kemHandle owner.kemPublic)
    (before : RegistrationNativePlatformCutJournal.State Native) :
    letI : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
    Prod.map id Prod.fst <$> (AdapterPublicBundleBody.withKeys (m := CutM) self control prekey oneTime kem rng).run.run before =
      (fun result => (AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1, result.2)) <$>
        (tree coins setup checks representation created writer index owner scalar).run before.1 := by
  let : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
  rw [AdapterPublicBundleMaterial.withKeys view getters setup.joint pool setup.dh self owner world related
    (leaves coins setup checks representation created writer index owner failure other recording self law)
    control controlView prekey oneTime kem scalar prekeyView oneTimeView kemView rng]
  exact with_material coins setup checks representation created writer index owner failure other recording self law scalar prekey oneTime kem rng before

omit platform localOps in
theorem with_coins {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view setup.joint pool self owner world)
    (law : Leaves (n := n) coins setup checks representation created writer index owner failure self)
    (control : pqxdh.BeaconFresh) (scalar : PqxdhJointGapDh.ScalarBytes)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (stored : self.state = .FreshWithCoins control prekey oneTime kem)
    (phase : owner.phase = .freshWithCoins scalar)
    (publicView : view.kxPublic oneTime.public_key = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
    (before : RegistrationNativePlatformCutJournal.State Native) :
    letI : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
    Prod.map id Prod.fst <$>
      ((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT CutM) generator self rng).run).run before =
      (fun result => (AdapterPublicBundlePublication.install self prekey oneTime kem rng result.1, result.2)) <$>
        (tree coins setup checks representation created writer index owner scalar).run before.1 := by
  let : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
  rw [AdapterPublicBundleMaterial.with_coins_related view getters setup.joint pool setup.dh self owner world related
    (leaves coins setup checks representation created writer index owner failure other recording self law)
    control scalar prekey oneTime kem generator rng stored phase publicView]
  exact with_material coins setup checks representation created writer index owner failure other recording self law scalar prekey oneTime kem rng before


noncomputable def sample : RegistrationNativePlatformExperiment.M n KemSK source m PqxdhJointGapDh.ScalarBytes :=
  RegistrationNativePlatformFrontend.interpret
    (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
    (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
      (RegistrationNativeBeaconFrontend.sample PqxdhJointGapDh.sampleScalar))

omit platform localOps in
theorem fresh {R Error : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicBundleMaterial.Getters (m := CutM) view)
    (pool : PqxdhLiveKemBirth.Pool KemSK) (world : Option PqxdhRecordLiftBeacon.Phase)
    (related : AdapterPublicWrapperState.Beacon view setup.joint pool self owner world)
    (law : Leaves (n := n) coins setup checks representation created writer index owner failure self)
    (control : pqxdh.BeaconFresh) (prekey : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (generator : rand_core.TryCryptoRng R Error) (rng : R)
    (generation : AdapterPublicAgreementGeneration.Contract generator view
      (fun scalar => PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar))
      (liftWorld (sample (n := n) (source := source) coins setup checks representation created writer)))
    (stored : self.state = .Fresh control prekey kem) (phase : owner.phase = .fresh)
    (before : RegistrationNativePlatformCutJournal.State Native) :
    letI : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
    Prod.map id Prod.fst <$>
      ((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT CutM) generator self rng).run).run before = (do
      let drawn ← (sample coins setup checks representation created writer).run before.1
      let realized := generation.realize drawn.1 rng
      (fun result => (AdapterPublicBundlePublication.install self prekey realized.1 kem realized.2 result.1, result.2)) <$>
        (tree coins setup checks representation created writer index owner drawn.1).run drawn.2) := by
  let : ChildOperations (RustT CutM) := children coins setup checks representation created writer index owner other recording
  rw [AdapterPublicBundleMaterial.fresh_related view getters setup.joint pool setup.dh self owner world related
    (leaves coins setup checks representation created writer index owner failure other recording self law)
    control prekey kem generator rng (liftWorld (sample coins setup checks representation created writer)) generation stored phase]
  change Prod.map id Prod.fst <$> ((do
    let scalar ← liftWorld (sample coins setup checks representation created writer)
    AdapterPublicBundleMaterial.withMaterial setup.joint setup.dh self owner
      (leaves coins setup checks representation created writer index owner failure other recording self law)
      scalar prekey (generation.realize scalar rng).1 kem (generation.realize scalar rng).2 : CutM _).run before) = _
  rw [StateT.run_bind]
  simp only [RegistrationNativePlatformCutErasure.liftWorld, StateT.run, map_bind, bind_map_left]
  apply bind_congr
  intro drawn
  exact with_material coins setup checks representation created writer index owner failure other recording self law
    drawn.1 prekey (generation.realize drawn.1 rng).1 kem (generation.realize drawn.1 rng).2 (drawn.2, before.2)

end BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.encoder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.encoder_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.with_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.with_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.with_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.with_keys

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.with_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.with_coins

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleSourceExecution.fresh

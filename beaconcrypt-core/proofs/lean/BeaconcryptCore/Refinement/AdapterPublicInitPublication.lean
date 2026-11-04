-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicInitReady
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
/-! Actual source Ed/ML reply conversion and the public Init driver's fingerprint/hash/ML stages fold to the stateful native publication stages. Primitive getter/sign/hash leaf contracts are explicit; every source serializer failure and common monadic poststate is retained. Whole Ed-stage and beginning-of-bundle folds are separate continuation work. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicInitPublication
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m] {Encoded : Type}
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

def borrowed (reply : core.option.Option (alloc.vec.Vec U8)) : core.option.Option (Slice U8) :=
  match reply with
  | .None => .None
  | .Some bytes => .Some ⟨bytes.val, bytes.property⟩

omit material platform primitive localOps crypto children [LawfulMonad m] in
theorem borrowed_source (reply : core.option.Option (alloc.vec.Vec U8)) :
    core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) reply = .ok (borrowed reply) := by
  cases reply <;> rfl

def resultOption (reply : core.result.Result (alloc.vec.Vec U8) primitive.Error) :
    core.option.Option (alloc.vec.Vec U8) :=
  match reply with
  | .Ok value => .Some value
  | .Err _ => .None

def edMethod (publicKey : Std.Array U8 32#usize)
    (sign : Slice U8 → m (core.result.Result (alloc.vec.Vec U8) primitive.Error))
    (request : registration.Ed25519SigningRequest) : m RegistrationSigningShared.SignReply :=
  if decide (publicKey.val = request.public_key.val) then
    (fun reply => borrowed (resultOption reply)) <$> sign request.message
  else pure .None

omit platform localOps children in
theorem ed_leaf (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (publicKey : Std.Array U8 32#usize)
    (sign : Slice U8 → m (core.result.Result (alloc.vec.Vec U8) primitive.Error))
    (getter : (crypto.edPublicBytes beacon.identity_key.public_key).run = pure (.ok publicKey))
    (signLeaf : ∀ message, (crypto.edSign message beacon.identity_key.secret_key).run = RustM.ok <$> sign message)
    (request : registration.Ed25519SigningRequest) :
    (AdapterPublicInitReady.ed (m := m) beacon request).run = RustM.ok <$> edMethod publicKey sign request := by
  rw [AdapterPublicInitReady.ed_run beacon request publicKey getter]
  unfold edMethod
  split
  · rw [signLeaf]
    simp only [bind_pure_comp, Functor.map_map]
    apply congrArg (fun function => function <$> sign request.message)
    funext reply
    cases reply <;> rfl
  · simp only [map_pure]


def outgoing (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → m (core.option.Option (alloc.vec.Vec U8))) (edMethod : registration.Ed25519SigningRequest → m RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec m
  | .inl (.hash request) => hash request
  | .inl (.sign request _ _) => borrowed <$> sign request
  | .inr request => edMethod request

def publication (control : pqxdh.BeaconFresh)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (work : RustT m (core.option.Option registration.BeaconInitReady)) :
    m (RustM (RegistrationBeaconInitExecutor.Result Encoded)) := do
  let reply ← work.run
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok (.Err control))
  | .ok (.Some ready) => RegistrationNativePlatformBeaconPublication.ready encode ready

omit material platform primitive localOps crypto children in
theorem publication_step (control : pqxdh.BeaconFresh)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (body : registration.BeaconInitEffect → RustT m
      (ControlFlow registration.BeaconInitEffect (core.option.Option registration.BeaconInitReady)))
    (fuel : Nat) (effect : registration.BeaconInitEffect) :
    publication control encode (AdapterPublicWrapperLiftFunction.loopFuel (fuel + 1) body effect) = (do
      let reply ← (body effect).run
      match reply with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.cont next) => publication control encode (AdapterPublicWrapperLiftFunction.loopFuel fuel body next)
      | .ok (.done value) => publication control encode (pure value)) := by
  rw [AdapterPublicWrapperLiftFunction.loopFuel]
  simp only [publication, RustT.run_bind, bind_assoc]
  apply bind_congr
  intro reply
  cases reply with
  | fail error | div => simp only [pure_bind]
  | ok decision => cases decision with
    | done value => simp only [RustT.run_pure, pure_bind]
    | cont next => rfl


omit material platform primitive localOps crypto children [Monad m] [LawfulMonad m] in
theorem signing_shapes (pending : registration.BeaconMldsaSigning)
    (signature : core.option.Option (Slice U8)) :
    ∃ effect, pending.resume signature = .ok effect ∧
      (effect = .Rejected pending.state.original_control ∨ ∃ ready, effect = .Ready ready) := by
  cases signature with
  | none => exact ⟨_, rfl, .inl rfl⟩
  | some signature =>
      obtain ⟨effect, resumed, shapes⟩ := RegistrationSigningContinuations.beacon_mldsa_signature_exact pending signature
      refine ⟨effect, resumed, ?_⟩
      cases effect with
      | Rejected original => exact .inl (congrArg registration.BeaconInitEffect.Rejected shapes.1)
      | Ready ready => exact .inr ⟨ready, rfl⟩
      | _ => cases shapes

theorem signing_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconMldsaSigning)
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → m (core.option.Option (alloc.vec.Vec U8)))
    (edMethod : registration.Ed25519SigningRequest → m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (signLeaf : ∀ request, (localOps.auth_MldsaIdentity_sign_requested beacon.authentication.identity request).run =
      RustM.ok <$> sign request) :
    publication pending.state.original_control encode
      (beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) (.MldsaSigningRequested pending) beacon) =
    RegistrationNativePlatformBeaconPublication.fromSigning (outgoing hash sign edMethod) encode payload digest pending := by
  rw [AdapterPublicInitReady.loop_source]
  simp only [AdapterPublicInitSourceLoop.rank, AdapterPublicWrapperLiftFunction.loopFuel,
    AdapterPublicInitReady.step, publication, RustT.run_bind, RustT.run_liftRust, RustT.run_pure,
    RegistrationNativePlatformBeaconPublication.fromSigning]
  cases requested : pending.request with
  | fail error | div => simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith]
  | ok request =>
      simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith,
        signLeaf, outgoing, bind_map_left, bind_assoc]
      apply bind_congr
      intro signature
      simp only [borrowed_source]
      obtain ⟨effect, resumed, shapes⟩ := signing_shapes pending (borrowed signature)
      rw [resumed]
      rcases shapes with rfl | ⟨ready, rfl⟩
      all_goals simp only [pure_bind, RustT.run_pure]


theorem hash_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconInitHash)
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → m (core.option.Option (alloc.vec.Vec U8)))
    (edMethod : registration.Ed25519SigningRequest → m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request)
    (signLeaf : ∀ request, (localOps.auth_MldsaIdentity_sign_requested beacon.authentication.identity request).run =
      RustM.ok <$> sign request) :
    publication pending.state.original_control encode
      (beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) (.HashRequested pending) beacon) =
    RegistrationNativePlatformBeaconPublication.fromHash (outgoing hash sign edMethod) encode pending := by
  rw [AdapterPublicInitReady.loop_source]
  simp only [AdapterPublicInitSourceLoop.rank, AdapterPublicWrapperLiftFunction.loopFuel,
    AdapterPublicInitReady.step, publication, RustT.run_bind, RustT.run_liftRust, RustT.run_pure,
    RegistrationNativePlatformBeaconPublication.fromHash]
  cases requested : pending.request with
  | fail error | div => simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith]
  | ok request =>
      simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith,
        hashLeaf, outgoing, bind_map_left, bind_assoc]
      apply bind_congr
      intro digest
      obtain ⟨signing, resumed, stateSame, _fingerprint, _digest, _request⟩ :=
        RegistrationSigningContinuations.beacon_init_hash_some_exact pending (RegistrationAuthenticationShared.digestArray digest)
      simp only [resumed]
      have continued := signing_source beacon signing hash sign edMethod encode
        ⟨.beacon, RegistrationInputs.hashBytes request⟩ digest signLeaf
      rw [AdapterPublicInitReady.loop_source] at continued
      simpa only [AdapterPublicInitSourceLoop.rank, AdapterPublicWrapperLiftFunction.loopFuel,
        AdapterPublicInitReady.step, publication, RustT.run_bind, RustT.run_liftRust, RustT.run_pure,
        stateSame, pure_bind] using continued


theorem fingerprint_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconFingerprint)
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (sign : registration.MldsaSigningRequest → m (core.option.Option (alloc.vec.Vec U8)))
    (edMethod : registration.Ed25519SigningRequest → m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → m (RustM (core.option.Option Encoded)))
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request)
    (signLeaf : ∀ request, (localOps.auth_MldsaIdentity_sign_requested beacon.authentication.identity request).run =
      RustM.ok <$> sign request) :
    publication pending.state.original_control encode
      (beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) (.FingerprintRequested pending) beacon) =
    RegistrationNativePlatformBeaconPublication.fromFingerprint (outgoing hash sign edMethod) encode pending := by
  rw [AdapterPublicInitReady.loop_source]
  simp only [AdapterPublicInitSourceLoop.rank, AdapterPublicWrapperLiftFunction.loopFuel,
    AdapterPublicInitReady.step, publication, RustT.run_bind, RustT.run_liftRust, RustT.run_pure,
    RegistrationNativePlatformBeaconPublication.fromFingerprint]
  cases requested : pending.request with
  | fail error | div => simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith]
  | ok request =>
      simp only [pure_bind, RegistrationNativePlatformBeaconPublication.continueWith,
        hashLeaf, outgoing, bind_map_left, bind_assoc]
      apply bind_congr
      intro digest
      obtain ⟨hashing, resumed, stateSame, _fingerprint, _request⟩ :=
        RegistrationSigningContinuations.beacon_fingerprint_some_exact pending (RegistrationAuthenticationShared.digestArray digest)
      simp only [resumed]
      have continued := hash_source beacon hashing hash sign edMethod encode hashLeaf signLeaf
      rw [AdapterPublicInitReady.loop_source] at continued
      simpa only [AdapterPublicInitSourceLoop.rank, AdapterPublicWrapperLiftFunction.loopFuel,
        AdapterPublicInitReady.step, publication, RustT.run_bind, RustT.run_liftRust, RustT.run_pure,
        stateSame, pure_bind] using continued

end BeaconcryptCore.Refinement.AdapterPublicInitPublication

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.borrowed_source' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.borrowed_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.ed_leaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.ed_leaf

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.publication_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.publication_step

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.signing_shapes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.signing_shapes

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.signing_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.signing_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.hash_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.fingerprint_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.fingerprint_source

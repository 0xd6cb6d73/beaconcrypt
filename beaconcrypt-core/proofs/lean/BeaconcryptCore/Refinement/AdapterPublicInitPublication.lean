-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicInitReady
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
/-! Actual source Ed reply conversion and the public Init driver's final request-hash stage fold to the stateful native publication stages. Primitive getter/sign/hash leaf contracts are explicit; every source serializer failure and common monadic poststate is retained. Whole Ed-stage and beginning-of-bundle folds are separate continuation work. -/
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
    (edMethod : registration.Ed25519SigningRequest → m RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec m
  | .inl (.hash request) => hash request
  | .inl (.sign _ _ _) => pure .None
  | .inr request => edMethod request

def publication (control : pqxdh.BeaconFresh)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
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
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
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



omit platform localOps in
theorem hash_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (pending : registration.BeaconInitHash)
    (hash : registration.HashRequest → m CtxRomAuth.CtxDigest)
    (edMethod : registration.Ed25519SigningRequest → m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (hashLeaf : ∀ request, (children.executeHash request).run =
      (fun digest => .ok (some (RegistrationAuthenticationShared.digestArray digest))) <$> hash request) :
    publication pending.state.original_control encode
      (beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) (.HashRequested pending) beacon) =
    RegistrationNativePlatformBeaconPublication.fromHash (outgoing hash edMethod) encode pending := by
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
      obtain ⟨ready, resumed, stateSame, _digest, _message⟩ :=
        RegistrationSigningContinuations.beacon_init_hash_some_exact pending (RegistrationAuthenticationShared.digestArray digest)
      simp only [resumed, pure_bind, RustT.run_pure, RegistrationNativePlatformBeaconPublication.ready]

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

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitPublication.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitPublication.hash_source

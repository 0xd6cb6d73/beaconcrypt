-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterPublicWrapperRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
import BeaconcryptCore.Refinement.PqxdhSurface
/-! The actual source Init-ready body factors into its literal Ed equality/signing leaf and pure protocol resumes. The equality gate and exact captured signing secret are derived from the source, and Rust failure/divergence and all shared poststates are retained. This component does not assume equality of a complete wrapper or native experiment. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicInitReady
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

omit material platform primitive [LawfulMonad m] localOps crypto children in
private theorem branch_bind {A B : Type} (decision : Bool) (yes no : RustT m A) (next : A → RustT m B) :
    ((if decision then yes else no) >>= next) =
      if decision then (yes >>= next) else (no >>= next) := by
  cases decision <;> rfl

def ed (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (request : registration.Ed25519SigningRequest) : RustT m (core.option.Option (Slice U8)) := do
  let publicKey ← beaconcrypt_public_request.beacon.Beacon.identity_pk beacon
  let bytes ← crypto.edPublicBytes publicKey
  let matched ← liftRust (core.Array.Insts.CoreCmpPartialEqArray.eq core.U8.Insts.CoreCmpPartialEqU8 bytes request.public_key)
  if matched then
    let secret ← beaconcrypt_public_request.beacon.Beacon.identity_sk beacon
    let signed ← crypto.edSign request.message secret
    let optional ← liftRust (core.result.Result.ok signed)
    liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) optional)
  else
    liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) .None)

def borrow (reply : core.result.Result (alloc.vec.Vec U8) primitive.Error) :
    RustM (core.option.Option (Slice U8)) := do
  let optional ← core.result.Result.ok reply
  core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) optional

omit platform localOps children in
theorem ed_run (beacon : beaconcrypt_public_wrapper.beacon.Beacon)
    (request : registration.Ed25519SigningRequest) (publicKey : Std.Array U8 32#usize)
    (getter : (crypto.edPublicBytes beacon.identity_key.public_key).run = pure (.ok publicKey)) :
    (ed beacon request).run =
      if decide (publicKey.val = request.public_key.val) then
        (do let reply ← (crypto.edSign request.message beacon.identity_key.secret_key).run
            pure (reply >>= borrow))
      else pure (.ok .None) := by
  unfold ed
  dsimp only [beaconcrypt_public_request.beacon.Beacon.identity_pk,
    beaconcrypt_public_request.beacon.Beacon.identity_sk, AdapterPublicWrapperLiftFunction.call,
    AdapterPublicWrapperLiftFunction.LiftFunction.lift, AdapterPublicWrapperLiftFunction.function,
    AdapterPublicWrapperLiftFunction.result, liftRust]
  simp only [RustT.run_bind, pure_bind, getter, PqxdhSurface.byte_array_eq_exact]
  split
  · simp only [RustT.run_bind, pure_bind]
    apply bind_congr
    intro reply
    cases reply with
    | fail error | div => rfl
    | ok reply => cases reply <;> rfl
  · rfl

def step (beacon : beaconcrypt_public_wrapper.beacon.Beacon) (effect : registration.BeaconInitEffect) :
    RustT m (ControlFlow registration.BeaconInitEffect (core.option.Option registration.BeaconInitReady)) := do
  match effect with
  | .Rejected _ => pure (.done .None)
  | .Ready ready => pure (.done (.Some ready))
  | .Ed25519SigningRequested pending =>
      let request ← liftRust pending.request
      let reply ← ed beacon request
      let next ← liftRust (pending.resume reply)
      pure (.cont next)
  | .FingerprintRequested pending =>
      let request ← liftRust pending.request
      let reply ← children.executeHash request
      let next ← liftRust (pending.resume reply)
      pure (.cont next)
  | .HashRequested pending =>
      let request ← liftRust pending.request
      let reply ← children.executeHash request
      let next ← liftRust (pending.resume reply)
      pure (.cont next)
  | .MldsaSigningRequested pending =>
      let request ← liftRust pending.request
      let signature ← localOps.auth_MldsaIdentity_sign_requested beacon.authentication.identity request
      let borrowed ← liftRust (core.option.Option.as_deref (alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice U8) signature)
      let next ← liftRust (pending.resume borrowed)
      pure (.cont next)

theorem body_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon) (effect : registration.BeaconInitEffect) :
    beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop.body (m := RustT m) beacon effect =
      step beacon effect := by
  cases effect <;> simp only [beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop.body, step, ed,
    bind_assoc, branch_bind] <;> rfl

theorem loop_source (beacon : beaconcrypt_public_wrapper.beacon.Beacon) (effect : registration.BeaconInitEffect) :
    beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop (m := RustT m) effect beacon =
      AdapterPublicWrapperLiftFunction.loopFuel (AdapterPublicInitSourceLoop.rank effect + 1) (step beacon) effect := by
  unfold beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop
  simp only [body_source]

end BeaconcryptCore.Refinement.AdapterPublicInitReady

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitReady.ed_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitReady.ed_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitReady.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitReady.body_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicInitReady.loop_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicInitReady.loop_source

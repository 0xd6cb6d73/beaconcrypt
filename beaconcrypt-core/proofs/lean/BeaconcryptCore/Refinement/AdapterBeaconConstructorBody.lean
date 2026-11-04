-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterBeaconConstructorRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Factoring the unchanged actual constructor retains every parsed-key rejection, key-generation error, Rust failure/divergence and complete caller RNG. No primitive availability or material premise is used here. -/
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorBody
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
variable [crypto : CryptoOperations (RustT m)] [children : ChildOperations (RustT m)]
universe u v w
omit material primitive in
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
omit material primitive in
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
omit material primitive in
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl

abbrev Outcome (R : Type) := core.result.Result beaconcrypt_public_wrapper.beacon.Beacon Unit × R

def reject {R : Type} (rng : R) : RustT m (Outcome R) := pure (.Err (), rng)

def withKeys {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (binding : pqxdh.ServerBinding) (pin : session.ServerAuthenticationPin)
    (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) (rng : R) : RustT m (Outcome R) := do
  let (signing, rng1) ← generators.edGenerate generator rng
  match signing with
  | .Err _ => reject rng1
  | .Ok signing =>
    let control ← liftRust (pqxdh.BeaconFresh.new binding)
    let (prekey, rng2) ← crypto.kxGenerate generator rng1
    match prekey with
    | .Err _ => reject rng2
    | .Ok prekey =>
      let (kem, rng3) ← generators.kemGenerate generator rng2
      match kem with
      | .Err _ => reject rng3
      | .Ok kem => pure (.Ok ⟨signing, identifier, .Fresh control prekey kem, serverId, ⟨identity, pin⟩⟩, rng3)

def withInputs {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mldsa : Std.Array U8 1952#usize) (rng : R) : RustT m (Outcome R) := do
  let publicKey ← crypto.edPublicBytes serverId
  let binding : pqxdh.ServerBinding := ⟨publicKey, identifier⟩
  let (identity, rng1) ← generators.mldsaGenerate generator rng
  match identity with
  | .Err _ => reject rng1
  | .Ok identity =>
    let pin ← beaconcrypt_public_request.auth.fingerprint_pin (m := RustT m) binding mldsa
    match pin with
    | .None => reject rng1
    | .Some pin => withKeys generator identifier serverId binding pin identity rng1

def source {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (rng : R) : RustT m (Outcome R) := do
  let parsed ← liftRust (beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes identityKey)
  match parsed with
  | .Err _ => reject rng
  | .Ok serverId =>
    let key : core.result.Result (Std.Array U8 1952#usize) core.array.TryFromSliceError ← liftRust (core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      1952#usize core.U8.Insts.CoreMarkerCopy mldsaKey)
    core.result.Result.casesOn (motive := fun _ => RustT m (Outcome R)) key
      (fun key => withInputs generator identifier serverId key rng)
      (fun _ => reject rng)

theorem body {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (identityKey mldsaKey : Slice U8) (rng : R) :
    beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng (m := RustT m) generator identifier identityKey mldsaKey rng =
      source generator identifier identityKey mldsaKey rng := by
  unfold beaconcrypt_constructor_request.beacon.Beacon.try_new_with_rng source
  simp only [call_apply, call_result]
  dsimp only [beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once]
  simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual]
  dsimp only [beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once,
    beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once]
  apply bind_congr
  intro parsed
  cases parsed with
  | Err error => simp [reject, lift_ok, core.convert.From.Blanket.from]
  | Ok serverId =>
    simp only [lift_ok, pure_bind]
    apply bind_congr
    intro key
    cases key with
    | Err error => simp [reject, lift_ok, core.convert.From.Blanket.from]
    | Ok key =>
      simp only [lift_ok, pure_bind, withInputs]
      apply bind_congr
      intro publicKey
      apply bind_congr
      rintro ⟨identity, nextRng⟩
      cases identity with
      | Err error => cases error; simp [reject, lift_ok, core.convert.From.Blanket.from]
      | Ok identity =>
        simp only [lift_ok, pure_bind]
        apply bind_congr
        intro pin
        cases pin with
        | none => simp [core.option.Option.ok_or, reject, lift_ok, core.convert.From.Blanket.from]
        | some pin =>
          simp only [core.option.Option.ok_or, lift_ok, pure_bind, withKeys]
          apply bind_congr
          rintro ⟨signing, nextRng⟩
          cases signing with
          | Err error => simp [reject, lift_ok, core.convert.From.Blanket.from]
          | Ok signing =>
            simp only [lift_ok, pure_bind]
            apply bind_congr
            intro control
            apply bind_congr
            rintro ⟨prekey, nextRng⟩
            cases prekey with
            | Err error => simp [reject, lift_ok, core.convert.From.Blanket.from]
            | Ok prekey =>
              simp only [lift_ok, pure_bind]
              apply bind_congr
              rintro ⟨kem, nextRng⟩
              cases kem <;> simp [reject, lift_ok, core.convert.From.Blanket.from]

end BeaconcryptCore.Refinement.AdapterBeaconConstructorBody

/-- info: 'BeaconcryptCore.Refinement.AdapterBeaconConstructorBody.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterBeaconConstructorBody.body

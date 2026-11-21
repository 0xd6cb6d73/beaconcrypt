-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementFields
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! Primitive-field algebra for the actual source agreement callbacks. These equalities expose the exact source scalar multiplication, private-key getters and returned RNG without replacing any primitive by a whole agreement contract. The fixed primitive representation/sampling contract can be applied to these leaves separately. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
open AdapterPublicAgreementFields (Array32 LocalIdentity KeyPair)
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]

def scalar (secret publicKey : Array32) : RustT m (core.option.Option Array32) := do
  let result ← crypto.scalarMult secret.to_slice publicKey.to_slice
  liftRust (core.result.Result.ok result)

noncomputable section

theorem local_scalar {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (secret : LocalIdentity) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once
      (m := RustT m) generator publicKey secret = scalar secret.value publicKey := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once,
    scalar, call_apply, call_result, zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,
    core.array.Array.as_slice, rust_primitives.slice.array_as_slice, Aeneas.Std.lift, lift_ok, pure_bind]

theorem ephemeral_scalar {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (secret : KeyPair) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once
      (m := RustT m) generator publicKey secret = (do
        let bytes ← crypto.kxSecretBytes secret.secret_key
        scalar bytes publicKey) := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once,
    scalar, call_apply, call_result]
  apply bind_congr
  intro bytes
  simp only [core.array.Array.as_slice, rust_primitives.slice.array_as_slice, Aeneas.Std.lift, lift_ok, pure_bind]

theorem prekey_scalar {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (secret : beaconcrypt_crypto.crypto_kx.SecretKey) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
      (m := RustT m) generator publicKey secret = (do
        let bytes ← crypto.kxSecretBytes secret
        scalar bytes publicKey) := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once,
    scalar, call_apply, call_result]
  apply bind_congr
  intro bytes
  simp only [core.array.Array.as_slice, rust_primitives.slice.array_as_slice, Aeneas.Std.lift, lift_ok, pure_bind]

theorem one_time_scalar {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (secret : beaconcrypt_crypto.crypto_kx.SecretKey) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
      (m := RustT m) generator publicKey secret = (do
        let bytes ← crypto.kxSecretBytes secret
        scalar bytes publicKey) := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once,
    scalar, call_apply, call_result]
  apply bind_congr
  intro bytes
  simp only [core.array.Array.as_slice, rust_primitives.slice.array_as_slice, Aeneas.Std.lift, lift_ok, pure_bind]

theorem generation {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (rng : R) :
    AdapterPublicAgreementFields.generate (m := m) generator rng = (do
      let (result, nextRng) ← crypto.kxGenerate generator rng
      match result with
      | .Err _ => pure (.None, .None, nextRng)
      | .Ok pair =>
        let bytes ← crypto.kxPublicBytes pair.public_key
        pure (.Some bytes, .Some pair, nextRng)) := by
  simp only [AdapterPublicAgreementFields.generate]
  apply bind_congr
  rintro ⟨result, nextRng⟩
  cases result with
  | Err prior =>
    simp only [core.result.Result.ok, core.option.Option.as_ref,
      AdapterPublicWrapperRequestMonad.Option.map, lift_ok, pure_bind]
  | Ok pair =>
    simp only [core.result.Result.ok, core.option.Option.as_ref,
      AdapterPublicWrapperRequestMonad.Option.map,
      beaconcrypt_public_request.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832.call_once,
      lift_ok, pure_bind, bind_assoc]

theorem secret_conversion (secret : beaconcrypt_crypto.crypto_sign.SecretKey) :
    AdapterPublicAgreementFields.convertSecret (m := m) secret = (do
      let result ← crypto.convertSecret secret
      pure (match result with
        | .Err _ => .None
        | .Ok bytes => .Some (⟨bytes⟩ : LocalIdentity))) := by
  simp only [AdapterPublicAgreementFields.convertSecret]
  apply bind_congr
  intro result
  cases result with
  | Err prior =>
    simp only [core.result.Result.ok, AdapterPublicWrapperRequestMonad.Option.map, lift_ok, pure_bind]
  | Ok bytes =>
    simp only [core.result.Result.ok, AdapterPublicWrapperRequestMonad.Option.map,
      AdapterPublicWrapperLiftFunction.call, AdapterPublicWrapperLiftFunction.LiftFunction.lift,
      zeroize.P.Insts.CoreOpsFunctionFnOnceTupleZZeroizing, AdapterPublicWrapperRequestMonad.FnOnce.liftRust, zeroize.Zeroizing.new,
      lift_ok, pure_bind]

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.local_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.local_scalar

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.ephemeral_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.ephemeral_scalar

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.prekey_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.prekey_scalar

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.one_time_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.one_time_scalar

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.generation

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.secret_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementPrimitiveFields.secret_conversion

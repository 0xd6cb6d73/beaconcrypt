-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterServerConstructorRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperRustT
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The honest unseeded entry is factored from the checked source AST, retaining Ed then ML generation, actual std object construction, every failure and the reached caller RNG. -/
namespace BeaconcryptCore.Refinement.AdapterServerConstructorBody
open AdapterPublicWrapperRustT (RustT)
open AdapterRecordRequestMonad (liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [standard : AdapterServerConstructorPrimitive.Standard]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [generators : AdapterBeaconConstructorRequestMonad.Operations (RustT m)]
universe u v w
omit material platform primitive standard in
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
omit material platform primitive standard in
private theorem call_result {m : Type → Type} [AdapterRecordRequestMonad.LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
omit material platform primitive standard in
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl

abbrev Outcome (R : Type) := core.result.Result beaconcrypt_public_wrapper.server.Server Unit × R

def assemble (identifier : U64) (signing : beaconcrypt_crypto.crypto_sign.KeyPair)
    (identity : beaconcrypt_public_wrapper.auth.MldsaIdentity) : RustT m beaconcrypt_public_wrapper.server.Server := do
  let bytes ← liftRust (standard.edSecretBytes signing.secret_key)
  let slice ← liftRust (Aeneas.Std.lift (Array.to_slice bytes))
  let known ← liftRust (standard.mapWithKey U64
    (beaconcrypt_public_wrapper.shared.EstablishedRemote beaconcrypt_crypto.crypto_sign.PublicKey) slice)
  let slice ← liftRust (Aeneas.Std.lift (Array.to_slice bytes))
  let consumed ← liftRust (standard.setWithKey (Array U8 64#usize) slice)
  let shared ← liftRust (standard.arcNew (⟨signing,identity,identifier⟩ : beaconcrypt_public_wrapper.server.ServerIdentity))
  let control ← liftRust (pqxdh.ServerState.new identifier)
  pure ⟨shared,control,known,consumed⟩

def source {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (rng : R) : RustT m (Outcome R) := do
  let (signing,nextRng) ← generators.edGenerate generator rng
  match signing with
  | .Err _ => pure (.Err (),nextRng)
  | .Ok signing =>
    let (identity,finalRng) ← generators.mldsaGenerate generator nextRng
    match identity with
    | .Err _ => pure (.Err (),finalRng)
    | .Ok identity =>
      let server ← assemble identifier signing identity
      pure (.Ok server,finalRng)

theorem honest {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (identifier : U64) (rng : R) :
    beaconcrypt_server_constructor_request.server.Server.try_new_with_rng (m := RustT m)
      generator identifier .None .None rng = source generator identifier rng := by
  unfold beaconcrypt_server_constructor_request.server.Server.try_new_with_rng source
  simp only [call_apply,call_result]
  dsimp only [beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError,
    beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once]
  simp only [core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry_traitTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual]
  dsimp only [beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError.call_once]
  apply bind_congr
  rintro ⟨signing,nextRng⟩
  cases signing with
  | Err error => simp [lift_ok,core.convert.From.Blanket.from]
  | Ok signing =>
    simp only [lift_ok,pure_bind]
    apply bind_congr
    rintro ⟨identity,finalRng⟩
    cases identity with
    | Err error => cases error; simp [lift_ok,core.convert.From.Blanket.from]
    | Ok identity =>
      simp only [lift_ok,pure_bind]
      simp only [assemble,bind_assoc,pure_bind]
      rfl
end BeaconcryptCore.Refinement.AdapterServerConstructorBody

/-- info: 'BeaconcryptCore.Refinement.AdapterServerConstructorBody.honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterServerConstructorBody.honest

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterBeaconConstructorExtraction.Funs
import BeaconcryptCore.AdapterPublicWrapperRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open beaconcrypt_constructor beaconcrypt_public_wrapper
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
namespace BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [primitive : BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
/-- Shared constructor requests: only the Server controller uses ML generation. -/
class Operations (m : Type → Type) where
  mldsaGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → m
    (core.result.Result beaconcrypt_public_wrapper.auth.MldsaIdentity Unit × R)
  edGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → m
    (core.result.Result beaconcrypt_crypto.crypto_sign.KeyPair primitive.Error × R)
  kemGenerate {R E : Type} : rand_core.TryCryptoRng R E → R → m
    (core.result.Result beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair primitive.Error × R)
@[instance_reducible] def rustOperations [ops : AdapterBeaconConstructorPrimitive.Operations] : Operations RustM where
  mldsaGenerate := ops.mldsaGenerate
  edGenerate := ops.edGenerate
  kemGenerate := ops.kemGenerate
attribute [instance] rustOperations
end BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad
noncomputable section
namespace beaconcrypt_constructor_request
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard]
variable {m : Type → Type} [Monad m] [BeaconcryptCore.Refinement.AdapterRecordRequestMonad.LiftRust m]
variable [BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad.Operations m]
variable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.CryptoOperations m]
variable [BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.ChildOperations m]
/-- [beaconcrypt::beacon::{beaconcrypt::beacon::Beacon}::try_new_with_rng]:
    Source: 'beaconcrypt/src/beacon.rs', lines 101:4-132:5
    Visibility: public -/
def beacon.Beacon.try_new_with_rng
  {R : Type} {Clause0_Clause0_Error : Type} (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) (server_kid : Std.U64)
  (server_id_pk : Slice Std.U8) (server_mldsa_pk : Slice Std.U8) (rng : R) :
  m ((core.result.Result beacon.Beacon error.KeyGenError) × R)
  := do
  let r ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes) server_id_pk
  let r1 ←
    (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.map_err)
      (beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError
      rand_coreTryCryptoRngInst) r ()
  let cf ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r2 ←
      (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from)
        1952#usize core.U8.Insts.CoreMarkerCopy server_mldsa_pk
    let r3 ←
      (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.map_err)
        (beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError
        rand_coreTryCryptoRngInst) r2 ()
    let cf1 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r3
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let a ← (BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.CryptoOperations.edPublicBytes (m := m)) val
      let o ←
        (beaconcrypt_public_request.auth.server_pin (m := m))
          { identity_public_key := a, identity_key_id := server_kid } val1
      let r4 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.option.Option.ok_or) o ()
      let cf2 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r4
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let (r5, rng1) ←
          (BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad.Operations.edGenerate (m := m))
            rand_coreTryCryptoRngInst rng
        let r6 ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.map_err)
            (beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_2.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError
            rand_coreTryCryptoRngInst) r5 ()
        let cf3 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r6
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let bf ←
            (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) beaconcrypt_core.pqxdh.BeaconFresh.new)
              { identity_public_key := a, identity_key_id := server_kid }
          let (r7, rng2) ←
            (BeaconcryptCore.Refinement.AdapterPublicWrapperRequestMonad.CryptoOperations.kxGenerate (m := m))
              rand_coreTryCryptoRngInst rng1
          let r8 ←
            (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.map_err)
              (beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_3.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError
              rand_coreTryCryptoRngInst) r7 ()
          let cf4 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r8
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let (r9, rng3) ←
              (BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad.Operations.kemGenerate (m := m))
                rand_coreTryCryptoRngInst rng2
            let r10 ←
              (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.map_err)
                (beaconcrypt_constructor.beacon.Beacon.try_new_with_rng.closure_4.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError
                rand_coreTryCryptoRngInst) r9 ()
            let cf5 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r10
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              pure (core.result.Result.Ok
                {
                  identity_key := val3,
                  identity_key_kid := server_kid,
                  state := (beacon.BeaconState.Fresh bf val4 val5),
                  server_id := val,
                  authentication := { server_pin := val2 }
                }, rng3)
            | core.ops.control_flow.ControlFlow.Break residual =>
              let r11 ←
                (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
                  beacon.Beacon (core.convert.From.Blanket error.KeyGenError)
                  residual
              pure (r11, rng3)
          | core.ops.control_flow.ControlFlow.Break residual =>
            let r9 ←
              (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
                beacon.Beacon (core.convert.From.Blanket error.KeyGenError)
                residual
            pure (r9, rng2)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r7 ←
            (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
              beacon.Beacon (core.convert.From.Blanket error.KeyGenError)
              residual
          pure (r7, rng1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r5 ←
          (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
            beacon.Beacon (core.convert.From.Blanket error.KeyGenError)
            residual
        pure (r5, rng)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r4 ←
        (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
          beacon.Beacon (core.convert.From.Blanket error.KeyGenError) residual
      pure (r4, rng)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
        beacon.Beacon (core.convert.From.Blanket error.KeyGenError) residual
    pure (r2, rng)


/-- [beaconcrypt::beacon::{beaconcrypt::beacon::Beacon}::try_new]:
    Source: 'beaconcrypt/src/beacon.rs', lines 87:4-98:5
    Visibility: public -/
def beacon.Beacon.try_new
  (server_kid : Std.U64) (server_id_pk : Slice Std.U8)
  (server_mldsa_pk : Slice Std.U8) :
  m (core.result.Result beacon.Beacon error.KeyGenError)
  := do
  let (r, _) ←
    (beacon.Beacon.try_new_with_rng (m := m))
      beaconcrypt_crypto.OsRng.Insts.Rand_coreTryCryptoRngError server_kid
      server_id_pk server_mldsa_pk ()
  pure r


/-- [beaconcrypt::beacon::{beaconcrypt::beacon::Beacon}::new]:
    Source: 'beaconcrypt/src/beacon.rs', lines 80:4-83:5
    Visibility: public -/
def beacon.Beacon.new
  (server_kid : Std.U64) (server_id_pk : Slice Std.U8)
  (server_mldsa_pk : Slice Std.U8) :
  m beacon.Beacon
  := do
  let r ← (beacon.Beacon.try_new (m := m)) server_kid server_id_pk server_mldsa_pk
  (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.expect) error.KeyGenError.Insts.CoreFmtDebug r (toStr
    "Failed to construct beacon" BeaconcryptCore.Refinement.AdapterBeaconConstructorString.failure_bound)


end beaconcrypt_constructor_request

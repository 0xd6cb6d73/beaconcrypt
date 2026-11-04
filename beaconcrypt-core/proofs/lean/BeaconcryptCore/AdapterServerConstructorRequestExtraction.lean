-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.AdapterServerConstructorExtraction.Funs
import BeaconcryptCore.AdapterBeaconConstructorRequestExtraction
import BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
open beaconcrypt_server_constructor beaconcrypt_public_wrapper
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
noncomputable section
namespace beaconcrypt_server_constructor_request
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Material]
variable [BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable [BeaconcryptCore.Refinement.AdapterInitEdPrimitive.Operations]
variable [BeaconcryptCore.Refinement.AdapterServerConstructorPrimitive.Standard]
variable [BeaconcryptCore.Refinement.AdapterBeaconConstructorPrimitive.Standard]
variable {m : Type → Type} [Monad m] [BeaconcryptCore.Refinement.AdapterRecordRequestMonad.LiftRust m]
variable [BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad.Operations m]
/-- [beaconcrypt::server::{beaconcrypt::server::Server}::try_new_with_rng]:
    Source: 'beaconcrypt/src/server.rs', lines 199:4-228:5
    Visibility: public -/
def server.Server.try_new_with_rng
  {R : Type} {Clause0_Clause0_Error : Type} (rand_coreTryCryptoRngInst :
  rand_core.TryCryptoRng R Clause0_Clause0_Error) (server_kid : Std.U64)
  (id_seed : core.option.Option (Slice Std.U8))
  (mldsa_seed : core.option.Option (Slice Std.U8)) (rng : R) :
  m ((core.result.Result server.Server error.KeyGenError) × R)
  := do
  let (rng1, r) ←
    match id_seed with
    | core.option.Option.None =>
      do
      let (r1, rng2) ←
        (BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad.Operations.edGenerate (m := m))
          rand_coreTryCryptoRngInst rng
      pure (rng2, r1)
    | core.option.Option.Some seed =>
      do
      let r1 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) beaconcrypt_crypto.crypto_sign.KeyPair.from_seed) seed
      pure (rng, r1)
  let r1 ←
    (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.map_err)
      (beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure.Insts.CoreOpsFunctionFnOnceTupleCryptoErrorKeyGenError
      rand_coreTryCryptoRngInst) r ()
  let cf ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    match mldsa_seed with
    | core.option.Option.None =>
      let (r2, rng2) ←
        (BeaconcryptCore.Refinement.AdapterBeaconConstructorRequestMonad.Operations.mldsaGenerate (m := m)) rand_coreTryCryptoRngInst rng1
      let cf1 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r2
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let a ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) beaconcrypt_crypto.crypto_sign.SecretKey.as_bytes) val.secret_key
        let s ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) Aeneas.Std.lift) (Array.to_slice a)
        let known_ids ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) collections.map_with_key) Std.U64 (shared.EstablishedRemote
            beaconcrypt_crypto.crypto_sign.PublicKey) s
        let s1 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) Aeneas.Std.lift) (Array.to_slice a)
        let consumed_registrations ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) collections.set_with_key) (Array Std.U8 64#usize) s1
        let a1 ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) alloc.sync.Arc.new)
            ({
               identity_key := val,
               mldsa_identity := val1,
               identity_key_kid := server_kid
             } : server.ServerIdentity)
        let ss ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) beaconcrypt_core.pqxdh.ServerState.new) server_kid
        pure (core.result.Result.Ok
          { identity := a1, control := ss, known_ids, consumed_registrations },
          rng2)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r3 ←
          (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
            server.Server (core.convert.From.Blanket error.KeyGenError)
            residual
        pure (r3, rng2)
    | core.option.Option.Some seed =>
      let r2 ←
        (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from)
          32#usize core.U8.Insts.CoreMarkerCopy seed
      let r3 ←
        (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.map_err)
          (beaconcrypt_server_constructor.server.Server.try_new_with_rng.closure_1.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorKeyGenError
          rand_coreTryCryptoRngInst) r2 ()
      let cf1 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.Insts.CoreOpsTry_traitTry.branch) r3
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let mldsa_identity ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) auth.MldsaIdentity.from_seed) val1
        let a ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) beaconcrypt_crypto.crypto_sign.SecretKey.as_bytes) val.secret_key
        let s ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) Aeneas.Std.lift) (Array.to_slice a)
        let known_ids ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) collections.map_with_key) Std.U64 (shared.EstablishedRemote
            beaconcrypt_crypto.crypto_sign.PublicKey) s
        let s1 ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) Aeneas.Std.lift) (Array.to_slice a)
        let consumed_registrations ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) collections.set_with_key) (Array Std.U8 64#usize) s1
        let a1 ←
          (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) alloc.sync.Arc.new)
            ({
               identity_key := val,
               mldsa_identity,
               identity_key_kid := server_kid
             } : server.ServerIdentity)
        let ss ← (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) beaconcrypt_core.pqxdh.ServerState.new) server_kid
        pure (core.result.Result.Ok
          { identity := a1, control := ss, known_ids, consumed_registrations },
          rng1)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
            server.Server (core.convert.From.Blanket error.KeyGenError)
            residual
        pure (r4, rng1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r2 ←
      (fun T conversion residual => BeaconcryptCore.Refinement.AdapterRecordRequestMonad.liftRust (m := m) (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual T conversion residual))
        server.Server (core.convert.From.Blanket error.KeyGenError) residual
    pure (r2, rng1)


/-- [beaconcrypt::server::{beaconcrypt::server::Server}::try_new]:
    Source: 'beaconcrypt/src/server.rs', lines 184:4-195:5
    Visibility: public -/
def server.Server.try_new
  (server_kid : Std.U64) (id_seed : core.option.Option (Slice Std.U8))
  (mldsa_seed : core.option.Option (Slice Std.U8)) :
  m (core.result.Result server.Server error.KeyGenError)
  := do
  let (r, _) ←
    (server.Server.try_new_with_rng (m := m))
      beaconcrypt_crypto.OsRng.Insts.Rand_coreTryCryptoRngError server_kid
      id_seed mldsa_seed ()
  pure r


/-- [beaconcrypt::server::{beaconcrypt::server::Server}::new]:
    Source: 'beaconcrypt/src/server.rs', lines 177:4-179:5
    Visibility: public -/
def server.Server.new
  (server_kid : Std.U64) (id_seed : core.option.Option (Slice Std.U8))
  (mldsa_seed : core.option.Option (Slice Std.U8)) :
  m server.Server
  := do
  let r ← (server.Server.try_new (m := m)) server_kid id_seed mldsa_seed
  (BeaconcryptCore.Refinement.AdapterPublicWrapperLiftFunction.call (m := m) core.result.Result.expect) error.KeyGenError.Insts.CoreFmtDebug r (toStr
    "Failed to construct server" BeaconcryptCore.Refinement.AdapterServerConstructorString.failure_bound)


end beaconcrypt_server_constructor_request

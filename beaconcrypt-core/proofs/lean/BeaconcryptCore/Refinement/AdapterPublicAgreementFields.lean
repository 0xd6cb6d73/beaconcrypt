-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicBundleBody
import BeaconcryptCore.Computational.RegistrationAgreementTermination
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Actual source agreement callbacks factored at typed primitive fields, retaining private objects, optional conversion failures, RNG captures and complete zeroizing/borrowed views. No aggregate agreement behavior is assumed. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementFields
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
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
abbrev Array32 := Array U8 32#usize
abbrev CipherArray := Array U8 1088#usize
abbrev KemArray := Array U8 1184#usize
abbrev LocalIdentity := zeroize.Zeroizing Array32
abbrev KeyPair := beaconcrypt_crypto.crypto_kx.KeyPair
abbrev Keys := beaconcrypt_public_wrapper.pqxdh.RegistrationKeys

def convertPublic (input : Array32) : RustT m (core.option.Option Array32) := do
  let parsed ← liftRust (beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes input.to_slice)
  match parsed with
  | .Err _ => pure .None
  | .Ok publicKey =>
    let result ← crypto.convertPublic publicKey
    liftRust (core.result.Result.ok result)

def root (request : agreement.RootKdfRequest) : RustT m (core.option.Option Array32) := do
  let extracted ← crypto.extract .None request.input.to_slice
  match extracted with
  | .Err _ => pure .None
  | .Ok prk =>
    let expanded ← crypto.expand 32#usize (.Some request.info.to_slice) prk
    match expanded with
    | .Err _ => pure .None
    | .Ok output =>
      let wrapped ← liftRust (zeroize.Zeroizing.new (zeroize.alloc.vec.Vec.Insts.ZeroizeZeroize
        (zeroize.Zeroize.Blanket zeroize.U8.Insts.ZeroizeDefaultIsZeroes)) output)
      let borrowed ← liftRust (zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref
        (zeroize.alloc.vec.Vec.Insts.ZeroizeZeroize (zeroize.Zeroize.Blanket zeroize.U8.Insts.ZeroizeDefaultIsZeroes)) wrapped)
      let bytes ← liftRust (alloc.vec.Vec.as_slice borrowed)
      let parsed ← liftRust (core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
        32#usize core.U8.Insts.CoreMarkerCopy bytes)
      liftRust (core.result.Result.ok parsed)

def encapsulate {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (input : core.option.Option KemArray) (rng : R) : RustT m (core.option.Option (CipherArray × Array32) × R) := do
  match input with
  | .None => pure (.None, rng)
  | .Some input =>
    let parsed ← crypto.kemPublicFromBytes input.to_slice
    match parsed with
    | .Err _ => pure (.None, rng)
    | .Ok publicKey =>
      let (result, nextRng) ← crypto.encapsulate generator publicKey rng
      match result with
      | .Err _ => pure (.None, nextRng)
      | .Ok (ciphertext, shared) =>
        let ciphertextBytes ← crypto.kemCipherBytes ciphertext
        let sharedBytes ← crypto.kemSharedBytes shared
        pure (.Some (ciphertextBytes, sharedBytes), nextRng)

def decapsulate (input : core.option.Option CipherArray)
    (secret : core.option.Option beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey) :
    RustT m (core.option.Option Array32) := do
  match input with
  | .None => pure .None
  | .Some input =>
    let parsed ← crypto.kemCipherFromBytes input.to_slice
    match parsed with
    | .Err _ => pure .None
    | .Ok ciphertext =>
      match secret with
      | .None => pure .None
      | .Some secret =>
        let result ← crypto.decapsulate ciphertext secret
        match result with
        | .Err _ => pure .None
        | .Ok shared =>
          let bytes ← crypto.kemSharedBytes shared
          pure (.Some bytes)

def convertSecret (secret : beaconcrypt_crypto.crypto_sign.SecretKey) : RustT m (core.option.Option LocalIdentity) := do
  let result ← crypto.convertSecret secret
  let optional ← liftRust (core.result.Result.ok result)
  AdapterPublicWrapperRequestMonad.Option.map
    (call (m := RustT m) zeroize.P.Insts.CoreOpsFunctionFnOnceTupleZZeroizing
      (zeroize.Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket zeroize.U8.Insts.ZeroizeDefaultIsZeroes)))
    optional (zeroize.Zeroizing.new
      (zeroize.Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket zeroize.U8.Insts.ZeroizeDefaultIsZeroes)))

noncomputable def generate {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (rng : R) :
    RustT m (core.option.Option Array32 × core.option.Option KeyPair × R) := do
  let (result, nextRng) ← crypto.kxGenerate generator rng
  let optional ← liftRust (core.result.Result.ok result)
  let borrowed ← liftRust (core.option.Option.as_ref optional)
  let publicKey ← AdapterPublicWrapperRequestMonad.Option.map
    (beaconcrypt_public_request.pqxdh.execute_agreement.closure_1.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairArrayU832 generator)
    borrowed ()
  pure (publicKey, optional, nextRng)

noncomputable def dh {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (localIdentity : core.option.Option LocalIdentity) (ephemeral : core.option.Option KeyPair)
    (request : agreement.DhRequest) : RustT m (core.option.Option Array32) := do
  match request.secret_role with
  | .LocalIdentity =>
    let borrowed ← liftRust (core.option.Option.as_ref localIdentity)
    AdapterPublicWrapperRequestMonad.Option.and_then
      (beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832 generator)
      borrowed request.public_key
  | .ServerEphemeral =>
    let borrowed ← liftRust (core.option.Option.as_ref ephemeral)
    AdapterPublicWrapperRequestMonad.Option.and_then
      (beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832 generator)
      borrowed request.public_key
  | .BeaconPrekey =>
    AdapterPublicWrapperRequestMonad.Option.and_then
      (beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832 generator)
      keys.beacon_prekey request.public_key
  | .BeaconOneTime =>
    AdapterPublicWrapperRequestMonad.Option.and_then
      (beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832 generator)
      keys.beacon_one_time request.public_key

noncomputable section

theorem root_source {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (pending : agreement.RootKdfPending) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call
      (m := RustT m) generator pending () = (do
        let request ← liftRust pending.request
        root request) := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement.closure_8.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call,
    root, call_apply, call_result]
  apply bind_congr
  intro request
  simp only [Aeneas.Std.lift, lift_ok, pure_bind]
  apply bind_congr
  intro extracted
  cases extracted with
  | Err prior =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | Ok prk =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
       lift_ok, pure_bind]
    apply bind_congr
    intro expanded
    cases expanded with
    | Err prior =>
      simp only [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
    | Ok output =>
      simp only [
         lift_ok, pure_bind]

theorem decapsulate_source {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (pending : agreement.DecapsulationPending)
    (secret : core.option.Option beaconcrypt_crypto.crypto_kem.mlkem768.SecretKey) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call
      (m := RustT m) generator (pending, secret) () = (do
        let input ← liftRust pending.ciphertext
        decapsulate input secret) := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement.closure_3.Insts.CoreOpsFunctionFnTupleOptionArrayU832.call,
    decapsulate, call_apply, call_result]
  apply bind_congr
  intro input
  cases input with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | some input =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      Aeneas.Std.lift, lift_ok, pure_bind]
    apply bind_congr
    intro parsed
    cases parsed with
    | Err prior =>
      simp only [core.result.Result.ok,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
    | Ok ciphertext =>
      cases secret with
      | none =>
        simp only [core.result.Result.ok,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
      | some secret =>
        simp only [core.result.Result.ok,
           lift_ok, pure_bind]
        apply bind_congr
        intro shared
        cases shared with
        | Err prior =>
          simp only [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
        | Ok shared =>
          simp only [
             lift_ok, pure_bind]

theorem encapsulate_source {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (pending : agreement.EncapsulationPending) (rng : R) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_2.Insts.CoreOpsFunctionFnMutTupleOptionPairArrayU81088ArrayU832.call_mut
      (m := RustT m) generator (pending, rng) () = (do
        let input ← liftRust pending.public_key
        let (result, nextRng) ← encapsulate generator input rng
        pure (result, (pending, nextRng), fun capture => let (_, next) := capture; (pending, next))) := by
  simp only [beaconcrypt_public_request.pqxdh.execute_agreement.closure_2.Insts.CoreOpsFunctionFnMutTupleOptionPairArrayU81088ArrayU832.call_mut,
    encapsulate, call_apply, call_result]
  apply bind_congr
  intro input
  cases input with
  | none =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
    rfl
  | some input =>
    simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
      Aeneas.Std.lift, lift_ok, pure_bind, bind_assoc]
    apply bind_congr
    intro parsed
    cases parsed with
    | Err prior =>
      simp only [core.result.Result.ok,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
      rfl
    | Ok publicKey =>
      simp only [core.result.Result.ok,
         lift_ok, pure_bind, bind_assoc]
      apply bind_congr
      rintro ⟨result, nextRng⟩
      cases result with
      | Err prior =>
        simp only [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
        rfl
      | Ok pair =>
        rcases pair with ⟨ciphertext, shared⟩
        simp only [
           lift_ok, pure_bind, bind_assoc]
        apply bind_congr
        intro ciphertextBytes
        apply bind_congr
        intro sharedBytes
        rfl

abbrev State (R : Type) := agreement.AgreementEffect × R × core.option.Option LocalIdentity × core.option.Option KeyPair
abbrev Exit (R : Type) := ControlFlow (State R) (agreement.AgreementEffect × R)

def body {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys) (state : State R) :
    RustT m (Exit R) := do
  let (phase, rng, localIdentity, ephemeral) := state
  match phase with
  | .Rejected _ | .ServerComplete _ | .BeaconComplete _ => pure (.done (phase, rng))
  | .ConvertPublic pending =>
    let input ← liftRust pending.public_key
    let reply ← convertPublic input
    let next ← liftRust (pending.resume reply)
    pure (.cont (next, rng, localIdentity, ephemeral))
  | .ConvertSecret pending =>
    let stored ← convertSecret keys.identity_secret
    let success ← liftRust (core.option.Option.is_some stored)
    let next ← liftRust (pending.resume success)
    pure (.cont (next, rng, stored, ephemeral))
  | .GenerateEphemeral pending =>
    let (reply, stored, nextRng) ← generate generator rng
    let next ← liftRust (pending.resume reply)
    pure (.cont (next, nextRng, localIdentity, stored))
  | .Encapsulate pending =>
    let input ← liftRust pending.public_key
    let (reply, nextRng) ← encapsulate generator input rng
    let next ← liftRust (pending.resume reply)
    pure (.cont (next, nextRng, localIdentity, ephemeral))
  | .Decapsulate pending =>
    let input ← liftRust pending.ciphertext
    let reply ← decapsulate input keys.beacon_kem
    let next ← liftRust (pending.resume reply)
    pure (.cont (next, rng, localIdentity, ephemeral))
  | .Dh pending =>
    let request ← liftRust pending.request
    let reply ← dh generator keys localIdentity ephemeral request
    let next ← liftRust (pending.resume reply)
    pure (.cont (next, rng, localIdentity, ephemeral))
  | .RootKdf pending =>
    let request ← liftRust pending.request
    let reply ← root request
    let next ← liftRust (pending.resume reply)
    pure (.cont (next, rng, localIdentity, ephemeral))

theorem body_source {R Error : Type} (generator : rand_core.TryCryptoRng R Error) (keys : Keys)
    (state : State R) :
    beaconcrypt_public_request.pqxdh.execute_agreement_loop.body (m := RustT m) generator
      keys.identity_secret keys.beacon_prekey keys.beacon_one_time keys.beacon_kem
      state.1 state.2.1 state.2.2.1 state.2.2.2 = body generator keys state := by
  rcases state with ⟨phase, rng, localIdentity, ephemeral⟩
  cases phase with
  | Rejected aborted | ServerComplete completed | BeaconComplete completed => rfl
  | ConvertPublic pending =>
    simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, body,
      convertPublic, call_apply, call_result]
    apply bind_congr
    intro input
    simp only [Aeneas.Std.lift, lift_ok, pure_bind, bind_assoc]
    apply bind_congr
    intro parsed
    cases parsed with
    | Err prior =>
      simp only [core.result.Result.ok, AdapterPublicWrapperRequestMonad.Option.and_then,
        pure_bind, lift_ok]
    | Ok publicKey =>
      simp only [core.result.Result.ok, AdapterPublicWrapperRequestMonad.Option.and_then,

        beaconcrypt_public_request.pqxdh.execute_agreement.closure.Insts.CoreOpsFunctionFnOnceTuplePublicKeyOptionArrayU832.call_once,
        call_apply, call_result, lift_ok, pure_bind, bind_assoc]
  | ConvertSecret pending =>
    simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, body,
      convertSecret, call_apply, call_result, bind_assoc]
    apply bind_congr
    intro converted
    apply bind_congr
    intro optional
    apply bind_congr
    intro stored
    apply bind_congr
    intro success
    apply bind_congr
    intro next
    rfl
  | GenerateEphemeral pending =>
    simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, body,
      generate, call_apply, call_result, bind_assoc, pure_bind]
    rfl
  | Encapsulate pending =>
    simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, body,
      encapsulate_source, call_apply, call_result, bind_assoc, pure_bind]
    apply bind_congr
    intro input
    apply bind_congr
    rintro ⟨reply, nextRng⟩
    apply bind_congr
    intro next
    rfl
  | Decapsulate pending =>
    simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, body,
      decapsulate_source, call_apply, call_result, bind_assoc]
    rfl
  | Dh pending =>
    simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, body,
      dh, call_apply, call_result]
    apply bind_congr
    intro request
    rcases request with ⟨role, publicKey⟩
    cases role <;> simp only [bind_assoc, lift_ok]
  | RootKdf pending =>
    simp only [beaconcrypt_public_request.pqxdh.execute_agreement_loop.body, body,
      root_source, call_apply, call_result, bind_assoc]
    rfl

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementFields

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFields.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFields.root_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFields.decapsulate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFields.decapsulate_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFields.encapsulate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFields.encapsulate_source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementFields.body_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementFields.body_source

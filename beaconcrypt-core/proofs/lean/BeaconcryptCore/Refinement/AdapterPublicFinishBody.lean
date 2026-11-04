-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishReady
/-! The actual extracted public Beacon finish wrapper factors through its literal early Aborted update before decoding, actual response authentication, actual source agreement executor, initial HKDF and first-open/install loop. Every stored phase, primitive error, private key capture and returned object field is retained. No codec, primitive or whole agreement correspondence premise is used in this source-body equality. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishBody
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.CryptoOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [codec : Codecs (RustT m)] [children : ChildOperations (RustT m)]
abbrev Result := core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon

def beginOpen (self : beaconcrypt_public_wrapper.beacon.Beacon) (agreement : agreement.BeaconAgreement) : RustT m Result := do
  let pending ← liftRust (registration.begin_beacon_completion agreement)
  let request ← liftRust pending.request
  let bytes ← localOps.ratchet_initial_ratchet_hkdf request
  let response ← liftRust (pqxdh.concrete.InitialRatchetKdfResponse.from_bytes bytes)
  let resumed ← liftRust (pending.resume (.Some response))
  match resumed with
  | .Err control => pure (.None, { self with state := .Aborted control })
  | .Ok effect =>
      let (plaintext, identifier, state) ← beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration_loop effect self.identity_key_kid
      pure (plaintext, { self with identity_key_kid := identifier, state := state })

def fromAgreement (self : beaconcrypt_public_wrapper.beacon.Beacon) (effect : agreement.AgreementEffect) : RustT m Result :=
  match effect with
  | .Rejected (.some control) => pure (.None, { self with state := .Aborted control })
  | .BeaconComplete completed => beginOpen self completed
  | _ => pure (.None, self)

noncomputable def active (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (input : Slice U8) : RustT m Result := do
  let parsed ← codec.decodeResponse input
  let packet ← AdapterPublicWrapperRequestMonad.Option.and_then
    beaconcrypt_public_request.beacon.ProviderBeaconBeacon.finish_registration.closure.Insts.CoreOpsFunctionFnOnceTuplekexresponseOptionResponsePacket parsed ()
  let authenticated ← children.authenticateResponse pending packet
  match authenticated with
  | .Err control => pure (.None, { self with state := .Aborted control })
  | .Ok authenticated =>
      let effect ← liftRust (agreement.begin_beacon_agreement authenticated)
      let finished ← beaconcrypt_public_request.pqxdh.execute_beacon_agreement effect
        ⟨self.identity_key.secret_key, .Some prekey.secret_key, .Some oneTime.secret_key, .Some kem.secret_key⟩
      fromAgreement self finished

noncomputable def program (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) : RustT m Result := do
  match self.state with
  | .InitSent pending prekey oneTime kem =>
      let aborted ← liftRust pending.aborted_state
      active { self with state := .Aborted aborted } pending prekey oneTime kem input
  | _ => pure (.None, self)

/-- The literal early Aborted state is captured before decoding or any primitive call. -/
theorem source (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) :
    beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration (m := RustT m) self input =
      program (m := m) self input := by
  cases state : self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control =>
      simp only [beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration,
        program, state, call_apply, call_result, lift_ok]
  | InitSent pending prekey oneTime kem =>
      simp only [beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration,
        program, state, call_apply, call_result, registration.BeaconPending.aborted_state,
        pqxdh.beacon_abort_init, core.mem.replace, Aeneas.Std.core.mem.replace, lift_ok, pure_bind, active,
        beaconcrypt_public_request.beacon.Beacon.identity_sk]
      apply bind_congr
      intro parsed
      apply bind_congr
      intro packet
      apply bind_congr
      intro authenticated
      cases authenticated with
      | Err control => rfl
      | Ok authenticated =>
          apply bind_congr
          intro effect
          apply bind_congr
          intro finished
          cases finished with
          | Rejected aborted => cases aborted <;> rfl
          | BeaconComplete completed =>
              simp only [fromAgreement, beginOpen]
              apply bind_congr
              intro initial
              apply bind_congr
              intro request
              apply bind_congr
              intro material
              apply bind_congr
              intro response
              apply bind_congr
              intro resumed
              cases resumed <;> rfl
          | _ => rfl
end BeaconcryptCore.Refinement.AdapterPublicFinishBody

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishBody.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishBody.source

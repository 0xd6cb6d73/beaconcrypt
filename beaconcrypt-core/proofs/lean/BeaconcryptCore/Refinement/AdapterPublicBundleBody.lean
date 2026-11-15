-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicInitEdPublication
/-! The actual extracted public get_registration_bundle_with_rng body factors into source key generation, ordered field getters, actual Core begin/driver, actual child serialization and literal object installation. Every stored phase, generator error, Rust failure/divergence, serializer failure, returned RNG and source private key object is retained in this monadic equality. No getter, codec, primitive or publication-success premise is used in this factoring theorem. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicBundleBody
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)
open AdapterPublicWrapperLiftFunction (LiftFunction call)
open BeaconcryptCore.Computational
universe u v w
private theorem call_apply {m : Type → Type} {A : Type u} {F : A → Type v} {G : A → Type w}
    [∀ a, LiftFunction m (F a) (G a)] (source : (a : A) → F a) (arg : A) :
    call (m := m) source arg = call (m := m) (source arg) := rfl
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (liftRust (.ok value) : RustT m A) = pure value := rfl
private theorem call_result {m : Type → Type} [LiftRust m] {A : Type} (source : RustM A) :
    call (m := m) source = liftRust source := rfl

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

omit material platform primitive localOps crypto children [LawfulMonad m] [Monad m] in
def packet (view : registration.InitView) : beaconcrypt_parse.transport.initkex :=
  ⟨Array.to_slice view.fields.identity_key, Array.to_slice view.fields.pre_key,
    Array.to_slice view.fields.one_time_key, Array.to_slice view.fields.pq_key⟩

def publish {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (rng : R) (selected : core.option.Option registration.BeaconInitReady) :
    RustT m (core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon × R) := do
  match selected with
  | .None => pure (.None, self, rng)
  | .Some ready =>
      let message ← liftRust ready.message
      let buffer ← children.encodeInit (packet message)
      let published ← liftRust (ready.publish buffer)
      match published with
      | .Err _ => pure (.None, self, rng)
      | .Ok finished =>
          let (pending, encoded) ← liftRust finished.into_parts
          pure (.Some encoded, { self with state := .InitSent pending prekey oneTime kem }, rng)

def withKeys {R : Type} (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconFresh)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R) :
    RustT m (core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon × R) := do
  let prekeyPublic ← crypto.kxPublicBytes prekey.public_key
  let kemPublic ← crypto.kemPublicBytes kem.public_key
  let oneTimePublic ← crypto.kxPublicBytes oneTime.public_key
  let identity ← crypto.edPublicBytes self.identity_key.public_key
  let effect ← liftRust (registration.begin_beacon_init control ⟨identity, prekeyPublic, kemPublic⟩
    ⟨oneTimePublic⟩ self.authentication.server_pin)
  let ready ← beaconcrypt_public_request.beacon._proof_beacon_init_ready_loop effect self
  publish self prekey oneTime kem rng ready

-- The complete checked source body, specialized only by its literal stored FreshWithCoins variant.
omit platform localOps in
theorem with_coins {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R) (control : pqxdh.BeaconFresh)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (state : self.state = .FreshWithCoins control prekey oneTime kem) :
    beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT m) rngType self rng =
      withKeys (m := m) self control prekey oneTime kem rng := by
  simp only [beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng, state,
    call_apply, call_result, withKeys, beaconcrypt_public_request.beacon.Beacon.identity_pk,
    beaconcrypt_public_request.beacon._proof_beacon_init_ready, lift_ok, pure_bind]
  apply bind_congr
  intro prekeyPublic
  apply bind_congr
  intro kemPublic
  apply bind_congr
  intro oneTimePublic
  apply bind_congr
  intro identity
  apply bind_congr
  intro effect
  apply bind_congr
  intro ready
  cases ready with
  | none =>
      simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift_ok, pure_bind,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, publish]
  | some ready =>
      simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch, lift_ok, pure_bind, publish]
      apply bind_congr
      intro message
      simp only [Aeneas.Std.lift, lift_ok, pure_bind, packet]
      apply bind_congr
      intro buffer
      apply bind_congr
      intro published
      cases published with
      | Err prior =>
          simp only [core.result.Result.ok, lift_ok, pure_bind,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
      | Ok finished =>
          simp only [core.result.Result.ok, lift_ok, pure_bind,
            registration.PublishedBeaconInit.into_parts, registration.BeaconPending.aborted_state, core.mem.replace,
            pqxdh.beacon_abort_init, Aeneas.Std.core.mem.replace]

def generated {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (control : pqxdh.BeaconFresh)
    (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (rng : R) :
    RustT m (core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon × R) := do
  let (result, after) ← crypto.kxGenerate rngType rng
  match result with
  | .Err _ => pure (.None, self, after)
  | .Ok oneTime => withKeys self control prekey oneTime kem after

omit platform localOps in
theorem fresh {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R) (control : pqxdh.BeaconFresh)
    (prekey : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (state : self.state = .Fresh control prekey kem) :
    beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT m) rngType self rng =
      generated (m := m) rngType self control prekey kem rng := by
  simp only [beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng, state,
    call_apply, call_result, generated]
  apply bind_congr
  intro generated
  rcases generated with ⟨result, rngAfter⟩
  cases result with
  | Err failure =>
      simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, lift_ok, pure_bind]
  | Ok oneTime =>
      simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitTryTOptionInfallible.branch,
        core.option.Option.as_ref, lift_ok, pure_bind, withKeys,
        beaconcrypt_public_request.beacon.Beacon.identity_pk,
            beaconcrypt_public_request.beacon._proof_beacon_init_ready, call_apply, call_result]
      apply bind_congr
      intro prekeyPublic
      apply bind_congr
      intro kemPublic
      apply bind_congr
      intro oneTimePublic
      apply bind_congr
      intro identity
      apply bind_congr
      intro effect
      apply bind_congr
      intro ready
      cases ready with
      | none =>
          simp only [lift_ok, pure_bind,
            core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, publish]
      | some ready =>
          simp only [lift_ok, pure_bind, publish]
          apply bind_congr
          intro message
          simp only [Aeneas.Std.lift, lift_ok, pure_bind, packet]
          apply bind_congr
          intro buffer
          apply bind_congr
          intro published
          cases published with
          | Err prior =>
              simp only [lift_ok, pure_bind,
                core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
          | Ok finished =>
              simp only [lift_ok, pure_bind,
                registration.PublishedBeaconInit.into_parts, registration.BeaconPending.aborted_state, core.mem.replace,
                pqxdh.beacon_abort_init, Aeneas.Std.core.mem.replace, core.option.Option.take, Aeneas.Std.core.option.Option.take]

def program {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R) :
    RustT m (core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon × R) :=
  match self.state with
  | .Fresh control prekey kem => generated rngType self control prekey kem rng
  | .FreshWithCoins control prekey oneTime kem => withKeys self control prekey oneTime kem rng
  | _ => pure (.None, self, rng)

omit platform localOps in
/-- All stored phases and every source primitive/serializer failure are retained in the factored actual body. -/
theorem source {R Error : Type} (rngType : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R) :
    beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng (m := RustT m) rngType self rng =
      program (m := m) rngType self rng := by
  cases state : self.state with
  | Fresh control prekey kem =>
      simpa only [program, state] using fresh rngType self rng control prekey kem state
  | FreshWithCoins control prekey oneTime kem =>
      simpa only [program, state] using with_coins rngType self rng control prekey oneTime kem state
  | InitSent pending prekey oneTime kem | Established control binding manager | Aborted control =>
      simp only [program, state, beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng,
        call_apply, call_result, lift_ok]
end BeaconcryptCore.Refinement.AdapterPublicBundleBody

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleBody.with_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleBody.with_coins

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleBody.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleBody.fresh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicBundleBody.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicBundleBody.source

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishBody
import BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs
import BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative
/-! The complete literal Beacon finish wrapper composes the concrete all-input source response parser with actual native authentication while retaining the early Aborted update and literal source agreement and record suffix. This is the authentication prefix composition; it introduces no whole agreement law or success premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.CryptoOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [children : ChildOperations (RustT m)]

noncomputable def accepted (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated : registration.AuthenticatedResponse) : RustT m AdapterPublicFinishBody.Result := do
  let effect ← liftRust (agreement.begin_beacon_agreement authenticated)
  let finished ← beaconcrypt_public_request.pqxdh.execute_beacon_agreement effect
    ⟨self.identity_key.secret_key, .Some prekey.secret_key, .Some oneTime.secret_key, .Some kem.secret_key⟩
  AdapterPublicFinishBody.fromAgreement self finished

noncomputable def after (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) : m (RustM AdapterPublicFinishBody.Result) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err control) => pure (.ok (.None, {self with state := .Aborted control}))
  | .ok (.Ok authenticated) => (accepted self prekey oneTime kem authenticated).run

omit children in
theorem active (native : QueryImpl RegistrationAuthenticationExecutor.Spec m)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (input : Slice U8) :
    letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication native parseEd verifyEd) recording writer
    letI : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
    (AdapterPublicFinishBody.active (m := m) self pending prekey oneTime kem input).run = (do
      let reply ← simulateQ native (RegistrationResponseExecutor.begin pending
        (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
      after self prekey oneTime kem reply) := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication native parseEd verifyEd) recording writer
  let : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
  change (AdapterPublicFinishBody.active (m := m) self pending prekey oneTime kem input).run = (do
    let reply ← simulateQ native (RegistrationResponseExecutor.begin pending
      (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
    after self prekey oneTime kem reply)
  have parsed : AdapterPublicConcreteCodecs.responsePacket (m := m) input =
      pure (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) := by
    apply RustT.ext
    rw [AdapterPublicConcreteCodecs.response_source, RustT.run_pure]
  have grouped : AdapterPublicFinishBody.active (m := m) self pending prekey oneTime kem input = (do
      let packet ← AdapterPublicConcreteCodecs.responsePacket input
      let authenticated ← ChildOperations.authenticateResponse pending packet
      match authenticated with
      | .Err control => pure (.None, { self with state := .Aborted control })
      | .Ok authenticated => accepted self prekey oneTime kem authenticated) := by
    simp only [AdapterPublicFinishBody.active, AdapterPublicConcreteCodecs.responsePacket, bind_assoc, accepted]
    rfl
  rw [grouped, parsed]
  simp only [pure_bind, RustT.run_bind, AdapterPublicWrapperChildNative.response]
  apply bind_congr
  intro reply
  cases reply with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

omit children in
theorem source (native : QueryImpl RegistrationAuthenticationExecutor.Spec m)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) :
    letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication native parseEd verifyEd) recording writer
    letI : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
    (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration (m := RustT m) self input).run =
      match self.state with
      | .InitSent pending prekey oneTime kem =>
          match pending.aborted_state with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok control => do
              let reply ← simulateQ native (RegistrationResponseExecutor.begin pending
                (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
              after {self with state := .Aborted control} prekey oneTime kem reply
      | _ => pure (.ok (.None, self)) := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication native parseEd verifyEd) recording writer
  let : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
  change (beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration (m := RustT m) self input).run = _
  rw [AdapterPublicFinishBody.source]
  unfold AdapterPublicFinishBody.program
  cases state : self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control => rfl
  | InitSent pending prekey oneTime kem =>
      simp only [RustT.run_bind, RustT.run_liftRust]
      cases aborted : pending.aborted_state with
      | fail error | div => simp only [pure_bind]
      | ok control =>
          simp only [pure_bind]
          exact active native parseEd verifyEd recording writer {self with state := .Aborted control} pending prekey oneTime kem input
end BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication.active

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication.source

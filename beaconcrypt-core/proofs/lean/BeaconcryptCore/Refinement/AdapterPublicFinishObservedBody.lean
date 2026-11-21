-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicFinishAuthentication
import BeaconcryptCore.AdapterPublicFinishObservedExtraction
/-! The actual extracted public Beacon finish wrapper factors through its literal early Aborted update before decoding, actual response authentication, actual source agreement executor, initial HKDF and first-open/install loop. Every stored phase, primitive error, private key capture and returned object field is retained. No codec, primitive or whole agreement correspondence premise is used in this source-body equality. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody
open BeaconcryptCore.Computational
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
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.CryptoOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]
variable [codec : Codecs (RustT m)] [children : ChildOperations (RustT m)]
abbrev Result := core.option.Option (alloc.vec.Vec U8) × beaconcrypt_public_wrapper.beacon.Beacon

variable (completion :beaconcrypt_public_wrapper.beacon.Beacon→agreement.BeaconAgreement→RustT m Result)

def fromAgreement (self :beaconcrypt_public_wrapper.beacon.Beacon) (effect :agreement.AgreementEffect) :RustT m Result :=
  match effect with
  | .Rejected (.Some control)=>pure (.None,{self with state:=.Aborted control})
  | .BeaconComplete agreed=>completion self agreed
  | _=>pure (.None,self)
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
      fromAgreement completion self finished

noncomputable def program (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) : RustT m Result := do
  match self.state with
  | .InitSent pending prekey oneTime kem =>
      let aborted ← liftRust pending.aborted_state
      active completion { self with state := .Aborted aborted } pending prekey oneTime kem input
  | _ => pure (.None, self)


omit localOps platform in
theorem source (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8) :
    AdapterPublicFinishObservedRequest.run (m:=RustT m) completion self input=program completion self input :=by
  cases state:self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control=>
    simp only [AdapterPublicFinishObservedRequest.run,program,state,call_apply,call_result,lift_ok]
  | InitSent pending prekey oneTime kem=>
    simp only [AdapterPublicFinishObservedRequest.run,program,state,call_apply,call_result,registration.BeaconPending.aborted_state,
      pqxdh.beacon_abort_init,core.mem.replace,Aeneas.Std.core.mem.replace,lift_ok,pure_bind,active,
      beaconcrypt_public_request.beacon.Beacon.identity_sk]
    apply bind_congr
    intro parsed
    apply bind_congr
    intro packet
    apply bind_congr
    intro authenticated
    cases authenticated with
    | Err control=>rfl
    | Ok authenticated=>
      apply bind_congr
      intro effect
      apply bind_congr
      intro finished
      cases finished with
      | Rejected aborted=>cases aborted <;>rfl
      | _=>rfl

omit completion in
theorem literal (self :beaconcrypt_public_wrapper.beacon.Beacon) (input :Slice U8) :
    AdapterPublicFinishObservedRequest.run (m:=RustT m) AdapterPublicFinishBody.beginOpen self input=
      beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration (m:=RustT m) self input :=by
  rw [source,AdapterPublicFinishBody.source]
  rfl

variable {E :Type}

noncomputable def accepted (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (authenticated : registration.AuthenticatedResponse) : RustT m AdapterPublicFinishBody.Result := do
  let effect ← liftRust (agreement.begin_beacon_agreement authenticated)
  let finished ← beaconcrypt_public_request.pqxdh.execute_beacon_agreement effect
    ⟨self.identity_key.secret_key, .Some prekey.secret_key, .Some oneTime.secret_key, .Some kem.secret_key⟩
  fromAgreement completion self finished

noncomputable def after (self : beaconcrypt_public_wrapper.beacon.Beacon)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (reply : RustM RegistrationResponseExecutor.ResponseResult) : m (RustM AdapterPublicFinishBody.Result) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err control) => pure (.ok (.None, {self with state := .Aborted control}))
  | .ok (.Ok authenticated) => (accepted completion self prekey oneTime kem authenticated).run

omit children codec localOps platform in
theorem active_auth (native : QueryImpl RegistrationAuthenticationExecutor.Spec m)
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
    (active completion self pending prekey oneTime kem input).run = (do
      let reply ← simulateQ native (RegistrationResponseExecutor.begin pending
        (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
      after completion self prekey oneTime kem reply) := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication native parseEd verifyEd) recording writer
  let : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
  change (active completion self pending prekey oneTime kem input).run = (do
    let reply ← simulateQ native (RegistrationResponseExecutor.begin pending
      (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
    after completion self prekey oneTime kem reply)
  have parsed : AdapterPublicConcreteCodecs.responsePacket (m := m) input =
      pure (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)) := by
    apply RustT.ext
    rw [AdapterPublicConcreteCodecs.response_source, RustT.run_pure]
  have grouped : active completion self pending prekey oneTime kem input = (do
      let packet ← AdapterPublicConcreteCodecs.responsePacket input
      let authenticated ← ChildOperations.authenticateResponse pending packet
      match authenticated with
      | .Err control => pure (.None, { self with state := .Aborted control })
      | .Ok authenticated => accepted completion self prekey oneTime kem authenticated) := by
    simp only [active, AdapterPublicConcreteCodecs.responsePacket, bind_assoc, accepted]
  rw [grouped, parsed]
  simp only [pure_bind, RustT.run_bind, AdapterPublicWrapperChildNative.response]
  apply bind_congr
  intro reply
  cases reply with
  | fail error | div => rfl
  | ok result => cases result <;> rfl

omit children codec localOps platform in
theorem authentication (native : QueryImpl RegistrationAuthenticationExecutor.Spec m)
    (parseEd : Slice U8 → m (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → m (RustM (core.option.Option (alloc.vec.Vec U8))))
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8) :
    letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication native parseEd verifyEd) recording writer
    letI : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
    (AdapterPublicFinishObservedRequest.run (m:=RustT m) completion self input).run =
      match self.state with
      | .InitSent pending prekey oneTime kem =>
          match pending.aborted_state with
          | .fail error => pure (.fail error)
          | .div => pure .div
          | .ok control => do
              let reply ← simulateQ native (RegistrationResponseExecutor.begin pending
                (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)))
              after completion {self with state := .Aborted control} prekey oneTime kem reply
      | _ => pure (.ok (.None, self)) := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication native parseEd verifyEd) recording writer
  let : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
  change (AdapterPublicFinishObservedRequest.run (m:=RustT m) completion self input).run = _
  rw [source]
  unfold program
  cases state : self.state with
  | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control => rfl
  | InitSent pending prekey oneTime kem =>
      simp only [RustT.run_bind, RustT.run_liftRust]
      cases aborted : pending.aborted_state with
      | fail error | div => simp only [pure_bind]
      | ok control =>
          simp only [pure_bind]
          exact active_auth completion native parseEd verifyEd recording writer {self with state := .Aborted control} pending prekey oneTime kem input
end BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.source

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.literal

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.active_auth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.active_auth

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishObservedBody.authentication

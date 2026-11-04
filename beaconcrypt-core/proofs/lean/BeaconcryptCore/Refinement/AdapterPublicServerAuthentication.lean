-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody
import BeaconcryptCore.Refinement.AdapterPublicConcreteCodecs
import BeaconcryptCore.Refinement.AdapterPublicWrapperChildNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual public Server authentication prefix uses the complete concrete source decoder and actual native authentication controller with distinct source Ed parse/open operations. It retains the literal source pin getter and every failed/rejected reply, before any replay reservation or agreement. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAuthentication
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m] {E : Type}
variable [localOps : LocalOperations (RustT m)] [crypto : CryptoOperations (RustT m)]

omit material platform ed localOps crypto in
def observed (control : pqxdh.ServerState)
    (reply : RustM (List RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) :
    RustM (core.option.Option peer.RegistrationLookup) := do
  let authenticated ← AdapterInitAuthenticationDriver.observe reply
  match authenticated with
  | .None => .ok .None
  | .Some authenticated => do
    let lookup ← peer.begin_registration_lookup control authenticated
    .ok (.Some lookup)

omit material platform ed localOps crypto [LawfulMonad m] in
private theorem lift_ok {A : Type} (value : A) : (liftRust (.ok value) : RustT m A) = pure value := rfl

noncomputable def afterPin (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec m)
    (control : pqxdh.ServerState) (packet : registration.InitPacket)
    (reply : RustM (core.option.Option session.ServerAuthenticationPin)) :
    m (RustM (core.option.Option peer.RegistrationLookup)) :=
  match reply with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok .None)
  | .ok (.Some pin) => observed control <$>
      simulateQ (native ∘ₛ AdapterInitAuthenticationStateful.abstractNative)
        (RegistrationAuthenticationExecutor.begin pin packet)

theorem authenticate (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) :
    letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
    letI : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
    (AdapterPublicServerAcceptBody.authenticate (m := m) self input).run =
      (match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
      | .none => pure (.ok .None)
      | .some packet => do
        let reply ← (beaconcrypt_public_request.server.Server.authentication_pin (m := RustT m) self).run
        afterPin native self.control packet reply) := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
  let : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
  have grouped : AdapterPublicServerAcceptBody.authenticate (m := m) self input = (do
      let packet ← AdapterPublicConcreteCodecs.initPacket input
      match packet with
      | .none => pure .None
      | .some packet =>
        let pin ← beaconcrypt_public_request.server.Server.authentication_pin self
        match pin with
        | .None => pure .None
        | .Some pin =>
          let authenticated ← ChildOperations.authenticateInit pin packet
          match authenticated with
          | .none => pure .None
          | .some authenticated => do
            let lookup ← liftRust (peer.begin_registration_lookup self.control authenticated)
            pure (.Some lookup)) := by
    simp only [AdapterPublicServerAcceptBody.authenticate, AdapterPublicConcreteCodecs.initPacket, bind_assoc]
    apply bind_congr
    intro parsed
    cases parsed <;> simp only [pure_bind]
    rfl
  have parsed : AdapterPublicConcreteCodecs.initPacket (m := m) input =
      pure (RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input)) := by
    apply RustT.ext
    rw [AdapterPublicConcreteCodecs.init_source, RustT.run_pure]
  rw [grouped, parsed]
  simp only [pure_bind]
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => rfl
  | some packet =>
    simp only [RustT.run_bind]
    apply bind_congr
    intro pinReply
    cases pinReply with
    | fail error | div => rfl
    | ok pin => cases pin with
      | none => rfl
      | some pin =>
        simp only [RustT.run_bind]
        rw [AdapterPublicWrapperChildNative.init native recording writer pin packet]
        simp only [bind_map_left, afterPin, bind_pure_comp]
        conv_rhs => rw [← bind_pure_comp]
        apply bind_congr
        intro reply
        cases reply with
        | fail error | div => rfl
        | ok result =>
          rcases result with ⟨events, state⟩
          cases state <;> first
          | rfl
          | simp [observed, AdapterInitAuthenticationDriver.observe, AdapterInitAuthenticationStateful.stateOption,
              peer.begin_registration_lookup, lift_ok, RustT.run_pure]

theorem source (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec m)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec m)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) m)
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) :
    letI : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
    letI : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
    (beaconcrypt_public_request.server.Server.authenticate_registration_lookup (m := RustT m) self input).run =
      (match RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
      | .none => pure (.ok .None)
      | .some packet => do
        let reply ← (beaconcrypt_public_request.server.Server.authentication_pin (m := RustT m) self).run
        afterPin native self.control packet reply) := by
  let : ChildOperations (RustT m) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
  let : Codecs (RustT m) := AdapterPublicConcreteCodecs.codecs
  rw [AdapterPublicServerAcceptBody.authenticate_source]
  exact authenticate native recording writer self input
end BeaconcryptCore.Refinement.AdapterPublicServerAuthentication

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthentication.authenticate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthentication.authenticate

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthentication.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthentication.source

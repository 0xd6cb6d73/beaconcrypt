-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAuthentication
import BeaconcryptCore.Refinement.RegistrationAuthenticationReparse
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
/-! Every lookup actually returned by the full SDK authentication prefix carries the source Ed reparse receipt for its original bound Beacon identity. Decoder rejection, pin failure and every authentication rejection remain in the source program; the receipt is derived only from its actual returned capability. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {S E : Type}
variable [localOps : LocalOperations (RustT (StateT S ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT S ProbComp))]
attribute [local irreducible] RegistrationAuthenticationExecutor.begin RegistrationAuthenticationExecutor.execute
attribute [local irreducible] beaconcrypt_public_request.server.Server.authenticate_registration_lookup

theorem source (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp))
    (parser : RegistrationAuthenticationReparse.Parser native)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT S ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S ProbComp))
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) :
    letI : ChildOperations (RustT (StateT S ProbComp)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
    letI : Codecs (RustT (StateT S ProbComp)) := AdapterPublicConcreteCodecs.codecs
    ∀ lookup before after, (.ok (.Some lookup), after) ∈ support
      (((beaconcrypt_public_request.server.Server.authenticate_registration_lookup
        (m := RustT (StateT S ProbComp)) self input).run).run before) →
      ∃ publicKey, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
        lookup.authenticated.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) := by
  let : ChildOperations (RustT (StateT S ProbComp)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
  let : Codecs (RustT (StateT S ProbComp)) := AdapterPublicConcreteCodecs.codecs
  intro lookup before after supported
  rw [AdapterPublicServerAuthentication.source native recording writer self input] at supported
  cases decoded : RegistrationNativeConcreteCodec.wire.decodeInit (TranscriptAuthParts.absSlice input) with
  | none => simp only [RustM.ok.injEq, core.option.Option.Some, core.option.Option.None, decoded, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | some packet =>
    simp only [decoded, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨pinReply, middle⟩, _pinCalled, continued⟩ := supported
    cases pinReply with
    | fail error | div => simp only [core.option.Option.Some, AdapterPublicServerAuthentication.afterPin, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
    | ok optional => cases optional with
      | none => simp only [RustM.ok.injEq, core.option.Option.Some, core.option.Option.None, AdapterPublicServerAuthentication.afterPin, StateT.run_pure,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
      | some pin =>
        simp only [AdapterPublicServerAuthentication.afterPin, StateT.run_map, support_map] at continued
        obtain ⟨⟨reply, current⟩, queried, returned⟩ := continued
        cases reply with
        | fail error | div => simp [AdapterPublicServerAuthentication.observed, AdapterInitAuthenticationDriver.observe, bind_tc_fail, bind_tc_div] at returned
        | ok answer =>
          rcases answer with ⟨events, state⟩
          cases state <;>
            simp [AdapterPublicServerAuthentication.observed, AdapterInitAuthenticationDriver.observe,
              AdapterInitAuthenticationStateful.stateOption, bind_tc_ok, Prod.mk.injEq,
              RustM.ok.injEq, reduceCtorEq] at returned
          case Accepted authenticated =>
            have same : lookup.authenticated = authenticated := by
              have output : ({ control := self.control, authenticated := authenticated } : peer.RegistrationLookup) = lookup := by
                simpa only [peer.begin_registration_lookup, bind_tc_ok, RustM.ok.injEq, core.option.Option.Some, _root_.Option.some.injEq] using returned.1
              exact congrArg peer.RegistrationLookup.authenticated output.symm
            rw [same]
            exact RegistrationAuthenticationReparse.reparse native parser pin packet events authenticated middle current queried
end BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationReceipt.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationReceipt.source

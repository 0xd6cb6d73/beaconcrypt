-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementSourceBinding
import BeaconcryptCore.Refinement.AdapterPublicServerAuthenticationReceipt
import BeaconcryptCore.Refinement.PeerOwnership
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Successful actual source replay insertion retains the authenticated identity parse receipt. The selected per-primitive agreement interpretation supplies binding preservation; container failures and all shared poststates remain literal source operations. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementPrimitiveModel (Model)
open AdapterPublicServerToken (ParsedBinding ParsedToken)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {S : Type}
variable [crypto : CryptoOperations (RustT (StateT S ProbComp))]
variable [containers : ContainerOperations (RustT (StateT S ProbComp))]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {R Error : Type} {generator : rand_core.TryCryptoRng R Error}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK} {checks : PqxdhServerAuthExperiment.Checks}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

omit crypto in
theorem record_completed (self : beaconcrypt_public_wrapper.server.Server) (rng nextRng : R)
    (effect : agreement.AgreementEffect) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : S)
    (supported : (.ok (.Some token, current, nextRng), after) ∈ support
      (((AdapterPublicServerAcceptBody.record (m := StateT S ProbComp) self rng effect).run).run before)) :
    ∃ completed, effect = .ServerComplete completed ∧ token.registration.agreement = completed := by
  cases effect <;> try { simp only [AdapterPublicServerAcceptBody.record, RustT.run_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq,
    reduceCtorEq, false_and] at supported }
  case ServerComplete completed =>
    exact ⟨completed, rfl, (AdapterPublicServerToken.record_token self rng nextRng completed token current before after supported).1⟩

omit containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] platform in
theorem execute_binding (model : Model (m := StateT S ProbComp) generator setup checks view) (keys : Keys)
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit)
    (phase : agreement.AgreementEffect)
    (started : agreement.begin_server_agreement control .Fresh authenticated = .ok phase)
    (completed : agreement.ServerAgreement) (rng nextRng : R) (before after : S)
    (supported : (.ok (.ServerComplete completed, nextRng), after) ∈ support
      (((beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT (StateT S ProbComp))
        generator phase keys rng).run).run before)) :
    completed.binding = authenticated.binding := by
  apply AdapterPublicAgreementSourceBinding.server_binding model keys control .Fresh authenticated completed rng nextRng before after
  rw [← AdapterPublicAgreementSourceEntries.server, started, lift_ok, pure_bind]
  exact supported

omit crypto containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
private theorem identity_sk (self : beaconcrypt_public_wrapper.server.Server) :
    beaconcrypt_public_request.server.Server.identity_sk (m := RustT (StateT S ProbComp)) self =
      pure (platform.arcView self.identity).identity_key.secret_key := by
  rfl

noncomputable section
theorem reserved_parsed (model : Model (m := StateT S ProbComp) generator setup checks view)
    (self : beaconcrypt_public_wrapper.server.Server) (control : pqxdh.ServerState)
    (authenticated : registration.AuthenticatedInit) (phase : agreement.AgreementEffect)
    (started : agreement.begin_server_agreement control .Fresh authenticated = .ok phase)
    (parsed : ParsedBinding authenticated.binding)
    (rng nextRng : R) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : S)
    (supported : (.ok (.Some token, current, nextRng), after) ∈ support
      (((AdapterPublicServerAcceptBody.reserved (m := StateT S ProbComp) generator self rng phase).run).run before)) :
    ParsedToken token := by
  simp only [AdapterPublicServerAcceptBody.reserved, RustT.run_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨allocationReply, middle⟩, _allocated, continued⟩ := supported
  cases allocationReply with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok pair =>
    rcases pair with ⟨allocation, history⟩
    cases allocation with
    | Err error => simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
    | Ok _reserved =>
      dsimp only at continued
      rw [identity_sk, pure_bind] at continued
      simp only [RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨⟨agreementReply, agreedState⟩, agreed, recorded⟩ := continued
      cases agreementReply with
      | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, reduceCtorEq, false_and] at recorded
      | ok pair =>
        rcases pair with ⟨effect, updatedRng⟩
        obtain ⟨completed, same, tokenSame⟩ := record_completed _ updatedRng nextRng effect token current agreedState after recorded
        cases same
        unfold ParsedToken
        rw [tokenSame]
        rw [execute_binding model _ control authenticated phase started completed rng updatedRng middle agreedState agreed]
        exact parsed

theorem lookup_parsed (model : Model (m := StateT S ProbComp) generator setup checks view)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup)
    (parsed : ParsedBinding pending.authenticated.binding)
    (rng nextRng : R) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : S)
    (supported : (.ok (.Some token, current, nextRng), after) ∈ support
      (((AdapterPublicServerAcceptBody.acceptLookup (m := StateT S ProbComp) generator self pending rng).run).run before)) :
    ParsedToken token := by
  obtain ⟨identifier, requested, _canonical⟩ := PeerOwnership.registration_lookup_request_bytes pending
  simp only [AdapterPublicServerAcceptBody.acceptLookup, requested,
    pqxdh.RegistrationId.as_bytes, lift_ok, pure_bind, RustT.run_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨membership, middle⟩, _queried, continued⟩ := supported
  cases membership with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok consumed =>
    dsimp only at continued
    cases consumed with
    | true =>
      simp only [peer.RegistrationLookup.resume, ↓reduceIte, lift_ok, pure_bind,
        RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
    | false =>
      obtain ⟨phase, started⟩ : ∃ phase, agreement.begin_server_agreement pending.control .Fresh pending.authenticated =
          .ok (.GenerateEphemeral phase) := by
        rw [(BeaconcryptCore.Refinement.KeyAgreement.server_entry_refines pending.control pending.authenticated).2]
        simp only [agreement.AgreementState.new, ratchet.RatchetChain.from_bytes, bind_tc_ok]
        exact ⟨_, rfl⟩
      simp only [peer.RegistrationLookup.resume, Bool.false_eq_true, ↓reduceIte, started,
        lift_ok] at continued
      exact reserved_parsed model self pending.control pending.authenticated (.GenerateEphemeral phase) started
        parsed rng nextRng token current middle after continued
theorem source_lookup_parsed (model : Model (m := StateT S ProbComp) generator setup checks view)
    (self : beaconcrypt_public_wrapper.server.Server) (pending : peer.RegistrationLookup)
    (parsed : ParsedBinding pending.authenticated.binding)
    (rng nextRng : R) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : S)
    (supported : (.ok (.Some token, current, nextRng), after) ∈ support
      (((beaconcrypt_public_request.server.Server.get_shared_secret_from_lookup_with_rng
        (m := RustT (StateT S ProbComp)) generator self pending rng).run).run before)) :
    ParsedToken token := by
  rw [AdapterPublicServerAcceptBody.accept_lookup_source] at supported
  exact lookup_parsed model self pending parsed rng nextRng token current before after supported

section Authenticated
variable [localOps : LocalOperations (RustT (StateT S ProbComp))]
variable [children : ChildOperations (RustT (StateT S ProbComp))] [codecs : Codecs (RustT (StateT S ProbComp))]

section Binding
attribute [local irreducible] RegistrationAuthenticationExecutor.begin RegistrationAuthenticationExecutor.execute
attribute [local irreducible] beaconcrypt_public_request.server.Server.authenticate_registration_lookup

omit children codecs containers [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
set_option backward.isDefEq.respectTransparency true in
/-- Every lookup returned by the SDK authentication prefix carries the parser receipt for the identity copied from its pending binding's owned Init fields, the exact key the actual Ed parser admitted. -/
theorem authenticated_binding {E : Type}
    (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp))
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
      ParsedBinding lookup.authenticated.binding := by
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
            exact ⟨authenticated.registration.beacon_identity_public_key,
              RegistrationAuthenticationReparse.binding_identity _ pin packet events authenticated middle current queried,
              RegistrationAuthenticationReparse.reparse native parser pin packet events authenticated middle current queried⟩
end Binding

noncomputable def sequence (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) :
    RustT (StateT S ProbComp)
      (core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R) := do
  let authenticated ← beaconcrypt_public_request.server.Server.authenticate_registration_lookup self input
  match authenticated with
  | .None => pure (.None, self, rng)
  | .Some pending => beaconcrypt_public_request.server.Server.get_shared_secret_from_lookup_with_rng generator self pending rng

omit children codecs in
theorem sequence_parsed {E : Type}
    (model : Model (m := StateT S ProbComp) generator setup checks view)
    (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp))
    (parser : RegistrationAuthenticationReparse.Parser native)
    (recording : QueryImpl AdapterRecordRequestMonad.Spec (StateT S ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT S ProbComp))
    (self : beaconcrypt_public_wrapper.server.Server) (input : Slice U8) (rng : R) :
    letI : ChildOperations (RustT (StateT S ProbComp)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
    letI : Codecs (RustT (StateT S ProbComp)) := AdapterPublicConcreteCodecs.codecs
    ∀ token current nextRng before after, (.ok (.Some token, current, nextRng), after) ∈ support
      (((sequence (S := S) (generator := generator) self input rng).run).run before) → ParsedToken token := by
  let : ChildOperations (RustT (StateT S ProbComp)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.normalAuthentication native) recording writer
  let : Codecs (RustT (StateT S ProbComp)) := AdapterPublicConcreteCodecs.codecs
  intro token current nextRng before after supported
  simp only [sequence, RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨authenticated, middle⟩, checked, continued⟩ := supported
  cases authenticated with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok reply => cases reply with
    | none => simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
    | some pending =>
      have parsed : ParsedBinding pending.authenticated.binding :=
        authenticated_binding native parser recording writer self input pending before middle checked
      exact source_lookup_parsed model self pending parsed rng nextRng token current middle after continued
end Authenticated

end
end BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.record_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.record_completed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.execute_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.execute_binding

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.reserved_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.reserved_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.lookup_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.lookup_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.source_lookup_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.source_lookup_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.authenticated_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.authenticated_binding

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.sequence_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerAcceptReceipt.sequence_parsed

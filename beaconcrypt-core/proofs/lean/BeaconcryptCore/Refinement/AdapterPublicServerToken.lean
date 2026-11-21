-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerAcceptBody
import BeaconcryptCore.Refinement.PeerOwnership
import BeaconcryptCore.Refinement.RegistrationAuthenticationReparse
import BeaconcryptCore.Computational.RegistrationAgreementMetadata
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual replay insertion returns the original complete agreement and registration identifier in its SDK token. A parsed-identity receipt can therefore be retained across this move without validating arbitrary caller-created tokens. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerToken
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open BeaconcryptCore.Computational
private theorem lift_ok {m : Type → Type} [Monad m] {A : Type} (value : A) :
    (AdapterRecordRequestMonad.liftRust (.ok value) : RustT m A) = pure value := rfl
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [primitive : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [containers : ContainerOperations (RustT m)]

noncomputable def result {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (completed : agreement.ServerAgreement) (inserted : Bool) (history : AdapterPublicWrapperStorage.ReplaySet) :
    core.option.Option beaconcrypt_public_wrapper.server.RegistrationOutput × beaconcrypt_public_wrapper.server.Server × R :=
  (if inserted then .Some ⟨⟨completed⟩, completed.pending.registration_id.bytes⟩ else .None,
    { self with consumed_registrations := history }, rng)

theorem record {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng : R) (completed : agreement.ServerAgreement) :
    AdapterPublicServerAcceptBody.record (m := m) self rng (.ServerComplete completed) = (do
      let (inserted, history) ← AdapterPublicServerAcceptBody.setInsert self.consumed_registrations completed.pending.registration_id.bytes
      pure (result self rng completed inserted history)) := by
  simp only [AdapterPublicServerAcceptBody.record, peer.begin_registration_insert,
    PeerOwnership.registration_insert_request, pqxdh.RegistrationId.as_bytes, lift_ok, pure_bind]
  apply bind_congr
  rintro ⟨inserted, history⟩
  cases inserted <;> simp only [PeerOwnership.registration_insert_resume, lift_ok, pure_bind, result] <;> rfl

omit containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
def ParsedKey (key : Std.Array U8 32#usize) : Prop :=
  ∃ publicKey, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes key.to_slice = .ok (.Ok publicKey)

omit containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
/-- A pending token retains the actual identity-copy request together with the parser receipt for that exact key. -/
def ParsedBinding (binding : session.RegistrationBinding) : Prop :=
  ∃ key, authentication.OwnedInitFields.identity_public_key binding.init_fields = .ok key ∧ ParsedKey key

omit material platform containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem completed_parsed (pending : session.RegistrationBinding) (digest : Std.Array U8 64#usize)
    (completed : session.CompletedRegistrationBinding) (resumed : pending.complete digest = .ok completed)
    (parsed : ParsedBinding pending) : ParsedKey completed.beacon_identity_public_key := by
  obtain ⟨key, copied, admitted⟩ := parsed
  have exactCopy := SessionBinding.complete_identity pending digest completed resumed
  have same : key = completed.beacon_identity_public_key := RustM.ok.inj (copied.symm.trans exactCopy)
  exact same ▸ admitted

omit containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
def ParsedToken (token : beaconcrypt_public_wrapper.server.RegistrationOutput) : Prop :=
  ParsedBinding token.registration.agreement.binding

omit containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem result_token {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (completed : agreement.ServerAgreement) (inserted : Bool) (history : AdapterPublicWrapperStorage.ReplaySet)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (returned : (result self rng completed inserted history).1 = .Some token) :
    token.registration.agreement = completed ∧ token.registration_id = completed.pending.registration_id.bytes := by
  cases inserted with
  | false => simp only [result, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at returned
  | true =>
    change core.option.Option.Some (⟨⟨completed⟩, completed.pending.registration_id.bytes⟩ : beaconcrypt_public_wrapper.server.RegistrationOutput) = core.option.Option.Some token at returned
    injection returned with same
    cases same
    exact ⟨rfl, rfl⟩

omit containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem result_parsed {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (completed : agreement.ServerAgreement) (inserted : Bool) (history : AdapterPublicWrapperStorage.ReplaySet)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (returned : (result self rng completed inserted history).1 = .Some token)
    (parsed : ParsedBinding completed.binding) : ParsedToken token := by
  unfold ParsedToken
  rw [(result_token self rng completed inserted history token returned).1]
  exact parsed

section Supported
variable {S : Type} [stateContainers : ContainerOperations (RustT (StateT S ProbComp))]

omit containers [Monad m] [LawfulMonad m] in
theorem record_token {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng nextRng : R)
    (completed : agreement.ServerAgreement) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : S)
    (supported : (.ok (.Some token, current, nextRng), after) ∈ support
      (((AdapterPublicServerAcceptBody.record (m := StateT S ProbComp) self rng (.ServerComplete completed)).run).run before)) :
    token.registration.agreement = completed ∧ token.registration_id = completed.pending.registration_id.bytes := by
  rw [record self rng completed] at supported
  simp only [RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, _called, returned⟩ := supported
  cases reply with
  | fail error | div =>
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at returned
  | ok pair =>
      rcases pair with ⟨inserted, history⟩
      simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at returned
      have same := RustM.ok.inj (congrArg Prod.fst returned)
      exact result_token self rng completed inserted history token (congrArg Prod.fst same).symm

omit containers [Monad m] [LawfulMonad m] in
theorem record_parsed {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng nextRng : R)
    (completed : agreement.ServerAgreement) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (current : beaconcrypt_public_wrapper.server.Server) (before after : S)
    (supported : (.ok (.Some token, current, nextRng), after) ∈ support
      (((AdapterPublicServerAcceptBody.record (m := StateT S ProbComp) self rng (.ServerComplete completed)).run).run before))
    (parsed : ParsedBinding completed.binding) : ParsedToken token := by
  unfold ParsedToken
  rw [(record_token self rng nextRng completed token current before after supported).1]
  exact parsed
end Supported

section Agreement
variable {S : Type}

omit containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] material platform in
theorem agreement_parsed (implementation : QueryImpl RegistrationAgreementExecutor.Spec (StateT S ProbComp))
    (control : pqxdh.ServerState) (status : pqxdh.RegistrationStatus) (authenticated : registration.AuthenticatedInit)
    (completed : agreement.ServerAgreement) (before after : S)
    (supported : (.ok (.ServerComplete completed), after) ∈ support
      ((simulateQ implementation (RegistrationAgreementExecutor.server control status authenticated)).run before))
    (parsed : ParsedBinding authenticated.binding) :
    ParsedBinding completed.binding := by
  rw [RegistrationAgreementExecutor.interpreted_server_binding implementation before after control status authenticated completed supported]
  exact parsed

omit containers [Monad m] [LawfulMonad m] [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] material platform primitive in
theorem lookup_program (pending : peer.RegistrationLookup) (consumed : Bool) :
    RegistrationAgreementExecutor.continueWith (pending.resume consumed) (RegistrationAgreementExecutor.drive 9) =
      RegistrationAgreementExecutor.server pending.control (if consumed then .Consumed else .Fresh) pending.authenticated := by
  cases consumed <;> rfl
end Agreement
end BeaconcryptCore.Refinement.AdapterPublicServerToken

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.record

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.result_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.result_token

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.result_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.result_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.record_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.record_token

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.record_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.record_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.agreement_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.agreement_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.lookup_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.lookup_program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerToken.completed_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerToken.completed_parsed

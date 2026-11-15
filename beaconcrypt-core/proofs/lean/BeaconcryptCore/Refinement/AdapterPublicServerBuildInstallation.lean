-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerInstallStateful
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! A successful actual SDK response builder installs the original token binding with the source sequence-one advanced kernel and the exact serialized response. Its source Ed reparse receipt is derived from the authenticated token and actual source continuations. Allocation, crypto, signing and serialization are not assumed successful: the theorem starts from an actual supported successful enclosing call and exposes the same reached continuation states. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildInstallation
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildBody (Server)
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {State : Type} [localOps : LocalOperations (RustT (StateT State ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT State ProbComp))]
variable [containers : ContainerOperations (RustT (StateT State ProbComp))]
variable [children : ChildOperations (RustT (StateT State ProbComp))]

theorem source (operations : AdapterPublicServerPublication.Primitives (StateT State ProbComp))
    (self : Server) (contract : AdapterPublicServerPublication.Contract operations self)
    (kdf : AdapterPublicServerRecord.Kdf (StateT State ProbComp))
    (kdfContract : AdapterPublicServerRecord.KdfContract kdf)
    (token : beaconcrypt_public_wrapper.server.RegistrationOutput) (parsed : AdapterPublicServerToken.ParsedToken token)
    (data : core.option.Option (Slice U8)) (response : beaconcrypt_public_wrapper.server.RegResponse)
    (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT (StateT State ProbComp)) self token data).run).run before)) :
    ∃ digest binding initial known beforeRecord published beforeInstall pending publicKey,
      token.registration.agreement.binding.complete digest = .ok binding ∧
      initial.binding = binding ∧
      initial.candidate.previous_state = self.control ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.record (m := StateT State ProbComp) { self with known_ids := known } initial).run).run beforeRecord) ∧
      (.ok (.Ok published), beforeInstall) ∈ support
        ((AdapterPublicServerRecordReceipt.completion operations kdf initial).run beforeRecord) ∧
      peer.begin_peer_insert self.control published = .ok (.Ok pending) ∧
      beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.install (m := StateT State ProbComp) { self with known_ids := known } pending).run).run beforeInstall) ∧
      pending.previous = self.control ∧ pending.next = initial.candidate.next_state ∧
      pending.peer.binding = RegistrationPublication.completedBinding binding initial.candidate.key_id ∧
      (∃ selected : ratchet.concrete.SendSeal record_effects.SealFrameContext,
        pending.peer.ratchet = selected.advanced ∧ selected.sequence.val = 1 ∧
        selected.context.associated_data = binding.associated_data) ∧
      response.serialized = pending.encoded ∧ response.kid = pending.peer.binding.assigned_key_id ∧
      current.control = pending.next ∧ current.identity = self.identity ∧
      current.consumed_registrations = self.consumed_registrations := by
  obtain ⟨digest, binding, initial, known, beforeRecord, completedBinding, bindingSame, previous, recorded⟩ :=
    AdapterPublicServerBuildReceipt.actual self token data response current before after supported
  have initialParsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key := by
    rw [bindingSame]
    exact AdapterPublicServerToken.completed_parsed token.registration.agreement.binding digest binding completedBinding parsed
  have contractCurrent : AdapterPublicServerPublication.Contract operations { self with known_ids := known } := ⟨AdapterPublicServerPublication.Contract.hash (self := self) contract, AdapterPublicServerPublication.Contract.sign (self := self) contract⟩
  obtain ⟨published, beforeInstall, pending, publication, began, reparsed, installed⟩ :=
    AdapterPublicServerRecordReceipt.parsed operations { self with known_ids := known } contractCurrent kdf kdfContract initial
      response current beforeRecord after recorded initialParsed
  obtain ⟨publicKey, parsedKey⟩ := reparsed
  have retained := RegistrationServerSourceCompletionReceipt.stateful _ _ _ _ _ _ initial
    (.ok (.Ok published)) beforeRecord beforeInstall publication
  obtain ⟨result, actual, fields⟩ := PeerOwnership.peer_insert_begin_retains self.control published
  have same : result = .Ok pending := RustM.ok.inj (actual.symm.trans began)
  rw [same] at fields
  obtain ⟨selected, kernelSame, sequence, adSame⟩ := retained.2.2
  obtain ⟨vacant, back, changed, insertedBack, _entryState, _lookedUp, _inserted, bytesSame, identifierSame, returnedSelf⟩ :=
    AdapterPublicServerInstallStateful.success { self with known_ids := known } pending publicKey parsedKey
      response current beforeInstall after installed
  refine ⟨digest, binding, initial, known, beforeRecord, published, beforeInstall, pending, publicKey,
    completedBinding, bindingSame, previous, recorded, publication, began, parsedKey, installed,
    fields.1, fields.2.1.trans retained.1, ?_, ?_, bytesSame, identifierSame, ?_, ?_, ?_⟩
  · rw [fields.2.2.1, retained.2.1, bindingSame]
  · exact ⟨selected, fields.2.2.2.1.trans kernelSame, sequence, by simpa only [bindingSame] using adSame⟩
  · rw [returnedSelf]
  · rw [returnedSelf]
  · rw [returnedSelf]
end BeaconcryptCore.Refinement.AdapterPublicServerBuildInstallation

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildInstallation.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildInstallation.source

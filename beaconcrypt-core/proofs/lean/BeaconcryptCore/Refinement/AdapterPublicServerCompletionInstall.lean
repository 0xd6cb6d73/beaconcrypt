-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerInstallFunctional
import BeaconcryptCore.Refinement.AdapterPublicServerToken
import BeaconcryptCore.Computational.RegistrationServerSourceCompletionReceipt
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual source completion carries its authentication-derived Ed parsing receipt through first-record sealing, mutable commitment hashing, signing, response writing and native insertion setup. The final installer needs only narrow standard container contracts, with no blanket valid-key or parser-success assumption. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperStorage AdapterPublicWrapperState
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

omit material platform in
theorem initial_parsed (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (availability : pqxdh.KeyIdAvailability) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (application : Slice U8) (initial : registration.ServerInitialKdf)
    (began : registration.begin_server_completion control pin availability token.registration.agreement application = .ok (.Ok initial))
    (parsed : AdapterPublicServerToken.ParsedToken token) :
    AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key := by
  rw [RegistrationServerRecordExecutor.initial_binding control pin availability token.registration.agreement application initial began]
  exact parsed

omit material platform in
theorem insertion_parsed {Encoded : Type} (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf)
    (published : registration.PublishedServerResponse Encoded) (pending : peer.PeerInsert Encoded)
    (retained : RegistrationServerSourceCompletionReceipt.Post initial (.ok (.Ok published)))
    (began : peer.begin_peer_insert control published = .ok (.Ok pending))
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key) :
    AdapterPublicServerToken.ParsedKey pending.peer.binding.beacon_identity_public_key := by
  obtain ⟨result, actual, fields⟩ := PeerOwnership.peer_insert_begin_retains control published
  have same : result = .Ok pending := RustM.ok.inj (actual.symm.trans began)
  rw [same] at fields
  rw [fields.2.2.1, RegistrationServerSourceCompletionReceipt.identity initial published retained]
  exact parsed

variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable {State : Type} [containers : ContainerOperations (RustT (StateT State ProbComp))]
variable {mldsaSource : RegistrationNativeMldsa.Source} {KemSK : Type} {n : Nat}

theorem source (view : MaterialView mldsaSource KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mldsaSource)
    (self : beaconcrypt_public_wrapper.server.Server) (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (record : QueryImpl RegistrationRecordPrimitives.Spec (StateT State ProbComp))
    (sealing : record_effects.AeadSealRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → StateT State ProbComp RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → StateT State ProbComp (RustM (core.option.Option (Slice U8))))
    (signing : QueryImpl RegistrationSigningShared.Spec (StateT State ProbComp))
    (encode : registration.SignedResponseView → StateT State ProbComp (RustM (core.option.Option (alloc.vec.Vec U8))))
    (initial : registration.ServerInitialKdf) (published : registration.PublishedServerResponse (alloc.vec.Vec U8))
    (before after : State)
    (supported : (.ok (.Ok published), after) ∈ support
      ((RegistrationServerSourceCompletionReceipt.program record sealing hash write signing encode initial).run before))
    (pending : peer.PeerInsert (alloc.vec.Vec U8))
    (began : peer.begin_peer_insert self.control published = .ok (.Ok pending))
    (parsed : AdapterPublicServerToken.ParsedKey initial.binding.beacon_identity_public_key)
    (standard : ∀ publicKey, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      pending.peer.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) →
      AdapterPublicServerInstallFunctional.Standard (m := StateT State ProbComp) views self pending publicKey) :
    ∃ reply current next,
      AdapterPublicServerBuildBody.install (m := StateT State ProbComp) self pending = pure (reply, current) ∧
      (AdapterPublicServerInstallNative.capability pending).run native = pure (_root_.Option.isSome reply, next) ∧
      Server view views created credential current
        { next with control := if _root_.Option.isSome reply then pending.next else pending.previous } ∧
      (∀ response, reply = .Some response → response.serialized = pending.encoded ∧ response.kid = pending.peer.binding.assigned_key_id) := by
  have retained := RegistrationServerSourceCompletionReceipt.stateful record sealing hash write signing encode initial
    (.ok (.Ok published)) before after supported
  obtain ⟨publicKey, reparsed⟩ := insertion_parsed self.control initial published pending retained began parsed
  exact AdapterPublicServerInstallFunctional.functional view views created credential self native related published pending began
    publicKey reparsed (standard publicKey reparsed)
end BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall.initial_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall.initial_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall.insertion_parsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall.insertion_parsed

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerCompletionInstall.source

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerRecordHistoryOrigin
import BeaconcryptCore.Computational.RegistrationNativeServerHistoryOrigin

/-! Successful native Beacon completion and earlier same-key unsigned response issuance retain their actual same-run source stages. The response's public agreement inputs, ciphertext, assigned identifier and Init hash agree exactly. Both local root/initializer stages are retained; cross-role root equality is a separate good-sample DH/KEM obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCausalRecordContents
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationSigningShared (Receipt)
open RegistrationNativeServerIssuance (history)
open RegistrationNativeMldsaRoleFrame (serverReceipts)
open RegistrationNativeServerRecordHistoryOrigin (SourceAt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

private theorem issued_member (before : Native) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before)))) :
    ∃ receipt ∈ serverReceipts (history before.server),
      receipt.observation.payload = RegistrationResponseExecutor.payload pending packet ∧
      absBytes receipt.observation.publicKey = absBytes pending.binding.server_pin.public_key := by
  obtain ⟨signed, member, samePayload⟩ := issued
  have historyMember : signed ∈ BeaconcryptCore.Refinement.RegistrationSigningTrace.historyFor
      (absBytes pending.binding.server_pin.public_key) ((history before.server).map Receipt.observation) := member
  obtain ⟨observation, observed, key, sameCall⟩ :=
    (BeaconcryptCore.Refinement.RegistrationSigningHistory.history_mem_iff _ _ _).mp historyMember
  obtain ⟨receipt, recorded, sameObservation⟩ := List.mem_map.mp observed
  subst observation
  have content : receipt.observation.payload = RegistrationResponseExecutor.payload pending packet :=
    (congrArg MldsaTranscriptAuth.SigningCall.payload sameCall).trans samePayload
  refine ⟨receipt, List.mem_filter.mpr ⟨recorded, ?_⟩, content, key⟩
  simp only [content, RegistrationResponseExecutor.payload, MldsaTranscriptAuth.responsePayload, decide_true]

attribute [local irreducible] RegistrationNativeExperiment.handler

/-- An actual successful finish with prior unsigned response issuance has an earlier same-run root-bearing Server stage with exact public response contents, together with its actual Beacon completion receipt. -/
theorem path_contents (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)) (final : Native)
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Native) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) ∈ calls)
    (found : beforeFinish.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (issued : MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject beforeFinish)))) :
    RegistrationNativeCompletionReceipt.Receipt beforeFinish.beacons index (some packet) application ∧
      MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash afterFinish.server.world.world.1.primitive.2) source.verify
        (RegistrationResponseExecutor.trial true pending packet (RegistrationSigningShared.historyFor
          (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish))) ∧
      ∃ leading trailing serverCall receipt serverIndex serverInput token current plaintext availability serverInitial hashed,
        calls = leading ++ (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) :: trailing ∧
        serverCall ∈ leading ∧ serverCall.query = .inr (.build serverIndex serverInput) ∧
        RegistrationServerSdkSource.take serverIndex serverCall.before.server = (some token, current) ∧ serverInput = some plaintext ∧
        SourceAt setup wire serverCall receipt ∧ BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext serverInitial ∧
        RegistrationServerRecordExecutor.Path serverInitial hashed ∧
        RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) serverInitial hashed (RegistrationNativeWorldCache.cache serverCall.after) ∧
        hashed.candidate.server_identity_public_key = packet.public.identity_key ∧
        hashed.candidate.ephemeral_public_key = packet.public.ephemeral_key ∧
        hashed.candidate.kem_ciphertext = packet.public.kem_cipher_text ∧ hashed.ciphertext = packet.application ∧
        hashed.candidate.key_id = packet.public.key_id ∧ hashed.binding.init_hash = pending.binding.init_hash ∧
        pqxdh.concrete.start_server_candidate_ratchet_kdf serverInitial.candidate token.agreement.root.bytes = .ok serverInitial.pending := by
  obtain ⟨leading, trailing, split, prefixRun, finished, _suffixRun⟩ := actual.member
    (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) member
  have completed := RegistrationNativeCompletionReceipt.typed_finish setup checks representation initial.created wire route initial.credential
    index (some packet) beforeFinish afterFinish application finished
  have verified := RegistrationNativeResponseFinish.typed_trial setup checks representation initial.created wire route initial.credential
    index owner pending oneTime packet beforeFinish afterFinish application found phase finished true rfl
  obtain ⟨receipt, present, content, _key⟩ := issued_member beforeFinish pending packet issued
  rcases RegistrationNativeServerRecordHistoryOrigin.path_origin setup checks wire route representation initial.created initial.credential
      prefixRun receipt present with old | ⟨serverCall, earlier, origin⟩
  · have empty := RegistrationNativeServerHistoryOrigin.start_empty setup ensureInit identityIndex serverKid initial startup
    change receipt ∈ serverReceipts (history initial.state.server) at old
    rw [empty] at old
    cases old
  · have stageReceipt := origin
    obtain ⟨serverIndex, serverInput, token, current, plaintext, availability, serverInitial, hashed, query, taken, plaintextEq,
      admitted, path, recordCut, _publicKey, payload⟩ := origin
    have samePayload : Command.payload (.server hashed) = RegistrationResponseExecutor.payload pending packet := payload.symm.trans content
    obtain ⟨identity, ephemeral, kem, ciphertext, assigned, initHash⟩ :=
      RegistrationNativeResponseStageContents.native_fields serverInitial hashed path pending packet samePayload
    obtain ⟨_adDigest, _completedBinding, _completedAt, _initialBinding, _application, rooted⟩ :=
      (RegistrationNativeServerBindingReceipt.initial_root current.control current.pin availability token.agreement plaintext serverInitial admitted).2
    exact ⟨completed, verified, leading, trailing, serverCall, receipt, serverIndex, serverInput, token, current, plaintext, availability, serverInitial, hashed,
      split, earlier, query, taken, plaintextEq, stageReceipt, admitted, path, recordCut, identity, ephemeral, kem, ciphertext, assigned, initHash, rooted⟩

end BeaconcryptCore.Computational.RegistrationNativeCausalRecordContents
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCausalRecordContents.path_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCausalRecordContents.path_contents

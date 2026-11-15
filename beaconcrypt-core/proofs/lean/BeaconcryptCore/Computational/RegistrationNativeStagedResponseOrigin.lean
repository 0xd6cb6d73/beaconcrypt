-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCausalResponseContents
import BeaconcryptCore.Computational.RegistrationNativeTokenRootReceipt
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginJournal

/-! Protected successful native Beacon completion has the actual earlier accept/root/token/build stages in the same execution outside the one bounded original origin event. The stages retain exact public contents and both local initializer receipts. Cross-role private-root equality and completed peer installation remain separate properties. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStagedResponseOrigin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationSigningShared (Receipt)
open RegistrationNativeServerIssuance (history)
open RegistrationNativeMldsaRoleFrame (serverReceipts)
open RegistrationNativeServerHistoryOrigin (SourceAt)
open BeaconcryptCore.Refinement.RegistrationSigningTrace (Command)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree

/-- Outside the bounded original native origin exception, every protected successful finish has an earlier same-run accept/root/token/build chain with exact source response contents and its actual local Beacon completion receipt. -/
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
    (good : ¬ RegistrationNativeMldsaOriginJournal.BadCalls initial.credential calls)
    (keyProtected : pending.binding.server_pin.public_key = initial.credential.publicKey) :
    RegistrationNativeCompletionReceipt.Receipt beforeFinish.beacons index (some packet) application ∧
      MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash afterFinish.server.world.world.1.primitive.2) source.verify
        (RegistrationResponseExecutor.trial true pending packet (RegistrationSigningShared.historyFor
          (absBytes pending.binding.server_pin.public_key) (RegistrationNativeMldsaShared.nativeProject beforeFinish))) ∧
      ∃ leading trailing serverCall receipt serverIndex serverInput token current plaintext availability serverInitial hashed,
        calls = leading ++ (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) :: trailing ∧
        serverCall ∈ leading ∧ serverCall.query = .inr (.build serverIndex serverInput) ∧
        RegistrationServerSdkSource.take serverIndex serverCall.before.server = (some token, current) ∧ serverInput = some plaintext ∧
        SourceAt serverCall receipt ∧ BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext serverInitial ∧
        RegistrationServerRecordExecutor.Path serverInitial hashed ∧
        hashed.candidate.server_identity_public_key = packet.public.identity_key ∧
        hashed.candidate.ephemeral_public_key = packet.public.ephemeral_key ∧
        hashed.candidate.kem_ciphertext = packet.public.kem_cipher_text ∧ hashed.ciphertext = packet.application ∧
        hashed.candidate.key_id = packet.public.key_id ∧ hashed.binding.init_hash = pending.binding.init_hash ∧
        pqxdh.concrete.start_server_candidate_ratchet_kdf serverInitial.candidate token.agreement.root.bytes = .ok serverInitial.pending ∧
        ∃ buildLeading buildTrailing acceptCall acceptLeading between acceptedPacket events authenticated afterAuthentication afterAgreement consumedHistory,
          calls = buildLeading ++ serverCall :: buildTrailing ∧ buildLeading = acceptLeading ++ acceptCall :: between ∧
          Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
            initial.state acceptLeading acceptCall.before ∧
          RegistrationNativeStageTrace.Executed (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) acceptCall ∧
          Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
            acceptCall.after between serverCall.before ∧
          acceptCall.query = .inr (.accept acceptedPacket) ∧
          (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
            ((RegistrationServerNativeSource.authenticate setup (RegistrationNativeWire.ledgerCodec wire) route source.verify initial.created acceptedPacket).run acceptCall.before.server) ∧
          (.ok (.ServerComplete token.agreement), afterAgreement) ∈ support
            ((RegistrationServerNativeSource.agree setup checks representation initial.created acceptedPacket authenticated).run afterAuthentication) ∧
          RegistrationReplaySchedule.consume token.agreement afterAgreement.consumed = .ok (.Some token, consumedHistory) ∧
          Nonempty (RegistrationNativeTokenRootReceipt.Input setup checks representation initial.created
            acceptedPacket authenticated afterAuthentication afterAgreement token.agreement) := by
  have issued := RegistrationNativeMldsaOriginJournal.finish_issued initial.credential calls good index packet application
    beforeFinish afterFinish member owner pending oneTime found phase keyProtected
  obtain ⟨completed, verified, leading, trailing, serverCall, receipt, serverIndex, serverInput, token, current,
    plaintext, availability, serverInitial, hashed, split, earlier, queryEq, taken, inputEq, stage,
    admitted, path, identity, ephemeral, kem, ciphertext, assigned, initHash, rooted⟩ :=
    RegistrationNativeCausalResponseContents.path_contents setup checks wire route representation ensureInit identityIndex serverKid
      initial startup calls final actual index pending packet owner oneTime beforeFinish afterFinish application member found phase issued
  have buildPresent : serverCall ∈ calls := by
    rw [split]
    exact List.mem_append.mpr (Or.inl earlier)
  obtain ⟨buildLeading, buildTrailing, buildSplit, beforeBuild, _built, _afterBuild⟩ := actual.member serverCall buildPresent
  have empty := RegistrationNativeTokenTrace.start_empty setup ensureInit identityIndex serverKid initial startup
  obtain ⟨acceptCall, acceptLeading, between, acceptedPacket, events, authenticated, afterAuthentication, afterAgreement,
    consumedHistory, acceptSplit, beforeAccept, accepted, betweenPath, acceptQuery, checked, agreed, consumed, inputs⟩ :=
    RegistrationNativeTokenRootReceipt.taken setup checks representation initial.created wire route initial.credential
      beforeBuild empty serverIndex token current taken
  exact ⟨completed, verified, leading, trailing, serverCall, receipt, serverIndex, serverInput, token, current,
    plaintext, availability, serverInitial, hashed, split, earlier, queryEq, taken, inputEq, stage,
    admitted, path, identity, ephemeral, kem, ciphertext, assigned, initHash, rooted,
    buildLeading, buildTrailing, acceptCall, acceptLeading, between, acceptedPacket, events, authenticated,
    afterAuthentication, afterAgreement, consumedHistory, buildSplit, acceptSplit, beforeAccept, accepted,
    betweenPath, acceptQuery, checked, agreed, consumed, inputs⟩

end BeaconcryptCore.Computational.RegistrationNativeStagedResponseOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedResponseOrigin.path_contents' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedResponseOrigin.path_contents

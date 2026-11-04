-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLoggedPairedCoordinates
import BeaconcryptCore.Computational.RegistrationNativePairedRoots
import BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands

/-! A consumed same-run token with its checked matched Init receipt and a genuinely successful native Beacon agreement have equal roots when the actual public Response stages correspond. Equal Root bytes or the actual finite-recipient marker is derived from reached primitive operands; no root, initializer agreement or perfect-correctness premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLoggedStagedRootAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_pure lower_bind)
variable {n count : Nat} {ι KemSK V Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {κ : Type} {spec : OracleSpec κ}

private theorem lower_simulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (implementation : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State)) (work : OracleComp spec V) :
    lower setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- Actual logged collectors give equal Root bytes unless their own finite-recipient execution's common marker fired. No perfect correctness or desired Root equality is assumed. -/
theorem root_or_marker (setup : Setup base KemSK) (checks : Checks)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (RegistrationNativeKemCountedProgram.Spec KemSK) Value)
    (result : RegistrationNativeKemRecipientLogSource.Result KemSK Value count)
    (supported : result ∈ support (RegistrationNativeKemRecipientLogSource.experiment setup functional work count))
    (packet : registration.InitPacket) (initAuth : registration.AuthenticatedInit)
    (serverBefore serverAfter : RegistrationNativeKemServerState.State n source) (accepted : agreement.ServerAgreement)
    (receipt : RegistrationNativeKemTracedServerSource.Receipt setup checks representation created packet initAuth serverBefore serverAfter accepted result.2.1.1.2)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (token : peer.ConsumedRegistration) (tokenEq : token.agreement = accepted)
    (matched : initAuth.registration = {
      beacon_identity_public_key := rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
      beacon_prekey_public_key := owner.prekeyPublic,
      beacon_one_time_public_key := rootArray (setup.dh.publicKey oneTime),
      beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic })
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (completed : agreement.BeaconAgreement) (before after : Local n KemSK source)
    (beaconAgreed : (.ok (.BeaconComplete completed), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before))
    (target : Fin count) (row : before.2.2.pool.keys[owner.kemHandle]? = some (result.1 target).1)
    (publicKey : (result.1 target).1.1 = owner.kemPublic)
    (prekey : owner.prekeyPublic = rootArray (setup.dh.publicKey owner.prekeyScalar))
    (serverIdentity : authenticated.packet.public.identity_key = rootArray (setup.joint.publicKeys created.seed).ed25519)
    (ephemeral : authenticated.packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key)
    (ciphertext : authenticated.packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext) :
    token.agreement.root.bytes = completed.root.bytes ∨ result.2.2 = true := by
  obtain ⟨beaconInput, atRoot, original, beaconCollected, _fields, prepared, completedEq, _afterEq⟩ :=
    RegistrationNativeBeaconAgreementInputReceipt.local_cut setup checks representation created owner oneTime
      authenticated coherent completed before after beaconAgreed
  rw [lower_simulate] at beaconCollected
  obtain ⟨identity, prekeyEq, oneTimeKey, pqKey⟩ := RegistrationNativeTokenPublicOperands.tuple setup owner oneTime packet initAuth prekey matched
  rw [tokenEq] at ephemeral ciphertext
  obtain ⟨ephemeralEq, ciphertextEq⟩ := RegistrationNativeTokenPublicOperands.token setup checks representation created packet initAuth
    serverBefore.server serverAfter.server accepted receipt.nativeInput
  have matchedIdentity : receipt.nativeInput.collected.verified.identity = (setup.joint.publicKeys owner.identitySeed).ed25519 := by
    rw [receipt.nativeInput.verified]
    exact identity
  have matchedPrekey : receipt.nativeInput.collected.verified.keys.prekey = setup.dh.publicKey owner.prekeyScalar := by
    rw [receipt.nativeInput.verified]
    exact prekeyEq
  have matchedOneTime : receipt.nativeInput.collected.verified.keys.oneTime = setup.dh.publicKey oneTime := by
    rw [receipt.nativeInput.verified]
    exact oneTimeKey
  have matchedKem : receipt.nativeInput.collected.verified.keys.pqKey = (result.1 target).1.1 := by
    rw [receipt.nativeInput.verified]
    exact pqKey.trans publicKey.symm
  obtain ⟨firstEq, secondEq, thirdEq, fourthEq, secret⟩ := RegistrationNativeLoggedPairedCoordinates.collected setup checks functional representation created
    packet initAuth serverBefore serverAfter accepted result.2.1.1.2 receipt owner oneTime authenticated beaconInput before atRoot beaconCollected
      result.1 target row matchedKem (ciphertext.trans ciphertextEq) matchedIdentity matchedPrekey matchedOneTime serverIdentity (ephemeral.trans ephemeralEq)
  rcases secret with kemEq | bad
  · have serverBytes := receipt.nativeInput.bytes
    have beaconBytes := RegistrationNativeAgreementInputReceipt.beacon_bytes authenticated.pending.control beaconInput original prepared
    have sameBytes : absBytes receipt.nativeInput.original.root_key_input.bytes = absBytes original.root_key_input.bytes := by
      rw [serverBytes, beaconBytes, firstEq, secondEq, thirdEq, fourthEq, kemEq]
    have nativeBytes : receipt.nativeInput.original.root_key_input.bytes = original.root_key_input.bytes := by
      apply Subtype.ext
      exact (absBytes_inj_iff _ _).mp sameBytes
    have sameRoot := congrArg (fun bytes => RegistrationAgreementShared.rootResponse setup.source.crypto ⟨bytes, pqxdh.PQXDH_INFO⟩) nativeBytes
    have serverRoot := RegistrationNativeTokenRootReceipt.Input.root setup checks representation created packet initAuth serverBefore.server serverAfter.server accepted receipt.nativeInput
    have beaconRoot := congrArg (fun value : agreement.BeaconAgreement => value.root.bytes) completedEq
    rw [tokenEq]
    exact Or.inl (serverRoot.trans (sameRoot.trans beaconRoot.symm))
  · exact Or.inr (RegistrationNativeKemRecipientLogSource.sound setup functional work count result supported _ receipt.encapsulated bad)

end BeaconcryptCore.Computational.RegistrationNativeLoggedStagedRootAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLoggedStagedRootAgreement.root_or_marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLoggedStagedRootAgreement.root_or_marker

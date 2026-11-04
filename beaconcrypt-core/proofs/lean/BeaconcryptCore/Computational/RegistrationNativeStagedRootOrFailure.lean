-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedRootsOrFailure
import BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands

/-! A consumed same-run token and actual successful Beacon agreement have equal roots, or retain the actual collected primitive recipient-failure sample at the private generated row. No perfect-correctness or root-equality premise is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStagedRootOrFailure
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_pure lower_bind)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {κ : Type} {spec : OracleSpec κ}

private theorem lower_simulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (implementation : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State)) (work : OracleComp spec V) :
    lower setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- Actual matched Init and completed native Response agreement determine the same source-derived root, without any caller-supplied root equality. -/
theorem root (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverReceipt : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token pin cache)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.pending.control.expected_server_binding = authenticated.pending.binding.server_pin.binding)
    (completed : agreement.BeaconAgreement) (before after : Local n KemSK source)
    (beaconAgreed : (.ok (.BeaconComplete completed), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before))
    (generatedPool : RegistrationNativeKemBirthPool.Generated setup.baseImpl setup.kem before.2.2.pool)
    (owned : ∃ pair, before.2.2.pool.keys[owner.kemHandle]? = some pair ∧ pair.1 = owner.kemPublic)
    (prekey : owner.prekeyPublic = rootArray (setup.dh.publicKey owner.prekeyScalar))
    (serverIdentity : authenticated.packet.public.identity_key = rootArray (setup.joint.publicKeys created.seed).ed25519)
    (ephemeral : authenticated.packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key)
    (ciphertext : authenticated.packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext)
    :
    token.agreement.root.bytes = completed.root.bytes ∨
      ∃ (beaconInput : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) (atRoot : Local n KemSK source),
        (some beaconInput, atRoot) ∈ support ((lower setup checks representation created
          (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
            (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
              (PqxdhBeaconPhase2Preparation.collect () false true () [])))).run before) ∧
        RegistrationNativeRecipientFailure.FailureAt setup before.2.2.pool owner.kemHandle serverReceipt.root.collected beaconInput := by
  obtain ⟨beaconInput, atRoot, original, beaconCollected, _fields, prepared, completedEq, _afterEq⟩ :=
    RegistrationNativeBeaconAgreementInputReceipt.local_cut setup checks representation created owner oneTime
      authenticated coherent completed before after beaconAgreed
  rw [lower_simulate] at beaconCollected
  obtain ⟨identity, prekeyEq, oneTimeKey, pqKey⟩ := RegistrationNativeTokenPublicOperands.tuple setup owner oneTime
    serverReceipt.packet serverReceipt.authenticated prekey serverReceipt.registration
  obtain ⟨ephemeralEq, ciphertextEq⟩ := RegistrationNativeTokenPublicOperands.token setup checks representation created
    serverReceipt.packet serverReceipt.authenticated serverReceipt.afterAuthentication serverReceipt.afterAgreement token.agreement serverReceipt.root
  have compared := RegistrationNativePairedRootsOrFailure.collect setup checks representation created owner oneTime
    (RegistrationRootInput.verified serverReceipt.packet serverReceipt.authenticated) serverReceipt.root.collected
    (RegistrationWorldAgreement.project serverReceipt.afterAuthentication.world) serverReceipt.root.atRoot serverReceipt.root.supported
    authenticated beaconInput before atRoot beaconCollected generatedPool owned identity prekeyEq oneTimeKey pqKey
    serverIdentity (ephemeral.trans ephemeralEq) (ciphertext.trans ciphertextEq)
    serverReceipt.afterAuthentication.control serverReceipt.root.next serverReceipt.authenticated.binding.server_pin.binding
    serverReceipt.root.original serverReceipt.root.accepted authenticated.pending.control original prepared
  rcases compared with good | failed
  · obtain ⟨_sameInput, sameRoot⟩ := good
    have serverRoot := RegistrationNativeTokenRootReceipt.Input.root setup checks representation created
      serverReceipt.packet serverReceipt.authenticated serverReceipt.afterAuthentication serverReceipt.afterAgreement token.agreement serverReceipt.root
    have beaconRoot := congrArg (fun value : agreement.BeaconAgreement => value.root.bytes) completedEq
    exact Or.inl (serverRoot.trans (sameRoot.trans beaconRoot.symm))
  · exact Or.inr ⟨beaconInput, atRoot, by simpa only [lower_simulate] using beaconCollected, failed⟩

end BeaconcryptCore.Computational.RegistrationNativeStagedRootOrFailure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedRootOrFailure.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedRootOrFailure.root

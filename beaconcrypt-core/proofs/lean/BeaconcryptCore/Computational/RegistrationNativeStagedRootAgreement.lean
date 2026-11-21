-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedRoots
import BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands

/-! A consumed same-run token with its checked matched Init receipt and a genuinely successful native Beacon agreement have equal roots when the actual public Response stages correspond. The equality is derived from reached primitive operands and ordinary honest-recipient KEM correctness; no root or initializer agreement premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStagedRootAgreement
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner M)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_pure lower_bind)
variable {n : Nat} {ι KemSK V : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {κ : Type} {spec : OracleSpec κ}

private theorem lower_simulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl spec (M n KemSK source RegistrationServerRoleBackend.State)) (work : OracleComp spec V) :
    lower setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- Actual matched Init and completed native Response agreement determine the same source-derived root, without any caller-supplied root equality. -/
theorem root (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverReceipt : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token pin cache)
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
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
    (correct : RegistrationNativePairedCoordinates.RecipientCorrect setup) :
    token.agreement.root.bytes = completed.root.bytes := by
  obtain ⟨beaconInput, atRoot, original, beaconCollected, _fields, prepared, completedEq, _afterEq⟩ :=
    RegistrationNativeBeaconAgreementInputReceipt.local_cut setup checks representation created owner oneTime
      authenticated coherent completed before after beaconAgreed
  rw [lower_simulate] at beaconCollected
  obtain ⟨identity, prekeyEq, oneTimeKey, pqKey⟩ := RegistrationNativeTokenPublicOperands.tuple setup owner oneTime
    serverReceipt.packet serverReceipt.authenticated prekey serverReceipt.registration
  obtain ⟨ephemeralEq, ciphertextEq⟩ := RegistrationNativeTokenPublicOperands.token setup checks representation created
    serverReceipt.packet serverReceipt.authenticated serverReceipt.afterAuthentication serverReceipt.afterAgreement token.agreement serverReceipt.root
  obtain ⟨_sameInput, sameRoot⟩ := RegistrationNativePairedRoots.collect setup checks representation created owner oneTime
    (RegistrationRootInput.verified serverReceipt.packet serverReceipt.authenticated) serverReceipt.root.collected
    (RegistrationWorldAgreement.project serverReceipt.afterAuthentication.world) serverReceipt.root.atRoot serverReceipt.root.supported
    authenticated beaconInput before atRoot beaconCollected generatedPool owned identity prekeyEq oneTimeKey pqKey
    serverIdentity (ephemeral.trans ephemeralEq) (ciphertext.trans ciphertextEq) correct
    serverReceipt.afterAuthentication.control serverReceipt.root.next serverReceipt.authenticated.binding.server_pin.binding
    serverReceipt.root.original serverReceipt.root.accepted authenticated.control original prepared
  have serverRoot := RegistrationNativeTokenRootReceipt.Input.root setup checks representation created
    serverReceipt.packet serverReceipt.authenticated serverReceipt.afterAuthentication serverReceipt.afterAgreement token.agreement serverReceipt.root
  have beaconRoot := congrArg (fun value : agreement.BeaconAgreement => value.root.bytes) completedEq
  exact serverRoot.trans (sameRoot.trans beaconRoot.symm)

end BeaconcryptCore.Computational.RegistrationNativeStagedRootAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedRootAgreement.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedRootAgreement.root

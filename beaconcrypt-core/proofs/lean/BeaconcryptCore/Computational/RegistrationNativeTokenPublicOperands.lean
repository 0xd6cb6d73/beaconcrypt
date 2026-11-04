-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput
import BeaconcryptCore.Computational.RegistrationNativeCapturedCoordinates

/-! The same consumed token's actual source acceptance retains the public ephemeral and KEM ciphertext of its collector. The already matched authenticated Init tuple supplies its four exact source public operands, without assuming private input or root equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- A token's retained root receipt identifies the actual ephemeral public key and KEM ciphertext computed before source root erasure. -/
theorem token (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : RegistrationServerFrontendCompiler.State n) (completed : agreement.ServerAgreement)
    (receipt : RegistrationNativeTokenRootReceipt.Input setup checks representation created packet authenticated before after completed) :
    completed.pending.ephemeral_public_key = receipt.collected.ephemeral.publicKey ∧
      completed.pending.kem_ciphertext = receipt.collected.ciphertext := by
  have used := (PqxdhRegistrationInputs.accepted_used before.control receipt.next
    (PqxdhProtocolAcceptance.verified receipt.collected.verified.identity receipt.collected.verified.keys) .Fresh
    authenticated.binding.server_pin.binding ⟨receipt.collected.ephemeral.publicKey, receipt.collected.ciphertext⟩
    (PqxdhServerRelatedRootInput.secrets receipt.collected) receipt.original receipt.accepted).2
  refine ⟨?_, ?_⟩
  · exact (congrArg (fun value : agreement.ServerAgreement => value.pending.ephemeral_public_key) receipt.completedEq).trans
      (congrArg PqxdhRegistrationInputs.UsedInput.ephemeral_public_key used)
  · exact (congrArg (fun value : agreement.ServerAgreement => value.pending.kem_ciphertext) receipt.completedEq).trans
      (congrArg PqxdhRegistrationInputs.UsedInput.kem_ciphertext used)

/-- Exact authenticated native Init fields determine the source verified tuple, including correlated identity conversion and the genuine KEM public key. -/
theorem tuple (setup : Setup base KemSK) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (prekey : owner.prekeyPublic = rootArray (setup.dh.publicKey owner.prekeyScalar))
    (matched : authenticated.registration = {
      beacon_identity_public_key := rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
      beacon_prekey_public_key := owner.prekeyPublic,
      beacon_one_time_public_key := rootArray (setup.dh.publicKey oneTime),
      beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }) :
    (RegistrationRootInput.verified packet authenticated).identity = (setup.joint.publicKeys owner.identitySeed).ed25519 ∧
      (RegistrationRootInput.verified packet authenticated).keys.prekey = setup.dh.publicKey owner.prekeyScalar ∧
      (RegistrationRootInput.verified packet authenticated).keys.oneTime = setup.dh.publicKey oneTime ∧
      (RegistrationRootInput.verified packet authenticated).keys.pqKey = owner.kemPublic := by
  simp only [RegistrationRootInput.verified, RegistrationRootInput.identity, RegistrationRootInput.keys,
    matched, prekey, PqxdhPhase2InputBytes.word_rootArray, RegistrationNativeBeaconPublication.pq_key]
  trivial

end BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands.token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands.token

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands.tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeTokenPublicOperands.tuple

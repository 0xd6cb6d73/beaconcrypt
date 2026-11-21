-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBirth
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublication
import BeaconcryptCore.Computational.RegistrationNativeKemBirthLifecycle

/-! Successful Word bundle publication retains the actual selected owner's signed prekey under arbitrary material replies. The proof descends through the literal native outgoing controller and preserves every reached source state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublication
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicOwners (Owner State)
open RegistrationNativeKemBirthInvariant (metadata)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

/-- Actual symbolic outgoing publication has the original retained owner's decoded signed PQ payload. -/
theorem bundle_prekey (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (readback : RegistrationNativeWire.InitReadBack wire) (selected index : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (owners : State source) (env : EnvState Auxiliary)
    (raw : Pqxdh.Bytes) (afterOwners : State source) (afterEnv : EnvState Auxiliary)
    (supported : ((.ok (some raw), afterOwners), afterEnv) ∈ support
      (((RegistrationNativeSecretWordOwners.bundle (n := n) setup source wire selected publicPrekey index).run owners).run env)) :
    ∃ owner packet, owners[index]? = some owner ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.view.prekeyPublic) := by
  simp only [RegistrationNativeSecretWordOwners.bundle, RegistrationNativeSecretWordOwners.executeLocal,
    StateT.run] at supported
  have pubSupport := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported
  simp only [RegistrationNativePublicOwners.executeLocal,
    StateT.run, support_map] at pubSupport
  obtain ⟨⟨⟨reply, reachedOwners⟩, reachedEnv⟩, reached, equal⟩ := pubSupport
  have replyEq : reply = .ok (some raw) := congrArg (fun result => result.1.1) equal
  subst reply
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  obtain ⟨restored, published, found, encoded, receipt⟩ := RegistrationNativePrekeyPublication.bundle_prekey
    setup source wire index (owners.map RegistrationNativePublicOwners.restore) reachedOwners env reachedEnv raw native
  simp only [List.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨owner, ownerAt, restoredEq⟩ := found
  subst restored
  obtain ⟨packet, decoded, keyMatches⟩ := RegistrationNativePrekeyPublication.decoded_key wire readback
    (PqxdhPhase2InputBytes.word (RegistrationNativePublicOwners.restore owner).prekeyPublic) published receipt
  exact ⟨owner, packet, ownerAt, encoded ▸ decoded, keyMatches⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublication.bundle_prekey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyPublication.bundle_prekey

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecipientFailure

/-! Actual collectors and source builders give equal pre-erasure root inputs and fixed-source HKDF outputs, or retain an actual same-row primitive recipient failure sample. No zero-error recipient correctness or root agreement premise is assumed. The finite adaptive probability reduction for these samples is separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePairedRootsOrFailure
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Matching actual public stage fields force equality of the two checked private root inputs and their actual source-derived outputs. -/
theorem collect (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (verified : PqxdhServerRootPreparation.Verified registration.InitPacket)
    (serverInput : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
    (serverBefore serverAfter : RawCtxSharedPrimitive.SharedState RegistrationServerRoleBackend.State)
    (serverCollected : (some serverInput, serverAfter) ∈ support
      ((simulateQ (RegistrationAgreementShared.implementation setup.source (RegistrationServerRoleBackend.native setup checks representation created.seed))
        (simulateQ RegistrationAgreementRoot.callbacks (PqxdhServerRootPreparation.collectVerified verified))).run serverBefore))
    (authenticated : registration.AuthenticatedResponse)
    (beaconInput : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
    (before after : Local n KemSK source)
    (beaconCollected : (some beaconInput, after) ∈ support
      ((simulateQ (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query))
        (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
          (PqxdhBeaconPhase2Preparation.collect () false true () []))).run before))
    (generatedPool : RegistrationNativeKemBirthPool.Generated setup.baseImpl setup.kem before.2.2.pool)
    (owned : ∃ pair, before.2.2.pool.keys[owner.kemHandle]? = some pair ∧ pair.1 = owner.kemPublic)
    (identity : verified.identity = (setup.joint.publicKeys owner.identitySeed).ed25519)
    (prekey : verified.keys.prekey = setup.dh.publicKey owner.prekeyScalar)
    (oneTimeKey : verified.keys.oneTime = setup.dh.publicKey oneTime)
    (pqKey : verified.keys.pqKey = owner.kemPublic)
    (serverIdentity : authenticated.packet.public.identity_key = rootArray (setup.joint.publicKeys created.seed).ed25519)
    (ephemeral : authenticated.packet.public.ephemeral_key = serverInput.ephemeral.publicKey)
    (ciphertext : authenticated.packet.public.kem_cipher_text = serverInput.ciphertext)
    (serverControl serverNext : pqxdh.ServerState) (serverBinding : pqxdh.ServerBinding)
    (serverPending : pqxdh.PendingServerRegistration)
    (serverAccepted : PqxdhServerRelatedRootInput.accept serverControl serverBinding serverInput = .ok (.Ok (serverNext, serverPending)))
    (beaconControl : pqxdh.BeaconInitSent) (beaconPending : pqxdh.BeaconRegistrationCandidate)
    (beaconAccepted : pqxdh.beacon_prepare_finish beaconControl beaconInput.finishInputs = .ok (.Ok beaconPending)) :
    (serverPending.root_key_input.bytes = beaconPending.root_key_input.bytes ∧
      RegistrationAgreementShared.rootResponse setup.source.crypto ⟨serverPending.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ =
        RegistrationAgreementShared.rootResponse setup.source.crypto ⟨beaconPending.root_key_input.bytes, pqxdh.PQXDH_INFO⟩) ∨
      RegistrationNativeRecipientFailure.FailureAt setup before.2.2.pool owner.kemHandle serverInput beaconInput := by
  rcases RegistrationNativeRecipientFailure.collect_or_failure
    setup checks representation created owner oneTime verified serverInput serverBefore serverAfter serverCollected
    authenticated beaconInput before after beaconCollected generatedPool owned identity prekey oneTimeKey pqKey serverIdentity ephemeral ciphertext with
    good | failure
  · rcases good with ⟨firstEq, secondEq, thirdEq, fourthEq, kemEq⟩
    have serverBytes := RegistrationNativeAgreementInputReceipt.server_bytes serverControl serverNext serverBinding serverInput serverPending serverAccepted
    have beaconBytes := RegistrationNativeAgreementInputReceipt.beacon_bytes beaconControl beaconInput beaconPending beaconAccepted
    have sameBytes : absBytes serverPending.root_key_input.bytes = absBytes beaconPending.root_key_input.bytes := by
      rw [serverBytes, beaconBytes, firstEq, secondEq, thirdEq, fourthEq, kemEq]
    have sameNative : serverPending.root_key_input.bytes = beaconPending.root_key_input.bytes := by
      apply Subtype.ext
      exact (absBytes_inj_iff _ _).mp sameBytes
    exact Or.inl ⟨sameNative, congrArg (fun bytes => RegistrationAgreementShared.rootResponse setup.source.crypto ⟨bytes, pqxdh.PQXDH_INFO⟩) sameNative⟩
  · exact Or.inr failure

end BeaconcryptCore.Computational.RegistrationNativePairedRootsOrFailure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePairedRootsOrFailure.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePairedRootsOrFailure.collect

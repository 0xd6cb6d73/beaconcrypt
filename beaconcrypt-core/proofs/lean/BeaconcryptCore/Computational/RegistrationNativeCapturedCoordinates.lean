-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePairedCoordinates

/-! Actual source collector success for a captured owner uses its actual private handle independently of the mutable current phase/roster. Honest generated pool rows and matching public stage fields determine equal private coordinates; only primitive honest-recipient correctness is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCapturedCoordinates
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

open RegistrationNativePairedCoordinates (RecipientCorrect)

private theorem peer_root (value : List.Vector UInt8 32) : PqxdhPhase2GapDhSource.peer (rootArray value) = value :=
  PqxdhPhase2InputBytes.word_rootArray value
private theorem pq_root (value : PqxdhKemIndCca.MlKem768PublicKey) :
    RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray value) = value := by
  apply Subtype.ext
  simp [RegistrationRootInput.pqKey, RegistrationAgreementRoot.pqArray, absBytes, List.map_map, Function.comp_def]

/-- The two actual collectors agree on every private root coordinate when their public source-stage fields match. -/
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
    (correct : RecipientCorrect setup) :
    serverInput.first = beaconInput.finishInputs.shared_secrets.dh1 ∧
    serverInput.second = beaconInput.finishInputs.shared_secrets.dh2 ∧
    serverInput.third = beaconInput.finishInputs.shared_secrets.dh3 ∧
    serverInput.fourth = beaconInput.finishInputs.shared_secrets.dh4 ∧
    serverInput.kem = beaconInput.finishInputs.shared_secrets.kem_shared_secret := by
  obtain ⟨scalar, _sampled, encapsulated, encapsSupport, ephemeralEq, ciphertextEq, kemEq,
      serverConverted, _serverPrivate, serverFirst, serverSecond, serverThird, serverFourth, _role, _cache⟩ :=
    RegistrationNativeServerCollectedOperands.collect setup checks representation created.seed verified serverInput serverBefore serverAfter serverCollected
  obtain ⟨converted, pair, beaconConverted, _beaconPrivate, row, decapsulated,
      beaconFirst, beaconSecond, beaconThird, beaconFourth, _keys⟩ :=
    RegistrationNativeBeaconCollectedOperands.collect setup checks representation created owner oneTime authenticated beaconInput before after beaconCollected
  have convertedBeacon : PqxdhPhase2GapDhSource.peer converted = (setup.joint.publicKeys created.seed).convertedX25519 :=
    RegistrationNativeDhAgreement.converted setup created.seed converted (serverIdentity ▸ beaconConverted)
  have convertedServer : PqxdhPhase2GapDhSource.peer serverInput.convertedIdentity = (setup.joint.publicKeys owner.identitySeed).convertedX25519 :=
    RegistrationNativeDhAgreement.converted setup owner.identitySeed serverInput.convertedIdentity (identity ▸ serverConverted)
  have firstEq : serverInput.first = beaconInput.finishInputs.shared_secrets.dh1 := by
    simp only [prekey, peer_root, setup.dh.agreement] at serverFirst
    simp only [RegistrationNativeBeaconDhReplies.reply, convertedBeacon] at beaconFirst
    exact Option.some.inj (serverFirst.symm.trans beaconFirst)
  have secondEq : serverInput.second = beaconInput.finishInputs.shared_secrets.dh2 := by
    simp only [convertedServer] at serverSecond
    simp only [RegistrationNativeBeaconDhReplies.reply, ephemeral, ephemeralEq, peer_root, setup.dh.agreement] at beaconSecond
    exact Option.some.inj (serverSecond.symm.trans beaconSecond)
  have thirdEq : serverInput.third = beaconInput.finishInputs.shared_secrets.dh3 := by
    simp only [prekey, peer_root] at serverThird
    simp only [RegistrationNativeBeaconDhReplies.reply, ephemeral, ephemeralEq, peer_root] at beaconThird
    have commute := RegistrationNativeDhAgreement.scalar_comm setup scalar owner.prekeyScalar
    change PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar (setup.dh.publicKey owner.prekeyScalar) =
      setup.dh.dh owner.prekeyScalar (setup.dh.publicKey scalar) at commute
    rw [commute] at serverThird
    exact Option.some.inj (serverThird.symm.trans beaconThird)
  have fourthEq : serverInput.fourth = beaconInput.finishInputs.shared_secrets.dh4 := by
    simp only [oneTimeKey, peer_root] at serverFourth
    simp only [RegistrationNativeBeaconDhReplies.reply, ephemeral, ephemeralEq, peer_root] at beaconFourth
    have commute := RegistrationNativeDhAgreement.scalar_comm setup scalar oneTime
    change PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar (setup.dh.publicKey oneTime) =
      setup.dh.dh oneTime (setup.dh.publicKey scalar) at commute
    rw [commute] at serverFourth
    exact Option.some.inj (serverFourth.symm.trans beaconFourth)
  obtain ⟨honestPair, honestRow, publicKey⟩ := owned
  have pairEq : pair = honestPair := Option.some.inj (row.symm.trans honestRow)
  subst honestPair
  have generated := generatedPool pair (List.mem_of_getElem? row)
  have encapsActual : encapsulated ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1)) := by
    simpa only [pq_root, pqKey, publicKey] using encapsSupport
  have decapsActual : some (PqxdhPhase2InputBytes.word beaconInput.finishInputs.shared_secrets.kem_shared_secret) ∈ support
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.decaps pair.2 encapsulated.1)) := by
    rw [ciphertext, ciphertextEq, (PqxdhPhase2InputBytes.ciphertext_roundtrip serverInput.ciphertext encapsulated.1).2] at decapsulated
    exact decapsulated
  have sameSecret := Option.some.inj (correct pair generated encapsulated encapsActual _ decapsActual)
  have sameWord := congrArg rootArray sameSecret
  rw [PqxdhPhase2InputBytes.word_roundtrip] at sameWord
  exact ⟨firstEq, secondEq, thirdEq, fourthEq, kemEq.trans sameWord.symm⟩

end BeaconcryptCore.Computational.RegistrationNativeCapturedCoordinates

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCapturedCoordinates.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCapturedCoordinates.collect

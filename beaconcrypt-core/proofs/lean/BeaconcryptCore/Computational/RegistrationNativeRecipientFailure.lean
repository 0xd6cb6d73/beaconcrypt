-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCapturedCoordinates

/-! Actual collector receipts identify a primitive recipient sample at the same generated private table row. Root-coordinate disagreement is covered by an actual sampled keygen/encaps/decaps failure receipt, without assuming perfect correctness. This local receipt is not itself a quantitative multi-query reduction; its finite adaptive ordinal billing remains separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecipientFailure
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- One literal honest-recipient primitive sample, retaining all three actual ordinary primitive support receipts. -/
structure Sample (setup : Setup base KemSK) where
  keyPair : MlKem768PublicKey × KemSK
  generated : keyPair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  encapsulated : MlKem768Ciphertext × MlKemSharedSecret
  encapsulatedSupport : encapsulated ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps keyPair.1))
  answer : Option MlKemSharedSecret
  decapsulatedSupport : answer ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.decaps keyPair.2 encapsulated.1))

def Sample.Bad (setup : Setup base KemSK) (sample : Sample setup) : Prop := sample.answer ≠ some sample.encapsulated.2

def FailureAt (setup : Setup base KemSK) (pool : PqxdhLiveKemBirth.Pool KemSK) (handle : Nat)
    (serverInput : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
    (beaconInput : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse) : Prop :=
  ∃ sample : Sample setup, pool.keys[handle]? = some sample.keyPair ∧
    sample.answer = some (PqxdhPhase2InputBytes.word beaconInput.finishInputs.shared_secrets.kem_shared_secret) ∧
    serverInput.kem = rootArray sample.encapsulated.2 ∧ sample.Bad setup

abbrev Trial (KemSK : Type) := (MlKem768PublicKey × KemSK) × ((MlKem768Ciphertext × MlKemSharedSecret) × Option MlKemSharedSecret)

/-- The ordinary one-key/one-encapsulation/one-decapsulation primitive experiment, with no native protocol event. -/
noncomputable def experiment (setup : Setup base KemSK) : ProbComp (Trial KemSK) := do
  let pair ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let encapsulated ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1)
  let answer ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.decaps pair.2 encapsulated.1)
  pure (pair, (encapsulated, answer))

/-- Every retained source sample belongs to that literal ordinary primitive experiment. -/
theorem sample_supported (setup : Setup base KemSK) (sample : Sample setup) :
    (sample.keyPair, (sample.encapsulated, sample.answer)) ∈ support (experiment setup) := by
  simp only [experiment, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
  exact ⟨sample.keyPair, sample.generated, sample.encapsulated, sample.encapsulatedSupport,
    sample.answer, sample.decapsulatedSupport, rfl⟩

/-- Ordinary primitive honest-recipient failure mass; no claim of zero error is built into this definition. -/
noncomputable def failureRate (setup : Setup base KemSK) : ENNReal :=
  Pr{let sample ← experiment setup}[sample.2.2 ≠ some sample.2.1.2]

/-- The earlier universal support correctness condition is precisely the zero-error case of this ordinary primitive experiment. -/
theorem zero_iff (setup : Setup base KemSK) : failureRate setup = 0 ↔ RegistrationNativePairedCoordinates.RecipientCorrect setup := by
  rw [failureRate, prEvent_eq_zero_iff]
  constructor
  · intro zero pair generated encapsulated encapsulatedSupport answer decapsulatedSupport
    let sample : Sample setup := ⟨pair, generated, encapsulated, encapsulatedSupport, answer, decapsulatedSupport⟩
    exact Classical.not_not.mp (zero (pair, (encapsulated, answer)) (sample_supported setup sample))
  · intro correct sample supported
    simp only [experiment, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨pair, generated, encapsulated, encapsulatedSupport, answer, decapsulatedSupport, returned⟩ := supported
    cases returned
    exact fun failure => failure (correct pair generated encapsulated encapsulatedSupport answer decapsulatedSupport)

/-- A retained actual bad primitive sample entails positive ordinary primitive failure mass. -/
theorem failure_positive (setup : Setup base KemSK) (sample : Sample setup) (bad : sample.Bad setup) : 0 < failureRate setup := by
  apply (prEvent_pos_iff (experiment setup) _).mpr
  exact ⟨(sample.keyPair, (sample.encapsulated, sample.answer)), sample_supported setup sample, bad⟩

private theorem peer_root (value : List.Vector UInt8 32) : PqxdhPhase2GapDhSource.peer (rootArray value) = value :=
  PqxdhPhase2InputBytes.word_rootArray value
private theorem pq_root (value : MlKem768PublicKey) : RegistrationRootInput.pqKey (RegistrationAgreementRoot.pqArray value) = value := by
  apply Subtype.ext
  simp [RegistrationRootInput.pqKey, RegistrationAgreementRoot.pqArray, absBytes, List.map_map, Function.comp_def]

/-- The two actual collectors agree on every private root coordinate when their public source-stage fields match. -/
theorem collect_or_failure (setup : Setup base KemSK) (checks : Checks)
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
    :
    (serverInput.first = beaconInput.finishInputs.shared_secrets.dh1 ∧
      serverInput.second = beaconInput.finishInputs.shared_secrets.dh2 ∧
      serverInput.third = beaconInput.finishInputs.shared_secrets.dh3 ∧
      serverInput.fourth = beaconInput.finishInputs.shared_secrets.dh4 ∧
      serverInput.kem = beaconInput.finishInputs.shared_secrets.kem_shared_secret) ∨
      FailureAt setup before.2.2.pool owner.kemHandle serverInput beaconInput := by
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
  by_cases sameSecret : PqxdhPhase2InputBytes.word beaconInput.finishInputs.shared_secrets.kem_shared_secret = encapsulated.2
  · have sameWord := congrArg rootArray sameSecret
    rw [PqxdhPhase2InputBytes.word_roundtrip] at sameWord
    exact Or.inl ⟨firstEq, secondEq, thirdEq, fourthEq, kemEq.trans sameWord.symm⟩
  · exact Or.inr ⟨⟨pair, generated, encapsulated, encapsActual,
      some (PqxdhPhase2InputBytes.word beaconInput.finishInputs.shared_secrets.kem_shared_secret), decapsActual⟩,
      row, rfl, kemEq, by intro equal; exact sameSecret (Option.some.inj equal)⟩

end BeaconcryptCore.Computational.RegistrationNativeRecipientFailure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.sample_supported' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.sample_supported

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.zero_iff

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.failure_positive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.failure_positive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.collect_or_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecipientFailure.collect_or_failure

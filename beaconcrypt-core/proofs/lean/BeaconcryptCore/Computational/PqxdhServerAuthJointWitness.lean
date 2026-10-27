import BeaconcryptCore.Computational.PqxdhServerAuthWitnessDh
import BeaconcryptCore.Computational.PqxdhFirstBeaconRecordCanonical

open OracleComp OracleSpec
set_option autoImplicit false
set_option maxRecDepth 10000
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointWitness
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open PqxdhHypothesisWitness PqxdhServerAuthWitnessDh

/-- An explicitly insecure abstract primitive bundle for checking joint consistency, using the two-preimage symmetric toy and source-compatible signing format. -/
noncomputable def crypto : Pqxdh.Crypto :=
  { PqxdhServerAuthControlWitness.wCrypto with
    xsk := fun _ => zeroDh.toList
    xpub := publicKey
    x25519 := rawAgreement
    conv_agree := fun _ => congrArg (some ∘ List.Vector.toList) (normalize_word zeroDh).symm
    dh_comm := raw_comm
    xpub_length := fun a => (normalize a).toList_length
    x25519_length := fun a b => (agreement (normalize a) (normalize b)).toList_length }

/-- The toy satisfies the same complete X25519 peer-class contract used in the reduction. -/
theorem class_law : PqxdhServerAuthAssumptions.X25519ClassLaw crypto :=
  fun a left right same b => raw_class a b left right same

/-- The toy's two-scalar fibers satisfy the approved 64-preimage contract on the actual uniform scalar space. -/
theorem scalar_spread : PqxdhServerAuthAssumptions.X25519ScalarSpread crypto :=
  fun peer value _ => (raw_fiber_card peer value).trans (by decide)

/-- Honest agreement is nonzero on the same toy, with no distinct-key premise. -/
theorem nonzero_honest : PqxdhServerAuthAssumptions.NonzeroHonestDh crypto :=
  fun a b => raw_nonzero a (publicKey b)

/-- The full toy retains the original prefix-consistent HMAC/HKDF construction. -/
theorem prefix_consistent : PqxdhJointKdf.ProductionHkdfPrefixConsistent crypto :=
  ⟨fun input => hkdfOf_prefix toyHmac input _ 32 (by decide),
    fun input => hkdfOf_prefix toyHmac input _ 64 (by decide)⟩

noncomputable def source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource := ⟨crypto, prefix_consistent⟩

/-- All source 76-byte outputs are the actual two-block expansion of the toy HMAC. -/
theorem full_correct : SourceFullCorrect source toyHmac :=
  fun domain input => Subtype.ext (hkdfOf_full toyHmac domain input)

/-- The source root is the actual first32 projection of the same toy construction. -/
theorem root_correct : SourceRootCorrect source toyHmac := hkdfOf_root toyHmac

abbrev secret := PqxdhServerAuthControlWitness.wSecret

/-- The joint identity uses the same converted secret as the raw toy, with the existing attached-signature format. -/
noncomputable def joint : Primitives :=
  { PqxdhServerAuthControlWitness.wJoint with
    staticDh := fun seed peer => sourceDhReply crypto (secret seed).toList peer }

/-- One joint instance satisfies the exact Ed25519/X25519 source wiring without any authentication assumption. -/
theorem wiring : SourceWiring crypto joint secret where
  edPublic _ := rfl
  xPublic _ := congrArg List.Vector.toList (normalize_word zeroDh).symm
  attachedSign := PqxdhServerAuthControlWitness.wWiring.attachedSign
  verifyAttached := PqxdhServerAuthControlWitness.wWiring.verifyAttached
  staticDh _ _ := rfl

/-- The optional joint interface accepts every normalized toy peer; this is functional availability only. -/
theorem joint_available (seed : IdentitySeed) (peer : PeerEncoding) : (joint.staticDh seed peer).isSome = true := by
  simp only [joint, sourceDhReply, crypto, List.Vector.toList_mk, raw_nonzero, ↓reduceIte]
  rfl

/-- All scalar-interface calls are available on the same toy instance. -/
theorem scalar_available (scalar : ScalarBytes) (peer : PeerEncoding) :
    (sourceScalarDh crypto scalar peer).isSome = true := by
  simp only [sourceScalarDh, crypto, List.Vector.toList_mk, raw_nonzero, ↓reduceIte]
  rfl

noncomputable def serverDomain : PqxdhServerStaticDhSource.PublicDomain joint where
  accepts _ := true
  available := joint_available

noncomputable def beaconDomain : PqxdhPhase2GapDhSource.PublicDomain (sourceInterface crypto joint secret wiring) where
  accepts _ := true
  available := scalar_available
  nonzero := PqxdhServerAuthAssumptions.sourceScalarDh_nonzero crypto

/-- The complete toy setup shares its primitive bundle, related-identity interface and KEM with every subsequent theorem. -/
noncomputable def setup : PqxdhServerAuthExperiment.Setup Base Unit where
  source := source
  hmac := toyHmac
  joint := joint
  secretOfSeed := secret
  wiring := wiring
  serverDomain := serverDomain
  beaconDomain := beaconDomain
  kem := toyKem
  baseImpl := baseImpl
  serverKeyId := 0#u64

noncomputable abbrev codec := PqxdhServerAuthControlWitness.wCodec

/-- The same complete setup and abstract codec meet every relay and negative-control functional law, for any public size bound. -/
theorem control_laws (limit : Nat) : PqxdhServerAuthNegativeControl.ControlLaws setup codec limit where
  nonzero := nonzero_honest
  bodyLength _ _ _ _ := rfl
  phase1 := (PqxdhServerAuthControlWitness.wLaws limit).phase1
  phase2 := (PqxdhServerAuthControlWitness.wLaws limit).phase2
  frame := (PqxdhServerAuthControlWitness.wLaws limit).frame
  phase1Total := (PqxdhServerAuthControlWitness.wLaws limit).phase1Total
  frameBounded := (PqxdhServerAuthControlWitness.wLaws limit).frameBounded
  phase2Bounded := (PqxdhServerAuthControlWitness.wLaws limit).phase2Bounded

/-- The same setup's constant KEM has zero correctness error. -/
theorem kem_error : PqxdhServerAuthNegativeControl.kemError setup = 0 :=
  PqxdhServerAuthControlWitness.wKemError

/-- The existing abstract writer supports every frame decoded by its reader; no canonical-byte or serialization premise is used. -/
theorem read_writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead :=
  fun _ frame _ => ⟨PqxdhServerAuthControlWitness.enc _ frame, rfl⟩

/-- One instance simultaneously satisfies every new functional primitive and control-message premise. This is consistency, not a security claim. -/
theorem joint_witness : ∃ (s : PqxdhServerAuthExperiment.Setup Base Unit)
    (messages : PqxdhServerAuthExperiment.Codec PqxdhEd25519EufCma.Phase1Candidate
      PqxdhServerRegistrationPublication.ResponseFields),
    (∀ limit, PqxdhServerAuthNegativeControl.ControlLaws s messages limit) ∧
    PqxdhServerAuthAssumptions.X25519ClassLaw s.source.crypto ∧
    PqxdhServerAuthAssumptions.X25519ScalarSpread s.source.crypto ∧
    SourceRootCorrect s.source s.hmac ∧ SourceFullCorrect s.source s.hmac ∧
    PqxdhServerAuthNegativeControl.kemError s = 0 ∧
    PqxdhFirstBeaconRecordCanonical.ReadWritable messages.frameWrite messages.frameRead ∧
    Nonempty (PqxdhChallengeSecretRouting.FunctionalDecapsulation s.kem) :=
  ⟨setup, codec, control_laws, class_law, scalar_spread, root_correct, full_correct, kem_error, read_writable, ⟨toyFunctional⟩⟩

/-- The seed-reveal attack succeeds on the jointly satisfying instance, for every admission-check function. -/
theorem seed_control_wins (checks : PqxdhServerAuthExperiment.Checks) :
    1 ≤ (Pr{let result ← (PqxdhServerAuthExperiment.gameState setup codec checks true
        (PqxdhServerAuthNegativeControl.controlAdversary setup codec [1]))}[PqxdhServerAuthExperiment.W1 setup result.1 result.2.1 result.2.2.1.ghost]).toReal := by
  simpa only [kem_error, sub_zero] using
    PqxdhServerAuthNegativeControl.negative_control setup codec checks 100 (control_laws 100)
      toyFunctional [1] (by simp) (by simp)

/-- Honest relay has zero authentication-winning probability on the same joint witness, for any checks and payload. -/
theorem relay_zero (checks : PqxdhServerAuthExperiment.Checks) (payload : Option Pqxdh.Bytes) :
    (Pr{let x ← (PqxdhServerAuthExperiment.serverAuthGame setup codec checks false
      (PqxdhServerAuthNegativeControl.relayAdversary payload))}[x = true]).toReal = 0 := by
  exact le_antisymm (by simpa only [kem_error] using
    PqxdhServerAuthNegativeControl.relay_not_win setup codec checks (control_laws 0).toRelayLaws toyFunctional payload)
    ENNReal.toReal_nonneg

/-- The honest relay also reaches actual Beacon acceptance on that same jointly satisfying setup. -/
theorem relay_accepts :
    1 ≤ (Pr{let result ← (PqxdhServerAuthExperiment.gameState setup codec PqxdhServerAuthNegativeControl.acceptAll false
        (PqxdhServerAuthNegativeControl.relayAdversary none))}[result.2.2.1.ghost.acceptance ≠ none]).toReal := by
  have live := PqxdhServerAuthNegativeControl.relay_live setup codec 100 (control_laws 100) toyFunctional none
    (by simp [PqxdhServerRegistrationPublication.registrationWitness])
    (by simp [PqxdhServerRegistrationPublication.registrationWitness]; scalar_tac)
    (by simp [PqxdhServerRegistrationPublication.registrationWitness])
    (by decide)
  simpa only [kem_error, sub_zero] using live

end BeaconcryptCore.Computational.PqxdhServerAuthJointWitness

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.class_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.class_law
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.scalar_spread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.scalar_spread
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.nonzero_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.nonzero_honest
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.prefix_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.prefix_consistent
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.full_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.full_correct
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.root_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.root_correct
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.wiring' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.wiring
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.joint_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.joint_available
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.scalar_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.scalar_available
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.control_laws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.control_laws
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.kem_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.kem_error
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.read_writable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.read_writable
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.joint_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.joint_witness
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.seed_control_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.seed_control_wins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.relay_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.relay_zero
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.relay_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointWitness.relay_accepts

import BeaconcryptCore.Computational.PqxdhServerAuthNegativeControl
import BeaconcryptCore.Computational.PqxdhHypothesisWitness

/-!
A concrete deliberately insecure instance satisfies all functional premises of the registration negative and relay controls, with zero KEM correctness error. The instance checks that those controls reach the intended acceptance/winning events. Its constant nonzero DH does not satisfy scalar spread, and no hardness, security, or full-headline satisfiability conclusion is asserted. This ports only the separate witness portion of the handed-over scratch file; the existing control proofs are imported unchanged.
-/

open OracleComp OracleSpec ENNReal
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthControlWitness
open BeaconcryptCore.Computational
open PqxdhJointIdentity PqxdhJointGapDh PqxdhHypothesisWitness PqxdhJointKdfGame

/-! Toy primitives: F6's toy with a constant nonzero X25519 and a signature scheme that attaches 64 zero bytes. -/

def one32 : Pqxdh.Bytes := List.replicate 32 1

def wCrypto : Pqxdh.Crypto :=
  { toyCrypto with
    sign := fun _ message => List.replicate 64 0 ++ message
    verify := fun _ message => if 64 ≤ message.length then some (message.drop 64) else none
    x25519 := fun _ _ => one32
    verify_sign := by intro sk m; simp
    dh_comm := fun _ _ => rfl
    x25519_length := fun _ _ => by simp [one32] }

theorem w_prefix : PqxdhJointKdf.ProductionHkdfPrefixConsistent wCrypto :=
  ⟨fun input => hkdfOf_prefix toyHmac input _ 32 (by omega),
    fun input => hkdfOf_prefix toyHmac input _ 64 (by omega)⟩

def wSecret : IdentitySeed → List.Vector UInt8 64 := fun _ => List.Vector.replicate 64 0

def wJoint : Primitives where
  publicKeys _ := ⟨List.Vector.replicate 32 0, List.Vector.replicate 32 0⟩
  sign _ _ := List.Vector.replicate 64 0
  verify _ _ _ := true
  staticDh seed peer := sourceDhReply wCrypto (wSecret seed).toList peer

theorem one32_ne : one32 ≠ Pqxdh.zero32 := by decide

theorem wWiring : SourceWiring wCrypto wJoint wSecret where
  edPublic _ := rfl
  xPublic _ := rfl
  attachedSign _ _ := by simp [wJoint, wCrypto, PqxdhEd25519EufCma.attachSignature]
  verifyAttached _ _ _ := by simp [wJoint, wCrypto, PqxdhEd25519EufCma.attachSignature]
  staticDh _ _ := rfl

def wServerDomain : PqxdhServerStaticDhSource.PublicDomain wJoint where
  accepts _ := true
  available _ _ := by
    simp only [wJoint, sourceDhReply]
    change (if one32 = Pqxdh.zero32 then _ else _ : Option DhOutput).isSome = true
    rw [ite_eq_right one32_ne]
    rfl

def wBeaconDomain : PqxdhPhase2GapDhSource.PublicDomain (sourceInterface wCrypto wJoint wSecret wWiring) where
  accepts _ := true
  available _ _ := by
    simp only [sourceInterface, sourceScalarDh]
    change (if one32 = Pqxdh.zero32 then _ else _ : Option DhOutput).isSome = true
    rw [ite_eq_right one32_ne]
    rfl
  nonzero _ _ value found := by
    simp only [sourceInterface, sourceScalarDh] at found
    change (if one32 = Pqxdh.zero32 then _ else _ : Option DhOutput) = _ at found
    rw [ite_eq_right one32_ne] at found
    cases found
    intro same
    exact one32_ne (congrArg List.Vector.toList same)

noncomputable def wSetup : PqxdhServerAuthExperiment.Setup Base Unit where
  source := ⟨wCrypto, w_prefix⟩
  hmac := toyHmac
  joint := wJoint
  secretOfSeed := wSecret
  wiring := wWiring
  serverDomain := wServerDomain
  beaconDomain := wBeaconDomain
  kem := toyKem
  baseImpl := baseImpl
  serverKeyId := 0#u64

/-! An abstract injective codec: each message is written as a unary byte string of an injective natural-number code, and read back by the inverse. -/

noncomputable def natCode (α : Type) [Countable α] : α → ℕ := Classical.choose (Countable.exists_injective_nat α)

theorem natCode_inj (α : Type) [Countable α] : Function.Injective (natCode α) :=
  Classical.choose_spec (Countable.exists_injective_nat α)

noncomputable def enc (α : Type) [Countable α] (a : α) : Pqxdh.Bytes := List.replicate (natCode α a + 1) 0

theorem enc_inj (α : Type) [Countable α] : Function.Injective (enc α) := by
  intro a b h
  have := congrArg List.length h
  simp only [enc, List.length_replicate, Nat.add_right_cancel_iff] at this
  exact natCode_inj α this

open Classical in
noncomputable def dec (α : Type) [Countable α] (bytes : Pqxdh.Bytes) : Option α :=
  if h : ∃ a, enc α a = bytes then some (Classical.choose h) else none

theorem dec_enc {α : Type} [Countable α] (a : α) : dec α (enc α a) = some a := by
  have h : ∃ b, enc α b = enc α a := ⟨a, rfl⟩
  simp only [dec, dite_eq_left h]
  exact congrArg some (enc_inj α (Classical.choose_spec h))

instance (ty : UScalarTy) : Countable (UScalar ty) :=
  Function.Injective.countable (f := UScalar.bv) (fun x y h => (UScalar.eq_equiv_bv_eq x y).2 h)

instance (n : Usize) : Countable (Std.Array U8 n) := inferInstanceAs (Countable { l : List U8 // l.length = n.val })

instance : Countable PqxdhEd25519EufCma.Phase1Candidate :=
  Function.Injective.countable (f := fun c => (c.identityKey, c.preKey, c.oneTimeKey, c.pqKey)) (by
    intro a b h
    cases a
    cases b
    simp_all)

instance : Countable PqxdhServerRegistrationPublication.ResponseFields :=
  Function.Injective.countable (f := fun c => (c.keyId, c.ephemeral, c.identity, c.kemCiphertext, c.appCiphertext)) (by
    intro a b h
    cases a
    cases b
    simp_all)

instance : Countable RawCtxReceive.DecodedFrame :=
  Function.Injective.countable (f := fun c => (c.sequence, c.sender, c.payload)) (by
    intro a b h
    cases a
    cases b
    simp_all)

noncomputable def wCodec : PqxdhServerAuthExperiment.Codec PqxdhEd25519EufCma.Phase1Candidate
    PqxdhServerRegistrationPublication.ResponseFields where
  read1 := dec _
  identity r := some r.identityKey
  pqField r := some r.pqKey
  preField r := some r.preKey
  oneField r := some r.oneTimeKey
  write1 c := some (enc _ c)
  write2 f := some (enc _ f)
  read2 := dec _
  ciphertext r := some r.kemCiphertext
  ephemeral r := some r.ephemeral
  serverIdentity r := some r.identity
  assignedId r := r.keyId
  application r := some r.appCiphertext
  frameRead := dec _
  frameWrite f := some (enc _ f)

/-! Joint satisfiability of every premise of both controls, with zero KEM error. -/

theorem wLaws (limit : Nat) : PqxdhServerAuthNegativeControl.ControlLaws wSetup wCodec limit where
  nonzero _ _ := one32_ne
  bodyLength _ _ _ _ := rfl
  phase1 c bytes h := by
    simp only [wCodec, Option.some.injEq] at h
    subst h
    exact ⟨c, dec_enc c, rfl, rfl, rfl, rfl⟩
  phase2 f bytes h := by
    simp only [wCodec, Option.some.injEq] at h
    subst h
    exact ⟨f, dec_enc f, rfl, rfl, rfl, rfl, rfl⟩
  frame f bytes h := by
    simp only [wCodec, Option.some.injEq] at h
    subst h
    exact ⟨by simp [enc], dec_enc f⟩
  phase1Total _ := ⟨_, rfl⟩
  frameBounded _ _ := ⟨_, rfl⟩
  phase2Bounded _ _ _ _ _ _ _ _ := ⟨_, rfl⟩

theorem wKemError : PqxdhServerAuthNegativeControl.kemError wSetup = 0 := by
  rw [PqxdhServerAuthNegativeControl.kemError, (OracleComp.prEvent_eq_zero_iff _ _).mpr, ENNReal.toReal_zero]
  simp [PqxdhKemCorrectnessError.errorExperiment, PqxdhKemCorrectnessError.sample, wSetup, toyKem]

/-- At the witness the negative control reaches `W1` with probability one, for every `Checks`. -/
theorem control_wins (checks : PqxdhServerAuthExperiment.Checks) :
    1 ≤ (Pr{let result ← (PqxdhServerAuthExperiment.gameState wSetup wCodec checks true
        (PqxdhServerAuthNegativeControl.controlAdversary wSetup wCodec [1]))}[PqxdhServerAuthExperiment.W1 wSetup result.1 result.2.1 result.2.2.1.ghost]).toReal := by
  have := PqxdhServerAuthNegativeControl.negative_control wSetup wCodec checks 100 (wLaws 100) toyFunctional [1]
    (by simp) (by simp)
  rwa [wKemError, sub_zero] at this

/-- At the witness the honest relay never wins, for every `Checks` and payload. -/
theorem relay_loses (checks : PqxdhServerAuthExperiment.Checks) (payload : Option Pqxdh.Bytes) :
    (Pr{let x ← (PqxdhServerAuthExperiment.serverAuthGame wSetup wCodec checks false
      (PqxdhServerAuthNegativeControl.relayAdversary payload))}[x = true]).toReal ≤ 0 := by
  have := PqxdhServerAuthNegativeControl.relay_not_win wSetup wCodec checks (wLaws 0).toRelayLaws toyFunctional
    payload
  rwa [wKemError] at this

/-- At the witness the honest relay with the default payload makes the Beacon accept with probability one. -/
theorem relay_accepts :
    1 ≤ (Pr{let result ← (PqxdhServerAuthExperiment.gameState wSetup wCodec PqxdhServerAuthNegativeControl.acceptAll false
        (PqxdhServerAuthNegativeControl.relayAdversary none))}[result.2.2.1.ghost.acceptance ≠ none]).toReal := by
  have := PqxdhServerAuthNegativeControl.relay_live wSetup wCodec 100 (wLaws 100) toyFunctional none
    (by simp [PqxdhServerRegistrationPublication.registrationWitness])
    (by simp [PqxdhServerRegistrationPublication.registrationWitness]; scalar_tac)
    (by simp [PqxdhServerRegistrationPublication.registrationWitness])
    (by
      intro h
      have := congrArg UScalar.val h
      rw [PqxdhRefinement.u64_max_val] at this
      simp [wSetup] at this)
  rwa [wKemError, sub_zero] at this


end BeaconcryptCore.Computational.PqxdhServerAuthControlWitness

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.w_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.w_prefix

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.one32_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.one32_ne

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.wWiring' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.wWiring

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.natCode_inj' depends on axioms: [Classical.choice] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.natCode_inj

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.enc_inj' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.enc_inj

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.dec_enc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.dec_enc

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.wLaws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.wLaws

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.wKemError' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.wKemError

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.control_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.control_wins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.relay_loses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.relay_loses

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.relay_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthControlWitness.relay_accepts

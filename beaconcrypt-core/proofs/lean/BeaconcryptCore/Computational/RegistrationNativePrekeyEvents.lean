-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical

/-! The public good APP event retains the equality between an accepted signed prekey and the signed prekey of the actual designated owner's published bundle. This equality is a literal public-transcript conjunct throughout later games. PQ-key equality alone does not imply it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativePrekeyEvents
open PqxdhEd25519EufCma (Phase1Candidate X25519PublicKey parsePrekeyMessage)
open PqxdhDeploymentInterface (Handle Budget)
variable {Value NativeState Reader Response : Type}

def publishedPrekey (candidate : Phase1Candidate) : Option X25519PublicKey :=
  parsePrekeyMessage (candidate.preKey.drop 64)

def publishedAt (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (index : Nat) : Option X25519PublicKey :=
  ((PqxdhDeploymentTranscript.bundleOf transcript index).bind (PqxdhDeploymentTranscript.candidateOf codec)).bind publishedPrekey

def acceptedAt (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (transcript : List PqxdhDeploymentInterface.Entry) (session : Nat) : Option X25519PublicKey :=
  (((PqxdhDeploymentTranscript.acceptOf transcript session).bind (PqxdhDeploymentTranscript.candidateOf codec)).bind
    (PqxdhDeploymentTranscript.acceptedKeys crypto)).map (fun keys => keys.2.prekey)

def Pinned (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKeyId : U64)
    (transcript : List PqxdhDeploymentInterface.Entry) : Handle → Prop
  | .owner _ => True
  | .peer keyId => ∀ session index,
      PqxdhDeploymentTranscript.designate crypto codec serverKeyId transcript (.peer keyId) = some (session, index) →
        acceptedAt crypto codec transcript session = publishedAt codec transcript index

def GoodApp (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState) : Prop :=
  ∃ index guess entry, claim observed.1 = some (index, guess) ∧
    observed.2.1.ledger.fresh[index]? = some entry ∧
    (PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript entry.handle).isSome ∧
    entry.message = guess ∧ Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId observed.2.1.ledger.transcript entry.handle

def GoodAt (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState) : Prop :=
  ∃ index guess entry session, claim observed.1 = some (index, guess) ∧
    observed.2.1.ledger.fresh[index]? = some entry ∧
    PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
    RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session.val target.1.val ∧
    entry.message = guess ∧ Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId observed.2.1.ledger.transcript entry.handle

open Classical in
noncomputable def goodEvent (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState) : Bool := decide (GoodApp crypto wire serverKeyId budget claim observed)

open Classical in
noncomputable def targetEvent (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState) : Bool := decide (GoodAt crypto wire serverKeyId budget target claim observed)

/-- Dropping only the public prekey conjunct recovers the original broad APP event. -/
theorem good_broad (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (good : GoodApp crypto wire serverKeyId budget claim observed) :
    RegistrationNativeEvents.CEAppWin crypto wire serverKeyId budget claim observed := by
  obtain ⟨index, guess, entry, claimed, fresh, designated, guessed, _pinned⟩ := good
  exact ⟨index, guess, entry, claimed, fresh, designated, guessed⟩

/-- The later selected event is the same canonical original target with its public pin equality retained. -/
theorem target_original (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (good : GoodAt crypto wire serverKeyId budget target claim observed) :
    RegistrationNativeParsedTargetCanonical.CEAppAt crypto wire serverKeyId budget target claim observed := by
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed, _pinned⟩ := good
  exact ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩
/-- The complementary event uses the original single parsed-accept by owner target product, preserving its same pinned winning handle. -/
theorem good_selected (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before))
    (good : GoodApp crypto wire serverKeyId budget claim observed) :
    ∃ target : Fin budget.accept × Fin budget.capacity, GoodAt crypto wire serverKeyId budget target claim observed := by
  obtain ⟨index, guess, entry, claimed, fresh, eligible, guessed, pinned⟩ := good
  obtain ⟨original, designated⟩ := Option.isSome_iff_exists.mp eligible
  have consistent := RegistrationNativeFullCompiler.ledger_projection crypto wire serverKeyId bounds typed mode work before observed supported
  have actual := designated
  rw [consistent] at actual
  obtain ⟨parsed, accepted⟩ := RegistrationNativeParsedTargetCanonical.designated_first crypto wire serverKeyId budget observed.2.1.transcript entry.handle original actual
  have smaller := RegistrationNativeParsedTargetCaps.accepted_lt wire _ original.1.val parsed
    (RegistrationNativeParsedTargetCanonical.accepted_original wire _ original.1.val parsed accepted)
  have capped := RegistrationNativeParsedTargetCaps.run_accepts crypto wire serverKeyId bounds typed mode work budget bounded before observed supported
  exact ⟨(⟨parsed, Nat.lt_of_lt_of_le smaller capped⟩, original.2), index, guess, entry, original.1,
    claimed, fresh, designated, accepted, guessed, pinned⟩

/-- The retained pin conjunct belongs to the unique original claimed fresh entry, regardless of which equivalent canonical witness a later proof extracts. -/
theorem target_pinned (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : RegistrationNativeEvents.Observed Value NativeState)
    (good : GoodAt crypto wire serverKeyId budget target claim observed)
    (index : Nat) (guess : Pqxdh.Bytes) (entry : PqxdhDeploymentSecrecy.FreshEntry)
    (claimed : claim observed.1 = some (index, guess)) (fresh : observed.2.1.ledger.fresh[index]? = some entry) :
    Pinned crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId observed.2.1.ledger.transcript entry.handle := by
  obtain ⟨otherIndex, otherGuess, otherEntry, _session, otherClaimed, otherFresh, _designated, _accepted, _guessed, pinned⟩ := good
  have pair := Option.some.inj (otherClaimed.symm.trans claimed)
  have sameIndex : otherIndex = index := congrArg Prod.fst pair
  subst otherIndex
  have sameEntry := Option.some.inj (otherFresh.symm.trans fresh)
  exact sameEntry ▸ pinned

end BeaconcryptCore.Computational.RegistrationNativePrekeyEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.good_broad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.good_broad

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.target_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.target_original

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.good_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.good_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.target_pinned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePrekeyEvents.target_pinned

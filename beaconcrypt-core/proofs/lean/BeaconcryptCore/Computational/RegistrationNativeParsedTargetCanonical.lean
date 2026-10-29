-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents

/-! The selected parsed attempt is the canonical successful accept used by the original broad designation. This stronger additive selector keeps the original session existential and adds no bundle-byte or ML-key membership restriction. The original broad probability still uses one parsed-accept by owner target product. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
open RegistrationNativeInterface (Entry ModeSpec Respects)
open RegistrationNativeWire (Wire)
open RegistrationNativeEvents (Observed CEAppWin parsedAcceptCount)
open PqxdhDeploymentInterface (Handle Budget Mode FreshBounds)
variable {Value NativeState : Type}

def AcceptedAt (wire : Wire) (transcript : List Entry) (session parsed : Nat) : Prop :=
  ∃ before raw packet after,
    transcript = before ++ (Entry.mk (.inl (.inr (.accept raw))) (some session)) :: after ∧
    parsedAcceptCount wire before = parsed ∧ RegistrationNativeWire.readInit wire raw = some packet ∧
    PqxdhDeploymentTranscript.acceptOf (transcript.map Entry.erase) session = some raw

def CEAppAt (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Prop :=
  ∃ index guess entry session, claim observed.1 = some (index, guess) ∧
    observed.2.1.ledger.fresh[index]? = some entry ∧
    PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
    AcceptedAt wire observed.2.1.transcript session.val target.1.val ∧ entry.message = guess

open Classical in
noncomputable def event (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Bool := decide (CEAppAt crypto wire serverKeyId budget target claim observed)

/-- The canonical witness includes the complete original successful native accept and actual bounded decoder result. -/
theorem accepted_original (wire : Wire) (transcript : List Entry) (session parsed : Nat)
    (accepted : AcceptedAt wire transcript session parsed) :
    RegistrationNativeParsedTarget.AcceptedAt wire transcript session parsed := by
  obtain ⟨before, raw, packet, after, actual, counted, read, _first⟩ := accepted
  exact ⟨before, raw, packet, after, actual, counted, read⟩

private theorem erase_accept (entry : Entry) (raw : Pqxdh.Bytes) (session : Nat)
    (equal : entry.erase = (⟨.inl (.inr (.accept raw)), some session⟩ : PqxdhDeploymentInterface.Entry)) :
    entry = ⟨.inl (.inr (.accept raw)), some session⟩ := by
  rcases entry with ⟨((coin | command) | secrecy), reply⟩
  · cases equal
  · cases command <;> cases equal
    rfl
  · cases equal

/-- Original designation supplies its canonical accept bytes and their exact native parsed ordinal. -/
theorem designated_first (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64)
    (budget : Budget) (transcript : List Entry) (handle : Handle)
    (target : Fin budget.accept × Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget (transcript.map Entry.erase) handle = some target) :
    ∃ parsed, AcceptedAt wire transcript target.1.val parsed := by
  have plain := PqxdhDeploymentKemTransfer.designateIn_some crypto _ serverKeyId budget _ handle target designated
  obtain ⟨raw, candidate, _, _, accepted, read, _⟩ :=
    PqxdhDeploymentKemTransfer.designate_keys crypto _ serverKeyId _ handle target.1.val target.2.val plain
  obtain ⟨packet, parsed⟩ := RegistrationNativeParsedTarget.candidate_parsed wire raw candidate read
  have member := PqxdhDeploymentKemTransfer.acceptOf_mem _ target.1.val raw accepted
  obtain ⟨entry, nativeMember, erased⟩ := List.mem_map.mp member
  have same := erase_accept entry raw target.1.val erased
  subst entry
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp nativeMember
  exact ⟨parsedAcceptCount wire before, before, raw, packet, after, split, rfl, parsed, accepted⟩

/-- The additive canonical selector keeps all original broad claim, fresh-message and designation conditions. -/
theorem selected_original (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) (winning : CEAppAt crypto wire serverKeyId budget target claim observed) :
    RegistrationNativeParsedTargetEvents.CEAppAt crypto wire serverKeyId budget target claim observed := by
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩ := winning
  exact ⟨index, guess, entry, session, claimed, fresh, designated,
    accepted_original wire _ session.val target.1.val accepted, guessed⟩

/-- Every actual broad native success has a canonical selected parsed attempt in the same original target product. -/
theorem broad_selected (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (budget : Budget) (bounded : Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState)
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before)) :
    CEAppWin crypto wire serverKeyId budget claim observed ↔
      ∃ target : Fin budget.accept × Fin budget.capacity, CEAppAt crypto wire serverKeyId budget target claim observed := by
  constructor
  · rintro ⟨index, guess, entry, claimed, fresh, eligible, guessed⟩
    obtain ⟨original, designated⟩ := Option.isSome_iff_exists.mp eligible
    have consistent := RegistrationNativeFullCompiler.ledger_projection crypto wire serverKeyId bounds typed mode work before observed supported
    have actual := designated
    rw [consistent] at actual
    obtain ⟨parsed, accepted⟩ := designated_first crypto wire serverKeyId budget observed.2.1.transcript entry.handle original actual
    have smaller := RegistrationNativeParsedTargetCaps.accepted_lt wire _ original.1.val parsed
      (accepted_original wire _ original.1.val parsed accepted)
    have capped := RegistrationNativeParsedTargetCaps.run_accepts crypto wire serverKeyId bounds typed mode work budget bounded before observed supported
    exact ⟨(⟨parsed, Nat.lt_of_lt_of_le smaller capped⟩, original.2), index, guess, entry, original.1,
      claimed, fresh, designated, accepted, guessed⟩
  · rintro ⟨target, winning⟩
    exact RegistrationNativeParsedTargetEvents.selected_broad crypto wire serverKeyId budget target claim observed
      (selected_original crypto wire serverKeyId budget target claim observed winning)

/-- The original broad event has a single canonical parsed-accept times owner union bound, retaining changed accepted packets. -/
theorem broad_probability (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (bounds : FreshBounds)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (mode : Mode) (work : OracleComp (ModeSpec mode) Value) (budget : Budget) (bounded : Respects budget work)
    (before : NativeState) (claim : Value → Option (Nat × Pqxdh.Bytes)) :
    Pr{let observed ← RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
      CEAppWin crypto wire serverKeyId budget claim observed] ≤
      ∑ target : Fin budget.accept × Fin budget.capacity,
        Pr{let observed ← RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
          CEAppAt crypto wire serverKeyId budget target claim observed] := by
  classical
  calc
    _ ≤ Pr{let observed ← RegistrationNativeFullCompiler.run crypto wire serverKeyId bounds typed mode work before}[
        ∃ target ∈ (Finset.univ : Finset (Fin budget.accept × Fin budget.capacity)),
          CEAppAt crypto wire serverKeyId budget target claim observed] := by
      apply prEvent_mono_of_support
      intro observed supported winning
      obtain ⟨target, selected⟩ := (broad_selected crypto wire serverKeyId bounds typed mode work budget bounded
        before claim observed supported).mp winning
      exact ⟨target, Finset.mem_univ target, selected⟩
    _ ≤ _ := prEvent_exists_finset_le Finset.univ _ _

end BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.accepted_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.accepted_original
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.designated_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.designated_first
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.selected_original' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.selected_original
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.broad_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.broad_selected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical.broad_probability

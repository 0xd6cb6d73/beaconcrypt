-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCaps

/-! The original broad native CE-APP event is covered by one parsed-accept by owner target product. The session handle stays existential and is not another finite sum. Every selected event retains the original private fresh entry, successful native accept, original public verified-key designation and exact guessed bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents
open RegistrationNativeWire (Wire)
open RegistrationNativeEvents (Observed CEAppWin)
open RegistrationNativeInterface (ModeSpec Respects)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable {Value NativeState : Type}

def CEAppAt (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Prop :=
  ∃ index guess entry session, claim observed.1 = some (index, guess) ∧
    observed.2.1.ledger.fresh[index]? = some entry ∧
    PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
    RegistrationNativeParsedTarget.AcceptedAt wire observed.2.1.transcript session.val target.1.val ∧
    entry.message = guess

open Classical in
noncomputable def ceAppAtEvent (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Bool :=
  decide (CEAppAt crypto wire serverKeyId budget target claim observed)

/-- Selecting the actual parsed attempt keeps every original broad APP condition. -/
theorem selected_broad (crypto : Pqxdh.Crypto) (wire : Wire) (serverKeyId : U64) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) (winning : CEAppAt crypto wire serverKeyId budget target claim observed) :
    CEAppWin crypto wire serverKeyId budget claim observed := by
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, _accepted, guessed⟩ := winning
  exact ⟨index, guess, entry, claimed, fresh, by simp only [designated, Option.isSome_some], guessed⟩

/-- Every successful actual full native execution has a selected parsed attempt and owner, with no equality between its successful session and either counter. -/
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
    obtain ⟨parsed, accepted⟩ := RegistrationNativeParsedTarget.designated_accept crypto wire serverKeyId budget
      observed.2.1.transcript entry.handle original actual
    have smaller := RegistrationNativeParsedTargetCaps.accepted_lt wire _ original.1.val parsed accepted
    have capped := RegistrationNativeParsedTargetCaps.run_accepts crypto wire serverKeyId bounds typed mode work budget bounded before observed supported
    exact ⟨(⟨parsed, Nat.lt_of_lt_of_le smaller capped⟩, original.2), index, guess, entry, original.1,
      claimed, fresh, designated, accepted, guessed⟩
  · rintro ⟨target, winning⟩
    exact selected_broad crypto wire serverKeyId budget target claim observed winning

/-- The original broad native source probability has one accept-times-owner union bound, without an extra session or getter factor. -/
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

end BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents.selected_broad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents.selected_broad
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents.broad_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents.broad_selected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents.broad_probability

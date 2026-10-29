-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEvents

/-! Selecting an owner partitions the original broad native CE-APP eligibility by the original designation's owner coordinate. It neither requires unchanged accepted bytes nor adds ML-key membership. This owner coordinate is one coordinate of the eventual accept-by-creation target product, not an additional guess outside that product. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectedEvents
open RegistrationNativeEvents (Observed CEAppWin)
variable {Value NativeState : Type}

def CEAppOwnerWin (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : Aeneas.Std.U64) (budget : PqxdhDeploymentInterface.Budget)
    (selectedOwner : Nat) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Prop :=
  ∃ index guess entry target, claim observed.1 = some (index, guess) ∧
    observed.2.1.ledger.fresh[index]? = some entry ∧
    PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript entry.handle = some target ∧
    target.2.val = selectedOwner ∧ entry.message = guess

open Classical in
noncomputable def ceAppOwnerEvent (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : Aeneas.Std.U64) (budget : PqxdhDeploymentInterface.Budget)
    (selectedOwner : Nat) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState) : Bool :=
  decide (CEAppOwnerWin crypto wire serverKeyId budget selectedOwner claim observed)

/-- The selected-owner event preserves every original claim, fresh-message and broad verified-key designation condition. -/
theorem selected_broad (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : Aeneas.Std.U64) (budget : PqxdhDeploymentInterface.Budget)
    (selectedOwner : Nat) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value NativeState)
    (winning : CEAppOwnerWin crypto wire serverKeyId budget selectedOwner claim observed) :
    CEAppWin crypto wire serverKeyId budget claim observed := by
  obtain ⟨index, guess, entry, target, claimed, fresh, designated, _owner, guessed⟩ := winning
  exact ⟨index, guess, entry, claimed, fresh, by simp only [designated, Option.isSome_some], guessed⟩

/-- Every original broad success belongs to an owner in the same original bounded target set. -/
theorem broad_selected (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : Aeneas.Std.U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (observed : Observed Value NativeState) :
    CEAppWin crypto wire serverKeyId budget claim observed ↔
      ∃ owner : Fin budget.capacity, CEAppOwnerWin crypto wire serverKeyId budget owner.val claim observed := by
  constructor
  · rintro ⟨index, guess, entry, claimed, fresh, designated, guessed⟩
    obtain ⟨target, found⟩ := Option.isSome_iff_exists.mp designated
    exact ⟨target.2, index, guess, entry, target, claimed, fresh, found, rfl, guessed⟩
  · rintro ⟨owner, winning⟩
    exact selected_broad crypto wire serverKeyId budget owner.val claim observed winning

/-- The original broad source probability is covered by its owner-coordinate shares, without multiplying an existing target product again. -/
theorem broad_probability (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (serverKeyId : Aeneas.Std.U64) (budget : PqxdhDeploymentInterface.Budget)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (work : ProbComp (Observed Value NativeState)) :
    Pr{let observed ← work}[CEAppWin crypto wire serverKeyId budget claim observed] ≤
      ∑ owner : Fin budget.capacity, Pr{let observed ← work}[
        CEAppOwnerWin crypto wire serverKeyId budget owner.val claim observed] := by
  classical
  calc
    _ ≤ Pr{let observed ← work}[∃ owner ∈ (Finset.univ : Finset (Fin budget.capacity)),
        CEAppOwnerWin crypto wire serverKeyId budget owner.val claim observed] := by
      apply prEvent_mono
      intro observed winning
      obtain ⟨owner, selected⟩ := (broad_selected crypto wire serverKeyId budget claim observed).mp winning
      exact ⟨owner, Finset.mem_univ owner, selected⟩
    _ ≤ _ := prEvent_exists_finset_le Finset.univ _ _

end BeaconcryptCore.Computational.RegistrationNativeSelectedEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedEvents.selected_broad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedEvents.selected_broad
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedEvents.broad_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedEvents.broad_selected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectedEvents.broad_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectedEvents.broad_probability

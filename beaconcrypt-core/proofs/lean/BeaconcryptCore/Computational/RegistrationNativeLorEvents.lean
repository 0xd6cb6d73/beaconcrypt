-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLedgerHiding
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor

/-! Public eligibility and eligible correct guessing for the unchanged native experiment. Eligibility recomputes test admission from the public transcript, including failed sends and rejected tests. It never reads the private test bit or a hidden-slot predicate. Winning reads the original bit retained in the same original ledger. These are native events and observation lemmas, not a native confidentiality bound. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeLorEvents
open PqxdhDeploymentInterface (Budget)
open PqxdhRecordLiftIdeal (firstTest AdmittedTest)
open PqxdhDeploymentTranscript (SameView designateIn)
open RegistrationNativeLedgerHiding (view StateRel)
variable {Value : Type}

abbrev PublicEntry := RegistrationNativeLedgerHiding.PublicEntry
abbrev Filter (Value : Type) := Value × List PublicEntry → Bool

/-- Every admitted test has the same broad public designation as the first admitted test. -/
def EligibleAt (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : Filter Value) (target : Fin budget.accept × Fin budget.capacity)
    (result : Value × RegistrationNativeLedger.State) : Prop :=
  filter (result.1, result.2.transcript.map view) = true ∧
    (∃ first, firstTest result.2.ledger.transcript = some first ∧
      designateIn crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget result.2.ledger.transcript first = some target) ∧
    ∀ before entry after handle left right, result.2.ledger.transcript = before ++ entry :: after →
      entry.query = .inr (.test handle left right) →
      AdmittedTest crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId before handle left right →
      designateIn crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget result.2.ledger.transcript handle = some target

/-- The native event retains the exact original private test bit. -/
def WinAt (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : Filter Value) (guess : Value → Bool)
    (target : Fin budget.accept × Fin budget.capacity) (result : Value × RegistrationNativeLedger.State) : Prop :=
  EligibleAt crypto wire serverKeyId budget filter target result ∧
    result.2.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess result.1)

open Classical in
noncomputable def j (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : Filter Value) (result : Value × RegistrationNativeLedger.State) : Bool :=
  decide (∃ target, EligibleAt crypto wire serverKeyId budget filter target result)

open Classical in
noncomputable def w (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
    (budget : Budget) (filter : Filter Value) (guess : Value → Bool)
    (result : Value × RegistrationNativeLedger.State) : Bool :=
  decide (∃ target, WinAt crypto wire serverKeyId budget filter guess target result)

variable (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire) (serverKeyId : U64)
  (budget : Budget) (filter : Filter Value)

/-- Eligibility depends only on the two permitted public transcript views and the adversary's output. -/
theorem eligible_view (target : Fin budget.accept × Fin budget.capacity) (value : Value)
    (first second : RegistrationNativeLedger.State)
    (original : SameView first.ledger.transcript second.ledger.transcript)
    (native : first.transcript.map view = second.transcript.map view)
    (eligible : EligibleAt crypto wire serverKeyId budget filter target (value, first)) :
    EligibleAt crypto wire serverKeyId budget filter target (value, second) := by
  rcases eligible with ⟨filtered, ⟨handle, tested, designated⟩, admitted⟩
  have sameDesignation := (PqxdhDeploymentTranscript.designate_view crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId _ _ original).2 budget
  exact ⟨native ▸ filtered,
    ⟨handle, (PqxdhDeploymentHeadlineLor.firstTest_view _ _ original).symm.trans tested,
      (congrFun sameDesignation handle).symm.trans designated⟩,
    PqxdhDeploymentHeadlineLor.admitted_view crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId
      (fun admittedHandle => designateIn crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId budget
        second.ledger.transcript admittedHandle = some target) _ _ original
      (fun before entry after admittedHandle left right split query admittedTest =>
        (congrFun sameDesignation admittedHandle).symm.trans
          (admitted before entry after admittedHandle left right split query admittedTest))⟩

/-- The broad native eligibility event is determined by the permitted public view alone. -/
theorem j_view (value : Value) (first second : RegistrationNativeLedger.State)
    (original : SameView first.ledger.transcript second.ledger.transcript)
    (native : first.transcript.map view = second.transcript.map view) :
    j crypto wire serverKeyId budget filter (value, first) = j crypto wire serverKeyId budget filter (value, second) := by
  exact decide_eq_decide.mpr
    ⟨fun ⟨target, eligible⟩ => ⟨target, eligible_view crypto wire serverKeyId budget filter target value first second original native eligible⟩,
      fun ⟨target, eligible⟩ => ⟨target, eligible_view crypto wire serverKeyId budget filter target value second first original.symm native.symm eligible⟩⟩

theorem w_eq (guess : Value → Bool) (result : Value × RegistrationNativeLedger.State) :
    w crypto wire serverKeyId budget filter guess result =
      (j crypto wire serverKeyId budget filter result &&
        decide (result.2.ledger.test.map PqxdhDeploymentSecrecy.TestState.bit = some (guess result.1))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [w, j, Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨fun ⟨target, eligible, bit⟩ => ⟨⟨target, eligible⟩, bit⟩,
    fun ⟨⟨target, eligible⟩, bit⟩ => ⟨target, eligible, bit⟩⟩

/-- Native ledger hiding preserves the public eligibility event and all native ML-pin observations. -/
theorem j_related (value : Value) (first second : RegistrationNativeLedger.State) (related : StateRel first second) :
    j crypto wire serverKeyId budget filter (value, first) = j crypto wire serverKeyId budget filter (value, second) := by
  exact j_view crypto wire serverKeyId budget filter value first second related.1.1 related.2

/-- Native ledger hiding preserves eligible correct guessing with the literal original test bit. -/
theorem w_related (guess : Value → Bool) (value : Value) (first second : RegistrationNativeLedger.State)
    (related : StateRel first second) :
    w crypto wire serverKeyId budget filter guess (value, first) = w crypto wire serverKeyId budget filter guess (value, second) := by
  rw [w_eq, w_eq, j_related crypto wire serverKeyId budget filter value first second related, related.1.2.1]

/-- One adaptive execution can designate at most one target for its first admitted test. -/
theorem target_unique (result : Value × RegistrationNativeLedger.State)
    (firstTarget secondTarget : Fin budget.accept × Fin budget.capacity)
    (first : EligibleAt crypto wire serverKeyId budget filter firstTarget result)
    (second : EligibleAt crypto wire serverKeyId budget filter secondTarget result) : firstTarget = secondTarget := by
  rcases first.2.1 with ⟨firstHandle, firstTest, firstDesignated⟩
  rcases second.2.1 with ⟨secondHandle, secondTest, secondDesignated⟩
  exact Option.some.inj
    (((Option.some.inj (firstTest.symm.trans secondTest)) ▸ firstDesignated).symm.trans secondDesignated)

end BeaconcryptCore.Computational.RegistrationNativeLorEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEvents.eligible_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEvents.eligible_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEvents.j_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEvents.j_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEvents.w_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEvents.w_eq
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEvents.j_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEvents.j_related
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEvents.w_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEvents.w_related
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLorEvents.target_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLorEvents.target_unique

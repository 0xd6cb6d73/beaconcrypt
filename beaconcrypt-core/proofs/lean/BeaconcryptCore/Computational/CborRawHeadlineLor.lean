-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordLor
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineLor
import BeaconcryptCore.Computational.CborRawHeadlineRecords

/-! The actual raw record-ideal world preserves the CE-LOR public eligibility with an unbiased hidden test bit. The projection and slot containment are literal view facts, while the bit coupling executes the complete original raw ledger under the cursor. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineLor
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (FreshBounds ModeSpec Budget)
open PqxdhRecordLiftInterface (Frame EffectKind)
open CborRawHeadlineRecords (randomLoss)
open PqxdhDeploymentIdealParams (Target)
open PqxdhRecordLiftIdeal (View ctxView publicHiding)
open PqxdhDeploymentHeadlineEvents (lorWinEvent lorEligEvent lorClaim)
open PqxdhDeploymentHeadlineChain (slotted)
open PqxdhDeploymentIdealTrace (IdealSlots)
open PqxdhDeploymentHeadlineLor (decided_view lorEligEvent_view lorClaim_view idealSlots_view decisionHiding
  hidingOf guess_hiding win_slotted eligible_hiding)
variable {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- In the actual complete raw random-record world, the native slotted CE-LOR win has exactly half the native slotted eligibility probability. -/
theorem lor_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment 2 E)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (g : Fin budget.accept × Fin budget.capacity) (guess : X → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool) :
    𝒟[slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
        lorClaim g <$> (ctxView <$> CborRawRecordHidingLaw.ctxRun (fun _ => .random) id setup codec route env setup.serverKeyId bounds .P adversary)] {true} =
      2⁻¹ * 𝒟[slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
        lorClaim g <$> (ctxView <$> CborRawRecordHidingLaw.ctxRun (fun _ => .random) id setup codec route env setup.serverKeyId bounds .P adversary)] {true} := by
  have invariant : ∀ view view' : View 2 (E) X, publicHiding view = publicHiding view' →
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view =
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view' := fun view view' same =>
    decided_view setup codec budget _ lorClaim g
      (fun transcript slots => IdealSlots setup.source.crypto codec setup.serverKeyId (Target.ofCE budget g) slots
        transcript)
      (lorEligEvent_view setup.source.crypto codec setup.serverKeyId budget filter)
      (lorClaim_view setup.source.crypto codec setup.serverKeyId budget)
      (fun first second slots same => idealSlots_view setup.source.crypto codec setup.serverKeyId _ slots first second
        same) view view' same
  have hidden : ∀ view : View 2 (E) X,
      slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g
        view = true → PqxdhRecordLiftIdeal.TestsHidden setup.source.crypto codec setup.serverKeyId view :=
    fun view held => PqxdhDeploymentHeadlineContain.lor_hidden setup codec budget filter g view held
  have win : slotted (E := E) setup codec budget
      (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorGuess setup.source.crypto codec setup.serverKeyId (decisionHiding guess)
        (hidingOf (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view := funext fun view => by
    rw [guess_hiding setup codec guess _ invariant hidden view, win_slotted]
  have eligible : slotted (E := E) setup codec budget
      (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter) lorClaim g =
      fun view => PqxdhRecordLiftIdeal.lorEligible setup.source.crypto codec setup.serverKeyId
        (hidingOf (slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
          lorClaim g)) view := funext fun view => (eligible_hiding setup codec _ invariant hidden view).symm
  conv_lhs => rw [win, Functor.map_map]
  conv_rhs => rw [eligible, Functor.map_map]
  exact CborRawRecordLor.lor setup codec route env setup.serverKeyId bounds adversary (decisionHiding guess) _

/-- The actual raw all-real record world's slotted CE-LOR advantage is bounded by explicit win and eligibility record reductions. -/
theorem slotted_record_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : PqxdhRecordLiftInterface.Environment 2 E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (budget : Budget)
    (respects : budget.Respects adversary) (g : Fin budget.accept × Fin budget.capacity) (guess : X → Bool)
    (filter : List (PqxdhDeploymentInterface.PublicEntry .P) → Bool)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) :
    let win : View 2 E X → Bool := slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
      lorClaim g
    let eligible : View 2 E X → Bool := slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
      lorClaim g
    let real := PqxdhRecordLiftIdeal.chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route
      (CborRawRecordLiftBounds.client env setup.source.crypto codec setup.serverKeyId bounds .P adversary)
    ENNReal.ofReal |(𝒟[win <$> real] {true}).toReal - (1 / 2) * (𝒟[eligible <$> real] {true}).toReal| ≤
      randomLoss setup codec route env setup.serverKeyId bounds .P budget adversary win startup allowance fallback +
      2⁻¹ * randomLoss setup codec route env setup.serverKeyId bounds .P budget adversary eligible startup allowance fallback := by
  dsimp only
  let win : View 2 E X → Bool := slotted setup codec budget (lorWinEvent setup.source.crypto codec setup.serverKeyId budget guess filter)
    lorClaim g
  let eligible : View 2 E X → Bool := slotted setup codec budget (lorEligEvent setup.source.crypto codec setup.serverKeyId budget filter)
    lorClaim g
  let real := PqxdhRecordLiftIdeal.chainView <$> PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route
    (CborRawRecordLiftBounds.client env setup.source.crypto codec setup.serverKeyId bounds .P adversary)
  let ideal := ctxView <$> PqxdhRecordLiftLaterWorlds.ctxRunOf (fun _ => .random) id setup codec route
    (CborRawRecordLiftBounds.client env setup.source.crypto codec setup.serverKeyId bounds .P adversary)
  have closeWin := CborRawHeadlineRecords.random_close setup codec route env startup allowance framed setup.serverKeyId
    bounds .P budget adversary respects win correct fallback
  have closeEligible := CborRawHeadlineRecords.random_close setup codec route env startup allowance framed setup.serverKeyId
    bounds .P budget adversary respects eligible correct fallback
  have half := lor_final setup codec route env bounds adversary budget g guess filter
  change 𝒟[win <$> ideal] {true} = 2⁻¹ * 𝒟[eligible <$> ideal] {true} at half
  have bound := PqxdhDeploymentHeadlineLor.lor_bound_server
    (𝒟[win <$> real] {true}) (𝒟[eligible <$> real] {true})
    (𝒟[win <$> real] {true}) (𝒟[eligible <$> real] {true})
    (𝒟[win <$> real] {true}) (𝒟[eligible <$> real] {true})
    (𝒟[win <$> ideal] {true}) (𝒟[eligible <$> ideal] {true})
    (PqxdhDeploymentHeadlineChain.chance_ne_top _ _) (PqxdhDeploymentHeadlineChain.chance_ne_top _ _)
    rfl rfl half 0 0 (by simp) (by simp) _ _ closeWin closeEligible
  simpa only [ENNReal.ofReal_zero, zero_add] using bound

end BeaconcryptCore.Computational.CborRawHeadlineLor

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLor.lor_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLor.lor_final

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineLor.slotted_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineLor.slotted_record_bound

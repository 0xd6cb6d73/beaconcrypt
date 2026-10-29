-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordLorCoupling
import BeaconcryptCore.Computational.CborRawRecordFlatRun
import BeaconcryptCore.Computational.CborRawRecordEntropyAveraging
import BeaconcryptCore.Computational.CborRawRecordHidingLaw

/-! Public eligibility remains unbiased in the actual raw CBOR random-record world. The original eligible test bit is swapped below the ledger while equal-length alternatives take the same cursor-refusal branches. All private draws, native states, accepted test records and public replies remain in the paired execution. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordLor
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (ModeSpec FreshBounds asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (zeros ledgerInv_empty)
open PqxdhRecordLiftLor (lorGuess_flip lorGuess_hiding lorEligible_hiding)
open CborRawRecordFlat (fullImpl)
open CborRawRecordLorCoupling (Related Escaped escaped_keep step_couple)
open CborRawRecordFlatRun (startup install)
local notation "rawRun" => CborRawRecordHidingLaw.ctxRun
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool) :
    Swap (fun r₁ r₂ => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView r₁) =
        lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible (ctxView r₂))
      (rawRun modes zeros setup codec route env serverKid bounds .P adversary)
      (rawRun modes zeros setup codec route env serverKid bounds .P adversary) := by
  have flat := CborRawRecordFlatRun.ctxRun_flat modes zeros setup codec route env serverKid bounds .P adversary
  change rawRun modes zeros setup codec route env serverKid bounds .P adversary = _ at flat
  rw [flat]
  refine (Swap.refl (startup modes zeros setup codec route env) (R := Eq) fun _ => rfl).bind fun born _ hborn => ?_
  subst hborn
  rcases born with ⟨⟨⟨born, shell⟩, control⟩, secret⟩
  rcases born with _ | ⟨created, initial⟩
  · exact .pure _ _ (by simp [ctxView, viewOf, lorGuess, TestsHidden])
  · refine (Swap.refl (install modes zeros setup codec route created shell control secret) (R := Eq) fun _ => rfl).bind
      fun installed _ hinstalled => ?_
    subst hinstalled
    refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env serverKid bounds)
      (fullImpl modes zeros setup codec route env serverKid bounds) Related
      (Escaped setup.source.crypto codec serverKid) (Escaped setup.source.crypto codec serverKid)
      (escaped_keep modes zeros setup codec route env serverKid bounds)
      (escaped_keep modes zeros setup codec route env serverKid bounds)
      (step_couple modes setup codec route env serverKid bounds) (asModeO .P adversary) _ _
      ⟨rfl, rfl, ledgerInv_empty⟩).map ?_
    rintro ⟨x₁, ledger₁, state₁⟩ ⟨x₂, ledger₂, state₂⟩ (⟨hx, hstate, hledger, _⟩ | ⟨escaped₁, escaped₂⟩)
    · dsimp only at hx hstate hledger
      subst x₂ state₂ ledger₂
      exact (lorGuess_flip setup.source.crypto codec serverKid decision eligible x₁ ledger₁ state₁.1.1.1 _ _ _).symm
    · exact (PqxdhRecordLiftLor.lorGuess_escaped setup.source.crypto codec serverKid decision eligible x₁ ledger₁ (CborRawRecordFlat.project state₁) _ _
        escaped₁).trans (PqxdhRecordLiftLor.lorGuess_escaped setup.source.crypto codec serverKid _ eligible x₂ ledger₂ (CborRawRecordFlat.project state₂) _ _
          escaped₂).symm



/-- In the actual zeroed raw record world, a public decision wins on exactly half the eligible runs whose admitted test handles are hidden. -/
theorem lor_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool) :
    𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
      rawRun modes zeros setup codec route env serverKid bounds .P adversary] {true} =
      2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
        rawRun modes zeros setup codec route env serverKid bounds .P adversary] {true} :=
  CborRawRecordEntropyAveraging.lor_half setup.source.crypto codec serverKid decision eligible _
    (world_couple modes setup codec route env serverKid bounds adversary decision eligible)

/-- The actual raw CBOR cursor-filtered record-ideal world keeps arbitrary public eligibility unbiased with respect to its hidden test bit. -/
theorem lor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool) :
    𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
      rawRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary] {true} =
      2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
        rawRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary] {true} := by
  rw [CborRawRecordHidingLaw.law_zeros setup codec route env serverKid bounds adversary _
      (lorGuess_hiding setup.source.crypto codec serverKid decision eligible),
    CborRawRecordHidingLaw.law_zeros setup codec route env serverKid bounds adversary _
      (lorEligible_hiding setup.source.crypto codec serverKid eligible)]
  exact lor_zeros (fun _ => .random) setup codec route env serverKid bounds adversary decision eligible

end BeaconcryptCore.Computational.CborRawRecordLor

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLor.world_couple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLor.world_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLor.lor_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLor.lor_zeros

/-- info: 'BeaconcryptCore.Computational.CborRawRecordLor.lor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordLor.lor

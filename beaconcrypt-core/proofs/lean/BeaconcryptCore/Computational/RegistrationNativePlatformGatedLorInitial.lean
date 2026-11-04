-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordLorCoupling
import BeaconcryptCore.Computational.CborRawRecordFlatRun
import BeaconcryptCore.Computational.CborRawRecordEntropyAveraging
import BeaconcryptCore.Computational.CborRawRecordHidingLaw
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyPreamble

/-! Native left-or-right fairness after arbitrary actual startup effects in the same cursor, control and shared CTX cache. The secrecy ledger begins empty, and all equal-length test alternatives retain their actual refusal and failure branches. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (ModeSpec FreshBounds asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (zeros ledgerInv_empty)
open PqxdhRecordLiftLor (lorGuess_flip lorGuess_hiding lorEligible_hiding)
open RegistrationNativePlatformGatedRecordFreshCoupling (fullImpl)
open RegistrationNativePlatformGatedRecordLorCoupling (Related Escaped escaped_keep step_couple)
open CborRawRecordFlatRun (startup install)
local notation "rawRun" => RegistrationNativePlatformGatedEntropyInitial.run
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X Failure : Type}

theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool)
    (created : PqxdhLiveServerConstruction.Created Unit) (state : CborRawRecordFlat.NativeState n E) :
    Swap (fun r₁ r₂ => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView r₁) =
        lorGuess setup.source.crypto codec serverKid (fun projection => !decision projection) eligible (ctxView r₂))
      (rawRun modes zeros setup codec route env reserve serverKid bounds .P adversary created state)
      (rawRun modes zeros setup codec route env reserve serverKid bounds .P adversary created state) := by
  unfold RegistrationNativePlatformGatedEntropyInitial.run
  refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env reserve serverKid bounds)
    (fullImpl modes zeros setup codec route env reserve serverKid bounds) Related
    (Escaped setup.source.crypto codec serverKid) (Escaped setup.source.crypto codec serverKid)
    (escaped_keep modes zeros setup codec route env reserve serverKid bounds)
    (escaped_keep modes zeros setup codec route env reserve serverKid bounds)
    (step_couple modes setup codec route env reserve serverKid bounds) (asModeO .P adversary) _ _
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
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool)
    (created : PqxdhLiveServerConstruction.Created Unit) (state : CborRawRecordFlat.NativeState n E) :
    𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
      rawRun modes zeros setup codec route env reserve serverKid bounds .P adversary created state] {true} =
      2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
        rawRun modes zeros setup codec route env reserve serverKid bounds .P adversary created state] {true} :=
  CborRawRecordEntropyAveraging.lor_half setup.source.crypto codec serverKid decision eligible _
    (world_couple modes setup codec route env reserve serverKid bounds adversary decision eligible created state)

/-- The actual raw CBOR cursor-filtered record-ideal world keeps arbitrary public eligibility unbiased with respect to its hidden test bit. -/
theorem lor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (decision eligible : PublicHiding n E X → Bool)
    (created : PqxdhLiveServerConstruction.Created Unit) (state : CborRawRecordFlat.NativeState n E) :
    𝒟[(fun result => lorGuess setup.source.crypto codec serverKid decision eligible (ctxView result)) <$>
      rawRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary created state] {true} =
      2⁻¹ * 𝒟[(fun result => lorEligible setup.source.crypto codec serverKid eligible (ctxView result)) <$>
        rawRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary created state] {true} := by
  rw [RegistrationNativePlatformGatedEntropyPreamble.law_zeros setup codec route env reserve serverKid bounds adversary created state _
      (lorGuess_hiding setup.source.crypto codec serverKid decision eligible),
    RegistrationNativePlatformGatedEntropyPreamble.law_zeros setup codec route env reserve serverKid bounds adversary created state _
      (lorEligible_hiding setup.source.crypto codec serverKid eligible)]
  exact lor_zeros (fun _ => .random) setup codec route env reserve serverKid bounds adversary decision eligible created state

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial.world_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial.lor_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial.lor_zeros

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial.lor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedLorInitial.lor

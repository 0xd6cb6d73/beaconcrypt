-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordFreshCoupling
import BeaconcryptCore.Computational.CborRawRecordFlatRun
import BeaconcryptCore.Computational.CborRawRecordEntropyAveraging
import BeaconcryptCore.Computational.CborRawRecordHidingLaw

/-! Fresh-message guessing in the actual raw CBOR record world uses its cursor-aware source interpreter and the unchanged secrecy ledger. The whole-world byte-shift coupling retains reached cursor and native state, then finite disjoint-shift averaging gives the byte-accurate bound without a session-count multiplier. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordFresh
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (zeros)
open PqxdhRecordLiftFresh (hitAt shiftedHit extend shiftLedger_empty hitAt_shift freshEvent_hiding)
open CborRawRecordFlat (fullImpl)
open CborRawRecordFreshCoupling (FreshRelated FreshEscaped freshEscaped_keep step_couple)
open CborRawRecordFlatRun (startup install)
local notation "rawRun" => CborRawRecordHidingLaw.ctxRun
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (index length : ℕ) (offsets : Fin length → Fin 256) :
    Swap (fun r₁ r₂ => hitAt claim index length (ctxView r₁) =
        shiftedHit bounds claim index length offsets (ctxView r₂))
      (rawRun modes zeros setup codec route env serverKid bounds mode adversary)
      (rawRun modes zeros setup codec route env serverKid bounds mode adversary) := by
  have flat := CborRawRecordFlatRun.ctxRun_flat modes zeros setup codec route env serverKid bounds mode adversary
  change rawRun modes zeros setup codec route env serverKid bounds mode adversary = _ at flat
  rw [flat]
  refine (Swap.refl (startup modes zeros setup codec route env) (R := Eq) fun _ => rfl).bind fun born _ hborn => ?_
  subst hborn
  rcases born with ⟨⟨⟨born, shell⟩, control⟩, secret⟩
  rcases born with _ | ⟨created, initial⟩
  · exact .pure _ _ (by simp [ctxView, viewOf, hitAt, shiftedHit, FreshHit])
  · refine (Swap.refl (install modes zeros setup codec route created shell control secret) (R := Eq) fun _ => rfl).bind
      fun installed _ hinstalled => ?_
    subst hinstalled
    refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env serverKid bounds)
      (fullImpl modes zeros setup codec route env serverKid bounds) (FreshRelated bounds index (extend offsets))
      (FreshEscaped index) (FreshEscaped index)
      (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
      (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
      (step_couple modes setup codec route env serverKid bounds index (extend offsets)) (asModeO mode adversary) _ _
      ⟨rfl, (shiftLedger_empty index (extend offsets)).symm, fun _ h => absurd h List.not_mem_nil⟩).map ?_
    rintro ⟨x₁, ledger₁, state₁⟩ ⟨x₂, ledger₂, state₂⟩ (⟨hx, hstate, hledger, long⟩ | ⟨escaped₁, escaped₂⟩)
    · dsimp only at hx hstate hledger long
      subst x₂ state₂ ledger₂
      exact hitAt_shift bounds claim index length offsets x₁ ledger₁ state₁.1.1.1 _ _ _ long
    · exact (PqxdhRecordLiftFresh.hitAt_escaped claim index length x₁ ledger₁ (CborRawRecordFlat.project state₁) _ _ escaped₁).trans
        (PqxdhRecordLiftFresh.shiftedHit_escaped bounds claim index length offsets x₂ ledger₂ (CborRawRecordFlat.project state₂) _ _ escaped₂).symm


/-- The original actual fresh-message draw is measured in bytes, even if native CBOR admission subsequently refuses the send. -/
theorem fresh_zeros_bytes (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (claim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$>
      rawRun modes zeros setup codec route env serverKid bounds mode adversary] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ :=
  CborRawRecordEntropyAveraging.fresh_bound bounds claim _
    (fun index length offsets => world_couple modes setup codec route env serverKid bounds mode adversary claim index length offsets)

/-- Actual raw CBOR record-ideal fresh guessing has the same byte-accurate bound; no unguarded-program theorem or assumed simulation is used. -/
theorem fresh_bytes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X) (claim : X → Option (Nat × Pqxdh.Bytes)) :
    𝒟[(fun result => freshEvent claim (ctxView result)) <$>
      rawRun (fun _ => .random) id setup codec route env serverKid bounds .P adversary] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ := by
  rw [CborRawRecordHidingLaw.law_zeros setup codec route env serverKid bounds adversary _ (freshEvent_hiding claim)]
  exact fresh_zeros_bytes (fun _ => .random) setup codec route env serverKid bounds .P adversary claim

end BeaconcryptCore.Computational.CborRawRecordFresh

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFresh.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFresh.world_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFresh.fresh_zeros_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFresh.fresh_zeros_bytes

/-- info: 'BeaconcryptCore.Computational.CborRawRecordFresh.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordFresh.fresh_bytes

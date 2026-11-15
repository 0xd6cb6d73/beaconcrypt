-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordEntropyPreamble
import BeaconcryptCore.Computational.CborRawRecordWeightedFresh

/-! Selector-weighted entropy after arbitrary actual startup effects. The original secrecy ledger starts empty; cursor, native environment, counters and the complete shared CTX/private state are retained at their reached values. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawRecordWeightedInitial
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (zeros)
open PqxdhRecordLiftFresh (hitAt shiftedHit extend shiftLedger_empty freshEvent_hiding)
open CborRawRecordFreshCoupling (FreshRelated FreshEscaped freshEscaped_keep step_couple)
open CborRawRecordSelector (mask mask_hitAt mask_shiftedHit selected_shift)
open CborRawRecordEntropyInitial (run)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {base : OracleSpec ι}

theorem world_couple (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (select : PublicHiding n E X → Bool) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (state : CborRawRecordFlat.NativeState n E) (index length : Nat) (offsets : Fin length → Fin 256) :
    Swap (fun first second => hitAt claim index length (ctxView (mask select first)) =
      shiftedHit bounds claim index length offsets (ctxView (mask select second)))
      (run modes zeros setup codec route env serverKid bounds mode adversary created state)
      (run modes zeros setup codec route env serverKid bounds mode adversary created state) := by
  unfold run
  refine (Swap.simulateQ_run (CborRawRecordFlat.fullImpl modes zeros setup codec route env serverKid bounds)
    (CborRawRecordFlat.fullImpl modes zeros setup codec route env serverKid bounds)
    (FreshRelated bounds index (extend offsets)) (FreshEscaped index) (FreshEscaped index)
    (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
    (freshEscaped_keep modes zeros setup codec route env serverKid bounds index)
    (step_couple modes setup codec route env serverKid bounds index (extend offsets))
    (asModeO mode adversary) _ _
    ⟨rfl, (shiftLedger_empty index (extend offsets)).symm, fun _ member => absurd member List.not_mem_nil⟩).map ?_
  rintro ⟨first, ledger, native⟩ ⟨second, otherLedger, otherNative⟩
    (⟨sameValue, sameNative, sameLedger, long⟩ | ⟨escapedFirst, escapedSecond⟩)
  · dsimp only at sameValue sameNative sameLedger long
    subst second otherNative otherLedger
    rw [mask_hitAt, mask_shiftedHit]
    exact selected_shift select bounds claim index length offsets first ledger native.1.1.1
      native.2.base.produced (PqxdhRecordLiftProtocol.rawCounters native.1.2) (handleSlot native.1.2) long
  · rw [mask_hitAt, mask_shiftedHit]
    change (select _ && hitAt claim index length
      (⟨some (first, ledger, (CborRawRecordFlat.project native).1.1), native.2.base.produced,
        PqxdhRecordLiftProtocol.rawCounters native.1.2, handleSlot (CborRawRecordFlat.project native).1.2⟩ : View n E X)) =
      (select _ && shiftedHit bounds claim index length offsets
        (⟨some (second, otherLedger, (CborRawRecordFlat.project otherNative).1.1), otherNative.2.base.produced,
          PqxdhRecordLiftProtocol.rawCounters otherNative.1.2,
          handleSlot (CborRawRecordFlat.project otherNative).1.2⟩ : View n E X))
    rw [PqxdhRecordLiftFresh.hitAt_escaped claim index length first ledger (CborRawRecordFlat.project native)
      native.2.base.produced (PqxdhRecordLiftProtocol.rawCounters native.1.2) escapedFirst,
      PqxdhRecordLiftFresh.shiftedHit_escaped bounds claim index length offsets second otherLedger
        (CborRawRecordFlat.project otherNative) otherNative.2.base.produced
        (PqxdhRecordLiftProtocol.rawCounters otherNative.1.2) escapedSecond]
    simp only [Bool.and_false]

theorem fresh_zeros (modes : Label n → KeyMode) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (select : PublicHiding n E X → Bool) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (state : CborRawRecordFlat.NativeState n E) :
    𝒟[(fun result => select (publicHiding (ctxView result)) && freshEvent claim (ctxView result)) <$>
      run modes zeros setup codec route env serverKid bounds mode adversary created state] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[(fun result => select (publicHiding (ctxView result))) <$>
          run modes zeros setup codec route env serverKid bounds mode adversary created state] {true} := by
  have entropy := CborRawRecordEntropyMass.fresh_bound bounds claim
    (mask select <$> run modes zeros setup codec route env serverKid bounds mode adversary created state)
    (fun index length offsets =>
      (world_couple modes setup codec route env serverKid bounds mode adversary claim select created state index length offsets).map
        (fun _ _ related => related))
  simp only [Functor.map_map, CborRawRecordSelector.mask_fresh] at entropy
  exact entropy.trans (mul_le_mul' le_rfl
    (CborRawRecordWeightedFresh.mask_mass select (run modes zeros setup codec route env serverKid bounds mode adversary created state)))


theorem fresh_bytes (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (select : PublicHiding n E X → Bool) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (state : CborRawRecordFlat.NativeState n E) :
    𝒟[(fun result => select (publicHiding (ctxView result)) && freshEvent claim (ctxView result)) <$>
      run (fun _ => .random) id setup codec route env serverKid bounds .P adversary created state] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[(fun result => select (publicHiding (ctxView result))) <$>
          run (fun _ => .random) id setup codec route env serverKid bounds .P adversary created state] {true} := by
  rw [CborRawRecordEntropyPreamble.law_zeros setup codec route env serverKid bounds adversary created state
    (fun view => select (publicHiding view) && freshEvent claim view)
    (fun first second same => congrArg₂ (fun left right : Bool => left && right)
      (CborRawRecordWeightedFresh.selector_hiding select first second same) (freshEvent_hiding claim first second same))]
  rw [CborRawRecordEntropyPreamble.law_zeros setup codec route env serverKid bounds adversary created state
    (fun view => select (publicHiding view)) (CborRawRecordWeightedFresh.selector_hiding select)]
  exact fresh_zeros (fun _ => .random) setup codec route env serverKid bounds .P adversary claim select created state

end BeaconcryptCore.Computational.CborRawRecordWeightedInitial

/-- info: 'BeaconcryptCore.Computational.CborRawRecordWeightedInitial.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordWeightedInitial.world_couple

/-- info: 'BeaconcryptCore.Computational.CborRawRecordWeightedInitial.fresh_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordWeightedInitial.fresh_zeros

/-- info: 'BeaconcryptCore.Computational.CborRawRecordWeightedInitial.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordWeightedInitial.fresh_bytes

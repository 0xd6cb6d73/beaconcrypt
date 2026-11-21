-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordWeightedFresh
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFreshCoupling

/-! Selector-weighted fresh-byte entropy for the actual common-state gated World client. Allocation runs after the private send and before the ledger; its retry history remains in the equal public environment throughout byte-shift and hiding couplings. -/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftSwap
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftFlat (zeros zeros_length)
open PqxdhRecordLiftFresh (hitAt shiftedHit extend shiftLedger_empty hitAt_shift freshEvent_hiding)
open RegistrationNativePlatformGatedRecordFreshCoupling (fullImpl)
open RegistrationNativePlatformGatedRecordFreshCoupling (FreshRelated FreshEscaped freshEscaped_keep step_couple)
open CborRawRecordFlatRun (startup install)
open CborRawRecordSelector (mask mask_hitAt mask_shiftedHit selected_shift)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X Failure : Type}

open CborRawRecordWeightedFresh (mask_mass selector_hiding)

noncomputable def ctxRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
    (RegistrationNativePlatformGatedRecordInterface.client env reserve setup.source.crypto codec serverKid bounds mode adversary)

local notation "rawRun" => ctxRun

/-- Byte shifts couple complete executions while retaining any selector on the analysis projection. -/
theorem world_couple (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (select : PublicHiding n E X → Bool) (index length : Nat) (offsets : Fin length → Fin 256) :
    Swap (fun r₁ r₂ => hitAt claim index length (ctxView (mask select r₁)) =
      shiftedHit bounds claim index length offsets (ctxView (mask select r₂)))
      (rawRun modes zeros setup codec route env reserve serverKid bounds mode adversary)
      (rawRun modes zeros setup codec route env reserve serverKid bounds mode adversary) := by
  have flat := RegistrationNativePlatformGatedRecordFlat.program_flat modes zeros setup codec route env reserve serverKid bounds mode adversary
  rw [show rawRun modes zeros setup codec route env reserve serverKid bounds mode adversary = _ from flat]
  refine (Swap.refl (startup modes zeros setup codec route env) (R := Eq) fun _ => rfl).bind fun born _ hborn => ?_
  subst hborn
  rcases born with ⟨⟨⟨born, shell⟩, control⟩, secret⟩
  rcases born with _ | ⟨created, initial⟩
  · exact .pure _ _ (by
      rw [mask_hitAt, mask_shiftedHit]
      simp [ctxView, viewOf, hitAt, shiftedHit, FreshHit])
  · refine (Swap.refl (install modes zeros setup codec route created shell control secret) (R := Eq) fun _ => rfl).bind
      fun installed _ hinstalled => ?_
    subst hinstalled
    refine (Swap.simulateQ_run (fullImpl modes zeros setup codec route env reserve serverKid bounds)
      (fullImpl modes zeros setup codec route env reserve serverKid bounds) (FreshRelated bounds index (extend offsets))
      (FreshEscaped index) (FreshEscaped index)
      (freshEscaped_keep modes zeros setup codec route env reserve serverKid bounds index)
      (freshEscaped_keep modes zeros setup codec route env reserve serverKid bounds index)
      (step_couple modes setup codec route env reserve serverKid bounds index (extend offsets)) (asModeO mode adversary) _ _
      ⟨rfl, (shiftLedger_empty index (extend offsets)).symm, fun _ h => absurd h List.not_mem_nil⟩).map ?_
    rintro ⟨x₁, ledger₁, state₁⟩ ⟨x₂, ledger₂, state₂⟩ (⟨hx, hstate, hledger, long⟩ | ⟨escaped₁, escaped₂⟩)
    · dsimp only at hx hstate hledger long
      subst x₂ state₂ ledger₂
      rw [mask_hitAt, mask_shiftedHit]
      exact selected_shift select bounds claim index length offsets x₁ ledger₁ state₁.1.1.1
        state₁.2.base.produced (PqxdhRecordLiftProtocol.rawCounters state₁.1.2) (handleSlot state₁.1.2) long
    · rw [mask_hitAt, mask_shiftedHit]
      change (select _ && hitAt claim index length
        (⟨some (x₁, ledger₁, (CborRawRecordFlat.project state₁).1.1), state₁.2.base.produced,
          PqxdhRecordLiftProtocol.rawCounters state₁.1.2, handleSlot (CborRawRecordFlat.project state₁).1.2⟩ : View n E X)) =
        (select _ && shiftedHit bounds claim index length offsets
          (⟨some (x₂, ledger₂, (CborRawRecordFlat.project state₂).1.1), state₂.2.base.produced,
            PqxdhRecordLiftProtocol.rawCounters state₂.1.2, handleSlot (CborRawRecordFlat.project state₂).1.2⟩ : View n E X))
      rw [PqxdhRecordLiftFresh.hitAt_escaped claim index length x₁ ledger₁ (CborRawRecordFlat.project state₁)
        state₁.2.base.produced (PqxdhRecordLiftProtocol.rawCounters state₁.1.2) escaped₁,
        PqxdhRecordLiftFresh.shiftedHit_escaped bounds claim index length offsets x₂ ledger₂ (CborRawRecordFlat.project state₂)
        state₂.2.base.produced (PqxdhRecordLiftProtocol.rawCounters state₂.1.2) escaped₂]
      simp only [Bool.and_false]
/-- The actual cursor-aware zero-plaintext ideal world pays one byte-entropy baseline weighted by its own analysis-selector mass. -/
theorem fresh_zeros (modes : Label n → KeyMode) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (select : PublicHiding n E X → Bool) :
    𝒟[(fun result => select (publicHiding (ctxView result)) && freshEvent claim (ctxView result)) <$>
      rawRun modes zeros setup codec route env reserve serverKid bounds mode adversary] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[(fun result => select (publicHiding (ctxView result))) <$>
          rawRun modes zeros setup codec route env reserve serverKid bounds mode adversary] {true} := by
  have entropy := CborRawRecordEntropyMass.fresh_bound bounds claim
    (mask select <$> rawRun modes zeros setup codec route env reserve serverKid bounds mode adversary)
    (fun index length offsets =>
      (world_couple modes setup codec route env reserve serverKid bounds mode adversary claim select index length offsets).map
        (fun _ _ related => related))
  simp only [Functor.map_map, CborRawRecordSelector.mask_fresh] at entropy
  exact entropy.trans (mul_le_mul' le_rfl
    (mask_mass select (rawRun modes zeros setup codec route env reserve serverKid bounds mode adversary)))
theorem law_zeros (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (observe : View n E X → Bool)
    (invariant : ∀ first second, hidingView first = hidingView second → observe first = observe second) :
    (fun result => observe (ctxView result)) <$> ctxRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary =
      (fun result => observe (ctxView result)) <$>
        ctxRun (fun _ => .random) zeros setup codec route env reserve serverKid bounds .P adversary := by
  let factor : HidingView n E X → Bool := fun projection =>
    @dite _ (∃ view, hidingView view = projection) (Classical.propDecidable _) (fun h => observe h.choose)
      (fun _ => false)
  have factored : ∀ view, observe view = factor (hidingView view) := fun view => by
    have h : ∃ other, hidingView other = hidingView view := ⟨view, rfl⟩
    simp only [factor, h]
    exact invariant _ _ (Eq.symm (Exists.choose_spec (p := fun other => hidingView other = hidingView view) _))
  have replaced := RegistrationNativePlatformGatedRecordInterface.hiding_replace setup codec route env reserve serverKid bounds adversary id zeros
    fun message => (zeros_length message).symm
  change (fun result => hidingView (ctxView result)) <$>
      ctxRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary =
    (fun result => hidingView (ctxView result)) <$>
      ctxRun (fun _ => .random) zeros setup codec route env reserve serverKid bounds .P adversary at replaced
  calc (fun result => observe (ctxView result)) <$> ctxRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary
      = factor <$> ((fun result => hidingView (ctxView result)) <$>
          ctxRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary) := by
        rw [Functor.map_map]
        exact congrArg (fun f => f <$> ctxRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary)
          (funext fun result => factored (ctxView result))
    _ = factor <$> ((fun result => hidingView (ctxView result)) <$>
          ctxRun (fun _ => .random) zeros setup codec route env reserve serverKid bounds .P adversary) := by
        rw [replaced]
    _ = _ := by
        rw [Functor.map_map]
        exact congrArg (fun f => f <$> ctxRun (fun _ => .random) zeros setup codec route env reserve serverKid bounds .P
          adversary) (funext fun result => (factored (ctxView result)).symm)


/-- The actual mode-P random-record ideal world has the selector-weighted byte bound with its original ledger and all later callbacks. -/
theorem fresh_bytes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (claim : X → Option (Nat × Pqxdh.Bytes))
    (select : PublicHiding n E X → Bool) :
    𝒟[(fun result => select (publicHiding (ctxView result)) && freshEvent claim (ctxView result)) <$>
      rawRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary] {true} ≤
      ((256 ^ bounds.min : Nat) : ℝ≥0∞)⁻¹ *
        𝒟[(fun result => select (publicHiding (ctxView result))) <$>
          rawRun (fun _ => .random) id setup codec route env reserve serverKid bounds .P adversary] {true} := by
  rw [law_zeros setup codec route env reserve serverKid bounds adversary
    (fun view => select (publicHiding view) && freshEvent claim view)
    (fun first second same => congrArg₂ (fun left right : Bool => left && right)
      (selector_hiding select first second same) (freshEvent_hiding claim first second same))]
  rw [law_zeros setup codec route env reserve serverKid bounds adversary
    (fun view => select (publicHiding view)) (selector_hiding select)]
  exact fresh_zeros (fun _ => .random) setup codec route env reserve serverKid bounds .P adversary claim select

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.world_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.world_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.fresh_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.fresh_zeros

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.law_zeros' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.law_zeros

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.fresh_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordEntropy.fresh_bytes

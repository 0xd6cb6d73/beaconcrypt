-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingEvent

/-! Retained binding-conflict probability in the complete actual adaptive source run. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode sharedHashTotal ctxRun)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsBindingEvent (conflictEvent)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The original complete source run's retained commitment conflict has the source-derived global collision bound. -/
theorem run_conflict_bound (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decisionCost : Nat) :
    𝒟[(fun result => conflictEvent result.2) <$>
      ctxRun modes replace setup codec route env serverKid bounds mode adversary] {true} ≤
      ((budget.sends * (budget.sends + sharedHashTotal ⟨budget, startup, allowance, bounds, n, decisionCost⟩) : Nat) : ENNReal) /
        (2 : ENNReal)^512 := by
  rw [(PqxdhRecordFactsBindingEvent.run_conflict_observation modes replace setup codec route env serverKid bounds mode adversary ideal).evalDist_eq]
  refine le_trans ?_ (PqxdhRecordFactsHashCollision.erased_collision modes ideal replace setup codec route env
    startup allowance framed serverKid bounds mode budget adversary respects decisionCost)
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  apply prEvent_mono_of_support
  intro result reached conflict
  exact @decide_eq_true _ (Classical.propDecidable _) (PqxdhRecordFactsBindingEvent.conflict_collision result.2
    (PqxdhRecordFactsBindingCache.erased_run_cached modes ideal replace setup codec route env serverKid bounds mode adversary result reached)
    (@of_decide_eq_true _ (Classical.propDecidable _) conflict))

/-- The derived two-class collision term fits the unchanged frozen binding loss, with no additional selection factor. -/
theorem collision_le_binding (input : PqxdhRecordLiftIdeal.BillInput) :
    ((input.budget.sends * (input.budget.sends + sharedHashTotal input) : Nat) : ENNReal) /
      (2 : ENNReal)^512 ≤ PqxdhRecordLiftIdeal.bindingTerm input := by
  rw [Nat.mul_comm input.budget.sends (input.budget.sends + sharedHashTotal input)]
  simp only [PqxdhRecordLiftIdeal.bindingTerm, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  omega

end BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability.run_conflict_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability.run_conflict_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability.collision_le_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsBindingProbability.collision_le_binding

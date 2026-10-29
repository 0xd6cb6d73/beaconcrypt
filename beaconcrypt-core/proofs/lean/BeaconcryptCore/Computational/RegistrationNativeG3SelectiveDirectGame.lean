-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection

/-! The actual original two-pass key client has the selected-only finite material44/seed64 table law. Nonselected protected outputs use their existing independent byte cache. The original total material allowance excludes the explicit zero fallback internally, so no sampler, refusal, source-equivalence or alias assumption remains in this finite-service source law. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeG3FirstTouchBound (IsValue)
variable {n : Nat} {Value : Type}

def compiled (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp RegistrationNativeRetainedService.Spec Value) :=
  RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work) RegistrationNativeKeyPhases.emptyMeta

/-- For each fixed table, the actual direct selective service is the original capped two-pass native client under the same selected-only first-touch table, retaining every client observation. -/
theorem fixed_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp RegistrationNativeRetainedService.Spec Value)
    (bounded : (compiled source input inside work).IsQueryBoundP IsValue n) :
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds) work).run'
      (RegistrationNativeHiddenService.initial, ∅) =
      (simulateQ (RegistrationNativeG3FirstTouch.fixed (RegistrationNativeG3Tables.join materials seeds))
        ((simulateQ (RegistrationNativeG3SelectedTableRouter.handler
          (RegistrationNativeSelectiveHiddenService.selected inside candidate)) (compiled source input inside work)).run' ∅)).run'
          PqxdhRegistrationJointKemSecondEntry.emptyAlloc := by
  rw [RegistrationNativeG3SelectiveDirectProjection.client_source]
  let routed := (simulateQ (RegistrationNativeG3SelectedTableRouter.handler
    (RegistrationNativeSelectiveHiddenService.selected inside candidate)) (compiled source input inside work)).run' ∅
  have cap : routed.IsQueryBoundP IsValue n := by
    simpa only [routed, StateT.run'_eq, isQueryBoundP_map_iff] using
      RegistrationNativeG3SelectedTableRouterRun.program_bound
        (RegistrationNativeSelectiveHiddenService.selected inside candidate) (compiled source input inside work) n bounded ∅
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeG3SelectedZeroTable.zero (RegistrationNativeG3Tables.join materials seeds))
    (RegistrationNativeG3SelectedTableRouter.handler (RegistrationNativeSelectiveHiddenService.selected inside candidate))
    (compiled source input inside work) ∅ PqxdhRegistrationJointKemSecondEntry.emptyAlloc
  have observed := congrArg (Functor.map (fun result => result.1.1)) nested
  have total := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3SelectedZeroTable.program_source (RegistrationNativeG3Tables.join materials seeds) routed n cap
      PqxdhRegistrationJointKemSecondEntry.emptyAlloc (by simp [PqxdhRegistrationJointKemSecondEntry.emptyAlloc]))
  have first :
      (simulateQ (RegistrationNativeG3SelectiveFixedKeysSource.target (RegistrationNativeG3Tables.join materials seeds)
        (RegistrationNativeSelectiveHiddenService.selected inside candidate)) (compiled source input inside work)).run'
          (∅, PqxdhRegistrationJointKemSecondEntry.emptyAlloc) =
      (simulateQ (RegistrationNativeG3SelectedZeroTable.zero (RegistrationNativeG3Tables.join materials seeds)) routed).run'
        PqxdhRegistrationJointKemSecondEntry.emptyAlloc := by
    simpa only [StateT.run'_eq, simulateQ_map, StateT.run_map, Functor.map_map,
      RegistrationNativeG3SelectiveFixedKeysSource.target, routed] using observed.symm
  exact first.trans total

/-- Sampling selected material and seed tables beside the actual nonselected cache yields the literal original native lazy byte-table client law. -/
theorem lazy_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (work : OracleComp RegistrationNativeRetainedService.Spec Value)
    (bounded : (compiled source input inside work).IsQueryBoundP IsValue n) :
    LazyOracleDiscard.LawEq ((simulateQ PqxdhRegistrationJointKemSecondEntry.lazyImpl (compiled source input inside work)).run' ∅)
      (do
        let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
        let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
        (simulateQ (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds) work).run'
          (RegistrationNativeHiddenService.initial, ∅)) := by
  have split := RegistrationNativeG3SelectedTableRouterRun.lazy_split
    (RegistrationNativeSelectiveHiddenService.selected inside candidate) (compiled source input inside work) bounded
  have same : (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      Prod.fst <$> RegistrationNativeG3FirstTouchEager.fixedRun (RegistrationNativeG3Tables.join materials seeds)
        ((simulateQ (RegistrationNativeG3SelectedTableRouter.handler
          (RegistrationNativeSelectiveHiddenService.selected inside candidate)) (compiled source input inside work)).run' ∅)
        PqxdhRegistrationJointKemSecondEntry.emptyAlloc) = (do
      let materials ← $ᵗ RegistrationNativeG3Tables.MaterialTable n
      let seeds ← $ᵗ RegistrationNativeG3Tables.SeedTable n
      (simulateQ (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds) work).run'
        (RegistrationNativeHiddenService.initial, ∅)) := by
    apply bind_congr
    intro materials
    apply bind_congr
    intro seeds
    exact (fixed_source source input inside candidate materials seeds work bounded).symm
  rw [← same]
  exact split

end BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame.fixed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame.lazy_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectGame.lazy_source

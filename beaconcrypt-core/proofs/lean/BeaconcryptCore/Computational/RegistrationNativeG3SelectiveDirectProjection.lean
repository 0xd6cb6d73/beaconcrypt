-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3SelectiveFixedKeysSource

/-! The actual selective direct108-byte service factors through the original native descriptor-flag service and selected-only first-touch table. The explicit projection keeps every flag, selected byte-to-slot assignment, cursor and nonselected cache. Only the separately analyzed demand counter and unused material-cache field are omitted from this direct key-service state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedService (Flags)
variable {n : Nat} {Value : Type}

def project (before : RegistrationNativeSelectiveHiddenService.State n) :=
  (before.1.prepared, RegistrationNativeG3SelectiveFixedKeysSource.project before)

noncomputable def target (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n) :=
  ((RegistrationNativeG3SelectiveFixedKeysSource.target (RegistrationNativeG3Tables.join materials seeds)
      (RegistrationNativeSelectiveHiddenService.selected inside candidate)).mapStateTBase
    (RegistrationNativeG3KeyService.direct source input inside)).flattenStateT

private theorem count_flags (query : RegistrationNativeRetainedService.Spec.Domain)
    (before : RegistrationNativeSelectiveHiddenService.State n) :
    (RegistrationNativeG3SelectiveService.count query before).1.prepared = before.1.prepared := by
  rcases query with coin | (message | message) <;> rfl

private theorem count_project (query : RegistrationNativeRetainedService.Spec.Domain)
    (before : RegistrationNativeSelectiveHiddenService.State n) :
    RegistrationNativeG3SelectiveFixedKeysSource.project (RegistrationNativeG3SelectiveService.count query before) =
      RegistrationNativeG3SelectiveFixedKeysSource.project before := by
  rcases query with coin | (message | message) <;> rfl

/-- Each actual direct selective prepare/demand callback is the original native flag service under the exact selected-only byte-table source, preserving its reached dictionary and known cache. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (query : RegistrationNativeRetainedService.Spec.Domain) (before : RegistrationNativeSelectiveHiddenService.State n) :
    Prod.map id project <$> (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds query).run before =
      (target source input inside candidate materials seeds query).run (project before) := by
  have actual := RegistrationNativeG3SelectiveFixedKeysSource.program_source materials seeds inside candidate
    ((RegistrationNativeG3KeyService.direct source input inside query).run before.1.prepared)
    (RegistrationNativeG3SelectiveService.count query before)
  rw [count_project] at actual
  have mapped := congrArg (Functor.map (fun result => (result.1.1, (result.1.2, result.2)))) actual
  change Prod.map id project <$> simulateQ RegistrationNativeG3MetricCoins.localCoins
    ((fun result => (result.1.1, ({ result.2.1 with prepared := result.1.2 }, result.2.2))) <$>
      (simulateQ (RegistrationNativeG3SelectiveService.fixedKeys materials seeds inside candidate)
        ((RegistrationNativeG3KeyService.direct source input inside query).run
          (RegistrationNativeG3SelectiveService.count query before).1.prepared)).run
            (RegistrationNativeG3SelectiveService.count query before)) = _
  rw [count_flags, simulateQ_map]
  simp only [target, project, QueryImpl.flattenStateT_mapStateTBase_apply_run, Functor.map_map,
    RegistrationNativeG3SelectiveFixedKeysSource.project, Prod.map_def, id_eq] at mapped ⊢
  exact mapped

/-- The entire actual direct selective service retains the original native flags and both table state coordinates throughout every adaptive retained-service continuation. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp RegistrationNativeRetainedService.Spec Value) (before : RegistrationNativeSelectiveHiddenService.State n) :
    Prod.map id project <$> (simulateQ (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds) work).run before =
      (simulateQ (target source input inside candidate materials seeds) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source source input inside candidate materials seeds) work before

/-- The actual cold direct selective service has the literal original two-pass native key compiler source under the selected-only fixed108-byte table router. -/
theorem client_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp RegistrationNativeRetainedService.Spec Value) :
    (simulateQ (RegistrationNativeG3RetainedCallbacks.keys source input inside candidate materials seeds) work).run'
      (RegistrationNativeHiddenService.initial, ∅) =
      (simulateQ (RegistrationNativeG3SelectiveFixedKeysSource.target (RegistrationNativeG3Tables.join materials seeds)
        (RegistrationNativeSelectiveHiddenService.selected inside candidate))
        (RegistrationNativeKeyCompiler.client source input inside (RegistrationNativeRetainedService.client work)
          RegistrationNativeKeyPhases.emptyMeta)).run' (∅, PqxdhRegistrationJointKemSecondEntry.emptyAlloc) := by
  have actual := congrArg (Functor.map Prod.fst)
    (program_source source input inside candidate materials seeds work (RegistrationNativeHiddenService.initial, ∅))
  rw [RegistrationNativeG3KeyServiceInlining.client_source]
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [target, project, RegistrationNativeG3SelectiveFixedKeysSource.project,
    RegistrationNativeHiddenService.initial, PqxdhRegistrationJointKemSecondEntry.emptyAlloc,
    Functor.map_map, Prod.map_def, id_eq] using actual

end BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveDirectProjection.client_source

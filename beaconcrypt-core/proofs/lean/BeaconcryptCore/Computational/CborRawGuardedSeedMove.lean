-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawGuardedRepresentation

/-! Hidden seeds relocate from the split service to the native interpreter's seed table without changing an early-admission client. Refusal reads no seed-table or service-backend field. The actual ideal instance retains independent source registration and ordinary record codecs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawGuardedSeedMove
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhRecordLiftInterface (EnvQuery)
open PqxdhDeploymentBackend (RegImpl XState)
open PqxdhDeploymentIdealSlots (SlotProgram slotCore)
open PqxdhDeploymentIdealErase (SlotFrame)
open PqxdhDeploymentIdealKeys (seedPut moveSeeds slotCoreX)
open PqxdhDeploymentSeedSplit (SlotService)
variable {ι KemSK Reader Response M Γ Result : Type} {baseSpec : OracleSpec ι} {n : Nat}
section Move
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

theorem fixed_move
    (reg₁ : RegImpl KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) ×
      (PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord n × Γ)) n)
    (reg₂ : RegImpl KemSK (M × (PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord n × Γ)) n)
    (query : Spec.Domain) (notEnv : ∀ command : EnvQuery, query ≠ .inr command.val)
    (state : XState KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) ×
      (PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord n × Γ)) n) :
    Prod.map id moveSeeds <$>
        (CborRawGuardedJoin.nativeHandler setup codec route reg₁ query).run state =
      (CborRawGuardedJoin.nativeHandler setup codec route reg₂ query).run (moveSeeds state) := by
  simp only [CborRawGuardedJoin.nativeHandler, StateT.run]
  have same : CborRecordNativeAdmission.nativeShell (moveSeeds state).base =
      CborRecordNativeAdmission.nativeShell state.base := rfl
  rw [same]
  cases refused : CborRawGuardedJoin.refusal (n := n) query (CborRecordNativeAdmission.nativeShell state.base) with
  | some reply => simp only [map_pure]; rfl
  | none => exact PqxdhDeploymentIdealKeys.fixed_moveSeeds setup codec route reg₁ reg₂ query notEnv state

/-- Complete arbitrary-client seed relocation, preserving actual refusal and all native outcomes. -/
theorem move_run (program : PqxdhLiveServerConstruction.Created Unit → SlotProgram KemSK Γ n)
    (frame : ∀ created query, SlotFrame seedPut (program created query))
    (service : SlotService (M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) n)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result)
    (state : XState KemSK ((M × (PqxdhRecordLiftWorld.SeedSpec n).QueryCache) ×
      (PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord n × Γ)) n) :
    Prod.map id moveSeeds <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup codec route (slotCore program service created)) work).run state =
      (simulateQ (CborRawGuardedJoin.nativeHandler setup codec route (slotCoreX program service created)) work).run
        (moveSeeds state) := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (CborRawGuardedJoin.nativeHandler setup codec route (slotCore program service created))
    (CborRawGuardedJoin.nativeHandler setup codec route (slotCoreX program service created)) moveSeeds ?_ work state
  intro query current
  by_cases registration : ∃ command : EnvQuery, query = .inr command.val
  · obtain ⟨command, rfl⟩ := registration
    rw [CborRawGuardedRepresentation.native_env, CborRawGuardedRepresentation.native_env]
    exact PqxdhDeploymentIdealKeys.slotCore_moveSeeds program frame service created command current
  · exact fixed_move setup codec route _ _ query (fun command same => registration ⟨command, same⟩) current

end Move
section Ideal
open PqxdhDeploymentIdealParams (Target Params)
variable {SourceReader SourceResponse : Type}

/-- Actual erased ideal registration with first-touch split seeds is the native first-touch split interpreter after exact seed relocation. -/
theorem seed_move (setup : Setup baseSpec KemSK) (recordCodec : Codec Reader Response)
    (sourceCodec : Codec SourceReader SourceResponse) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks)
    {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (work : OracleComp Spec Result) :
    Prod.map id moveSeeds <$>
        (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
          (PqxdhDeploymentIdealSteps.idealCoreErased setup sourceCodec route checks target parameters
            PqxdhDeploymentSeedSplit.splitService created)) work).run
          (PqxdhDeploymentBackend.xinitial created ((∅, ∅),
            (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhDeploymentIdealSteps.IdealCore.initial))) =
      (simulateQ (CborRawGuardedJoin.nativeHandler setup recordCodec route
        (PqxdhDeploymentIdealKeys.idealSplitX setup sourceCodec route checks target parameters created)) work).run
          (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)) := by
  exact move_run setup recordCodec route
    (PqxdhDeploymentIdealSteps.idealProg setup sourceCodec route checks target parameters
      (PqxdhDeploymentIdealSteps.erasedHidden setup sourceCodec checks))
    (fun created query => PqxdhDeploymentIdealKeys.idealProg_seedFrame setup sourceCodec route checks target parameters
      _ created query) PqxdhDeploymentSeedSplit.splitService created work _

end Ideal
end BeaconcryptCore.Computational.CborRawGuardedSeedMove

/-- info: 'BeaconcryptCore.Computational.CborRawGuardedSeedMove.fixed_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedSeedMove.fixed_move
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedSeedMove.move_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedSeedMove.move_run
/-- info: 'BeaconcryptCore.Computational.CborRawGuardedSeedMove.seed_move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawGuardedSeedMove.seed_move

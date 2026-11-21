-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleMarks
import BeaconcryptCore.Computational.CborRawInitializedPost

/-! The pending raw accept invokes the actual ideal registration operation. Its selected first-touch operation commutes with copied native kernels, and its public reply is logged before the adaptive raw continuation. The operation retains fallible-writer and admission behavior in the subsequent native handler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawSelectedAccept
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (cutState)
open PqxdhDeploymentIdealSlots (detach attach SlotSpec)
open PqxdhDeploymentIdealActive (selectedStep acceptAfter)
open PqxdhDeploymentIdealPostSource (Mid mergeX toX)
open PqxdhDeploymentIdealPostItemRun (afterSelected)
open CborRawPublicState (Public ofMemory)
open CborRawMiddleSimulation (Native)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
section Selected
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

def decorate (publicState : Public) (raw : Pqxdh.Bytes) (value : Option Nat × Native KemSK) :
    Option Nat × (Public × Native KemSK) :=
  (value.1, (⟨CborRegistrationPublicLog.update publicState.log (.inr (.accept raw)) value.1, publicState.lastId⟩,
    PqxdhDeploymentIdealCut.unghost value.2))

noncomputable def reject (base : PqxdhDeploymentNative.State KemSK) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) : ProbComp (Option Nat × Native KemSK) :=
  (fun value => (value.1.1, attach value.1.2 value.2.1 value.2.2)) <$>
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((selectedStep (fun state => do
        let value ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
          (setup.joint.publicKeys created.seed) state.2 (none, consumed)).run state)
        pure (((value.1, logged), (false, none)), value.2))).run (detach (cutState target created base)))).run
      ((cutState target created base).backend.2.1, (cutState target created base).backend.1)

/-- The actual selected accept has the native pre-encapsulation callbacks followed by its inactive or active slot operation. -/
theorem selected_run (base : PqxdhDeploymentNative.State KemSK) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse)
      checks raw = some value) (matched : value.keys.pqKey = parameters.chosen.1) :
    (PqxdhDeploymentBackend.handlerWith setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
      (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
        checks target parameters created) (.inr (.accept raw))).run (cutState target created base) =
      (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup (CborRawCompile.sourceCodec wire parse) checks created.seed)
        (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          base.native.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => reject (Reader := Reader) setup target created base pre.2 pre.1.2
        | some ephemeral =>
            (fun outcome => (outcome.1.1, attach outcome.1.2 outcome.2.1 outcome.2.2)) <$>
              (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
                ((selectedStep (acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed
                  parameters.challenge value ephemeral pre.2 pre.1.2)).run
                    (detach (cutState target created base)))).run
                ((cutState target created base).backend.2.1, (cutState target created base).backend.1) := by
  change (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created
    ⟨.accept raw, trivial⟩).run (cutState target created base) = _
  rw [PqxdhDeploymentIdealSlots.slotCore_run]
  change (fun outcome => (outcome.1.1, attach outcome.1.2 outcome.2.1 outcome.2.2)) <$>
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealSteps.acceptStep setup (CborRawCompile.sourceCodec wire parse) (CborRawCompile.route parse)
        checks target parameters created raw).run (detach (cutState target created base)))).run
      ((cutState target created base).backend.2.1, (cutState target created base).backend.1) = _
  rw [PqxdhDeploymentIdealActive.acceptStep_selected setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) checks target parameters created base raw value verified matched,
    simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealCut.slotImpl_lift, bind_map_left, map_bind]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩ <;> rfl

/-- The active slot operation starts from the actual source cut and reconstructs the complete native and public state after its reply. -/
theorem active_merge (memory : CborAdmissionCompiler.Local) (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes) :
    decorate (ofMemory memory) raw <$>
      ((fun outcome => (outcome.1.1, attach outcome.1.2 outcome.2.1 outcome.2.2)) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((selectedStep (acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed
            parameters.challenge value ephemeral consumed logged)).run
              (detach (cutState target created (PqxdhDeploymentCompile.merge memory.copies
                (PqxdhRegistrationJointSchedule.source joint)))))).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)) =
      (fun selected => (selected.1.1.1.1,
        CborRawMiddleSimulation.merge (CborRawCompileCut.logAccept memory raw selected.1.1.1.1)
          (afterSelected target joint selected))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed parameters.challenge value
            ephemeral consumed logged).run joint.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) := by
  have mergedStart : detach (cutState target created (PqxdhDeploymentCompile.merge memory.copies
      (PqxdhRegistrationJointSchedule.source joint))) =
      PqxdhDeploymentIdealPostSource.mergeY memory.copies (detach (toX
        (PqxdhDeploymentIdealPostReduce.cutMid target created joint))) := rfl
  rw [mergedStart, PqxdhDeploymentIdealPostSource.selectedStep_merge memory.copies _
    (PqxdhDeploymentIdealPostSource.acceptAfter_comm memory.copies setup (CborRawCompile.sourceCodec wire parse)
      checks created.seed parameters.challenge value ephemeral consumed logged)]
  rw [simulateQ_map, StateT.run_map, Functor.map_map]
  rw [show (selectedStep (acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed
      parameters.challenge value ephemeral consumed logged)).run (detach (toX
        (PqxdhDeploymentIdealPostReduce.cutMid target created joint))) = _ <$>
      (acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed parameters.challenge value ephemeral
        consumed logged).run joint.shared from rfl,
    simulateQ_map, StateT.run_map, Functor.map_map]
  simp only [Functor.map_map]
  rfl

end Selected
end BeaconcryptCore.Computational.CborRawSelectedAccept

/-- info: 'BeaconcryptCore.Computational.CborRawSelectedAccept.selected_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSelectedAccept.selected_run
/-- info: 'BeaconcryptCore.Computational.CborRawSelectedAccept.active_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawSelectedAccept.active_merge

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMarkedBranch

/-! The initialized source and independently defined native raw game agree at every selected cut. Active callbacks use the actual registration operation; inactive and rejected branches retain their complete execution while deciding false in law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawCutBranches
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealCut (CutCE cutState)
open PqxdhDeploymentIdealPostItemRun (afterSelected)
open CborRawPublicState (Public ofMemory)
open CborRawMiddleSimulation (Native)
open CborRawSelectedAccept (decorate)
open LazyOracleDiscard (LawEq)
variable {ι KemSK Reader Response A Result : Type} {baseSpec : OracleSpec ι}
section Branch
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- Actual native selected acceptance yields the same complete active continuation as the initialized raw source slot game. -/
theorem selected_resume (event : Result × CborRawPostActive.Produced → Bool)
    (memory : CborAdmissionCompiler.Local) (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp Spec Result)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse)
      checks raw = some value) (matched : value.keys.pqKey = parameters.chosen.1) :
    LawEq (CborRawMarkedPrefix.resume setup wire parse checks target parameters created event (.pending raw next)
        (CborRawMiddleSimulation.merge memory (PqxdhDeploymentIdealPostReduce.cutMid target created joint)))
      ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup (CborRawCompile.sourceCodec wire parse) checks created.seed)
        (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          joint.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => pure false
        | some ephemeral =>
            (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
              ((PqxdhDeploymentIdealActive.acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed
                parameters.challenge value ephemeral pre.2 pre.1.2).run joint.shared)).run
                (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun selected =>
              (fun result => event (result.1, result.2.2.base.produced) && selected.1.1.1.1.isSome) <$>
                (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
                  (next selected.1.1.1.1)).run
                  (CborRawMiddleSimulation.merge (CborRawCompileCut.logAccept memory raw selected.1.1.1.1)
                    (afterSelected target joint selected))) := by
  unfold CborRawMarkedPrefix.resume CborRawPrefixHandoff.resume
  change LawEq (CborRawMarkedPrefix.run setup wire parse checks target parameters created
    (PqxdhDeploymentIdealCut.finishCE (.pending raw next)) event
      (CborRawMiddleSimulation.merge memory (PqxdhDeploymentIdealPostReduce.cutMid target created joint))) _
  rw [CborRawMarkedPrefix.run]
  simp only [PqxdhDeploymentIdealCut.finishCE, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
  change LawEq ((CborRawMiddleSimulation.handler setup wire parse checks target parameters created
      (.inr (.accept raw))).run
        (CborRawMiddleSimulation.merge memory (PqxdhDeploymentIdealPostReduce.cutMid target created joint)) >>= fun accepted =>
      CborRawMarkedPrefix.run setup wire parse checks target parameters created (next accepted.1) event accepted.2) _
  rw [CborRawMiddleMarks.accept_run, bind_map_left]
  change LawEq ((PqxdhDeploymentBackend.handlerWith setup (CborRawCompile.sourceCodec wire parse)
      (CborRawCompile.route parse) (PqxdhDeploymentIdealSteps.idealReg setup (CborRawCompile.sourceCodec wire parse)
        (CborRawCompile.route parse) checks target parameters created) (.inr (.accept raw))).run
          (cutState target created (PqxdhDeploymentCompile.merge memory.copies
            (PqxdhRegistrationJointSchedule.source joint))) >>= fun accepted =>
      CborRawMarkedPrefix.run setup wire parse checks target parameters created (next accepted.1) event
        (decorate (ofMemory memory) raw accepted).2) _
  rw [CborRawSelectedAccept.selected_run setup wire parse checks target parameters created _ raw value verified matched,
    bind_assoc]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre _ => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · exact CborRawMarkedBranch.reject_dead setup wire parse checks target parameters created event (ofMemory memory)
      _ raw next consumed logged
  · dsimp only
    rw [bind_map_left]
    have merged := congrArg (fun program => program >>= fun accepted =>
        CborRawMarkedPrefix.run setup wire parse checks target parameters created (next accepted.1) event accepted.2)
      (CborRawSelectedAccept.active_merge setup wire parse checks target parameters created memory joint raw value
        ephemeral consumed logged)
    simp only [bind_map_left] at merged
    refine (LawEq.of_eq merged).trans ?_
    refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun selected supported => LawEq.of_eq ?_
    exact CborRawMarkedBranch.active_marked setup wire parse checks target parameters created event memory joint raw next
      value ephemeral consumed logged selected supported

end Branch
end BeaconcryptCore.Computational.CborRawCutBranches

/-- info: 'BeaconcryptCore.Computational.CborRawCutBranches.selected_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutBranches.selected_resume

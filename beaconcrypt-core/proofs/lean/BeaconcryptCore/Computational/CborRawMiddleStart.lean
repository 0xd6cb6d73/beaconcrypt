-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawMiddleInvariant
import BeaconcryptCore.Computational.CborRawCompileCut

/-! Selected acceptance starts the complete raw middle invariant from its derived pre-cut invariant. Allocation control is preserved through the actual marker and allocator execution, so the public assignment counter is established at this handoff. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawMiddleStart
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostItemRun (AcceptRun afterSelected)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

theorem acceptAfter_control (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes)
    (native : PqxdhServerAuthNative.NativeState KemSK) (slots : PqxdhDeploymentIdealPostSim.SlotState)
    (result : AcceptRun KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed challenge value ephemeral consumed
        logged).run native)).run slots)) :
    result.1.2.2.server.control = native.2.server.control := by
  have outer : result.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks seed challenge
      value ephemeral consumed logged).run native) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _ slots
    rw [StateT.run'_eq, support_map]
    exact ⟨result, supported, rfl⟩
  change result.1 ∈ support (PqxdhDeploymentIdealSteps.liftS _ >>= _) at outer
  rw [mem_support_bind_iff] at outer
  obtain ⟨prepared, preparedMember, outer⟩ := outer
  rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at preparedMember
  have marker := PqxdhDeploymentIdealKeymatch.program_marker _ value ephemeral
    (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge consumed prepared preparedMember
  rw [mem_support_bind_iff] at outer
  obtain ⟨answer, answerMember, outer⟩ := outer
  rw [support_pure, Set.mem_singleton_iff] at outer
  rw [outer]
  exact CborRawMiddleCounter.marker_tail_counter setup.hmac native.2.sessions setup.serverKeyId
    (setup.joint.publicKeys seed) native.2 prepared marker (native, none) answer answerMember

/-- A supported selected accept supplies the complete invariant needed by every adaptive raw continuation. -/
theorem good_after_selected (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (seed : PqxdhJointIdentity.IdentitySeed)
    (raw : Pqxdh.Bytes) (memory : CborAdmissionCompiler.Local)
    (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source joint))
    (value : PqxdhServerRootPreparation.Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse)
      checks raw = some value)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes)
    (slots : PqxdhDeploymentIdealPostSim.SlotState) (result : AcceptRun KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
      ((PqxdhDeploymentIdealActive.acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks seed
        parameters.challenge value ephemeral consumed logged).run joint.shared)).run slots)) :
    CborRawMiddleInvariant.Good setup wire parse target
      (CborRawCompileCut.logAccept memory raw result.1.1.1.1) (afterSelected target joint result) := by
  obtain ⟨server, keyId, sessions, others, rejected, accepted⟩ :=
    PqxdhDeploymentIdealPostGood.acceptAfter_footprint setup (CborRawCompile.sourceCodec wire parse)
      checks seed parameters.challenge value ephemeral consumed logged joint.shared slots result supported
  refine ⟨⟨?_, ?_⟩, Nat.lt_succ_self _⟩
  · exact PqxdhDeploymentIdealPostGood.good_of_accept setup (CborRawCompile.sourceCodec wire parse) raw
      memory.copies (PqxdhRegistrationJointSchedule.source joint)
      ⟨result.1.2, (PqxdhRegistrationJointSchedule.source joint).owners⟩ good.nativeGood result.1.1.1.1
      rfl server keyId sessions others rejected (fun session found => by
        obtain ⟨same, token, stored, identity⟩ := accepted session found
        exact ⟨same, token, stored, by
          rw [identity]
          exact PqxdhDeploymentIdealPostGood.identityOf_verified setup (CborRawCompile.sourceCodec wire parse)
            checks raw value verified⟩)
  · have control := acceptAfter_control setup (CborRawCompile.sourceCodec wire parse) checks seed
      parameters.challenge value ephemeral consumed logged joint.shared slots result supported
    exact good.lastId.trans (congrArg (fun state => state.last_key_id) control).symm

end BeaconcryptCore.Computational.CborRawMiddleStart

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleStart.acceptAfter_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleStart.acceptAfter_control

/-- info: 'BeaconcryptCore.Computational.CborRawMiddleStart.good_after_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawMiddleStart.good_after_selected

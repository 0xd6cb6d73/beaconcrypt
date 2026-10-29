-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawInitializedCut
import BeaconcryptCore.Computational.CborRawPostItemGeneric
import BeaconcryptCore.Computational.CborRawMiddleSimulation

/-! The selected raw-CBOR accept reaches the actual slot skeleton and then the independently defined native middle handler. The final observation sees the original result and produced frames; the selected acceptance flag is the actual returned session. Full admission, fallible writer, private backend and public adaptation state remain inside the checked continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawPostActive
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhServerRootPreparation (Verified)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealPostItemRun (afterSelected)
variable {ι KemSK Reader Response X A : Type} {baseSpec : OracleSpec ι}
section Active
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)

noncomputable def compiledNext (raw : Pqxdh.Bytes) (next : Option Nat → OracleComp Spec X)
    (memory : CborAdmissionCompiler.Local) : Option Nat →
    OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (X × CborAdmissionCompiler.Local) :=
  fun answer => (simulateQ (CborRawCompile.compileImpl setup wire parse) (next answer)).run
    (CborRawCompileCut.logAccept memory raw answer)

theorem opaqueRest_selected {X R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : (X × CborAdmissionCompiler.Local) × PqxdhRegistrationJointAcceptCutTag.Tag → R) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp Spec X) (copies : CborAdmissionCompiler.Local)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (value : Verified Reader) (verified : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse) checks raw = some value)
    (seed : PqxdhJointIdentity.IdentitySeed) (selected : ℕ) (pairs : List (PqxdhLiveKemReservation.Pair KemSK))
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (PqxdhDeploymentIdealCut.opaqueRest setup (CborRawCompile.sourceCodec wire parse) checks identityIndex publicIdentity observe
          ((CborRawInitializedCut.compilerCut setup wire parse (.pending raw next, copies), owners), shared))).run).run
        state =
      (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup (CborRawCompile.sourceCodec wire parse) checks seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
            (PqxdhRegistrationJointKemRawOpaque.rejectRun setup (CborRawCompile.sourceCodec wire parse) checks identityIndex publicIdentity observe raw
              (compiledNext setup wire parse raw next copies) owners shared (none, pre.2))).run).run state
        | some ephemeral => pure (some (.pending raw value ephemeral pre.2 shared owners
            (compiledNext setup wire parse raw next copies)), state) := by
  simp only [PqxdhDeploymentIdealCut.opaqueRest, CborRawInitializedCut.compilerCut, CborRawCompileCut.cut, verified]
  rw [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, PqxdhDeploymentIdealActive.stopped_before setup (CborRawCompile.sourceCodec wire parse) checks identityIndex
    raw seed selected pairs value shared.2.server.consumed state, bind_map_left]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · rfl
  · simp only [Option.elim, simulateQ_pure, OptionT.run_pure, StateT.run_pure]
    rfl


abbrev Produced := List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)

/-- Every supported active cut's slot continuation has exactly the native raw observation. The initial invariant and resource facts are cut obligations; no probability or event-simulation premise is used. -/
theorem itemPost_native {count : Nat} (target : Target count) (parameters : Params KemSK count)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (event : X × Produced → Bool) (created : PqxdhLiveServerConstruction.Created Unit)
    (identity : created.publicIdentity = setup.joint.publicKeys created.seed) (raw : Pqxdh.Bytes)
    (memory : CborAdmissionCompiler.Local) (joint : PqxdhRegistrationJointSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source joint))
    (value : Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse)
      checks raw = some value) (matched : value.keys.pqKey = parameters.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (parameters.pool target) joint.pool.2)
    (indexed : PqxdhDeploymentIdealCut.PoolIndexed joint)
    (next : Option Nat → OracleComp Spec X)
    (onlyAllowed : ∀ answer, (compiledNext setup wire parse raw next memory answer).IsQueryBoundP
      (fun query => ¬ PqxdhDeploymentIdealPostInvariant.Allowed (KemSK := KemSK) query) 0)
    (budget : Nat) (bounded : ∀ answer, (compiledNext setup wire parse raw next memory answer).IsQueryBoundP
      (PqxdhDeploymentIdealPostInvariant.Costly (KemSK := KemSK)) budget)
    (fits : budget ≤ (parameters.pool target).length - joint.pool.2.keys.length) (after : A) :
    CborRawPostItemGeneric.itemPost setup (CborRawCompile.sourceCodec wire parse) checks target parameters
        (fun result => event (result.1, result.2.copies.produced))
        (.ready (PqxdhRegistrationJointServerBirth.encode created) parameters.others
          (some (.pending raw value ephemeral consumed joint.shared
            (PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners
            (compiledNext setup wire parse raw next memory)))
          (joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2) after) =
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealActive.acceptAfter setup (CborRawCompile.sourceCodec wire parse) checks created.seed
            parameters.challenge value ephemeral consumed logged).run joint.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun selected =>
        (fun result => event (result.1, result.2.2.base.produced) && selected.1.1.1.1.isSome) <$>
          (simulateQ (CborRawMiddleSimulation.handler setup wire parse checks target parameters created)
            (next selected.1.1.1.1)).run
            (CborRawMiddleSimulation.merge (CborRawCompileCut.logAccept memory raw selected.1.1.1.1)
              (afterSelected target joint selected)) := by
  rw [CborRawPostItemGeneric.itemPost_middle setup (CborRawCompile.sourceCodec wire parse)
    (CborRawCompile.route parse) checks target parameters _ created identity raw value matched ephemeral consumed logged
    joint owned prefixed indexed _ onlyAllowed budget bounded fits after]
  refine bind_congr_of_forall_mem_support _ fun selected supported => ?_
  have start := CborRawMiddleStart.good_after_selected setup wire parse checks target parameters created.seed raw memory
    joint good value verified ephemeral consumed logged _ selected supported
  have simulated := CborRawMiddleSimulation.compile_simulation setup wire parse checks target parameters created
    phase1 phase2 (next selected.1.1.1.1) (CborRawCompileCut.logAccept memory raw selected.1.1.1.1)
    (afterSelected target joint selected) start
  rw [PqxdhRegistrationJointAcceptKemCut.tagged, simulateQ_map, StateT.run_map, Functor.map_map, ← simulated,
    Functor.map_map]
  cases answer : selected.1.1.1.1 <;> rfl

end Active
end BeaconcryptCore.Computational.CborRawPostActive

/-- info: 'BeaconcryptCore.Computational.CborRawPostActive.opaqueRest_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPostActive.opaqueRest_selected

/-- info: 'BeaconcryptCore.Computational.CborRawPostActive.itemPost_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawPostActive.itemPost_native

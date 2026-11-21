-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawPoolCompiler

/-! The two pre-cut implementations share one annotated pool execution for the actual raw compiler. The router equation retains the original accept ordinal and the complete public compiler memory. These operational statements introduce no assumed game simulation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawCutPrefix
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentIdealPoolSource (PoolOwned PoolPrefix sourcePool routerOf)
open PqxdhRegistrationJointGeneratedFinish (encodeState)
open PqxdhRegistrationJointAcceptCut (scan)
open PqxdhDeploymentIdealCut (scanCE)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

section Prefix
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : Nat)
    (pairs : List (PqxdhLiveKemReservation.Pair KemSK))

noncomputable def source :=
  sourcePool setup (CborRawCompile.sourceCodec wire parse) checks seed identityIndex pairs

/-- The native pool experiment is the erasure of the same annotated pool source used by the stopped KEM router, with the actual raw public reply and full native poststate. -/
theorem native_program (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (CborTaggedSimulation.boundaryWire wire parse))
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (work : OracleComp Spec X) (memory : CborAdmissionCompiler.Local)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state)) :
    (fun value => (value.1.1, CborAdmissionCompiler.merge value.1.2
      (PqxdhRegistrationJointSchedule.source value.2))) <$>
        (simulateQ (source setup wire parse checks seed identityIndex pairs)
          ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory)).run state =
      (simulateQ (CborRawPoolCompiler.native setup wire parse checks seed pairs) work).run
        (CborAdmissionCompiler.merge memory (PqxdhRegistrationJointSchedule.source state)) := by
  have erased := PqxdhDeploymentIdealPoolSource.programPool_native setup
    (CborRawCompile.sourceCodec wire parse) checks seed identityIndex pairs
    ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory) state
  have merged := congrArg (fun program => (fun value =>
    (value.1.1, CborAdmissionCompiler.merge value.1.2 value.2)) <$> program) erased
  rw [Functor.map_map] at merged
  exact merged.trans (CborRawPoolCompiler.compile_simulation setup wire parse checks seed pairs lengths parser
    phase1 phase2 work memory (PqxdhRegistrationJointSchedule.source state) good)

/-- Every reached annotated prefix preserves the complete reconstruction and assignment invariant. The assignment counter is not inferred from an existential build shape. -/
theorem good_program
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (work : OracleComp Spec X) (memory : CborAdmissionCompiler.Local)
    (state : PqxdhRegistrationJointSchedule.State KemSK)
    (good : CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) memory
      (PqxdhRegistrationJointSchedule.source state))
    (value : (X × CborAdmissionCompiler.Local) × PqxdhRegistrationJointSchedule.State KemSK)
    (supported : value ∈ support ((simulateQ (source setup wire parse checks seed identityIndex pairs)
      ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory)).run state)) :
    CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) value.1.2
      (PqxdhRegistrationJointSchedule.source value.2) := by
  have erased : (value.1, PqxdhRegistrationJointSchedule.source value.2) ∈ support
      ((simulateQ (CborRawPoolCompiler.source setup wire parse checks seed pairs)
        ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory)).run
          (PqxdhRegistrationJointSchedule.source state)) := by
    change _ ∈ support ((simulateQ (PqxdhDeploymentIdealPool.revealPool setup
      (CborRawCompile.sourceCodec wire parse) checks seed pairs)
      ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory)).run
        (PqxdhRegistrationJointSchedule.source state))
    rw [← PqxdhDeploymentIdealPoolSource.programPool_native setup (CborRawCompile.sourceCodec wire parse)
      checks seed identityIndex pairs, support_map]
    exact ⟨value, supported, rfl⟩
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at erased
  obtain ⟨final, reached, same⟩ := erased
  have invariant := PqxdhServerAuthExperiment.run_rel
    (CborRawPoolCompiler.compiled setup wire parse checks seed pairs)
    (fun before after => CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse)
      before.1 before.2 → CborAdmissionCompiler.Good setup (CborRawCompile.sourceCodec wire parse) after.1 after.2)
    (fun _ valid => valid) (fun _ _ _ left right valid => right (left valid))
    (fun query before after member valid => by
      rw [CborRawPoolCompiler.compiled_run, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact CborRawPoolCompiler.good_step setup wire parse checks seed pairs phase1 phase2 query
        before.1 before.2 valid inner innerMember)
    work (memory, PqxdhRegistrationJointSchedule.source state) final reached good
  have memories : final.2.1 = value.1.2 := congrArg (fun result => result.1.2) same
  have sources : final.2.2 = PqxdhRegistrationJointSchedule.source value.2 := congrArg (fun result => result.2) same
  rw [← memories, ← sources]
  exact invariant

/-- The stopped KEM router and the raw native prefix are images of one source execution. Scanning counts all original accept attempts and retains every reply continuation. -/
theorem stopped_scan (selected : Nat) (work : OracleComp Spec X) (index : Nat)
    (memory : CborAdmissionCompiler.Local) (state : PqxdhRegistrationJointSchedule.State KemSK)
    (owned : PoolOwned seed identityIndex state) (prefixed : PoolPrefix pairs state.pool.2)
    (budget : SourceKind → Nat)
    (certified : ∀ kind,
      (scan ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory) index).IsQueryBoundP
        (fun query => sourceKind (KemSK := KemSK) query = kind) (budget kind))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (room : state.pool.2.keys.length + budget (.inl 1) ≤ pairs.length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (PqxdhRegistrationJointKemCommands.program setup (CborRawCompile.sourceCodec wire parse) checks
          identityIndex (setup.joint.publicKeys seed)
          (scan ((simulateQ (CborRawCompile.compileImpl setup wire parse) work).run memory) index)
          ((encodeState setup state).owners, (encodeState setup state).inits) state.shared)).run).run (state.pool.1, routerOf state.pool.2) =
      (fun value => (some (((CborRawCompileCut.cut (CborRawCompile.compileImpl setup wire parse)
          CborRawCompileCut.logAccept value.1, ((encodeState setup value.2).owners, (encodeState setup value.2).inits)), value.2.shared)),
          (value.2.pool.1, routerOf value.2.pool.2))) <$>
        (simulateQ (source setup wire parse checks seed identityIndex pairs)
          ((simulateQ (CborRawCompile.compileImpl setup wire parse) (scanCE work index)).run memory)).run state := by
  rw [PqxdhDeploymentIdealPoolSource.kemCommands_stopped setup (CborRawCompile.sourceCodec wire parse) checks
    selected seed identityIndex pairs _ budget certified unreadIdentity unreadKem state owned prefixed room,
    CborRawCompileCut.raw_compile_scan, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

end Prefix
end BeaconcryptCore.Computational.CborRawCutPrefix

/-- info: 'BeaconcryptCore.Computational.CborRawCutPrefix.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutPrefix.native_program

/-- info: 'BeaconcryptCore.Computational.CborRawCutPrefix.good_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutPrefix.good_program

/-- info: 'BeaconcryptCore.Computational.CborRawCutPrefix.stopped_scan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawCutPrefix.stopped_scan

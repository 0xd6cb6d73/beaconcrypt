-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionInvariant
import BeaconcryptCore.Computational.CborAdmissionServerCompiler
import BeaconcryptCore.Computational.CborAdmissionBeaconCompiler

/-! Exact adaptive simulation of the size-admission compiler. The local state tracks the publicly returned assignment counter and the existing reconstruction log; source14 kernel reads remain within the existing compiler capabilities. These are operational equalities, with cryptographic event and budget transport stated separately. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionCompileStep
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentInterface (Spec)
open CborAdmissionCompiler (Local Good merge compileImpl nativeHandler)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The admission compiler under source14, retaining both complete states. -/
noncomputable def compiledImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) :
    QueryImpl Spec (StateT (Local × PqxdhRegistrationSchedule.State KemSK) ProbComp) :=
  ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed).mapStateTBase
    (compileImpl setup codec route)).flattenStateT

/-- A compiled step is its source14 run with the product states reassociated. -/
theorem compiledImpl_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (query : Spec.Domain)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup codec checks route seed query).run (memory, native) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
          ((compileImpl setup codec route query).run memory)).run native := rfl

/-- Fresh source states supply the reconstruction invariant and the public initial assignment counter. -/
theorem good_initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (lastId : native.shared.2.server.control.last_key_id = setup.serverKeyId)
    (peers : ∀ keyId, native.shared.2.server.server.peers keyId = none)
    (owners : native.owners = []) (pending : ∀ session, native.shared.2.pending session = none) :
    Good setup codec (Local.empty setup.serverKeyId) native :=
  ⟨PqxdhDeploymentCompileInvariant.good_initial setup codec native keyId peers owners pending, lastId.symm⟩

/-- Every command of the guarded compiler has exactly the native admission-filtered reply and merged poststate. -/
theorem step_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed) (query : Spec.Domain)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native) :
    Prod.map id (fun state : Local × PqxdhRegistrationSchedule.State KemSK => merge state.1 state.2) <$>
      (compiledImpl setup codec checks route seed query).run (memory, native) =
      (nativeHandler setup codec checks route seed query).run (merge memory native) := by
  rw [compiledImpl_run, Functor.map_map]
  cases query with
  | inl coin =>
    exact CborAdmissionInvariant.liftExisting_step_exact setup codec checks route seed
      (.inl coin) memory native good rfl
  | inr command =>
    cases command with
    | build session payload =>
      exact CborAdmissionCompiler.build_step_exact setup codec checks route seed
        session payload memory native good
    | serverSend keyId plaintext =>
      exact CborAdmissionServerCompiler.step_exact setup codec checks route seed
        keyId plaintext memory native good
    | beaconSend index plaintext =>
      exact CborAdmissionBeaconCompiler.step_exact setup codec checks route seed
        index plaintext memory native good
    | _ =>
      exact CborAdmissionInvariant.liftExisting_step_exact setup codec checks route seed
        _ memory native good rfl

/-- Every supported compiler step preserves reconstruction and the public assignment counter. -/
theorem good_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (query : Spec.Domain) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native)
    (result : Spec.Range query × (Local × PqxdhRegistrationSchedule.State KemSK))
    (supported : result ∈ support ((compiledImpl setup codec checks route seed query).run (memory, native))) :
    Good setup codec result.2.1 result.2.2 := by
  rw [compiledImpl_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  cases query with
  | inl coin =>
    exact CborAdmissionInvariant.liftExisting_good setup codec checks route seed phase1 phase2
      (.inl coin) (by simp [PqxdhDeploymentCompileBudget.commandKind]) memory native good reached member
  | inr command =>
    cases command with
    | build session payload =>
      exact CborAdmissionInvariant.build_good setup codec checks route seed phase2
        session payload memory native good reached member
    | serverSend keyId plaintext =>
      exact CborAdmissionServerCompiler.good_support setup codec checks route seed
        keyId plaintext memory native good reached member
    | beaconSend index plaintext =>
      exact CborAdmissionBeaconCompiler.good_support setup codec checks route seed
        index plaintext memory native good reached member
    | _ =>
      exact CborAdmissionInvariant.liftExisting_good setup codec checks route seed phase1 phase2
        _ (by simp [PqxdhDeploymentCompileBudget.commandKind]) memory native good reached member

/-- The exact compiler correspondence holds jointly with the output of every adaptive deployment program. -/
theorem compile_simulation {X : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp Spec X) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((simulateQ (compileImpl setup codec route) adversary).run memory)).run native =
      (simulateQ (nativeHandler setup codec checks route seed) adversary).run (merge memory native) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiledImpl setup codec checks route seed) (nativeHandler setup codec checks route seed)
    (fun state => Good setup codec state.1 state.2) (fun state => merge state.1 state.2)
    (fun query state valid result supported =>
      good_step setup codec checks route seed phase1 phase2 query state.1 state.2 valid result supported)
    (fun query state valid => step_merge setup codec checks route seed query state.1 state.2 valid)
    adversary (memory, native) good
  rw [← simulated]
  rfl

/-- Every supported adaptive compiler execution retains its reconstruction invariant and public counter. -/
theorem good_run {X : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp Spec X) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native)
    (result : (X × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((simulateQ (compileImpl setup codec route) adversary).run memory)).run native)) :
    Good setup codec result.1.2 result.2 := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  have preserved := PqxdhServerAuthExperiment.run_rel (compiledImpl setup codec checks route seed)
    (fun before after => Good setup codec before.1 before.2 → Good setup codec after.1 after.2)
    (fun _ valid => valid) (fun _ _ _ first second valid => second (first valid))
    (fun query state answer answerSupported valid =>
      good_step setup codec checks route seed phase1 phase2 query state.1 state.2 valid answer answerSupported)
    adversary (memory, native) reached member
  exact preserved good

/-- Fresh states yield an exact source14 implementation of native admission, without additional private capabilities. -/
theorem compile_native {X : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (adversary : OracleComp Spec X) (native : PqxdhRegistrationSchedule.State KemSK)
    (keyId : native.shared.2.server.identityKeyId = setup.serverKeyId)
    (lastId : native.shared.2.server.control.last_key_id = setup.serverKeyId)
    (peers : ∀ keyId, native.shared.2.server.server.peers keyId = none)
    (owners : native.owners = []) (pending : ∀ session, native.shared.2.pending session = none) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        (CborAdmissionCompiler.compile setup codec route adversary)).run native =
      (simulateQ (nativeHandler setup codec checks route seed) adversary).run
        ⟨native, 0, fun _ => 0, []⟩ :=
  by
  simpa only [CborAdmissionCompiler.compile, merge, Local.empty, PqxdhDeploymentCompile.merge_empty] using
    compile_simulation setup codec checks route seed phase1 phase2 adversary (Local.empty setup.serverKeyId)
      native (good_initial setup codec native keyId lastId peers owners pending)

end BeaconcryptCore.Computational.CborAdmissionCompileStep

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileStep.compiledImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileStep.compiledImpl_run
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileStep.good_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileStep.good_initial
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileStep.step_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileStep.step_merge
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileStep.good_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileStep.good_step
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileStep.compile_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileStep.compile_simulation
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileStep.good_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileStep.good_run
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileStep.compile_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileStep.compile_native

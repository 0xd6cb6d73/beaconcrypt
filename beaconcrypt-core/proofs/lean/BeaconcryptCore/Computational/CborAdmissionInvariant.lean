-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionCompiler
import BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleLedger

/-! The guarded compiler retains the existing native reconstruction invariant and tracks the publicly returned allocation counter. These are operational and capability-accounting facts, not an independent security assumption. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionInvariant
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhDeploymentRecordCache (SourceSpec)
open PqxdhRegistrationJointRevealCosts (sourceKind)
open CborAdmissionCompiler (Local Good merge build buildPayload)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every source14 query raises the allocation counter only within its build allowance. -/
theorem source_count_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain) (native : PqxdhRegistrationSchedule.State KemSK)
    (result : (SourceSpec KemSK).Range query × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run native)) :
    result.2.shared.2.server.control.last_key_id.val ≤ native.shared.2.server.control.last_key_id.val +
      if sourceKind (KemSK := KemSK) query = .inl 4 then 1 else 0 := by
  cases query with
  | inl request =>
    change result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks seed request).run native) at supported
    have upper := PqxdhRegistrationSchedule.handler_counter_count setup codec checks seed request native result supported
    cases request with
    | inl coin => exact upper
    | inr command => cases command <;> exact upper
  | inr request =>
    simp only [PqxdhRegistrationJointRevealSchedule.native, StateT.run, support_pure,
      Set.mem_singleton_iff] at supported
    subst supported
    exact Nat.le_add_right _ _

/-- Kernel reads and every source capability preserve monotonicity of the same allocation counter. -/
theorem source_monotone_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain) (native : PqxdhRegistrationSchedule.State KemSK)
    (result : (SourceSpec KemSK).Range query × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run native)) :
    native.shared.2.server.control.last_key_id.val ≤ result.2.shared.2.server.control.last_key_id.val := by
  cases query with
  | inl request =>
    change result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks seed request).run native) at supported
    rcases PqxdhRegistrationSchedule.handler_counter setup codec checks seed request native result supported with
      unchanged | advanced <;> omega
  | inr request =>
    simp only [PqxdhRegistrationJointRevealSchedule.native, StateT.run, support_pure,
      Set.mem_singleton_iff] at supported
    subst supported
    exact le_rfl

/-- An adaptive source14 program with no build request preserves the entire public allocation counter. -/
theorem source_no_build_counter {Result : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (seed : IdentitySeed)
    (work : OracleComp (SourceSpec KemSK) Result)
    (bounded : work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = .inl 4) 0)
    (native : PqxdhRegistrationSchedule.State KemSK) (result : Result × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      work).run native)) :
    result.2.shared.2.server.control.last_key_id = native.shared.2.server.control.last_key_id := by
  have upper := PqxdhServerAuthExperiment.run_count
    (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
    (fun query => sourceKind (KemSK := KemSK) query = .inl 4) (fun state => state.shared.2.server.control.last_key_id.val)
    (source_count_step setup codec checks seed) work 0 bounded native result supported
  have lower := PqxdhServerAuthExperiment.run_rel
    (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
    (fun before after => before.shared.2.server.control.last_key_id.val ≤ after.shared.2.server.control.last_key_id.val)
    (fun _ => le_rfl) (fun _ _ _ first second => first.trans second)
    (source_monotone_step setup codec checks seed) work native result supported
  exact UScalar.eq_of_val_eq (Nat.le_antisymm (by simpa only [Nat.add_zero] using upper) lower)

/-- Every delegated command outside the build class has zero source14 build queries. -/
theorem existing_no_build_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhDeploymentInterface.Spec.Domain)
    (quiet : PqxdhDeploymentCompileBudget.commandKind query ≠ 4) (copies : PqxdhDeploymentCompile.Local) :
    ((PqxdhDeploymentCompile.compileImpl setup codec route query).run copies).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inl 4) 0 := by
  have counted := PqxdhDeploymentCompileBudget.step_bound setup codec route (.inl 4) query copies
  cases query with
  | inl coin => exact counted
  | inr command =>
    cases command with
    | build session payload => exact (quiet rfl).elim
    | _ => exact counted

/-- A returned build ID updates the public counter; every failed build retains its previous value. -/
theorem build_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (session : Nat) (payload : Option Pqxdh.Bytes) (memory : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native)
    (result : (Option PqxdhServerRegistrationPublication.Response × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((build setup codec route session payload).run memory)).run native)) :
    Good setup codec result.1.2 result.2 := by
  rw [CborAdmissionCompiler.build_source_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  refine ⟨PqxdhDeploymentCompileInvariant.good_build setup codec checks seed phase2 session
    (buildPayload memory.lastId payload) memory.copies native good.nativeGood reached member, ?_⟩
  change (reached.1.map PqxdhServerRegistrationPublication.Response.keyId).getD memory.lastId =
    reached.2.shared.2.server.control.last_key_id
  rcases PqxdhRegistrationSchedule.build_counter setup codec checks seed session
    (buildPayload memory.lastId payload) native reached member with ⟨absent, unchanged⟩ | ⟨response, present, _, assigned⟩
  case inl =>
    simp only [absent, Option.map_none, Option.getD_none, unchanged]
    exact good.lastId
  case inr =>
    simp only [present, Option.map_some, Option.getD_some]
    exact assigned

/-- Extending the compiler's public counter leaves delegated source execution unchanged. -/
theorem liftExisting_source_run {Result : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (seed : IdentitySeed)
    (work : StateT PqxdhDeploymentCompile.Local (OracleComp (SourceSpec KemSK)) Result)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((CborAdmissionCompiler.liftExisting work).run memory)).run native =
      (fun result => ((result.1.1, { memory with copies := result.1.2 }), result.2)) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
          (work.run memory.copies)).run native := by
  change (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
    ((fun result => (result.1, { memory with copies := result.2 })) <$> work.run memory.copies)).run native = _
  rw [simulateQ_map, StateT.run_map]

/-- A delegated command retains the old compiler's exact native reconstruction. -/
theorem liftExisting_native_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (query : PqxdhDeploymentInterface.Spec.Domain) (memory : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((CborAdmissionCompiler.liftExisting (PqxdhDeploymentCompile.compileImpl setup codec route query)).run memory)).run native =
      (PqxdhDeploymentNative.handler setup codec checks route seed query).run (merge memory native) := by
  have old := PqxdhDeploymentCompileStep.step_merge setup codec checks route seed query memory.copies native
    (PqxdhDeploymentCompileInvariant.good_inv setup codec memory.copies native good.nativeGood)
  rw [PqxdhDeploymentCompileStep.compiledImpl_run] at old
  simpa only [liftExisting_source_run, Functor.map_map, merge, Prod.map_apply, id_eq] using old

/-- Delegating a command outside the build class preserves both reconstruction and the public counter. -/
theorem liftExisting_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (query : PqxdhDeploymentInterface.Spec.Domain)
    (quiet : PqxdhDeploymentCompileBudget.commandKind query ≠ 4)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native)
    (result : (PqxdhDeploymentInterface.Spec.Range query × Local) × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((CborAdmissionCompiler.liftExisting (PqxdhDeploymentCompile.compileImpl setup codec route query)).run memory)).run native)) :
    Good setup codec result.1.2 result.2 := by
  rw [liftExisting_source_run, support_map] at supported
  obtain ⟨reached, member, rfl⟩ := supported
  have oldSupported : (reached.1.1, (reached.1.2, reached.2)) ∈ support
      ((PqxdhDeploymentCompileStep.compiledImpl setup codec checks route seed query).run (memory.copies, native)) := by
    rw [PqxdhDeploymentCompileStep.compiledImpl_run, support_map]
    exact ⟨reached, member, rfl⟩
  refine ⟨PqxdhDeploymentCompileInvariant.good_step setup codec checks route seed phase1 phase2 query
    memory.copies native good.nativeGood (reached.1.1, (reached.1.2, reached.2)) oldSupported, ?_⟩
  change memory.lastId = reached.2.shared.2.server.control.last_key_id
  rw [source_no_build_counter setup codec checks seed
    ((PqxdhDeploymentCompile.compileImpl setup codec route query).run memory.copies)
    (existing_no_build_bound setup codec route query quiet memory.copies) native reached member]
  exact good.lastId

/-- On an admitted delegated command, the guarded target is the original native target. -/
theorem liftExisting_step_exact (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : IdentitySeed)
    (query : PqxdhDeploymentInterface.Spec.Domain) (memory : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) (good : Good setup codec memory native)
    (admitted : CborProductionBoundary.allowed query (merge memory native) = true) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((CborAdmissionCompiler.liftExisting (PqxdhDeploymentCompile.compileImpl setup codec route query)).run memory)).run native =
      (CborAdmissionCompiler.nativeHandler setup codec checks route seed query).run (merge memory native) := by
  rw [liftExisting_native_exact setup codec checks route seed query memory native good]
  change _ = if CborProductionBoundary.allowed query (merge memory native) then _ else _
  simp only [admitted, ite_true]

end BeaconcryptCore.Computational.CborAdmissionInvariant

/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.source_count_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.source_count_step
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.source_monotone_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.source_monotone_step
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.source_no_build_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.source_no_build_counter
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.existing_no_build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.existing_no_build_bound
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.build_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.build_good
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_source_run
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_native_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_native_exact
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_good
/-- info: 'BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_step_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionInvariant.liftExisting_step_exact

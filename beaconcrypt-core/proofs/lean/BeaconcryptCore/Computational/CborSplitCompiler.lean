-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionCompileStep
import BeaconcryptCore.Computational.CborAdmissionCompileBudget

/-! Registration and established records need different codecs: registration can use a total internal representation while record encoding remains fallible. The source14 interpreter below uses only the registration codec. Record commands keep the existing local record compiler and its native frame reader and writer. Changing these two fields does not change public identity reconstruction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborSplitCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentCompileBudget (commandKind cost unit)
open CborAdmissionCompiler (Local Good merge)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

def records (codec : Codec Reader Response) (decode : RawCtxReceive.FrameDecoder)
    (write : RawCtxMixedShared.Writer) : Codec Reader Response :=
  { codec with frameRead := decode, frameWrite := write }

def recordCommand : Spec.Domain → Bool
  | .inr (.serverSend _ _) | .inr (.serverRaw _) | .inr (.beaconSend _ _) | .inr (.beaconRaw _ _) => true
  | _ => false

def selected (codec : Codec Reader Response) (decode : RawCtxReceive.FrameDecoder)
    (write : RawCtxMixedShared.Writer) (query : Spec.Domain) : Codec Reader Response :=
  if recordCommand query then records codec decode write else codec

def RecordKind (kind : SourceKind) : Prop :=
  kind = .inl 7 ∨ kind = .inl 8 ∨ kind = .inr 4

/-- A program that issues only hash and addressed-kernel reads cannot observe the registration codec. The zero bounds cover every possible reply continuation. -/
theorem simulate_quiet {κ S Result : Type} {target : OracleSpec κ}
    (left right : QueryImpl (PqxdhDeploymentRecordCache.SourceSpec KemSK) (StateT S (OracleComp target)))
    (same : ∀ query, RecordKind (sourceKind (KemSK := KemSK) query) → left query = right query)
    (work : OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) Result)
    (quiet : ∀ kind, ¬RecordKind kind →
      work.IsQueryBoundP (fun query => sourceKind (KemSK := KemSK) query = kind) 0) :
    simulateQ left work = simulateQ right work := by
  classical
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    have permitted : RecordKind (sourceKind (KemSK := KemSK) query) := by
      by_contra forbidden
      have bound := quiet _ forbidden
      rw [isQueryBoundP_query_bind_iff] at bound
      simpa using bound.1
    simp only [simulateQ_bind, simulateQ_spec_query, same query permitted]
    congr 1
    funext reply
    apply ih reply
    intro kind forbidden
    have bound := quiet kind forbidden
    rw [isQueryBoundP_query_bind_iff] at bound
    simpa using bound.2 reply

theorem native_record_query (setup : Setup baseSpec KemSK)
    (left right : Codec Reader Response) (checks : Checks) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : (PqxdhDeploymentRecordCache.SourceSpec KemSK).Domain)
    (permitted : RecordKind (sourceKind (KemSK := KemSK) query)) :
    PqxdhRegistrationJointRevealSchedule.native setup left checks seed query =
      PqxdhRegistrationJointRevealSchedule.native setup right checks seed query := by
  rcases query with (coin | command) | ⟨index, field⟩
  · simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
  · cases command
    all_goals try simp [RecordKind, sourceKind, PqxdhRegistrationSchedule.sourceKind] at permitted
    all_goals rfl
  · cases field
    all_goals try simp [RecordKind, sourceKind, PqxdhRegistrationJointRevealCosts.fieldIndex] at permitted
    all_goals rfl

/-- Both frame fields are irrelevant to the existing public reconstruction invariant. -/
theorem good_records (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    Good setup (records codec decode write) memory native ↔ Good setup codec memory native := by
  constructor
  all_goals intro good
  all_goals exact ⟨⟨good.nativeGood.keyId, good.nativeGood.installed, good.nativeGood.serverVisible,
    good.nativeGood.count, good.nativeGood.copied, good.nativeGood.owners,
    good.nativeGood.pending, good.nativeGood.accepts, good.nativeGood.peers, good.nativeGood.pendingInit⟩,
    good.lastId⟩

theorem good_selected (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (query : Spec.Domain)
    (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    Good setup (selected codec decode write query) memory native ↔ Good setup codec memory native := by
  cases chosen : recordCommand query <;> simp only [selected, chosen, Bool.false_eq_true, ite_false, ite_true]
  exact good_records setup codec decode write memory native

noncomputable def compileImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT Local (OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK))) :=
  fun query => CborAdmissionCompiler.compileImpl setup (selected codec decode write query) route query

noncomputable def nativeHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (PqxdhDeploymentNative.State KemSK) ProbComp) :=
  fun query => CborAdmissionCompiler.nativeHandler setup (selected codec decode write query) checks route seed query

noncomputable def compiledImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl Spec (StateT (Local × PqxdhRegistrationSchedule.State KemSK) ProbComp) :=
  ((PqxdhRegistrationJointRevealSchedule.native setup codec checks seed).mapStateTBase
    (compileImpl setup codec decode write route)).flattenStateT

noncomputable def compile (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp Spec X) :
    OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) (X × Local) :=
  (simulateQ (compileImpl setup codec decode write route) work).run (Local.empty setup.serverKeyId)

theorem compiledImpl_source_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup codec decode write checks route seed query).run (memory, native) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
          ((compileImpl setup codec decode write route query).run memory)).run native := rfl

/-- Record steps issue no registration request. Consequently all native optional writer outcomes are retained while the source14 registration interpretation stays fixed. -/
theorem reinterpret_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (memory : Local) :
    simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((compileImpl setup codec decode write route query).run memory) =
      simulateQ (PqxdhRegistrationJointRevealSchedule.native setup (selected codec decode write query) checks seed)
        ((compileImpl setup codec decode write route query).run memory) := by
  classical
  by_cases record : recordCommand query = true
  · apply simulate_quiet _ _ (native_record_query setup codec _ checks seed)
    intro kind forbidden
    have bound := CborAdmissionCompileBudget.step_bound setup (selected codec decode write query)
      route kind query memory
    have zero : cost kind (commandKind query) = 0 := by
      rcases query with coin | command
      · simp [recordCommand] at record
      · cases command
        all_goals try simp [recordCommand] at record
        all_goals simp only [RecordKind, not_or] at forbidden
        all_goals simp [commandKind, cost, unit, forbidden.1, forbidden.2.1, forbidden.2.2]
    simpa only [compileImpl, zero] using bound
  · simp only [compileImpl, selected, record, Bool.false_eq_true, ite_false]

/-- Every split-codec command keeps the exact reply and the complete merged native poststate. -/
theorem step_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((compileImpl setup codec decode write route query).run memory)).run native =
      (nativeHandler setup codec decode write checks route seed query).run (merge memory native) := by
  rw [reinterpret_step]
  simpa only [CborAdmissionCompileStep.compiledImpl_run, Functor.map_map, Prod.map_apply,
    id_eq, compileImpl, nativeHandler] using
    CborAdmissionCompileStep.step_merge setup (selected codec decode write query) checks route seed query
      memory native ((good_selected setup codec decode write query memory native).mpr good)

theorem compiledImpl_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : Spec.Domain) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup codec decode write checks route seed query).run (memory, native) =
      (CborAdmissionCompileStep.compiledImpl setup (selected codec decode write query) checks route seed query).run
        (memory, native) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
      ((compileImpl setup codec decode write route query).run memory)).run native = _
  rw [reinterpret_step]
  rfl

/-- The public reconstruction invariant survives all optional failures with the split codecs. -/
theorem good_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (query : Spec.Domain) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native)
    (result : Spec.Range query × (Local × PqxdhRegistrationSchedule.State KemSK))
    (supported : result ∈ support ((compiledImpl setup codec decode write checks route seed query).run
      (memory, native))) : Good setup codec result.2.1 result.2.2 := by
  rw [compiledImpl_run] at supported
  apply (good_selected setup codec decode write query result.2.1 result.2.2).mp
  apply CborAdmissionCompileStep.good_step setup (selected codec decode write query) checks route seed
    ?_ ?_ query memory native ((good_selected setup codec decode write query memory native).mpr good) result supported
  · cases chosen : recordCommand query <;>
      simpa only [selected, chosen, Bool.false_eq_true, ite_false, ite_true,
        PqxdhServerAuthNegativeControl.Phase1ReadBack, records] using phase1
  · cases chosen : recordCommand query <;>
      simpa only [selected, chosen, Bool.false_eq_true, ite_false, ite_true,
        PqxdhServerAuthNegativeControl.Phase2ReadBack, records] using phase2

/-- Arbitrary adaptive programs use the registration codec only for registration and retain the genuine local record codec, jointly over their output and complete state. -/
theorem compile_simulation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (seed : PqxdhJointIdentity.IdentitySeed)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec)
    (work : OracleComp Spec X) (memory : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (good : Good setup codec memory native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
      (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed)
        ((simulateQ (compileImpl setup codec decode write route) work).run memory)).run native =
      (simulateQ (nativeHandler setup codec decode write checks route seed) work).run (merge memory native) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiledImpl setup codec decode write checks route seed) (nativeHandler setup codec decode write checks route seed)
    (fun state => Good setup codec state.1 state.2) (fun state => merge state.1 state.2)
    (fun query state valid result supported =>
      good_step setup codec decode write checks route seed phase1 phase2 query state.1 state.2 valid result supported)
    (fun query state valid => by
      rw [compiledImpl_source_run, Functor.map_map]
      exact step_merge setup codec decode write checks route seed query state.1 state.2 valid)
    work (memory, native) good
  rw [← simulated]
  rfl

/-- Splitting the codecs changes no source-query coordinate or per-command bill. -/
theorem step_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer)
    (route : RawCtxServerRouting.SenderDecoder) (kind : SourceKind) (query : Spec.Domain) (memory : Local) :
    ((compileImpl setup codec decode write route query).run memory).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (cost kind (commandKind query)) :=
  CborAdmissionCompileBudget.step_bound setup (selected codec decode write query) route kind query memory

theorem compile_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (write : RawCtxMixedShared.Writer)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp Spec X) (budget : Fin 12 → Nat)
    (bounded : ∀ command, work.IsQueryBoundP (fun query => commandKind query = command) (budget command))
    (kind : SourceKind) :
    (compile setup codec decode write route work).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind)
      (∑ command, cost kind command * budget command) :=
  FinitePartitionQueryBounds.weighted_bound commandKind (cost kind) budget
    (compileImpl setup codec decode write route) (fun request => sourceKind (KemSK := KemSK) request = kind)
    work bounded (fun query memory => step_bound setup codec decode write route kind query memory)
    (Local.empty setup.serverKeyId)

end BeaconcryptCore.Computational.CborSplitCompiler

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.compile_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.compile_simulation

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.compile_bound

-- Exact dependency observations for all public helper theorems.

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.simulate_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.simulate_quiet

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.native_record_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.native_record_query

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.good_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.good_records

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.good_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.good_selected

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.compiledImpl_source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.compiledImpl_source_run

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.reinterpret_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.reinterpret_step

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.step_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.step_merge

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.compiledImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.compiledImpl_run

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.good_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.good_step

/-- info: 'BeaconcryptCore.Computational.CborSplitCompiler.step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborSplitCompiler.step_bound

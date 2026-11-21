-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditTrace

/-! Erasing the paired chronology from the actual audited selective interpreter recovers the literal existing World audit on the same complete native callback program. The alternative state reassociation exposes its exact original pure monitor before the real private/World interpretations, so supported clean frontend results remain the same executions. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeG3AuditTrace (State handler)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

def forget (before : State n KemSK ProviderState) := (before.1.2, before.2)
def associate (before : State n KemSK ProviderState) := (before.1.1, before.1.2, before.2)

variable (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
  (wire : RegistrationNativeWire.Wire)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)

private theorem state_map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

noncomputable def closed :=
  ((RegistrationNativeG3AuditQuiet.world setup codec route seeds).mapStateTBase
    (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)).flattenStateT

noncomputable def tracedClosed :=
  ((closed setup codec route seeds wire sign seed scalar candidate provider).mapStateTBase
    RegistrationNativePairedTrace.handler).flattenStateT

private theorem trace_query (query : (Spec n KemSK).Domain) (before : State n KemSK ProviderState) :
    Prod.map id associate <$> (handler setup codec route seeds wire sign seed scalar candidate provider query).run before =
      (tracedClosed setup codec route seeds wire sign seed scalar candidate provider query).run (associate before) := by
  simp only [tracedClosed, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    RegistrationNativePairedTrace.handler, simulateQ_map, simulateQ_spec_query,
    handler, closed, StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq, associate, state_map_apply]

/-- The actual paired chronology and both concrete private interpreters reassociate exactly on the complete joint state. -/
theorem trace_program (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    Prod.map id associate <$> (simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider) work).run before =
      (simulateQ (tracedClosed setup codec route seeds wire sign seed scalar candidate provider) work).run (associate before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ associate
    (trace_query setup codec route seeds wire sign seed scalar candidate provider) work before

/-- The original pure paired monitor is followed by the same literal closed selective/native World execution, with no synthesized descriptor events. -/
theorem monitor_source (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    (fun result => ((result.1, result.2.1.1), forget result.2)) <$>
      (simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider) work).run before =
      (simulateQ (closed setup codec route seeds wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativePairedTrace.handler work).run before.1.1)).run (forget before) := by
  have reassociated := congrArg (Functor.map (fun result => ((result.1, result.2.1), result.2.2)))
    (trace_program setup codec route seeds wire sign seed scalar candidate provider work before)
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (closed setup codec route seeds wire sign seed scalar candidate provider)
    RegistrationNativePairedTrace.handler work before.1.1 (forget before)
  simpa only [tracedClosed, Functor.map_map, Prod.map_def, id_eq, associate, forget] using reassociated.trans nested.symm

/-- Every actual machine-supported value and chronology is a supported result of the same original open paired monitor program. -/
theorem open_support (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState)
    (result : Value × State n KemSK ProviderState)
    (supported : result ∈ support ((simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider) work).run before)) :
    (result.1, result.2.1.1) ∈ support ((simulateQ RegistrationNativePairedTrace.handler work).run before.1.1) := by
  have closedSupport : ((result.1, result.2.1.1), forget result.2) ∈ support
      ((simulateQ (closed setup codec route seeds wire sign seed scalar candidate provider)
        ((simulateQ RegistrationNativePairedTrace.handler work).run before.1.1)).run (forget before)) := by
    rw [← monitor_source, support_map]
    exact Set.mem_image_of_mem (fun result => ((result.1, result.2.1.1), forget result.2)) supported
  apply OracleComp.support_simulateQ_run'_subset (closed setup codec route seeds wire sign seed scalar candidate provider) _ (forget before)
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst closedSupport

private theorem query_forget (query : (Spec n KemSK).Domain) (before : State n KemSK ProviderState) :
    Prod.map id forget <$> (handler setup codec route seeds wire sign seed scalar candidate provider query).run before =
      (closed setup codec route seeds wire sign seed scalar candidate provider query).run (forget before) := by
  simp only [handler, closed, QueryImpl.flattenStateT, QueryImpl.mapStateTBase,
    StateT.run, StateT.mk, Functor.map_map, Prod.map_def, id_eq, forget]

/-- Forgetting only the paired observer recovers the same complete actual closed native callback execution. -/
theorem program_forget (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    Prod.map id forget <$> (simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider) work).run before =
      (simulateQ (closed setup codec route seeds wire sign seed scalar candidate provider) work).run (forget before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ forget
    (query_forget setup codec route seeds wire sign seed scalar candidate provider) work before

/-- The actual full audited run retains exactly the original private state and World when its trace is erased. -/
theorem audit_source (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState) (unmarked : before.2.2 = false) :
    (fun result => ((result.1, result.2.1.2), result.2.2)) <$>
      (simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider) work).run before =
      RegistrationNativeG3GuardedCoupling.audit setup codec route seeds
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work).run before.1.2) before.2.1 := by
  have erased := congrArg (Functor.map (fun result => ((result.1, result.2.1), result.2.2)))
    (program_forget setup codec route seeds wire sign seed scalar candidate provider work before)
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeG3AuditQuiet.world setup codec route seeds)
    (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work before.1.2 before.2
  have combined := erased.trans nested.symm
  simpa only [RegistrationNativeG3GuardedCoupling.audit, RegistrationNativeG3AuditQuiet.world,
    QueryImpl.simulateQ_compose, closed, Functor.map_map, Prod.map_def, id_eq, forget, ← unmarked] using combined

/-- Erasing only paired choice/bad instrumentation leaves the literal original G2 chronology inside the same private and marked World execution. -/
theorem trace_source (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    (fun result => (((result.1, result.2.1.1.trace), result.2.1.2), result.2.2)) <$>
      (simulateQ (handler setup codec route seeds wire sign seed scalar candidate provider) work).run before =
      (simulateQ (RegistrationNativeG3AuditQuiet.world setup codec route seeds)
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
          ((simulateQ RegistrationNativeG2Trace.handler work).run before.1.1.trace)).run before.1.2)).run before.2 := by
  have erased := congrArg (Functor.map (fun result => (((result.1.1, result.1.2.trace), result.2.1), result.2.2)))
    (monitor_source setup codec route seeds wire sign seed scalar candidate provider work before)
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeG3AuditQuiet.world setup codec route seeds)
    (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
    ((simulateQ RegistrationNativePairedTrace.handler work).run before.1.1) before.1.2 before.2
  have transported := congrArg (Functor.map (fun result => (((result.1.1.1, result.1.1.2.trace), result.1.2), result.2))) nested
  simp only [Functor.map_map, forget, closed] at erased
  simp only [Functor.map_map, ] at transported
  rw [← RegistrationNativePairedTrace.program_source work before.1.1]
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, closed, Prod.map_def, id_eq] using erased.trans transported.symm

end BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.program_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.program_forget
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.audit_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.audit_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.trace_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.trace_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.monitor_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.monitor_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.open_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.open_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.trace_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditTraceSource.trace_source

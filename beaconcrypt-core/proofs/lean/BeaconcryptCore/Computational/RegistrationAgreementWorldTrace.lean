-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementSampledState
import BeaconcryptCore.Computational.RegistrationAgreementQueryTracePrefix
open CoreModels Aeneas OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
/-! Returning the same private query/reply trace before counting is equivalent to the actual per-callback World interpreter. The public native journal is the ordered concatenation of recorded callback kinds from that trace; no final-role reconstruction is used. -/
namespace BeaconcryptCore.Computational.RegistrationAgreementWorldTrace
open RegistrationAgreementExecutor RegistrationAgreementQueryTrace
open RegistrationAgreementSampledState
variable {n : Nat} {Auxiliary Value : Type}

def recorded (journal : Trace) : List Request := journal.flatMap (fun entry => RegistrationWorldAgreement.recorded entry.1)

def restore (before : RegistrationWorldAgreement.State n Auxiliary)
    (result : ((Value × Trace) × Auxiliary) × PqxdhRecordLiftWorld.State n) :
    Value × RegistrationWorldAgreement.State n Auxiliary :=
  (result.1.1.1, ⟨result.1.2, before.requests ++ recorded result.1.1.2,
    before.recordRequests, (result.2, before.world.2)⟩)

def implementation (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) :
    QueryImpl Spec (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) := fun request before =>
  (fun result => (result.1.1, ⟨result.1.2, before.requests ++ RegistrationWorldAgreement.recorded request,
    before.recordRequests, (result.2, before.world.2)⟩)) <$>
    (PqxdhRecordLiftWorld.sampled ((backend request).run before.auxiliary)).run before.world.1

theorem program (backend : QueryImpl Spec (StateT Auxiliary ProbComp)) (work : OracleComp Spec Value)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    (simulateQ (implementation backend) work).run before =
      restore before <$> (PqxdhRecordLiftWorld.sampled
        ((simulateQ backend (trace work [])).run before.auxiliary)).run before.world.1 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, trace_pure, sampled_pure, map_pure]
    simp only [restore, recorded, List.flatMap_nil, List.append_nil]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      RegistrationAgreementQueryTracePrefix.query_bind_empty, simulateQ_map, StateT.run_map]
    rw [sampled_bind]
    simp only [implementation, StateT.run, bind_map_left, map_bind]
    apply bind_congr
    rintro ⟨⟨reply, auxiliary⟩, world⟩
    change (simulateQ (implementation backend) (next reply)).run
      ⟨auxiliary, before.requests ++ RegistrationWorldAgreement.recorded request,
        before.recordRequests, (world, before.world.2)⟩ = _
    rw [ih reply]
    change _ = restore before <$>
      (PqxdhRecordLiftWorld.sampled ((fun result => ((result.1.1, ⟨request, reply⟩ :: result.1.2), result.2)) <$>
        (simulateQ backend (trace (next reply) [])).run auxiliary)).run world
    rw [RegistrationAgreementSampledState.sampled_map, Functor.map_map]
    congr 1
    funext result
    rcases result with ⟨⟨⟨value, journal⟩, after⟩, final⟩
    simp only [restore, recorded, List.flatMap_cons, List.append_assoc, Prod.map_apply, id_eq]

theorem actual (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (primitive : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (work : OracleComp Spec Value) (before : RegistrationWorldAgreement.State n Auxiliary) :
    (simulateQ (RegistrationWorldAgreement.agreement source primitive) work).run before =
      restore before <$> (PqxdhRecordLiftWorld.sampled
        ((simulateQ (RegistrationAgreementShared.auxiliary source primitive) (trace work [])).run before.auxiliary)).run before.world.1 :=
  program (RegistrationAgreementShared.auxiliary source primitive) work before
end BeaconcryptCore.Computational.RegistrationAgreementWorldTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementWorldTrace.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementWorldTrace.program

/-- info: 'BeaconcryptCore.Computational.RegistrationAgreementWorldTrace.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAgreementWorldTrace.actual

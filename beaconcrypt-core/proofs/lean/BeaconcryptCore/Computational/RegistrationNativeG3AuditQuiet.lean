-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3AuditHistoryRun

/-! Every actual ordinary materialized World callback retains the used-role map and sticky repetition flag. The result applies to arbitrary adaptive ordinary programs, including actual publication, KEM, demand-coin and record continuations; no successful result or fixed-outcome trace is substituted. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3AuditQuiet
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3KnownWorldFrameCore (Allowed)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

noncomputable def world (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) :
    QueryImpl (WorldSpec n) (StateT (PqxdhRecordLiftWorld.State n × Bool) ProbComp) :=
  RegistrationNativeG3GuardedWorld.marked setup codec route seeds true ∘ₛ RegistrationNativeG3Materialize.materialize

private theorem materialize_ordinary (query : (WorldSpec n).Domain) (allowed : Allowed query) :
    RegistrationNativeG3Materialize.materialize query =
      (((RegistrationNativeG3AuditedWorld.Spec n).query (.ordinary query allowed)) :
        OracleComp (RegistrationNativeG3AuditedWorld.Spec n) ((WorldSpec n).Range query)) := by
  rcases query with created | (coin | capability) | record
  · rfl
  · rfl
  · cases capability with
    | installServer keyId binding kernel => cases kernel with
      | known kernel => rfl
      | hidden slot => exact False.elim (allowed trivial)
    | installBeacon owner shell kernel => cases kernel with
      | known kernel => rfl
      | hidden slot => exact False.elim (allowed trivial)
    | _ => rfl
  · rfl

/-- The exact known marked interpretation of an ordinary actual World query changes neither audited field. -/
theorem query (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (request : (WorldSpec n).Domain)
    (allowed : Allowed request) (before : PqxdhRecordLiftWorld.State n × Bool)
    (result : (WorldSpec n).Range request × (PqxdhRecordLiftWorld.State n × Bool))
    (supported : result ∈ support ((world setup codec route seeds request).run before)) :
    result.2.1.used = before.1.used ∧ result.2.2 = before.2 := by
  change result ∈ support ((simulateQ (RegistrationNativeG3GuardedWorld.marked setup codec route seeds true)
    (RegistrationNativeG3Materialize.materialize request)).run before) at supported
  rw [materialize_ordinary request allowed, simulateQ_spec_query] at supported
  have used := RegistrationNativeG3AuditHistory.query_used setup codec route seeds (.ordinary request allowed) before result supported
  refine ⟨used, ?_⟩
  simp only [RegistrationNativeG3GuardedWorld.marked, StateT.run, support_map] at supported
  obtain ⟨reached, _possible, equal⟩ := supported
  cases equal
  simp only [RegistrationNativeG3AuditedWorld.repeated, Bool.or_false]

/-- Actual adaptive ordinary World programs preserve the same used-role map and repetition flag through every failure continuation. -/
theorem program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) Value) (allowed : AllQueriesSatisfy work (Allowed (n := n)))
    (before : PqxdhRecordLiftWorld.State n × Bool) (result : Value × (PqxdhRecordLiftWorld.State n × Bool))
    (supported : result ∈ support ((simulateQ (world setup codec route seeds) work).run before)) :
    result.2.1.used = before.1.used ∧ result.2.2 = before.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨rfl, rfl⟩
  | query_bind request next ih =>
      obtain ⟨head, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, actual, continued⟩ := supported
      have first := query setup codec route seeds request head before middle actual
      have rest := ih middle.1 (later middle.1) middle.2 continued
      exact ⟨rest.1.trans first.1, rest.2.trans first.2⟩

end BeaconcryptCore.Computational.RegistrationNativeG3AuditQuiet
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditQuiet.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditQuiet.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3AuditQuiet.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3AuditQuiet.program

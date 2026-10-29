-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationProtocol
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentWorld

/-! Source allocation footprints distinguish the one real append request from every other callback. Actual cursor filtering and arbitrary private-service interpretation preserve these footprints; retaining owner count is an operational consequence of the actual Protocol controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore
open PqxdhRecordLiftInterface (WorldSpec EnvEffects)
open RegistrationNativeHiddenAllocationProtocol (delta effectDelta)
variable {n : Nat} {Reader Response Secret Value Index : Type} {spec : OracleSpec Index}

/-- A local request is allocation-free except for the literal forwarded environment append. -/
def Allowed : (RegistrationNativePublicFrontend.Spec n Unit).Domain → Prop
  | .inl (.inr (.inl (.inr (.inr effect)))) => effectDelta effect = 0
  | _ => True

def WorldAllowed (query : (WorldSpec n).Domain) : Prop := delta query = 0

/-- Observing a computed value adds no allocation request. -/
theorem mapped {Result : Type} (work : OracleComp spec Value) (observe : Value → Result)
    (predicate : Index → Prop) (safe : AllQueriesSatisfy work predicate) :
    AllQueriesSatisfy (observe <$> work) predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind safe (fun _ => allQueriesSatisfy_pure _ _)

/-- Query-by-query source footprints persist through the actual adaptive open interpreter. -/
theorem simulation {Target : Type} {target : OracleSpec Target} (implementation : QueryImpl spec (OracleComp target))
    (first : Index → Prop) (second : Target → Prop)
    (step : ∀ query, first query → AllQueriesSatisfy (implementation query) second)
    (work : OracleComp spec Value) (safe : AllQueriesSatisfy work first) :
    AllQueriesSatisfy (simulateQ implementation work) second := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind (step query allowed) (fun reply => ih reply (later reply))

/-- Cursor refusal can omit the current request and cannot introduce an owner allocation. -/
theorem cursor_query (query : (WorldSpec n).Domain) (shell : CborRecordWorldClient.Shell)
    (safe : WorldAllowed query) :
    AllQueriesSatisfy ((CborRecordWorldClient.handler query).run shell) WorldAllowed := by
  cases refused : CborRecordWorldClient.refusal query shell with
  | some reply => simp only [CborRecordWorldClient.handler, StateT.run, refused]; trivial
  | none =>
      simp only [CborRecordWorldClient.handler, StateT.run, refused, CborRecordWorldClient.forward]
      exact mapped _ _ WorldAllowed ((allQueriesSatisfy_query_iff _ _).mpr safe)

/-- The actual cursor client preserves the source zero-allocation footprint through every reply branch. -/
theorem cursor_program (work : OracleComp (WorldSpec n) Value) (shell : CborRecordWorldClient.Shell)
    (safe : AllQueriesSatisfy work WorldAllowed) :
    AllQueriesSatisfy ((simulateQ CborRecordWorldClient.handler work).run shell) WorldAllowed := by
  induction work using OracleComp.inductionOn generalizing shell with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (cursor_query query shell allowed) (fun reply => ih reply.1 reply.2 (later reply.1))

/-- Allocation-free World programs preserve the complete actual physical owner-slot count. -/
theorem protocol_program (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (before : PqxdhRecordLiftProtocol.Control n)
    (result : Value × PqxdhRecordLiftProtocol.Control n)
    (safe : AllQueriesSatisfy work WorldAllowed)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftProtocol.handler decode route) work).run before)) :
    result.2.owners.length = before.owners.length := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have step := RegistrationNativeHiddenAllocationProtocol.query_length decode route query before middle reached
      rw [show delta query = 0 from allowed, Nat.add_zero] at step
      exact (ih middle.1 middle.2 (later middle.1) continued).trans step

/-- Arbitrary private service callbacks retain the allocation-free actual Protocol count below the real cursor. -/
theorem interpreted_program (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (shell : CborRecordWorldClient.Shell)
    (before : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : ((Value × CborRecordWorldClient.Shell) × PqxdhRecordLiftProtocol.Control n) × Secret)
    (safe : AllQueriesSatisfy work WorldAllowed)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route work shell before secret)) :
    result.1.2.owners.length = before.owners.length := by
  have reached : result.1 ∈ support ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((simulateQ CborRecordWorldClient.handler work).run shell)).run before) := by
    apply support_simulateQ_run'_subset service _ secret
    rw [StateT.run'_eq, support_map]
    exact ⟨result, supported, rfl⟩
  exact protocol_program codec.frameRead route _ before result.1 (cursor_program work shell safe) reached

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.mapped' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.mapped
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.simulation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.simulation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.cursor_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.cursor_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.cursor_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.cursor_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.protocol_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.protocol_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.interpreted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore.interpreted_program

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore

/-! The concrete cursor and arbitrary private service retain the Protocol allocator's actual index and slot count. The local mutable state is preserved by a lifted append, and allocation-free local programs preserve the reached physical owner count. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld
open PqxdhRecordLiftInterface (WorldSpec effectLift)
open RegistrationNativeHiddenEnvironmentWorld (State lower)
open RegistrationNativeHiddenAllocationCore (WorldAllowed)
variable {n : Nat} {Reader Response Secret E Value : Type}

/-- The actual interpreted append returns the old physical roster length and appends exactly one slot, after its genuine charge. -/
theorem append_run (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (sender : U64) (identity : RawCtxServerRouting.Identity) (phase : PqxdhRecordLiftInterface.InactivePhase)
    (shell : CborRecordWorldClient.Shell) (before : PqxdhRecordLiftProtocol.Control n) (secret : Secret) :
    CborRawRecordOriginFlatten.interpret service codec route (effectLift (.inr (.appendOwner sender identity phase))) shell before secret =
      (fun charged => (((before.owners.length, shell), { before with owners := before.owners ++ [.inactive phase] }), charged.2)) <$>
        (service (.charge (PqxdhRecordLiftInterface.effectKind (n := n) (.inr (.appendOwner sender identity phase))))).run secret := by
  simp only [CborRawRecordOriginFlatten.interpret, effectLift, simulateQ_spec_query,
    CborRecordWorldClient.handler, StateT.run, CborRecordWorldClient.refusal,
    CborRecordWorldClient.forward, simulateQ_map,
    CborRecordWorldClient.next, PqxdhRecordLiftProtocol.handler]
  change (simulateQ service ((fun result => ((result.1, shell), result.2)) <$>
      (PqxdhRecordLiftProtocol.effects (.inr (.appendOwner sender identity phase))).run before)).run secret = _
  rw [RegistrationNativeHiddenAllocationProtocol.append_run]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- Lifted native append retains all local state and the allocator's exact returned index. -/
theorem append_facts (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (sender : U64) (identity : RawCtxServerRouting.Identity) (phase : PqxdhRecordLiftInterface.InactivePhase)
    (before : State n E Secret) (result : Nat × State n E Secret)
    (supported : result ∈ support ((lower service codec route
      (StateT.lift (effectLift (.inr (.appendOwner sender identity phase))))).run before)) :
    result.1 = before.1.2.owners.length ∧ result.2.1.2.owners.length = before.1.2.owners.length + 1 ∧
      result.2.1.1.1 = before.1.1.1 := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_lift, append_run, Functor.map_map, support_map] at supported
  obtain ⟨charged, _charged, rfl⟩ := supported
  exact ⟨rfl, by simp only [List.length_append, List.length_singleton], rfl⟩

/-- Closing an allocation-free local program retains the physical owner count under any actual private service interpreter. -/
theorem noappend (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) Value) (before : State n E Secret)
    (result : Value × State n E Secret)
    (safe : AllQueriesSatisfy (work.run before.1.1.1) WorldAllowed)
    (supported : result ∈ support ((lower service codec route work).run before)) :
    result.2.1.2.owners.length = before.1.2.owners.length := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact RegistrationNativeHiddenAllocationCore.interpreted_program service codec route
    (work.run before.1.1.1) before.1.1.2 before.1.2 before.2 inner safe reached

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld.append_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld.append_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld.append_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld.append_facts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld.noappend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationWorld.noappend

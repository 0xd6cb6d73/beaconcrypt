-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordSemantics
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhDeploymentInterface (Spec)
open PqxdhServerAuthExperiment (Codec)
open RegistrationNativePlatformGatedRecordFlat (State fold)
variable {n : Nat} {I J Reader Response E X S Failure : Type} {base : OracleSpec I} {other : OracleSpec J}

private theorem simulated_support (service : QueryImpl base (OracleComp other))
    (work : OracleComp base X) (value : X) (supported : value ∈ support (simulateQ service work)) :
    value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported ⊢
      obtain ⟨reply, _possible, later⟩ := supported
      exact ⟨reply, mem_support_query query reply, ih reply later⟩

/-- Interpreting a public closed computation cannot fabricate a value absent from that computation. -/
theorem closed_support (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E ProbComp X) (before : State n E S) (result : X × State n E S)
    (supported : result ∈ support ((fold service codec route (RegistrationNativePlatformGatedRecordInterface.closed work)).run before)) :
    ∃ after, (result.1, after) ∈ support (work.run before.1.1.1) := by
  unfold fold at supported
  change result ∈ support (RegistrationNativePlatformGatedRecordFlat.join <$>
    CborRawRecordOriginFlatten.interpret service codec route
      (simulateQ PqxdhRecordLiftInterface.coinLift (work.run before.1.1.1)) before.1.1.2 before.1.2 before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have first := PqxdhRecordLiftFlat.support_run_fst service _ before.2 inner reached
  have second := PqxdhRecordLiftFlat.support_run_fst (PqxdhRecordLiftProtocol.handler codec.frameRead route) _ before.1.2 inner.1 first
  have third := PqxdhRecordLiftFlat.support_run_fst CborRecordWorldClient.handler _ before.1.1.2 inner.1.1 second
  exact ⟨inner.1.1.1.2, simulated_support PqxdhRecordLiftInterface.coinLift _ _ third⟩

/-- The terminal gate returns either its original reply or a refusal, with all reserve effects retained. -/
theorem gate_reply {Output : Type} (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (size : Output → Nat) (reply : Option Output) (before : E) (result : Option Output × E)
    (supported : result ∈ support ((RegistrationNativePlatformOrdinaryGate.gate reserve size reply).run before)) :
    result.1 = reply ∨ result.1 = none := by
  cases reply with
  | none =>
      obtain rfl := (mem_support_pure_iff _ _).mp supported
      exact Or.inr rfl
  | some value =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reserved, _called, returned⟩ := supported
      cases reserved with
      | mk reserved after => cases reserved with
        | Err error =>
            obtain rfl := (mem_support_pure_iff _ _).mp returned
            exact Or.inr rfl
        | Ok returnedUnit =>
            obtain rfl := (mem_support_pure_iff _ _).mp returned
            exact Or.inl rfl

/-- Every interpreted send gate keeps the same source reply or removes its publication. -/
theorem send_reply {Output : Type} (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (size : Output → Nat) (reply : Option Output) (before : State n E S) (result : Option Output × State n E S)
    (supported : result ∈ support ((fold service codec route (RegistrationNativePlatformGatedRecordInterface.closed
      (RegistrationNativePlatformOrdinaryGate.gate reserve size reply))).run before)) :
    result.1 = reply ∨ result.1 = none := by
  obtain ⟨after, reached⟩ := closed_support service codec route _ before result supported
  exact gate_reply reserve size reply before.1.1.1 (result.1, after) reached

/-- A pure terminal branch retains its literal reply under every private interpreter. -/
theorem pure_reply (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (value : X) (before : State n E S) (result : X × State n E S)
    (supported : result ∈ support ((fold service codec route (pure value)).run before)) : result.1 = value := by
  unfold fold at supported
  change result ∈ support (RegistrationNativePlatformGatedRecordFlat.join <$>
    CborRawRecordOriginFlatten.interpret service codec route (pure (value, before.1.1.1))
      before.1.1.2 before.1.2 before.2) at supported
  rw [CborRawRecordOriginFlatten.interpret_pure, map_pure, mem_support_pure_iff] at supported
  exact congrArg Prod.fst supported

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.closed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.closed_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.gate_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.gate_reply

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.send_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.send_reply

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.pure_reply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordPost.pure_reply

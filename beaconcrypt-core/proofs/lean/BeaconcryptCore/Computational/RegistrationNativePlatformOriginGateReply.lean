-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironment
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage
/-! The actual terminal source reserve can suppress a publication but cannot change its ciphertext or its handle. All platform/private effects and failures remain in the reached execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateReply
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhDeploymentInterface (Spec Entry)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {S E Failure A Reader Response : Type}

private theorem closed_support (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (work : StateT E ProbComp A)
    (before : RegistrationNativePlatformGatedRecordFlat.State n E S)
    (result : A × RegistrationNativePlatformGatedRecordFlat.State n E S)
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold service codec route
      (RegistrationNativePlatformGatedRecordInterface.closed work)).run before)) :
    (result.1,result.2.1.1.1) ∈ support (work.run before.1.1.1) := by
  rw [RegistrationNativePlatformOriginGateSource.closed_source,support_map] at supported
  obtain ⟨actual,called,rfl⟩ := supported
  have free : actual.1 ∈ support (simulateQ RegistrationNativePlatformOriginGateSource.coins (work.run before.1.1.1)) :=
    support_simulateQ_run'_subset service _ before.2 (by
      rw [StateT.run'_eq,support_map]
      exact ⟨actual,called,rfl⟩)
  exact PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ free

private theorem gate_reply (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (reply : Option RawCtxSourceSend.Encrypted)
    (before : RegistrationNativePlatformGatedRecordFlat.State n E S)
    (result : Option RawCtxSourceSend.Encrypted × RegistrationNativePlatformGatedRecordFlat.State n E S)
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold service codec route
      (RegistrationNativePlatformGatedRecordInterface.closed (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value => value.ciphertext.length) reply))).run before)) :
    result.1=none ∨ result.1=reply := by
  have original := closed_support service codec route _ before result supported
  cases reply with
  | none =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq] at original
      exact Or.inl original.1
  | some value =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate,StateT.run_bind,mem_support_bind_iff] at original
      obtain ⟨⟨allocation,platform⟩,_allocated,returned⟩ := original
      cases allocation with
      | Ok returnedUnit =>
          simp only [StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq] at returned
          exact Or.inr returned.1
      | Err error =>
          simp only [StateT.run_pure,mem_support_pure_iff,Prod.mk.injEq] at returned
          exact Or.inl returned.1

/-- Every successful gated native publication is the original source publication; a refused gate has no publication. This holds for an arbitrary physical interpreter and complete reached platform/private state. -/
theorem post_subset (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain) (reply : Spec.Range query)
    (before : RegistrationNativePlatformGatedRecordFlat.State n E S)
    (result : Spec.Range query × RegistrationNativePlatformGatedRecordFlat.State n E S)
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold service codec route
      (RegistrationNativePlatformGatedRecordInterface.post reserve query reply)).run before)) :
    (⟨.inl query,result.1⟩ : Entry).published=none ∨
      (⟨.inl query,result.1⟩ : Entry).published=(⟨.inl query,reply⟩ : Entry).published := by
  rcases query with coin | command
  · exact Or.inl rfl
  · cases command
    case serverSend keyId plaintext =>
      rcases gate_reply service codec route reserve reply before result supported with absent | same
      · exact Or.inl (by rw [absent];rfl)
      · exact Or.inr (congrArg (fun output => (⟨.inl (.inr (.serverSend keyId plaintext)),output⟩ : Entry).published) same)
    case beaconSend owner plaintext =>
      rcases gate_reply service codec route reserve reply before result supported with absent | same
      · exact Or.inl (by rw [absent];rfl)
      · exact Or.inr (congrArg (fun output => (⟨.inl (.inr (.beaconSend owner plaintext)),output⟩ : Entry).published) same)
    all_goals exact Or.inl rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateReply

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateReply.post_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateReply.post_subset

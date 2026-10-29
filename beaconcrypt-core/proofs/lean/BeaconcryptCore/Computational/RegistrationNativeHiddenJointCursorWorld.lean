-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorProtocol

/-! The actual cursor filter, Protocol schedule and arbitrary private service preserve cursor allocation for every World AST. This supplies the cursor component of the native joint allocation invariant without constraining the frontend or KEM provider. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhRecordLiftProtocol (Control)
open RegistrationNativeHiddenJointCursor (Domain)
open PqxdhServerAuthExperiment (Codec)
variable {n : Nat} {Secret Value Reader Response E : Type}

/-- A refused World query stutters, and a forwarded query uses its actual supported Protocol allocation transition. -/
theorem client_query_domain (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (shell : CborRecordWorldClient.Shell) (control : Control n)
    (result : ((WorldSpec n).Range query × CborRecordWorldClient.Shell) × Control n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftProtocol.handler decode route)
      ((CborRecordWorldClient.handler query).run shell)).run control))
    (valid : Domain shell control.owners.length) : Domain result.1.2 result.2.owners.length := by
  cases refused : CborRecordWorldClient.refusal query shell with
  | some reply =>
      have literal : (CborRecordWorldClient.handler query).run shell = pure (reply, shell) := by
        simp only [CborRecordWorldClient.handler, StateT.run, refused]
      rw [literal] at supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact valid
  | none =>
      have literal : (CborRecordWorldClient.handler query).run shell =
          (fun reply => (reply, CborRecordWorldClient.next query reply shell)) <$>
            ((WorldSpec n).query query : OracleComp (WorldSpec n) _) := by
        simp only [CborRecordWorldClient.handler, StateT.run, refused, CborRecordWorldClient.forward]
      rw [literal] at supported
      simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
      obtain ⟨native, reached, returned⟩ := supported
      cases returned
      exact RegistrationNativeHiddenJointCursorProtocol.query_domain decode route query control native reached shell valid

/-- Actual private service interpretation preserves the same complete cursor allocation receipt. -/
theorem query_domain (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : Secret)
    (result : (((WorldSpec n).Range query × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route
      ((WorldSpec n).query query : OracleComp (WorldSpec n) _) shell control secret))
    (valid : Domain shell control.owners.length) : Domain result.1.1.2 result.1.2.owners.length := by
  have actual : result.1 ∈ support ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      ((CborRecordWorldClient.handler query).run shell)).run control) := by
    apply OracleComp.support_simulateQ_run'_subset service _ secret
    rw [StateT.run'_eq, support_map]
    apply Set.mem_image_of_mem Prod.fst
    simpa only [CborRawRecordOriginFlatten.interpret, simulateQ_spec_query] using supported
  exact client_query_domain codec.frameRead route query shell control result.1 actual valid

/-- Every complete adaptive World continuation retains the actual cursor-domain invariant. -/
theorem program_domain (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : Secret)
    (result : ((Value × CborRecordWorldClient.Shell) × Control n) × Secret)
    (supported : result ∈ support (CborRawRecordOriginFlatten.interpret service codec route work shell control secret))
    (valid : Domain shell control.owners.length) : Domain result.1.1.2 result.1.2.owners.length := by
  induction work using OracleComp.inductionOn generalizing shell control secret result with
  | pure value =>
      rw [CborRawRecordOriginFlatten.interpret_pure] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      rw [CborRawRecordOriginFlatten.interpret_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact ih middle.1.1.1 middle.1.1.2 middle.1.2 middle.2 result continued
        (query_domain service codec route query shell control secret middle reached valid)

/-- Stateful lowering retains that cursor invariant while preserving the complete frontend and private poststates. -/
theorem lower_domain (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) Value)
    (before : RegistrationNativeHiddenEnvironmentWorld.State n E Secret)
    (result : Value × RegistrationNativeHiddenEnvironmentWorld.State n E Secret)
    (supported : result ∈ support ((RegistrationNativeHiddenEnvironmentWorld.lower service codec route work).run before))
    (valid : Domain before.1.1.2 before.1.2.owners.length) : Domain result.2.1.1.2 result.2.1.2.owners.length := by
  rw [RegistrationNativeHiddenEnvironmentWorld.lower_run, support_map] at supported
  obtain ⟨native, reached, returned⟩ := supported
  cases returned
  exact program_domain service codec route _ before.1.1.2 before.1.2 before.2 native reached valid

end BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.client_query_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.client_query_domain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.query_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.query_domain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.program_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.program_domain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.lower_domain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenJointCursorWorld.lower_domain

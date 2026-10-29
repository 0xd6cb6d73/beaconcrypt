-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordFlat

/-! The raw cursor's exact operation law is independent of the private service interpreter. It therefore applies to both the complete CTX world and the selected sticky-marker world, preserving actual replies and complete refusal states. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginService
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftProtocol (ServiceSpec Control)
open PqxdhServerAuthExperiment (Codec)
open PqxdhDeploymentInterface (Spec Handle)
variable {n : Nat} {Reader Response E S X : Type}

abbrev State (n : Nat) (E S : Type) := ((E × CborRecordWorldClient.Shell) × Control n) × S

def project (state : State n E S) : (E × Control n) × S :=
  (CborRawRecordFlat.clientProject state.1, state.2)

noncomputable def native (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT (State n E S) ProbComp) :=
  (service.mapStateTBase (CborRawRecordFlat.clientImpl env codec route)).flattenStateT

noncomputable def original (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT ((E × Control n) × S) ProbComp) :=
  (service.mapStateTBase (PqxdhRecordLiftFlat.clientImpl env codec route)).flattenStateT

/-- Flattening retains the entire cursor state and every private service reply through an arbitrary native program. -/
theorem program_run (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp Spec X) (state : State n E S) :
    (simulateQ (native service env codec route) work).run state =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ service ((simulateQ (CborRawRecordFlat.clientImpl env codec route) work).run state.1)).run state.2 := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simp only [Functor.map_map, Prod.mk.eta, id_map', native]

/-- The complete guarded native call is an actual Protocol schedule over the original environment and cursor effects. -/
theorem source_run (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : Spec.Domain) (state : State n E S) :
    (native service env codec route query).run state =
      (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
        (simulateQ service ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
          ((simulateQ CborRecordWorldClient.handler ((PqxdhRecordLiftInterface.native env query).run state.1.1.1)).run
            state.1.1.2)).run state.1.2)).run state.2 := by
  simp only [native, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    CborRawRecordFlat.clientImpl_run, simulateQ_map, StateT.run_map, Functor.map_map]

/-- Every actual guarded native call preserves safe source control and its forward transition relation. -/
theorem native_step (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : Spec.Domain) (state : State n E S) (safe : PqxdhRecordLiftProtocolHistory.Safe state.1.2)
    (result : Spec.Range query × State n E S)
    (supported : result ∈ support ((native service env codec route query).run state)) :
    PqxdhRecordLiftProtocolHistory.Step state.1.2 result.2.1.2 := by
  rw [source_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordLiftProtocolHistory.interpreted_schedule service codec.frameRead route _ state.1.2 safe state.2 inner reached

/-- The actual cursor cannot change an installed handle's caller-known classification. -/
theorem native_known (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (handle : Handle) (query : Spec.Domain) (state : State n E S)
    (known : PqxdhRecordLiftFlat.KnownAt state.1.2 handle)
    (result : Spec.Range query × State n E S)
    (supported : result ∈ support ((native service env codec route query).run state)) :
    PqxdhRecordLiftFlat.KnownAt result.2.1.2 handle := by
  rw [source_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordLiftFlat.support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    (fun control => PqxdhRecordLiftFlat.KnownAt control handle)
    (PqxdhRecordLiftFlat.handler_known codec.frameRead route handle) _ state.1.2 known inner.1
      (PqxdhRecordLiftFlat.support_run_fst _ _ _ inner reached)

/-- Dropping only the public cursor commutes with every actual non-send operation, under any private interpreter. -/
theorem nonrecord_project (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : Spec.Domain) (state : State n E S)
    (free : ¬PqxdhRecordLiftBudget.NativeRecord .send query) :
    Prod.map id project <$> (native service env codec route query).run state =
      (original service env codec route query).run (project state) := by
  have observed := congrArg (fun work =>
    (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ service work).run state.2)
    (CborRawRecordFlat.clientImpl_project_nonrecord env codec route query state.1 free)
  simpa only [native, original, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    simulateQ_map, StateT.run_map, Functor.map_map, project, Prod.map, id_eq] using observed

/-- A send projects to its exact original private execution or a complete refusal stutter before any private callback. -/
theorem send_project (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (handle : Handle) (plaintext : Pqxdh.Bytes) (state : State n E S) :
    Prod.map id project <$> (simulateQ (native service env codec route)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run state =
      match CborRawRecordFlat.sendRefusal (n := n) handle plaintext state.1.1.2 with
      | some reply => pure (reply, project state)
      | none => (simulateQ (original service env codec route)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run (project state) := by
  have observed := congrArg (fun work =>
    (fun result => (result.1.1, (CborRawRecordFlat.clientProject result.1.2, result.2))) <$>
      (simulateQ service work).run state.2)
    (CborRawRecordFlat.clientImpl_send env codec route handle plaintext state.1)
  cases refused : CborRawRecordFlat.sendRefusal (n := n) handle plaintext state.1.1.2
  · rw [refused] at observed
    have originalRun :
        (simulateQ (original service env codec route) (PqxdhDeploymentSecrecy.send handle plaintext)).run (project state) =
          (fun result => (result.1.1, (result.1.2, result.2))) <$>
            (simulateQ service ((simulateQ (PqxdhRecordLiftFlat.clientImpl env codec route)
              (PqxdhDeploymentSecrecy.send handle plaintext)).run (CborRawRecordFlat.clientProject state.1))).run state.2 := by
      rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
      simp only [Functor.map_map, Prod.mk.eta, id_map', original, project]
    rw [program_run]
    simp only
    rw [originalRun]
    simpa only [original, simulateQ_map, StateT.run_map, Functor.map_map, CborRawRecordFlat.clientWithShell,
      CborRawRecordFlat.clientProject, project, Prod.map, id_eq, refused] using observed
  · rw [refused] at observed
    rw [program_run]
    simpa only [simulateQ_pure, StateT.run_pure, map_pure, Functor.map_map, project, Prod.map, id_eq, refused] using observed

/-- Every literal refusal of an established send has the ordinary missing-ciphertext reply. -/
theorem refused_none (handle : Handle) (plaintext : Pqxdh.Bytes) (shell : CborRecordWorldClient.Shell)
    (reply : Option RawCtxSourceSend.Encrypted)
    (refused : CborRawRecordFlat.sendRefusal (n := n) handle plaintext shell = some reply) : reply = none := by
  cases handle <;> simp only [CborRawRecordFlat.sendRefusal, CborRawRecordFlat.sendQuery,
    CborRecordWorldClient.refusal] at refused
  all_goals repeat' split at refused
  all_goals cases refused
  all_goals rfl

/-- Every actual guarded operation is supported by the identical original operation, or leaves its entire projected source state unchanged. -/
theorem support_or_stutter (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : Spec.Domain) (state : State n E S) (result : Spec.Range query × State n E S)
    (supported : result ∈ support ((native service env codec route query).run state)) :
    (result.1, project result.2) ∈ support ((original service env codec route query).run (project state)) ∨
      project result.2 = project state := by
  by_cases free : ¬PqxdhRecordLiftBudget.NativeRecord .send query
  · left
    rw [← nonrecord_project service env codec route query state free, support_map]
    exact ⟨result, supported, rfl⟩
  · have send_case (handle : Handle) (plaintext : Pqxdh.Bytes)
        (result : Option RawCtxSourceSend.Encrypted × State n E S)
        (supported : result ∈ support ((simulateQ (native service env codec route)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run state)) :
        (result.1, project result.2) ∈ support ((simulateQ (original service env codec route)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run (project state)) ∨ project result.2 = project state := by
      have mapped : (result.1, project result.2) ∈ support (Prod.map id project <$>
          (simulateQ (native service env codec route) (PqxdhDeploymentSecrecy.send handle plaintext)).run state) :=
        by
          rw [support_map]
          exact ⟨result, supported, rfl⟩
      rw [send_project] at mapped
      cases refused : CborRawRecordFlat.sendRefusal (n := n) handle plaintext state.1.1.2
      · simp only [refused] at mapped
        exact Or.inl mapped
      · simp only [refused, mem_support_pure_iff, Prod.mk.injEq] at mapped
        exact Or.inr mapped.2
    rcases query with coin | command
    · exact False.elim (free (by simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]))
    · cases command
      case serverSend keyId plaintext =>
        simpa only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] using send_case (.peer keyId) plaintext result (by simpa only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] using supported)
      case beaconSend owner plaintext =>
        simpa only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] using send_case (.owner owner) plaintext result (by simpa only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] using supported)
      all_goals exact False.elim (free (by simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]))

end BeaconcryptCore.Computational.CborRawRecordOriginService

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.program_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.program_run
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.nonrecord_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.nonrecord_project
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.send_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.send_project
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.refused_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.refused_none

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.source_run
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.native_step
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.native_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.native_known

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginService.support_or_stutter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginService.support_or_stutter

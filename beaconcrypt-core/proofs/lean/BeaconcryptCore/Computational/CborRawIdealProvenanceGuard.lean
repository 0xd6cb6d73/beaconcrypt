-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldSimulation
import BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins

/-! Provenance instrumentation of the actual early-admission World. Refusing an oversized established send leaves the complete World and its origin annotation unchanged. The cursor client stays below the original ledger, so secret draws and refusal entries retain their original order. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CborRawIdealProvenanceGuard
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open PqxdhRecordLiftOrigins (Origins)
open CborRecordWorldCursor (worldShell)
variable {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The same early send guard, with provenance updated only by a forwarded administrative request. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (WorldSpec n) (StateT (PqxdhRecordLiftOrigins.State n) ProbComp) := fun query state =>
  match CborRecordWorldClient.refusal query (worldShell state.1) with
  | some reply => pure (reply, state)
  | none => (PqxdhRecordLiftOrigins.handler setup codec route query).run state

/-- Erasing provenance gives the actual guarded World on every request, including refusal. -/
theorem handler_erase (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : PqxdhRecordLiftOrigins.State n) :
    Prod.map id Prod.fst <$> (handler setup codec route query).run state =
      (CborRecordWorldSimulation.guarded setup codec route query).run state.1 := by
  cases refused : CborRecordWorldClient.refusal query (worldShell state.1) <;>
    simp only [handler, CborRecordWorldSimulation.guarded, StateT.run, refused, map_pure]
  · exact PqxdhRecordLiftOrigins.handler_erase setup codec route query state
  · rfl

/-- The complete instrumented execution erases to the actual guarded World. -/
theorem run_erase {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Result)
    (state : PqxdhRecordLiftOrigins.State n) :
    Prod.map id Prod.fst <$> (simulateQ (handler setup codec route) work).run state =
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (fun query current => handler_erase setup codec route query current) work state

/-- Registration effects use the original annotated shared interpreter. -/
theorem effects (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    (handler setup codec route (n := n)) ∘ₛ effectLift =
      PqxdhDeploymentIdealOrigins.aEffects setup codec route := by
  funext query
  simp only [QueryImpl.apply_compose, effectLift, simulateQ_spec_query]
  rfl

private theorem map_state_apply {Input Output : Type} (f : Input → Output)
    (work : StateT (PqxdhRecordLiftOrigins.State n) ProbComp Input)
    (state : PqxdhRecordLiftOrigins.State n) :
    (f <$> work) state = Prod.map f id <$> work state :=
  bind_pure_comp (Prod.map f id) (work state)

/-- The public cursor client has exactly this annotated guarded execution; the annotation never changes its admission decision. -/
theorem client_simulation {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Result)
    (state : PqxdhRecordLiftOrigins.State n) :
    (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
      (CborRecordWorldClient.client work (worldShell state.1))).run state =
      (simulateQ (handler setup codec route) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [CborRecordWorldClient.client, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [CborRecordWorldClient.client, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      cases refusal : CborRecordWorldClient.refusal query (worldShell state.1) with
      | some reply =>
          simp only [CborRecordWorldClient.handler, StateT.run, refusal, pure_bind,
            simulateQ_map, handler]
          simpa only [CborRecordWorldClient.client, simulateQ_map, StateT.run, map_state_apply] using ih reply state
      | none =>
          simp only [CborRecordWorldClient.handler, StateT.run, refusal, CborRecordWorldClient.forward,
            bind_map_left, simulateQ_map, simulateQ_bind, simulateQ_spec_query, handler]
          simp only [map_state_apply]
          change Prod.map Prod.fst id <$> (do
            let result ← (PqxdhRecordLiftOrigins.handler setup codec route query).run state
            (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
              ((simulateQ CborRecordWorldClient.handler (next result.1)).run
                (CborRecordWorldClient.next query result.1 (worldShell state.1)))).run result.2) = _
          rw [map_bind]
          apply bind_congr_of_forall_mem_support
          intro result reached
          have erased : (result.1, result.2.1) ∈ support
              ((PqxdhRecordLiftWorld.handler setup codec route query).run state.1) := by
            rw [← PqxdhRecordLiftOrigins.handler_erase setup codec route query state, support_map]
            exact ⟨result, reached, rfl⟩
          rw [← CborRecordWorldSimulation.handler_shell setup codec route query state.1 _ erased]
          simpa only [CborRecordWorldClient.client, simulateQ_map, StateT.run, map_state_apply] using ih result.1 result.2

/-- The guarded annotation is an instrumentation of the full raw cursor client, for arbitrary result types and complete private World state. -/
theorem client_erase {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Result)
    (state : PqxdhRecordLiftOrigins.State n) :
    Prod.map id Prod.fst <$> (simulateQ (handler setup codec route) work).run state =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (CborRecordWorldClient.client work (worldShell state.1))).run state.1 := by
  rw [run_erase, CborRecordWorldSimulation.client_simulation]

end BeaconcryptCore.Computational.CborRawIdealProvenanceGuard

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.handler_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.handler_erase

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.run_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.run_erase

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.effects

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.client_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.client_simulation

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.client_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceGuard.client_erase

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldCursorAdmin
import BeaconcryptCore.Computational.CborRecordWorldCursorStep

/-!
The public cursor filter is coupled to the actual instrumented World, before every record callback. The complete output and source state are retained. Applying it to an entire environment program therefore keeps secret test/fresh sampling and ledger order unchanged.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRecordWorldSimulation
open PqxdhRecordLiftInterface
open PqxdhServerAuthExperiment (Setup Codec)
open CborRecordWorldCursor (worldShell)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem map_state_apply {Input Output : Type} (f : Input → Output)
    (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Input) (state : PqxdhRecordLiftWorld.State n) :
    (f <$> work) state = Prod.map f id <$> work state :=
  bind_pure_comp (Prod.map f id) (work state)

/-- Every supported actual World reply determines precisely the public cursor transition. -/
theorem handler_shell (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : PqxdhRecordLiftWorld.State n) (result : (WorldSpec n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.handler setup codec route query).run state)) :
    worldShell result.2 = CborRecordWorldClient.next query result.1 (worldShell state) := by
  cases query with
  | inl created => exact CborRecordWorldCursorAdmin.initialize_shell created state result supported
  | inr query =>
    cases query with
    | inl effect => exact CborRecordWorldCursorAdmin.effects_shell effect state result supported
    | inr record =>
      cases record with
      | inl server =>
        cases server with
        | inl pair => exact CborRecordWorldCursorStep.world_server_cursor setup codec route (.inl pair) state result supported
        | inr raw => exact CborRecordWorldCursorStep.world_server_cursor setup codec route (.inr raw) state result supported
      | inr beacon =>
        rcases beacon with ⟨owner, query⟩
        cases query with
        | inl plaintext => exact CborRecordWorldCursorStep.world_beacon_cursor setup codec owner (.inl plaintext) state result supported
        | inr raw => exact CborRecordWorldCursorStep.world_beacon_cursor setup codec owner (.inr raw) state result supported

/-- Size refusal precedes the actual record program and leaves its complete state untouched. -/
noncomputable def guarded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun query state => match CborRecordWorldClient.refusal query (worldShell state) with
  | some reply => pure (reply, state)
  | none => (PqxdhRecordLiftWorld.handler setup codec route query).run state

/-- The public filter and the actual early-admission World have exactly the same complete execution. -/
theorem client_simulation {Result : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Result)
    (state : PqxdhRecordLiftWorld.State n) :
    (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
      (CborRecordWorldClient.client work (worldShell state))).run state =
      (simulateQ (guarded setup codec route) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [CborRecordWorldClient.client, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [CborRecordWorldClient.client, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    cases refusal : CborRecordWorldClient.refusal query (worldShell state) with
    | some reply =>
      simp only [CborRecordWorldClient.handler, StateT.run, refusal, pure_bind,
        simulateQ_map, guarded]
      simpa only [CborRecordWorldClient.client, simulateQ_map, StateT.run, map_state_apply] using ih reply state
    | none =>
      simp only [CborRecordWorldClient.handler, StateT.run, refusal, CborRecordWorldClient.forward,
        bind_map_left, simulateQ_map, simulateQ_bind, simulateQ_spec_query, guarded]
      simp only [map_state_apply]
      change Prod.map Prod.fst id <$> (do
        let result ← (PqxdhRecordLiftWorld.handler setup codec route query).run state
        (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
          ((simulateQ CborRecordWorldClient.handler (next result.1)).run
            (CborRecordWorldClient.next query result.1 (worldShell state)))).run result.2) = _
      rw [map_bind]
      apply bind_congr_of_forall_mem_support
      intro result reached
      rw [← handler_shell setup codec route query state result reached]
      simpa only [CborRecordWorldClient.client, simulateQ_map, StateT.run, map_state_apply] using ih result.1 result.2

/-- The exact private Protocol interpreter realizes the same admitted open program, while the cursor is already determined by its Control projection. -/
theorem initial_protocol_simulation {Result : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Result) :
    (Prod.map id PqxdhRecordLiftWorldCompiler.world ∘ PqxdhRecordLiftProtocol.rejoin) <$>
      PqxdhRecordLiftProtocol.execute (PqxdhRecordLiftWorldCompiler.realPolicy setup codec)
        setup codec route (CborRecordWorldClient.client work)
        PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftProtocol.initialPrivate =
      (simulateQ (guarded setup codec route) work).run PqxdhRecordLiftWorld.initial :=
  (PqxdhRecordLiftProtocol.initial_schedule_source setup codec route (CborRecordWorldClient.client work)).trans
    (client_simulation setup codec route work PqxdhRecordLiftWorld.initial)

end BeaconcryptCore.Computational.CborRecordWorldSimulation

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldSimulation.handler_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldSimulation.handler_shell

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldSimulation.client_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldSimulation.client_simulation

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldSimulation.initial_protocol_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldSimulation.initial_protocol_simulation

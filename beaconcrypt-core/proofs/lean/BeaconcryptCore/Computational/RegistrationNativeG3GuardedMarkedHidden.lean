-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedKnown
import BeaconcryptCore.Computational.RegistrationNativeSeedDelayAccounting
import BeaconcryptCore.Computational.RegistrationNativeSeedDelay

/-! The marked hidden World is the actual guarded World started with the same full private seed table, after only seed/uniform accounting is observed away. Persistence of the actual cache derives the full-cache invariant from that literal initial state. Repeated-role refusal remains actual; neither unused roles nor a simulation equation is a caller premise. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeG3AuditedWorld (Spec Seeds seeded)
open RegistrationNativeG3GuardedWorld (step marked)
open RegistrationNativeSeedDelayCore (mask)
open RegistrationNativeSeedDelay (view)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

def Full (seeds : Seeds n) (before : State n) : Prop := ∀ slot, before.seeds.1 slot = some (seeds slot)

private theorem cache_full (seeds : Seeds n) (before : State n) (full : Full seeds before) :
    before.seeds.1 = ⟨fun slot => some (seeds slot)⟩ := QueryCache.ext full

private theorem guarded_full (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (WorldSpec n).Domain)
    (before : State n) (full : Full seeds before) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((CborRecordWorldSimulation.guarded setup codec route query).run before)) : Full seeds result.2 := by
  simp only [CborRecordWorldSimulation.guarded, StateT.run] at supported
  cases refusal : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply =>
      simp only [refusal, mem_support_pure_iff] at supported
      cases supported
      exact full
  | none =>
      simp only [refusal] at supported
      have persistent := (PqxdhRecordLiftWorld.handler_persists setup codec route query before result supported).1
      intro slot
      exact persistent (full slot)

/-- The exact actual guarded query retains every preassigned seed by the already proved persistent-cache source invariant. -/
theorem full_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain)
    (before : State n) (full : Full seeds before) (result : (Spec n).Range query × State n)
    (supported : result ∈ support ((step setup codec route seeds false query).run before)) : Full seeds result.2 := by
  cases query with
  | ordinary query allowed => exact guarded_full setup codec route seeds query before full result supported
  | server keyId binding slot =>
      apply guarded_full setup codec route seeds
        (.inr (.inl (.inr (.installServer keyId binding (.hidden slot))))) before full result
      simpa only [step, RegistrationNativeG3AuditedWorld.step, Bool.false_eq_true, ite_false,
        CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler, StateT.run] using supported
  | beacon owner shell slot =>
      apply guarded_full setup codec route seeds
        (.inr (.inl (.inr (.installBeacon owner shell (.hidden slot))))) before full result
      simpa only [step, RegistrationNativeG3AuditedWorld.step, Bool.false_eq_true, ite_false,
        CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler, StateT.run] using supported

private theorem guarded_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run before =
      Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run (mask before) := by
  have shell : CborRecordWorldCursor.worldShell (mask before) = CborRecordWorldCursor.worldShell before := rfl
  simp only [CborRecordWorldSimulation.guarded, StateT.run, shell]
  cases refusal : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply => simp only [map_pure, Prod.map_def, id_eq]; rfl
  | none => exact RegistrationNativeSeedDelayAccounting.handler_input setup codec route query before

private noncomputable def accounted (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) : QueryImpl (WorldSpec n) (StateT (State n) ProbComp) :=
  fun query before => Prod.map id mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run before

/-- Complete actual guarded execution never exposes its initial uniform or logical-seed accounting; semantic inputs and every returned client value remain literal. -/
theorem actual_value_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.fst <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before =
      Prod.fst <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run (mask before) := by
  have first := map_run_simulateQ_eq_of_query_map_eq
    (CborRecordWorldSimulation.guarded setup codec route) (accounted setup codec route) mask
    (guarded_input setup codec route) work before
  have second := map_run_simulateQ_eq_of_query_map_eq
    (CborRecordWorldSimulation.guarded setup codec route) (accounted setup codec route) mask
    (guarded_input setup codec route) work (mask before)
  rw [RegistrationNativeSeedDelayCore.mask_idempotent] at second
  have observed := congrArg (fun distribution => Prod.fst <$> distribution) (first.trans second.symm)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using observed

private theorem guarded_view_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id view <$> (CborRecordWorldSimulation.guarded setup codec route query).run before =
      Prod.map id view <$> (CborRecordWorldSimulation.guarded setup codec route query).run (mask before) := by
  have accounting := congrArg (fun distribution => Prod.map id view <$> distribution)
    (guarded_input setup codec route query before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, view, mask] using accounting

private theorem step_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain) (before : State n) :
    Prod.map id view <$> (step setup codec route seeds false query).run before =
      Prod.map id view <$> (step setup codec route seeds false query).run (mask before) := by
  cases query with
  | ordinary query allowed => exact guarded_view_input setup codec route query before
  | server keyId binding slot =>
      simpa only [step, RegistrationNativeG3AuditedWorld.step, Bool.false_eq_true, ite_false,
        CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler, StateT.run] using
        guarded_view_input setup codec route (.inr (.inl (.inr (.installServer keyId binding (.hidden slot))))) before
  | beacon owner shell slot =>
      simpa only [step, RegistrationNativeG3AuditedWorld.step, Bool.false_eq_true, ite_false,
        CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler, StateT.run] using
        guarded_view_input setup codec route (.inr (.inl (.inr (.installBeacon owner shell (.hidden slot))))) before

noncomputable def normalized (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) : QueryImpl (Spec n) (StateT (State n) ProbComp) :=
  fun query before => Prod.map id view <$> (step setup codec route seeds false query).run (seeded seeds before)

private theorem full_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain)
    (before : State n) (full : Full seeds before) :
    Prod.map id view <$> (step setup codec route seeds false query).run before =
      (normalized setup codec route seeds query).run (view before) := by
  rw [step_input]
  have same : mask before = seeded seeds (view before) := by
    simp only [mask, view, seeded, cache_full seeds before full]
  rw [same]
  rfl

private theorem marked_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain)
    (before : State n × Bool) :
    Prod.map id (fun reached => view reached.1) <$> (marked setup codec route seeds false query).run before =
      (normalized setup codec route seeds query).run (view before.1) := by
  have accounting := step_input setup codec route seeds query (seeded seeds before.1)
  simpa only [marked, normalized, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    RegistrationNativeG3AuditedInstall.view, view, seeded, mask] using accounting

/-- The marked hidden game and actual guarded hidden execution retain precisely the same complete client output from the same preassigned private seed table. -/
theorem value_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (Spec n) Value) (before : State n) (flag : Bool) :
    Prod.fst <$> (simulateQ (marked setup codec route seeds false) work).run (before, flag) =
      Prod.fst <$> (simulateQ (step setup codec route seeds false) work).run (seeded seeds before) := by
  have first := map_run_simulateQ_eq_of_query_map_eq _ _ (fun reached => view reached.1)
    (marked_project setup codec route seeds) work (before, flag)
  have second := map_run_simulateQ_eq_of_query_map_eq_inv'
    (step setup codec route seeds false) (normalized setup codec route seeds) (Full seeds) view
    (fun query current full result supported => full_keeps setup codec route seeds query current full result supported)
    (full_project setup codec route seeds) work (seeded seeds before) (fun _ => rfl)
  have same : view (seeded seeds before) = view before := rfl
  rw [same] at second
  have observed := congrArg (fun distribution => Prod.fst <$> distribution) (first.trans second.symm)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using observed

/-- The literal actual guarded World execution started with the private complete table is the hidden marked Tag execution with only its audit state erased. -/
theorem actual_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) Value) (before : State n) :
    Prod.fst <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run (seeded seeds before) =
      Prod.fst <$> (simulateQ (marked setup codec route seeds false)
        (simulateQ RegistrationNativeG3Materialize.materialize work)).run (before, false) := by
  rw [← RegistrationNativeG3GuardedWorld.program_source setup codec route seeds work]
  exact (value_source setup codec route seeds _ before false).symm

end BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.full_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.full_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.actual_value_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.actual_value_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.value_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.value_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.actual_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden.actual_source

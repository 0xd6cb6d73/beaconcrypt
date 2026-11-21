-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicWorldObservation
/-! The guarded known/hidden coupling retains terminal CTX-cache, produced-frame and raw-counter observations, in addition to the original client result. Private seed/use bookkeeping is erased only after the actual marked execution. The sole change is still charged to that same known-side repeated-role event. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeG3AuditedWorld (Spec Seeds seeded)
open RegistrationNativeG3GuardedWorld (step marked)
open RegistrationNativePlatformPublicWorldObservation (RecordView recordView)
open RegistrationNativeHiddenWorldInstall (view)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}

private theorem view_record (before : State n) : recordView (view before) = recordView before := rfl

/-- Forgetting the private known-side audit preserves the literal terminal record observation as well as the public result. -/
theorem known_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) A) (before : State n) :
    (fun result => (result.1, recordView result.2)) <$>
      (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds) work).run before =
      (fun result => (result.1, recordView result.2.1)) <$>
        (simulateQ (marked setup codec route seeds true)
          (simulateQ RegistrationNativeG3Materialize.materialize work)).run (before, false) := by
  have actual := RegistrationNativeG3GuardedMaterializedWorldProgram.program_project setup codec route seeds work before
  have audited := RegistrationNativeG3GuardedMarkedKnown.program_source setup codec route seeds
    (simulateQ RegistrationNativeG3Materialize.materialize work) (before, false)
  have unmarked := map_run_simulateQ_eq_of_query_map_eq
    (step setup codec route seeds true) (RegistrationNativeG3GuardedMarkedKnown.normalized setup codec route seeds) view
    (RegistrationNativeG3GuardedMaterializedWorldProgram.step_input setup codec route seeds)
    (simulateQ RegistrationNativeG3Materialize.materialize work) before
  have first := congrArg (Functor.map (fun result => (result.1, recordView result.2))) actual
  have second := congrArg (Functor.map (fun result => (result.1, recordView result.2)))
    (unmarked.trans audited.symm)
  simp only [Functor.map_map, Prod.map_def, id_eq, view_record,
    RegistrationNativeG3GuardedMarkedKnown.forget] at first second
  exact first.trans second
private theorem hidden_record (before : State n) :
    recordView (RegistrationNativeSeedDelay.view before) = recordView before := rfl

private theorem hidden_cache_full (seeds : Seeds n) (before : State n)
    (full : RegistrationNativeG3GuardedMarkedHidden.Full seeds before) :
    before.seeds.1 = ⟨fun slot => some (seeds slot)⟩ := QueryCache.ext full

private theorem hidden_guarded_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id RegistrationNativeSeedDelayCore.mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run before =
      Prod.map id RegistrationNativeSeedDelayCore.mask <$> (CborRecordWorldSimulation.guarded setup codec route query).run (RegistrationNativeSeedDelayCore.mask before) := by
  have shell : CborRecordWorldCursor.worldShell (RegistrationNativeSeedDelayCore.mask before) = CborRecordWorldCursor.worldShell before := rfl
  simp only [CborRecordWorldSimulation.guarded, StateT.run, shell]
  cases refusal : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | some reply => simp only [map_pure, Prod.map_def, id_eq]; rfl
  | none => exact RegistrationNativeSeedDelayAccounting.handler_input setup codec route query before


private theorem hidden_guarded_view_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain) (before : State n) :
    Prod.map id RegistrationNativeSeedDelay.view <$> (CborRecordWorldSimulation.guarded setup codec route query).run before =
      Prod.map id RegistrationNativeSeedDelay.view <$> (CborRecordWorldSimulation.guarded setup codec route query).run (RegistrationNativeSeedDelayCore.mask before) := by
  have accounting := congrArg (fun distribution => Prod.map id RegistrationNativeSeedDelay.view <$> distribution)
    (hidden_guarded_input setup codec route query before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeSeedDelay.view, RegistrationNativeSeedDelayCore.mask] using accounting

private theorem hidden_step_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain) (before : State n) :
    Prod.map id RegistrationNativeSeedDelay.view <$> (step setup codec route seeds false query).run before =
      Prod.map id RegistrationNativeSeedDelay.view <$> (step setup codec route seeds false query).run (RegistrationNativeSeedDelayCore.mask before) := by
  cases query with
  | ordinary query allowed => exact hidden_guarded_view_input setup codec route query before
  | server keyId binding slot =>
      simpa only [step, RegistrationNativeG3AuditedWorld.step, Bool.false_eq_true, ite_false,
        CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler, StateT.run] using
        hidden_guarded_view_input setup codec route (.inr (.inl (.inr (.installServer keyId binding (.hidden slot))))) before
  | beacon owner shell slot =>
      simpa only [step, RegistrationNativeG3AuditedWorld.step, Bool.false_eq_true, ite_false,
        CborRecordWorldSimulation.guarded, CborRecordWorldClient.refusal, PqxdhRecordLiftWorld.handler, StateT.run] using
        hidden_guarded_view_input setup codec route (.inr (.inl (.inr (.installBeacon owner shell (.hidden slot))))) before


private theorem hidden_full_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain)
    (before : State n) (full : RegistrationNativeG3GuardedMarkedHidden.Full seeds before) :
    Prod.map id RegistrationNativeSeedDelay.view <$> (step setup codec route seeds false query).run before =
      (RegistrationNativeG3GuardedMarkedHidden.normalized setup codec route seeds query).run (RegistrationNativeSeedDelay.view before) := by
  rw [hidden_step_input]
  have same : RegistrationNativeSeedDelayCore.mask before = seeded seeds (RegistrationNativeSeedDelay.view before) := by
    simp only [RegistrationNativeSeedDelayCore.mask, RegistrationNativeSeedDelay.view, seeded, hidden_cache_full seeds before full]
  rw [same]
  rfl

private theorem hidden_marked_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n) (query : (Spec n).Domain)
    (before : State n × Bool) :
    Prod.map id (fun reached => RegistrationNativeSeedDelay.view reached.1) <$> (marked setup codec route seeds false query).run before =
      (RegistrationNativeG3GuardedMarkedHidden.normalized setup codec route seeds query).run (RegistrationNativeSeedDelay.view before.1) := by
  have accounting := hidden_step_input setup codec route seeds query (seeded seeds before.1)
  simpa only [marked, RegistrationNativeG3GuardedMarkedHidden.normalized, StateT.run, Functor.map_map, Prod.map_def, id_eq,
    RegistrationNativeG3AuditedInstall.view, RegistrationNativeSeedDelay.view, seeded, RegistrationNativeSeedDelayCore.mask] using accounting

/-- Preassigned private seed cells preserve the complete literal hidden record observation through the marked same-run source execution. -/
theorem hidden_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) A) (before : State n) :
    (fun result => (result.1, recordView result.2)) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run (seeded seeds before) =
      (fun result => (result.1, recordView result.2.1)) <$>
        (simulateQ (marked setup codec route seeds false)
          (simulateQ RegistrationNativeG3Materialize.materialize work)).run (before, false) := by
  rw [← RegistrationNativeG3GuardedWorld.program_source setup codec route seeds work]
  have first := map_run_simulateQ_eq_of_query_map_eq _ _ (fun reached => RegistrationNativeSeedDelay.view reached.1)
    (hidden_marked_project setup codec route seeds)
    (simulateQ RegistrationNativeG3Materialize.materialize work) (before, false)
  have second := map_run_simulateQ_eq_of_query_map_eq_inv'
    (step setup codec route seeds false) (RegistrationNativeG3GuardedMarkedHidden.normalized setup codec route seeds)
    (RegistrationNativeG3GuardedMarkedHidden.Full seeds) RegistrationNativeSeedDelay.view
    (fun query current full result supported => RegistrationNativeG3GuardedMarkedHidden.full_keeps setup codec route seeds query current full result supported)
    (hidden_full_project setup codec route seeds)
    (simulateQ RegistrationNativeG3Materialize.materialize work) (seeded seeds before) (fun _ => rfl)
  have same : RegistrationNativeSeedDelay.view (seeded seeds before) = RegistrationNativeSeedDelay.view before := rfl
  rw [same] at second
  have observed := congrArg (Functor.map (fun result => (result.1, recordView result.2))) (first.trans second.symm)
  simpa only [Functor.map_map, Prod.map_def, id_eq, hidden_record] using observed.symm
noncomputable def known (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) A) (before : State n) : ProbComp (A × RecordView) :=
  (fun result => (result.1, recordView result.2)) <$>
    (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds) work).run before

noncomputable def hidden (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) A) (before : State n) : ProbComp (A × RecordView) :=
  (fun result => (result.1, recordView result.2)) <$>
    (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before

/-- Terminal record/cache observations incur precisely the same fixed-table repeated-role loss as the original public result. -/
theorem fixed_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) A) (before : State n) :
    discreteDistance (known setup codec route seeds work before) (hidden setup codec route work (seeded seeds before)) ≤
      (Pr{let result ← RegistrationNativeG3GuardedCoupling.audit setup codec route seeds work before}[result.2.2 = true]).toReal := by
  unfold known hidden
  rw [known_source, hidden_source]
  have mapped := discreteDistance_map_le (fun result : A × (State n × Bool) => (result.1, recordView result.2.1))
    ((simulateQ (marked setup codec route seeds true) (simulateQ RegistrationNativeG3Materialize.materialize work)).run (before, false))
    ((simulateQ (marked setup codec route seeds false) (simulateQ RegistrationNativeG3Materialize.materialize work)).run (before, false))
  exact mapped.trans (RegistrationNativeG3GuardedWorld.distance_le_repeat setup codec route seeds
    (simulateQ RegistrationNativeG3Materialize.materialize work) before)
end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling.known_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling.hidden_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling.hidden_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling.fixed_bound

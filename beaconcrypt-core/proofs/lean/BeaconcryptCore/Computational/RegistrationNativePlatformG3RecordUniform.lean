-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordCoupling
/-! Uniform completion removes the full private seed table while retaining the exact terminal cache, produced frames and raw counters. The known/hidden change is charged to the original same-run repeated-role audit event. Actual resource accounting is handled separately from the named security observation. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeG3AuditedWorld (Seeds seeded)
open RegistrationNativeSeedDelayCore (lens mask)
open RegistrationNativePlatformPublicWorldObservation (RecordView recordView)
open RegistrationNativePlatformG3RecordCoupling (known hidden)
open RegistrationNativeG3GuardedCoupling (overlay audit)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}

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

private theorem mask_record (before : State n) : recordView (mask before) = recordView before := rfl
private theorem view_record (before : State n) : recordView (RegistrationNativeSeedDelay.view before) = recordView before := rfl

private theorem hidden_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) A) (before : State n) :
    hidden setup codec route work before = hidden setup codec route work (mask before) := by
  have first := map_run_simulateQ_eq_of_query_map_eq
    (CborRecordWorldSimulation.guarded setup codec route) (accounted setup codec route) mask
    (guarded_input setup codec route) work before
  have second := map_run_simulateQ_eq_of_query_map_eq
    (CborRecordWorldSimulation.guarded setup codec route) (accounted setup codec route) mask
    (guarded_input setup codec route) work (mask before)
  rw [RegistrationNativeSeedDelayCore.mask_idempotent] at second
  have observed := congrArg (Functor.map (fun result => (result.1, recordView result.2))) (first.trans second.symm)
  simpa only [RegistrationNativePlatformG3RecordCoupling.hidden, Functor.map_map, Prod.map_def, id_eq, mask_record] using observed

private theorem preassigned (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) A) (before : State n) :
    hidden setup codec route work (seeded seeds before) =
      hidden setup codec route work (lens.set before ⟨fun slot => some (seeds slot)⟩) := by
  rw [hidden_input setup codec route work (seeded seeds before),
    hidden_input setup codec route work (lens.set before ⟨fun slot => some (seeds slot)⟩)]
  rfl

/-- The literal hidden terminal record observation has the same distribution under lazy and completed uniform private tables. -/
theorem hidden_uniform (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) A) (before : State n) :
    (do let seeds ← $ᵗ (Seeds n)
        hidden setup codec route work (seeded (overlay before seeds) before)) =ᵈ
      hidden setup codec route work before := by
  let : MeasurableSpace (A × RecordView) := ⊤
  let : DiscreteMeasurableSpace (A × RecordView) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have completed := (RegistrationNativeG3SeedTableCompletion.uniform_program setup codec route work before).map
    (fun result => (result.1, recordView result.2))
  have sampled := _root_.EvalDistEq.of_evalDist_eq completed.evalDist_eq
  have values : (do
      let seeds ← $ᵗ (Seeds n)
      hidden setup codec route work (seeded (overlay before seeds) before)) =
      (do
        let seeds ← $ᵗ (Seeds n)
        hidden setup codec route work (lens.set before ⟨fun slot => some (overlay before seeds slot)⟩)) := by
    apply bind_congr
    intro seeds
    exact preassigned setup codec route (overlay before seeds) work before
  rw [values]
  simpa only [map_bind, Functor.map_map, Prod.map_def, id_eq, overlay, RegistrationNativePlatformG3RecordCoupling.hidden, lens,
    RegistrationNativeG3SeedTableCompletion.Table, RegistrationNativeG3AuditedWorld.Seeds, view_record] using sampled

noncomputable def knownGame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) A) (before : State n) : ProbComp (A × RecordView) := do
  let seeds ← $ᵗ (Seeds n)
  known setup codec route (overlay before seeds) work before

/-- Broad record observers pay the same one actual repeated-role audit event as the value-only guarded comparison. -/
theorem bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) A) (before : State n) :
    ENNReal.ofReal (discreteDistance (knownGame setup codec route work before) (hidden setup codec route work before)) ≤
      Pr{let pair ← (do
        let seeds ← $ᵗ (Seeds n)
        let result ← audit setup codec route (overlay before seeds) work before
        pure (seeds, result))}[pair.2.2.2 = true] := by
  have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent ($ᵗ (Seeds n))
    (fun seeds => known setup codec route (overlay before seeds) work before)
    (fun seeds => hidden setup codec route work (seeded (overlay before seeds) before))
    (fun seeds => audit setup codec route (overlay before seeds) work before)
    (fun _ result => result.2.2 = true)
    (fun seeds _ => RegistrationNativePlatformG3RecordCoupling.fixed_bound setup codec route (overlay before seeds) work before)
  rw [discreteDistance_congr (.rfl) (hidden_uniform setup codec route work before)] at compared
  exact (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le
end BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform.hidden_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform.hidden_uniform

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformG3RecordUniform.bound

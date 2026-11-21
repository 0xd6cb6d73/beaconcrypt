-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3GuardedMarkedHidden
import BeaconcryptCore.Computational.RegistrationNativeG3SeedTableCompletion
import BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix

/-! The actual guarded materialized known World and the actual lazy hidden World differ by at most the privately audited repeated-role attempt probability. The full private seed table is genuinely sampled, preserves any earlier cached seed, and is removed by the concrete guarded seed-delay source law. Both executions retain every optional refusal and all client output. This theorem supplies no cryptographic estimate for the remaining actual repetition event. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorld (State)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeG3AuditedWorld (Seeds seeded)
open RegistrationNativeG3GuardedWorld (marked)
open RegistrationNativeSeedDelayCore (lens mask)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

noncomputable def known (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) Value) (before : State n) : ProbComp Value :=
  Prod.fst <$> (simulateQ (RegistrationNativeG3GuardedMaterializedWorld.source setup codec route seeds) work).run before

noncomputable def hidden (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) : ProbComp Value :=
  Prod.fst <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run before

noncomputable def audit (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) Value) (before : State n) :=
  (simulateQ (marked setup codec route seeds true) (simulateQ RegistrationNativeG3Materialize.materialize work)).run (before, false)

/-- For one fixed genuine private table, the actual known and actual guarded hidden outputs are coupled until the first actual repeated-role attempt. -/
theorem fixed_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) Value) (before : State n) :
    discreteDistance (known setup codec route seeds work before) (hidden setup codec route work (seeded seeds before)) ≤
      (Pr{let result ← audit setup codec route seeds work before}[result.2.2 = true]).toReal := by
  unfold known hidden
  rw [RegistrationNativeG3GuardedMarkedKnown.materialized_source,
    RegistrationNativeG3GuardedMarkedHidden.actual_source]
  exact (discreteDistance_map_le Prod.fst _ _).trans
    (RegistrationNativeG3GuardedWorld.distance_le_repeat setup codec route seeds _ before)

private theorem preassigned_value (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (seeds : Seeds n)
    (work : OracleComp (WorldSpec n) Value) (before : State n) :
    hidden setup codec route work (seeded seeds before) =
      hidden setup codec route work (lens.set before ⟨fun slot => some (seeds slot)⟩) := by
  unfold hidden
  rw [RegistrationNativeG3GuardedMarkedHidden.actual_value_input setup codec route work (seeded seeds before),
    RegistrationNativeG3GuardedMarkedHidden.actual_value_input setup codec route work
      (lens.set before ⟨fun slot => some (seeds slot)⟩)]
  rfl

def overlay (before : State n) (seeds : Seeds n) : Seeds n := OracleComp.completeTable before.seeds.1 seeds

/-- Sampling a full private table with its existing cache overlay and then running the actual guarded hidden continuation has exactly its original lazy source distribution. -/
theorem hidden_uniform (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    (do let seeds ← $ᵗ (Seeds n)
        hidden setup codec route work (seeded (overlay before seeds) before)) =ᵈ
      hidden setup codec route work before := by
  let : MeasurableSpace Value := ⊤
  let : DiscreteMeasurableSpace Value := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have completed := (RegistrationNativeG3SeedTableCompletion.uniform_program setup codec route work before).map Prod.fst
  have sampled := _root_.EvalDistEq.of_evalDist_eq completed.evalDist_eq
  have values : (do
      let seeds ← $ᵗ (Seeds n)
      hidden setup codec route work (seeded (overlay before seeds) before)) =
      (do
        let seeds ← $ᵗ (Seeds n)
        hidden setup codec route work (lens.set before ⟨fun slot => some (overlay before seeds slot)⟩)) := by
    apply bind_congr
    intro seeds
    exact preassigned_value setup codec route (overlay before seeds) work before
  rw [values]
  simpa only [map_bind, Functor.map_map, Prod.map_def, id_eq, overlay,
    hidden, lens, RegistrationNativeG3SeedTableCompletion.Table, RegistrationNativeG3AuditedWorld.Seeds] using sampled

noncomputable def knownGame (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) : ProbComp Value := do
  let seeds ← $ᵗ (Seeds n)
  known setup codec route (overlay before seeds) work before

/-- The complete actual guarded G3 change costs only its original known-side repeated-role audit probability. All seed completion, source and optional-refusal equations are derived internally. -/
theorem bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Value) (before : State n) :
    ENNReal.ofReal (discreteDistance (knownGame setup codec route work before) (hidden setup codec route work before)) ≤
      Pr{let pair ← (do
        let seeds ← $ᵗ (Seeds n)
        let result ← audit setup codec route (overlay before seeds) work before
        pure (seeds, result))}[pair.2.2.2 = true] := by
  have compared := PqxdhExtractRomHiddenSuffix.tvDist_bind_le_probEvent ($ᵗ (Seeds n))
    (fun seeds => known setup codec route (overlay before seeds) work before)
    (fun seeds => hidden setup codec route work (seeded (overlay before seeds) before))
    (fun seeds => audit setup codec route (overlay before seeds) work before)
    (fun _ result => result.2.2 = true) (fun seeds _ => fixed_bound setup codec route (overlay before seeds) work before)
  rw [discreteDistance_congr (.rfl) (hidden_uniform setup codec route work before)] at compared
  exact (ENNReal.ofReal_le_ofReal compared).trans (ENNReal.ofReal_toReal (prEvent_ne_top _)).le

end BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling.fixed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling.fixed_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling.hidden_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling.hidden_uniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3GuardedCoupling.bound

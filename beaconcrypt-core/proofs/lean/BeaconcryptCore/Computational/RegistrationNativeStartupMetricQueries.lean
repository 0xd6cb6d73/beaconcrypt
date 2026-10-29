-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStartupMetricInterface

/-! Both actual startup samplers agree after erasing their three independently billed accounting coordinates. The constructor and ML generator remain their literal samplers; every ordinary World reply and cache is retained through the existing bilateral non-read law. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStartupMetric
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeG3MetricWorld (mask)
open PqxdhRecordLiftInterface (coinLift)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem sampled_mask (draw : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$> (PqxdhRecordLiftWorld.sampled draw).run before =
      (fun value => (value, mask before)) <$> draw := by
  have erased := congrArg (Functor.map (Prod.map id RegistrationNativeWorldView.project))
    (RegistrationNativeKemWorldUniform.sampled_mask draw before)
  simpa only [Functor.map_map, Prod.map_def, id_eq, RegistrationNativeG3MetricWorld.mask] using erased

private theorem sampled_input (draw : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$> (PqxdhRecordLiftWorld.sampled draw).run before =
      Prod.map id mask <$> (PqxdhRecordLiftWorld.sampled draw).run (mask before) := by
  rw [sampled_mask, sampled_mask, RegistrationNativeG3MetricWorld.mask_idempotent]

private theorem coin_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (draw : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
        (simulateQ coinLift draw)).run before =
      (fun value => (value, mask before)) <$> draw := by
  have source := RegistrationNativeG3MetricCoins.program_source setup (RegistrationNativeWire.ledgerCodec wire) route draw before
  rw [← RegistrationNativeG3MetricWorld.program_source] at source
  have same : RegistrationNativeG3MetricCoins.program (n := n) draw = simulateQ coinLift draw := by
    simp only [RegistrationNativeG3MetricCoins.program, ← QueryImpl.simulateQ_compose]
    rfl
  rw [same] at source
  exact source

private theorem sampler_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (draw : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
        (simulateQ coinLift draw)).run before =
      Prod.map id mask <$> (PqxdhRecordLiftWorld.sampled draw).run (mask before) := by
  rw [coin_source, sampled_mask, RegistrationNativeG3MetricWorld.mask_idempotent]

noncomputable def normalized (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) :
    QueryImpl (Spec n source) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) := fun query before =>
  Prod.map id mask <$> (reference setup wire route source ensureInit identityIndex serverKeyId query).run (mask before)

/-- Each actual constructor, ML generation or World callback agrees with the normalized reference callback on the same input. -/
theorem actual_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (query : (Spec n source).Domain) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$> (actual setup wire route source ensureInit identityIndex serverKeyId query).run before =
      (normalized setup wire route source ensureInit identityIndex serverKeyId query).run (mask before) := by
  rcases query with constructor | generation | world
  · simpa only [actual, normalized, reference, StateT.run, RegistrationNativeG3MetricWorld.mask_idempotent] using
      sampler_source setup wire route ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()) before
  · simpa only [actual, normalized, reference, StateT.run, RegistrationNativeG3MetricWorld.mask_idempotent] using
      sampler_source setup wire route (RegistrationNativeMldsa.generate source) before
  · simpa only [actual, normalized, reference, StateT.run, RegistrationNativeG3MetricWorld.mask_idempotent] using
      RegistrationNativeG3MetricWorld.guarded_input setup (RegistrationNativeWire.ledgerCodec wire) route world before

/-- The original reference callbacks obey the same precise accounting normalization law. -/
theorem reference_query (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (query : (Spec n source).Domain) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$> (reference setup wire route source ensureInit identityIndex serverKeyId query).run before =
      (normalized setup wire route source ensureInit identityIndex serverKeyId query).run (mask before) := by
  rcases query with constructor | generation | world
  · simpa only [reference, normalized, StateT.run, RegistrationNativeG3MetricWorld.mask_idempotent] using
      sampled_input ((PqxdhLiveServerConstruction.construct (P := Unit) setup.joint ensureInit identityIndex serverKeyId none).run ()) before
  · simpa only [reference, normalized, StateT.run, RegistrationNativeG3MetricWorld.mask_idempotent] using
      sampled_input (RegistrationNativeMldsa.generate source) before
  · simpa only [normalized, reference, StateT.run, RegistrationNativeG3MetricWorld.mask_idempotent] using
      RegistrationNativeG3MetricWorld.guarded_input setup (RegistrationNativeWire.ledgerCodec wire) route world before

end BeaconcryptCore.Computational.RegistrationNativeStartupMetric
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupMetric.actual_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupMetric.actual_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupMetric.reference_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupMetric.reference_query

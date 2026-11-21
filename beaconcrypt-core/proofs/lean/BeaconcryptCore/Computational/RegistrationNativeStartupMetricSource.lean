-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStartupMetricQueries

/-! The actual guarded startup and original public startup have the same public credential/frontend and semantic World after erasing only the three independently billed accounting fields. This is an exact source equation, retaining startup failure, Server import and the shared ML-pin hash cache. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStartupMetric
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeG3MetricWorld (mask)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

/-- Every adaptive startup skeleton has the same normalized semantic World and literal returned result under both actual samplers. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (work : OracleComp (Spec n source) Value) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id mask <$> (simulateQ (actual setup wire route source ensureInit identityIndex serverKeyId) work).run before =
      Prod.map id mask <$> (simulateQ (reference setup wire route source ensureInit identityIndex serverKeyId) work).run before := by
  have actualEq := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (actual setup wire route source ensureInit identityIndex serverKeyId)
    (normalized setup wire route source ensureInit identityIndex serverKeyId) mask
    (actual_query setup wire route source ensureInit identityIndex serverKeyId) work before
  have referenceEq := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    (reference setup wire route source ensureInit identityIndex serverKeyId)
    (normalized setup wire route source ensureInit identityIndex serverKeyId) mask
    (reference_query setup wire route source ensureInit identityIndex serverKeyId) work before
  exact actualEq.trans referenceEq.symm

/-- The complete actual startup has the original credential/frontend and shared-cache state after only accounting normalization. -/
theorem startup_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (identity : PqxdhJointIdentity.PublicIdentity) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map (Option.map RegistrationNativeHiddenStartup.Started.native) mask <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route)
        (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId identity)).run before =
      Prod.map id mask <$>
        (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId identity).run before := by
  have compared := program_source setup wire route source ensureInit identityIndex serverKeyId
    (program source identityIndex serverKeyId identity) before
  rw [actual_source] at compared
  have observed := congrArg (Functor.map (Prod.map (Option.map RegistrationNativeHiddenStartup.Started.native) id)) compared
  have original := congrArg (Functor.map (Prod.map id mask))
    (reference_source setup wire route source ensureInit identityIndex serverKeyId identity before)
  simp only [Functor.map_map, Prod.map_def, id_eq] at observed original ⊢
  exact observed.trans original

/-- The actual cold startup and original public startup share their exact normalized source law, including every failure probability. -/
theorem cold_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    Prod.map (Option.map RegistrationNativeHiddenStartup.Started.native) mask <$>
      RegistrationNativeG3MaterializedStartup.startup (n := n) setup wire route source ensureInit identityIndex serverKeyId seed =
      Prod.map id mask <$>
        (RegistrationNativePublicStartupFrame.startup setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)).run
          PqxdhRecordLiftWorld.initial :=
  startup_source setup wire route source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed) PqxdhRecordLiftWorld.initial

end BeaconcryptCore.Computational.RegistrationNativeStartupMetric
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupMetric.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupMetric.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupMetric.startup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupMetric.startup_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStartupMetric.cold_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStartupMetric.cold_source

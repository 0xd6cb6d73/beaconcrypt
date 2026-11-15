-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeReferenceInterpreter
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeStage
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeRecord
import BeaconcryptCore.Computational.RegistrationNativeCommonCompiler

/-! The selected Beacon's canonical prepare/material/indexed-KEM interface is interpreted on one actual native World and private KEM pool. Preparation calls the native related-root source at that time; later material demand reads the returned root memo. Common record/signing components run through the concrete same-environment compiler and the actual native primitive wrapper. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRelatedRoot (RootSpec)
open RegistrationBeaconReferenceCompiler (Spec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev Extra (KemSK : Type) := RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK
abbrev Target (n : Nat) (KemSK : Type) := RegistrationNativeReferenceInterpreter.WithTarget (Extra KemSK) n
abbrev Inner (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeRelatedFamily.State × RegistrationNativeExperiment.State n KemSK source
abbrev State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeReferenceInterpreter.State × Inner n KemSK source

def onNative (work : StateT (RegistrationNativeExperiment.State n KemSK mlSource) ProbComp Value) :
    StateT (Inner n KemSK mlSource) ProbComp Value := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$> work.run before.2

noncomputable def target (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl (Target n KemSK) (StateT (Inner n KemSK mlSource) ProbComp)
  | .inl query => fun before => (fun result => (result.1, (result.2, before.2))) <$>
      (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar query).run before.1
  | .inr (.inl query) => onNative (RegistrationNativeExperiment.beacon setup checks representation created
      (StateT.lift (RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceNativeRecord.environment
        setup.source wire.frameWrite (RegistrationNativeMldsa.owned mlSource credential) query)))
  | .inr (.inr query) => onNative (RegistrationNativeExperiment.trusted setup checks representation created mlSource (.inr query))

noncomputable def implementation (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource) :
    QueryImpl (Spec n KemSK) (StateT (State n KemSK mlSource) ProbComp) :=
  ((target setup checks wire representation created scalar credential).mapStateTBase
    (RegistrationNativeReferenceInterpreter.compilerWith (Extra KemSK) setup.source)).flattenStateT

private theorem env_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    RegistrationNativeExperiment.beacon setup checks representation created
      (StateT.lift (StateT.lift ((RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl query) :
        OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) _))) =
      RegistrationNativeExperiment.trusted setup checks representation created mlSource (.inl query) := by
  have lifted (owners : RegistrationNativeBeaconFrontend.State mlSource)
      (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
      (((StateT.lift (StateT.lift ((RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl query) :
        OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) _)) :
        RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State _).run owners).run env) =
        (fun reply => ((reply, owners), env)) <$>
          ((RegistrationNativeBeaconFrontend.Trusted n KemSK).query (.inl query) :
            OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) _) := by
    simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]
  apply StateT.ext
  intro before
  unfold RegistrationNativeExperiment.beacon
  simp only [lifted, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  simp only [
    RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    StateT.run, Functor.map_map, RegistrationWorldAgreementCompiler.join, RegistrationWorldAgreementCompiler.erase,
    bind_pure_comp]

private theorem onNative_framed
    (work : StateT (RegistrationNativeExperiment.State n KemSK mlSource) ProbComp Value)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : Inner n KemSK mlSource) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (((fun reply => (reply, memo)) <$> onNative work).run before) =
      (fun result => (result.1, (memo, (before.1, result.2)))) <$> work.run before.2 := by
  rw [StateT.run_map]
  simp only [onNative, StateT.run, Functor.map_map]

/-- Actual root preparation runs now and stores only that returned reply; it neither evaluates108 material nor changes the native World. -/
theorem prepare (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource) (message : Message)
    (before : State n KemSK mlSource) :
    (implementation setup checks wire representation created scalar credential (.inl message)).run before = (do
      let actual ← (RegistrationNativeRelatedRoot.sourceImpl setup.source setup.hmac setup.joint setup.dh created.seed scalar
        (.inr (.derive message))).run before.2.1
      pure (actual.1.map (fun _ => message), (Function.update before.1 message actual.1, (actual.2, before.2.2)))) := by
  rw [implementation, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [
    RegistrationNativeReferenceInterpreter.compilerWith, RegistrationNativeReferenceInterpreter.compiler,
    RegistrationNativeReferenceInterpreter.targetLift, simulateQ_map, simulateQ_spec_query,
    target, StateT.run, bind_pure_comp]
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (((fun root : Option PqxdhSecretInputKdf.RootOutput =>
        (root.map (fun _ => message), Function.update before.1 message root)) <$>
          target setup checks wire representation created scalar credential (.inl (.inr (.derive message)))).run before.2) = _
  rw [StateT.run_map]
  simp only [target, StateT.run, Functor.map_map]

/-- Every deferred material request uses precisely the earlier root reply and retains the complete native/family state. -/
theorem demand_known (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource) (message : Message)
    (before : State n KemSK mlSource) (root : PqxdhSecretInputKdf.RootOutput)
    (prepared : before.1 message = some root) :
    (implementation setup checks wire representation created scalar credential (.inr (.inl (.inl message)))).run before =
      pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot setup.source root)), before) := by
  rw [implementation, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [
    RegistrationNativeReferenceInterpreter.compilerWith, RegistrationNativeReferenceInterpreter.compiler,
    StateT.run, prepared, Option.map_some, simulateQ_pure]
  rfl

/-- Failed or absent preparation cannot manufacture a root or trigger source108 evaluation at demand. -/
theorem demand_missing (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource) (message : Message)
    (before : State n KemSK mlSource) (missing : before.1 message = none) :
    (implementation setup checks wire representation created scalar credential (.inr (.inl (.inl message)))).run before =
      pure (none, before) := by
  rw [implementation, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [
    RegistrationNativeReferenceInterpreter.compilerWith, RegistrationNativeReferenceInterpreter.compiler,
    StateT.run, missing, Option.map_none, simulateQ_pure]
  rfl

/-- Ordinary native environment and indexed primitive calls use the same reached World and pool, while retaining the prepared roots and private family state. -/
theorem trusted_query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (before : State n KemSK mlSource) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (RegistrationBeaconReferenceCompiler.trustedLift query)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run before.2.2 := by
  cases query with
  | inl query =>
      simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
        simulateQ_spec_query]
      rw [implementation, QueryImpl.flattenStateT_mapStateTBase_apply_run]
      simp only [RegistrationNativeReferenceInterpreter.compilerWith, RegistrationNativeReferenceInterpreter.compiler,
        RegistrationNativeReferenceInterpreter.targetLift, simulateQ_map, simulateQ_spec_query,
        StateT.run, target, RegistrationNativeCommonCompiler.common,
        RegistrationBeaconReferenceNativeRecord.environment]
      rw [env_native]
      exact onNative_framed _ before.1 before.2
  | inr query =>
      simp only [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
        simulateQ_spec_query]
      rw [implementation, QueryImpl.flattenStateT_mapStateTBase_apply_run]
      simp only [RegistrationNativeReferenceInterpreter.compilerWith, simulateQ_map, simulateQ_spec_query,
        target, StateT.run]
      exact onNative_framed _ before.1 before.2

/-- An arbitrary adaptive ordinary primitive program retains the same complete native execution; no additional root or material queries are introduced. -/
theorem trusted_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (before : State n KemSK mlSource) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created mlSource) work).run before.2.2 := by
  rw [← QueryImpl.simulateQ_compose]
  let embed : RegistrationNativeExperiment.State n KemSK mlSource → State n KemSK mlSource :=
    fun native => (before.1, (before.2.1, native))
  have step (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
      (native : RegistrationNativeExperiment.State n KemSK mlSource) :
      Prod.map id embed <$>
        (RegistrationNativeExperiment.trusted setup checks representation created mlSource query).run native =
      ((implementation setup checks wire representation created scalar credential ∘ₛ
        RegistrationBeaconReferenceCompiler.trustedLift) query).run (embed native) := by
    simpa only [QueryImpl.apply_compose, embed, Prod.map_def, id_eq] using
      (trusted_query setup checks wire representation created scalar credential query (embed native)).symm
  simpa only [embed, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed step work before.2.2).symm

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.prepare

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.demand_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.demand_known

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.demand_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.demand_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.trusted_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.trusted_query

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeInterpreter.trusted_program

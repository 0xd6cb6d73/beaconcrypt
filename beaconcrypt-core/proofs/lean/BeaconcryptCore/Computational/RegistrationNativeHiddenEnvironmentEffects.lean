-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironment

/-! Closing the concrete frontend and thin backend is an actual stateful compiler. These finite source equations retain both complete local states and expose the exact shared-World effect and record surfaces before full-ledger composition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenEnvironment (State)
variable {n : Nat} {ι KemSK ProviderState Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : RegistrationNativePublicFrontend.M n KemSK source Value) :
    StateT (State n KemSK ProviderState source) (OracleComp (WorldSpec n)) Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider) (work.run before.1)).run before.2

/-- The stateful closure runs the literal frontend before returning both actual local poststates. -/
theorem close_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : State n KemSK ProviderState source) :
    (close setup wire sign seed scalar provider work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider)
          (work.run before.1)).run before.2 := rfl

/-- Closing pure frontend work preserves both actual local states without a World effect. -/
theorem pure_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (value : Value) :
    close (source := source) (n := n) setup wire sign seed scalar provider (pure value) = pure value := by
  funext before
  simp only [close, StateT.run_pure, simulateQ_pure, map_pure]
  rfl

/-- Actual sequential frontend work closes with the same state and callback order. -/
theorem bind_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (next : Value → RegistrationNativePublicFrontend.M n KemSK source Next) :
    close setup wire sign seed scalar provider (work >>= next) =
      (close setup wire sign seed scalar provider work >>= fun value => close setup wire sign seed scalar provider (next value)) := by
  apply StateT.ext
  intro before
  simp only [StateT.run_bind, close_run, simulateQ_bind, map_bind, bind_map_left]

/-- The actual frontend environment effect reaches the same shared World directly and retains both local states. -/
theorem effect_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : (EnvEffects n).Domain)
    (before : State n KemSK ProviderState source) :
    (close setup wire sign seed scalar provider (StateT.lift (RegistrationNativePublicFrontend.effect query))).run before =
      (fun reply => (reply, before)) <$> effectLift query := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeHiddenInterpreter.handler setup wire sign seed scalar provider)
      ((StateT.lift (RegistrationNativePublicFrontend.effect query)).run before.1)).run before.2 = _
  simp only [StateT.run_lift, bind_pure_comp,
    RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal,
    simulateQ_map, simulateQ_spec_query,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.effect]
  rfl

/-- Existing Server record handles are forwarded literally; neither local frontend nor thin service state changes. -/
theorem server_record_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (query : RawCtxServerMixed.SourceSpec.Domain)
    (before : State n KemSK ProviderState source) :
    (close setup wire sign seed scalar provider (RegistrationNativePublicFrontend.record (.inl query))).run before =
      (fun reply => (reply, before)) <$> ((WorldSpec n).query (.inr (.inr (.inl query))) : OracleComp (WorldSpec n) _) := by
  have actual : (RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) (.inl query)).run before.1 =
      (fun reply => (reply, before.1)) <$>
        ((RegistrationNativePublicFrontend.Spec n KemSK).query (.inr (.inl query)) : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _) := by
    cases query <;> rfl
  rw [close_run, actual]
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map,
    RegistrationNativeHiddenInterpreter.handler, StateT.run_lift, bind_pure_comp, Functor.map_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.pure_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.pure_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.bind_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.bind_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.effect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.effect_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.server_record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.server_record_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.close_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentEffects.close_run

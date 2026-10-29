-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MetricCoins
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenInterpreter

/-! The actual selective thin interpreter samples material through capability-free Env programs. After the proved accounting projection, those programs run in independent private key state and retain the entire semantic World. Every other callback remains the actual guarded World computation. The whole adaptive source equation below derives this separation from concrete callbacks rather than assuming that two stateful services share a World. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects)
open RegistrationNativeSelectiveHiddenInterpreter (onKeys)
open RegistrationNativeG3MetricWorld (mask)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := by
  exact StateT.run_map map work before

abbrev Private (n : Nat) (KemSK ProviderState : Type) := RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState
abbrev State (n : Nat) (KemSK ProviderState : Type) := Private n KemSK ProviderState × PqxdhRecordLiftWorld.State n

def project (before : State n KemSK ProviderState) : State n KemSK ProviderState := (before.1, mask before.2)

def getKeys (before : Private n KemSK ProviderState) : RegistrationNativeSelectiveHiddenService.State n :=
  (before.1.keys, before.2)

def putKeys (before : Private n KemSK ProviderState) (keys : RegistrationNativeSelectiveHiddenService.State n) :
    Private n KemSK ProviderState := ({ before.1 with keys := keys.1 }, keys.2)

noncomputable def execute (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState Value) :
    StateT (State n KemSK ProviderState) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeG3MetricWorld.handler setup codec route) (work.run before.1)).run before.2

noncomputable def localKeys (work : StateT (RegistrationNativeSelectiveHiddenService.State n)
    (OracleComp (EnvEffects n)) Value) : StateT (State n KemSK ProviderState) ProbComp Value := fun before =>
  (fun result => (result.1, (putKeys before.1 result.2, before.2))) <$>
    simulateQ RegistrationNativeG3MetricCoins.localCoins (work.run (getKeys before.1))

private theorem execute_run (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState Value)
    (before : State n KemSK ProviderState) :
    (execute setup codec route work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativeG3MetricWorld.handler setup codec route) (work.run before.1)).run before.2 := rfl

private theorem execute_pure (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (value : Value) :
    execute (n := n) (ProviderState := ProviderState) setup codec route (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [execute_run, StateT.run_pure, simulateQ_pure, map_pure]

private theorem execute_bind {Next : Type} (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (first : RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState Value)
    (next : Value → RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState Next) :
    execute setup codec route (first >>= next) =
      (execute setup codec route first >>= fun value => execute setup codec route (next value)) := by
  apply StateT.ext
  intro before
  simp only [execute_run, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

/-- Concrete World closure preserves every adaptive continuation and both full state coordinates. -/
theorem execute_program {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (implementation : QueryImpl spec (RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState))
    (work : OracleComp spec Value) :
    execute setup codec route (simulateQ implementation work) =
      simulateQ (fun query => execute setup codec route (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, execute_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, execute_bind]
      congr 1
      funext reply
      exact ih reply

/-- The complete concrete private computation commutes with the stated World accounting projection on both ends. -/
theorem execute_project (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (work : RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState Value)
    (before : State n KemSK ProviderState) :
    Prod.map id project <$> (execute setup codec route work).run before =
      (execute setup codec route work).run (project before) := by
  have result := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution)
    (RegistrationNativeG3MetricWorld.handler_program_mask setup codec route (work.run before.1) before.2)
  simpa only [execute, StateT.run, project, Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using result

/-- Every capability-free key-service program runs on its own private state and an independent sampler while retaining the actual semantic World. -/
theorem key_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT (RegistrationNativeSelectiveHiddenService.State n) (OracleComp (EnvEffects n)) Value)
    (before : State n KemSK ProviderState)
    (free : (work.run (getKeys before.1)).IsQueryBoundP RegistrationNativeHiddenServiceBounds.IsCapability 0) :
    Prod.map id project <$> (execute setup codec route (onKeys work)).run before =
      (localKeys work).run (project before) := by
  have result := congrArg
    (fun distribution => (fun result => (result.1.1, (putKeys before.1 result.1.2, result.2))) <$> distribution)
    (RegistrationNativeG3MetricCoins.environment_project setup codec route (work.run (getKeys before.1)) free before.2)
  simpa only [execute, onKeys, simulateQ_map, StateT.run, state_map_apply, localKeys,
    getKeys, putKeys, project, Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using result

noncomputable def actual (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (State n KemSK ProviderState) ProbComp) := fun query =>
  execute setup codec route (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider query)

noncomputable def handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (State n KemSK ProviderState) ProbComp)
  | .inl (.inl message) => localKeys (RegistrationNativeSelectiveHiddenService.prepare
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) message)
  | .inl (.inr (.inl (.inl message))) => localKeys (RegistrationNativeSelectiveHiddenService.demand setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message)
  | query => actual setup codec route wire sign seed scalar candidate provider query

/-- Every actual callback is the independent-key-state implementation after only the named accounting projection. -/
theorem query_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State n KemSK ProviderState) :
    Prod.map id project <$> (actual setup codec route wire sign seed scalar candidate provider query).run before =
      (handler setup codec route wire sign seed scalar candidate provider query).run (project before) := by
  rcases query with (message | (message | common) | kem) | record
  · change Prod.map id project <$> (execute setup codec route
        (onKeys (RegistrationNativeSelectiveHiddenService.prepare
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) message))).run before = _
    apply key_source
    simp only [RegistrationNativeSelectiveHiddenService.prepare, RegistrationNativeSelectiveHiddenService.onHidden,
      RegistrationNativeHiddenService.prepare, StateT.run, isQueryBoundP_map_iff]
    trivial
  · exact key_source setup codec route _ before
      (RegistrationNativeSelectiveHiddenServiceInvariant.demand_free _ _ _ _ _ _)
  · exact execute_project setup codec route _ before
  · exact execute_project setup codec route _ before
  · exact execute_project setup codec route _ before

/-- The exact callback source equations extend through arbitrary adaptive frontend code, retaining all private outputs and semantic World state. -/
theorem program_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    Prod.map id project <$> (simulateQ (actual setup codec route wire sign seed scalar candidate provider) work).run before =
      (simulateQ (handler setup codec route wire sign seed scalar candidate provider) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source setup codec route wire sign seed scalar candidate provider) work before

/-- The full literal selective thin World program is the independent-key-state program after the proved accounting projection. No callback or whole-source equation is a caller premise. -/
theorem original_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    (fun result => (result.1.1, (result.1.2, mask result.2))) <$>
      (simulateQ (CborRecordWorldSimulation.guarded setup codec route)
        ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work).run before.1)).run before.2 =
      (simulateQ (handler setup codec route wire sign seed scalar candidate provider) work).run (project before) := by
  have normalized := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution)
    (RegistrationNativeG3MetricWorld.program_source setup codec route
      ((simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work).run before.1) before.2)
  change _ = (execute setup codec route
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider) work)).run (project before) at normalized
  rw [← execute_project, execute_program] at normalized
  simpa only [Functor.map_map, Prod.map_def, id_eq, Function.comp_apply] using
    normalized.trans (program_source setup codec route wire sign seed scalar candidate provider work before)

end BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.execute_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.execute_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.execute_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.execute_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.key_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.key_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.original_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalKeys.original_source

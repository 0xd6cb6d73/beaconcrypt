-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerFrontend
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler

/-! The compiled native material service reads its caller's current mutable environment on every operation. The concrete local interface overrides only the actual demand and environment-effect leaves; unrelated callbacks remain the supplied executable fallback. Chronological receipts stay in the environment, while the same independent key state and full World are retained below it. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativeG3MaterializedTracedServerFrontend (ServiceSpec materialize)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {KemSK KeyState Auxiliary Value Next : Type}

abbrev Private (n : Nat) (KeyState : Type) := KeyState × (RegistrationNativeG2Trace.State × PqxdhRecordLiftWorld.State n)
abbrev Local (n : Nat) (Auxiliary KeyState : Type) := EnvState Auxiliary × Private n KeyState

noncomputable def effect (full : Bool) (seeds : Seeds n) :
    QueryImpl (EnvEffects n) (StateT (RegistrationNativeG2Trace.State × PqxdhRecordLiftWorld.State n) ProbComp) := fun query before =>
  (fun result => (result.1, (result.2.1, result.2.2.2))) <$>
    (RegistrationNativeG3MaterializedTracedServerCommon.effect full seeds query).run (before.1, ([], before.2))

def keys (full : Bool) (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (message : RegistrationNativeRelatedFamily.Message) : StateT (Private n KeyState) ProbComp (Option (RegistrationNativePairedChoice.Choice n)) := fun before =>
  (fun result => ((if full then result.1.map (materialize seeds) else result.1), (result.2, (RegistrationNativeG2Trace.begin (n := n) (KemSK := Unit) (.inl (.inr (.inl (.inl message)))) before.2.1, before.2.2)))) <$>
    (service message).run before.1

noncomputable def interface (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp)) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp)
  | .inr (.inl (.inl message)) => keys full seeds service message
  | .inr (.inl (.inr (.inr query))) => fun before =>
      (fun result => (result.1, (before.1, result.2))) <$> (effect full seeds query).run before.2
  | query => fallback query

def lower (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Value) :
    StateT (Local n Auxiliary KeyState) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ implementation (work.run before.1)).run before.2

noncomputable def source (full : Bool) (seeds : Seeds n)
    (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePairedServerService.PublicSpec n) (StateT (Local n Auxiliary KeyState) ProbComp) := fun query =>
  lower (interface full seeds service fallback)
    (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      RegistrationServerOpenReferenceCompiler.demand hkdf writer sign query)

def get (before : Local n Auxiliary KeyState) : RegistrationNativeG3MaterializedTracedServerFrontend.State n KeyState :=
  (before.2.1, (before.2.2.1, (before.1.receipts, before.2.2.2)))

def put (before : Local n Auxiliary KeyState) (after : RegistrationNativeG3MaterializedTracedServerFrontend.State n KeyState) :
    Local n Auxiliary KeyState :=
  ({ before.1 with receipts := after.2.2.1 }, (after.1, (after.2.1, after.2.2.2)))

/-- The exact returned environment is retained at the current operation's continuation. -/
theorem lower_run
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Value)
    (before : Local n Auxiliary KeyState) :
    (lower implementation work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ implementation (work.run before.1)).run before.2 := rfl

/-- A pure current-environment action retains the complete original local and private states. -/
theorem lower_pure
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (value : Value) : lower (Auxiliary := Auxiliary) implementation (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_pure, simulateQ_pure, map_pure]

/-- Current-environment lowering preserves each actual mutable continuation and the full independent private state. -/
theorem lower_bind
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Value)
    (next : Value → StateT (EnvState Auxiliary) (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK)) Next) :
    lower implementation (work >>= next) = (lower implementation work >>= fun value => lower implementation (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

/-- Every pure oracle component is lowered query by query against the then-current mutable environment. -/
theorem lower_program {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Private n KeyState) ProbComp))
    (compiler : QueryImpl spec (StateT (EnvState Auxiliary) (OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK))))
    (work : OracleComp spec Value) :
    lower implementation (simulateQ compiler work) = simulateQ (fun query => lower implementation (compiler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, lower_bind]
      congr 1
      funext reply
      exact ih reply


end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedServerInterface.lower_program

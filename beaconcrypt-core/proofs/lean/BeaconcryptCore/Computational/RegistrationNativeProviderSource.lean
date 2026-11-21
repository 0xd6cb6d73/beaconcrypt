-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter

/-! The provider reference client has one literal private source interpretation. Provider coins use its shared World sampler, while the same root source privately supplies the Server seed and selected Beacon scalar. Selected-accept routing remains explicit in the local source callback and is never erased by a fixed-real KEM interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider State M withBase)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def close (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : M n KemSK ProviderState Value) : StateT (State n KemSK ProviderState) ProbComp Value :=
  fun before => simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    (work.run before)

/-- Source closure of a non-provider callback retains the full provider state and uses the existing actual source callback. -/
theorem withBase_source (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : State n KemSK ProviderState) :
    (close setup seed scalar (withBase work)).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (RegistrationNativePublicSourceEffects.close setup seed scalar work).run before.1 := by
  simp only [close, withBase, StateT.run, simulateQ_map, RegistrationNativePublicSourceEffects.close]

/-- The same total KEM provider is executed literally under source closure; it receives no source seed/scalar or root/World state. -/
theorem routed_source (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : State n KemSK ProviderState) :
    (close setup seed scalar (RegistrationNativeProviderInterpreter.routed provider query)).run before =
      (fun result => (result.1.1,
        ({ before.1 with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
        ((PqxdhRecordLiftWorld.sampled ((provider query).run (before.1.pool, before.2))).run before.1.world) := by
  change simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((RegistrationNativeProviderInterpreter.routed provider query).run before) = _
  rw [RegistrationNativeProviderInterpreter.routed_run]
  simp only [simulateQ_map, ← QueryImpl.simulateQ_compose]
  have coins : RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar ∘ₛ
      RegistrationNativePublicInterpreter.coins = QueryImpl.ofLift unifSpec ProbComp := rfl
  rw [coins, simulateQ_ofLift_eq_self]

noncomputable def localHandler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) (selected : Bool) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (M n KemSK ProviderState) :=
  fun query => simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider)
    (RegistrationNativePublicFrontend.liftLocal selected query)

noncomputable def localImpl (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KemSK ProviderState) ProbComp) :=
  fun query => close setup seed scalar (localHandler setup wire route sign provider selected query)

private theorem close_simulate {Index : Type} {spec : OracleSpec Index}
    (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (implementation : QueryImpl spec (M n KemSK ProviderState))
    (work : OracleComp spec Value) (before : State n KemSK ProviderState) :
    (close setup seed scalar (simulateQ implementation work)).run before =
      (simulateQ (fun query => close setup seed scalar (implementation query)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, close, StateT.run,
        StateT.monad_bind_def, StateT.bind, simulateQ_bind]
      apply bind_congr
      rintro ⟨reply, after⟩
      exact ih reply after

/-- Whole adaptive local programs retain the selected getter route and the actual provider, without a provider-correctness or source-simulation premise. -/
theorem local_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (before : State n KemSK ProviderState) :
    (close setup seed scalar
      (simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider)
        (simulateQ (RegistrationNativePublicFrontend.liftLocal selected) work))).run before =
      (simulateQ (localImpl setup wire route sign seed scalar provider selected) work).run before := by
  rw [← QueryImpl.simulateQ_compose, close_simulate]
  rfl

abbrev FrontState (n : Nat) (KemSK ProviderState : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativePublicFrontend.State source × State n KemSK ProviderState

noncomputable def execute (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    {source : RegistrationNativeMldsa.Source} (work : RegistrationNativePublicFrontend.M n KemSK source Value) :
    StateT (FrontState n KemSK ProviderState source) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (close setup seed scalar
      (simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider) (work.run before.1))).run before.2

/-- The actual provider source retains an output permitted by the entire original open frontend, including its reached public state. -/
theorem observed_support (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState)
    {source : RegistrationNativeMldsa.Source} (work : RegistrationNativePublicFrontend.M n KemSK source Value)
    (before : FrontState n KemSK ProviderState source) (result : Value × FrontState n KemSK ProviderState source)
    (supported : result ∈ support ((execute setup wire route sign seed scalar provider work).run before)) :
    (result.1, result.2.1) ∈ support (work.run before.1) := by
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (close setup seed scalar
      (simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider) (work.run before.1))).run before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have possible := RegistrationNativePublicSourceSupport.simulate_support
    (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((simulateQ (RegistrationNativeProviderInterpreter.handler setup wire route sign provider) (work.run before.1)).run before.2)
    inner reached
  have raw : inner.1 ∈ support (work.run before.1) := by
    apply support_simulateQ_run'_subset (RegistrationNativeProviderInterpreter.handler setup wire route sign provider) _ before.2
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, possible, rfl⟩
  have same : inner.1 = (result.1, result.2.1) := congrArg (fun output => (output.1, output.2.1)) equal
  rw [← same]
  exact raw

end BeaconcryptCore.Computational.RegistrationNativeProviderSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSource.withBase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSource.withBase_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSource.routed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSource.routed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSource.local_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSource.local_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSource.observed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSource.observed_support

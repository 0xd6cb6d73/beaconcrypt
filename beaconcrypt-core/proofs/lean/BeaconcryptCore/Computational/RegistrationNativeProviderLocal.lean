-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderSource

/-! Actual local registration controllers lower their unchanged oracle AST through the provider source. The selected Server getter retains its routed tag; ordinary effects and preparation retain the complete mutable environment, World, pool and provider state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderLocal
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeProviderInterpreter (Provider State)
open RegistrationNativeProviderSource (close localImpl)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (Spec)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Value : Type} {base : OracleSpec ι}

def lower (implementation : QueryImpl (Spec n KemSK) (StateT (State n KemSK ProviderState) ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK)) Value) :
    StateT (EnvState Auxiliary × State n KemSK ProviderState) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$> (simulateQ implementation (work.run before.1)).run before.2

/-- Lowering the actual mutable environment commutes with complete adaptive local controller execution. -/
theorem lower_program {Query : Type} {spec : OracleSpec Query}
    (implementation : QueryImpl (Spec n KemSK) (StateT (State n KemSK ProviderState) ProbComp))
    (callbacks : QueryImpl spec (StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK))))
    (work : OracleComp spec Value) :
    lower implementation (simulateQ callbacks work) =
      simulateQ (fun query => lower implementation (callbacks query)) work := by
  have same : (fun query => lower implementation (callbacks query)) =
      (implementation.mapStateTBase callbacks).flattenStateT := rfl
  rw [same]
  funext before
  change (lower implementation (simulateQ callbacks work)).run before =
    (simulateQ (implementation.mapStateTBase callbacks).flattenStateT work).run before
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ implementation ((simulateQ callbacks work).run before.1)).run before.2 = _
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change (id <$> (simulateQ (implementation.mapStateTBase callbacks).flattenStateT work).run before) = _
  exact id_map _

noncomputable def backend (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool) :
    QueryImpl RegistrationAgreementExecutor.Spec
      (StateT (RegistrationServerReferenceCompiler.Environment × State n KemSK ProviderState) ProbComp) :=
  fun query => lower (localImpl setup wire route sign seed scalar provider selected)
    (RegistrationNativeKemReferenceCompiler.backend setup checks query)

noncomputable def primitive (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool) :
    QueryImpl RegistrationAgreementShared.PrimitiveSpec
      (StateT (RegistrationServerReferenceCompiler.Environment × State n KemSK ProviderState) ProbComp) :=
  fun query => backend setup checks wire route sign seed scalar provider selected query.toRequest

noncomputable def routedImpl (setup : Setup base KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (provider : Provider KemSK ProviderState) : QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK)
      (StateT (State n KemSK ProviderState) ProbComp) :=
  fun query => close setup seed scalar (RegistrationNativeProviderInterpreter.routed provider query)

/-- The local KEM callback retains its selected-getter route and executes the same provider, including every ordinary indexed decapsulation. -/
theorem kem_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before : State n KemSK ProviderState) :
    (localImpl setup wire route sign seed scalar provider selected (.inr (.inr query))).run before =
      (simulateQ (routedImpl setup seed scalar provider) (RegistrationNativeKemRouting.route selected query)).run before := by
  simp only [localImpl, RegistrationNativeProviderSource.localHandler, RegistrationNativePublicFrontend.liftLocal]
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeProviderInterpreter.handler (n := n) setup wire route sign provider ∘ₛ
      RegistrationNativePublicFrontend.liftRoutedKem = RegistrationNativeProviderInterpreter.routed provider := by
    funext request
    simp only [QueryImpl.apply_compose, RegistrationNativePublicFrontend.liftRoutedKem,
      simulateQ_spec_query, RegistrationNativeProviderInterpreter.handler]
  rw [same]
  rcases query with other | (pool | key)
  · simp only [RegistrationNativeKemRouting.route, simulateQ_spec_query, routedImpl]
  · simp only [RegistrationNativeKemRouting.route, simulateQ_spec_query, routedImpl]
  · cases selected <;> simp only [RegistrationNativeKemRouting.route, Bool.false_eq_true,
      ite_false, ite_true, simulateQ_spec_query, routedImpl]

/-- Source preparation returns the exact reference it records, retaining the complete provider frame. -/
theorem prepare_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (scalar : ScalarBytes) (provider : Provider KemSK ProviderState) (selected : Bool)
    (message : RegistrationNativeRelatedFamily.Message) (before : State n KemSK ProviderState) :
    (localImpl setup wire route sign seed scalar provider selected (.inl message)).run before =
      let root := RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message
      pure (root.map (fun _ => message),
        ({ before.1 with roots := Function.update before.1.roots message root }, before.2)) := by
  change simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    ((RegistrationNativeProviderInterpreter.handler setup wire route sign provider (.inl (.inl message))).run before) = _
  rw [RegistrationNativeProviderInterpreter.prepare_run]
  simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativeSourceRoot.handler,
    pure_bind, simulateQ_pure]

end BeaconcryptCore.Computational.RegistrationNativeProviderLocal

/--
info: 'BeaconcryptCore.Computational.RegistrationNativeProviderLocal.lower_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderLocal.lower_program
/--
info: 'BeaconcryptCore.Computational.RegistrationNativeProviderLocal.kem_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderLocal.kem_program
/--
info: 'BeaconcryptCore.Computational.RegistrationNativeProviderLocal.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderLocal.prepare_run

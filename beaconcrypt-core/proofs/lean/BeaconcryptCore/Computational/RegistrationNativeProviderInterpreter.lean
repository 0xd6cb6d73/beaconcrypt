-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun

/-! An additive reference interpreter delegates routed KEM operations to a separate pool/provider state. The provider cannot inspect the World, root memo or signing receipts. Its probability program is sampled by the shared World, retaining actual uniform-counter instrumentation. Root, authentication, publication and record callbacks keep their existing interpretation and the additional provider state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedRoot (RootSpec)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

abbrev Provider (KemSK ProviderState : Type) := QueryImpl (RegistrationNativePublicFrontend.RoutedKem KemSK)
  (StateT (PqxdhLiveKemBirth.Pool KemSK × ProviderState) ProbComp)

abbrev State (n : Nat) (KemSK ProviderState : Type) := RegistrationNativePublicInterpreter.State n KemSK × ProviderState
abbrev M (n : Nat) (KemSK ProviderState Value : Type) := StateT (State n KemSK ProviderState) (OracleComp RootSpec) Value

def withBase (work : RegistrationNativePublicInterpreter.M n KemSK Value) : M n KemSK ProviderState Value :=
  fun before => (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

/-- Every old reference callback retains the complete new provider frame before resuming its next operation. -/
theorem withBase_program {Index : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (RegistrationNativePublicInterpreter.M n KemSK))
    (work : OracleComp spec Value) (before : State n KemSK ProviderState) :
    (simulateQ (fun query => withBase (implementation query)) work).run before =
      (fun result => (result.1, (result.2, before.2))) <$> (simulateQ implementation work).run before.1 := by
  let embed : RegistrationNativePublicInterpreter.State n KemSK → State n KemSK ProviderState :=
    fun current => (current, before.2)
  simpa only [embed, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq implementation
      (fun query => withBase (implementation query)) embed (fun _ _ => rfl) work before.1).symm

noncomputable def routed (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) :
    M n KemSK ProviderState ((RegistrationNativePublicFrontend.RoutedKem KemSK).Range query) := fun before =>
  (fun result => (result.1.1,
    ({ before.1 with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
      simulateQ RegistrationNativePublicInterpreter.coins
        ((PqxdhRecordLiftWorld.sampled ((provider query).run (before.1.pool, before.2))).run before.1.world)

/-- KEM execution uses the current pool/provider and shared World sampler, retaining the entire root memo and signing log. -/
theorem routed_run (provider : Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) (before : State n KemSK ProviderState) :
    (routed provider query).run before =
      (fun result => (result.1.1,
        ({ before.1 with world := result.2, pool := result.1.2.1 }, result.1.2.2))) <$>
        simulateQ RegistrationNativePublicInterpreter.coins
          ((PqxdhRecordLiftWorld.sampled ((provider query).run (before.1.pool, before.2))).run before.1.world) := rfl

/-- Only routed KEM requests use the new provider. Every other callback is the original exact reference callback on its current state. -/
noncomputable def handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (M n KemSK ProviderState)
  | .inl (.inr (.inr query)) => routed provider query
  | query => withBase (RegistrationNativePublicInterpreter.handler setup wire route sign query)

/-- Preparation still reaches the root interface at its actual point; provider state and all non-memo fields remain retained. -/
theorem prepare_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) (message : RegistrationNativeRelatedFamily.Message)
    (before : State n KemSK ProviderState) :
    (handler setup wire route sign provider (.inl (.inl message))).run before = (do
      let root ← RootSpec.query (.inr (.derive message))
      pure (root.map (fun _ => message), ({ before.1 with roots := Function.update before.1.roots message root }, before.2))) := by
  change (fun result => (result.1, (result.2, before.2))) <$>
    (RegistrationNativePublicInterpreter.handler setup wire route sign (.inl (.inl message))).run before.1 = _
  rw [RegistrationNativePublicInterpreter.prepare_query]
  simp only [map_bind, map_pure]

noncomputable def run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : Provider KemSK ProviderState) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (frontend : RegistrationNativePublicFrontend.State source) (before : State n KemSK ProviderState) :=
  (simulateQ (handler setup wire route sign provider)
    (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
      serverKeyId bounds mode work frontend)).run before

end BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter.withBase_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter.withBase_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter.routed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter.routed_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderInterpreter.prepare_run

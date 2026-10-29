-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInstallRuntime

/-! The exact guarded typed kernel reassociates into its original frontend AST interpreted by one complete chronological runtime. Native owner preparation/completion cuts can therefore retain the same trace, thin state, cursor, Protocol control and private service state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationNativeSelectiveInstallKernel (State)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {ι KemSK ProviderState Reader Response Secret Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Runtime (n : Nat) (KemSK ProviderState Secret : Type) :=
  RegistrationNativeG2Trace.State × RegistrationNativeInstallRuntime.Runtime n KemSK ProviderState Secret

def runtime (before : State n KemSK ProviderState Secret source) : Runtime n KemSK ProviderState Secret :=
  (before.1, RegistrationNativeInstallRuntime.runtime before.2)

def attach (result : (Value × RegistrationNativePublicFrontend.State source) × Runtime n KemSK ProviderState Secret) :
    Value × State n KemSK ProviderState Secret source :=
  (result.1.1, (result.2.1, (RegistrationNativeInstallRuntime.attach (result.1, result.2.2)).2))

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp))
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

noncomputable def callback : QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
    (StateT (Runtime n KemSK ProviderState Secret) ProbComp) :=
  ((RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route).mapStateTBase
    RegistrationNativeG2Trace.handler).flattenStateT

private theorem state_map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The original actual guarded typed callback is its literal frontend AST with one complete chronological runtime. -/
theorem typed_source (selectedOwner selectedAccept : Nat) (query : TypedSpec.Domain)
    (before : State n KemSK ProviderState Secret source) :
    (RegistrationNativeSelectiveInstallKernel.typed setup checks wire sign seed scalar candidate provider service codec route
      selectedOwner selectedAccept query).run before =
      attach <$> (simulateQ (callback setup wire sign seed scalar candidate provider service codec route)
        ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar) query).run
          before.2.1.1.1.1)).run (runtime before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativeHiddenEnvironmentWorld.lower service codec route
      (RegistrationNativeSelectiveEntropyEffects.close setup wire sign seed scalar candidate provider
        (RegistrationNativeSelectiveInstallKernel.front
          (RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar))
          before.1 query))).run before.2 = _
  rw [RegistrationNativeInstallRuntime.frontend]
  simp only [RegistrationNativeSelectiveInstallKernel.front, StateT.run, simulateQ_map, state_map_apply, Functor.map_map]
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route)
    RegistrationNativeG2Trace.handler
    ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept (setup.dh.publicKey scalar) query).run
      before.2.1.1.1.1) before.1 (RegistrationNativeInstallRuntime.runtime before.2)
  simp only [StateT.run] at nested
  rw [nested]
  simp only [callback, Functor.map_map, runtime, RegistrationNativeInstallRuntime.attach,
    RegistrationNativeInstallRuntime.runtime, Prod.map_def, id_eq]
  rfl


/-- Every original native AST is interpreted after its same literal trace observer, retaining the full reached private runtime. -/
theorem program_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : Runtime n KemSK ProviderState Secret) :
    (fun result => ((result.1, result.2.1), result.2.2)) <$>
      (simulateQ (callback setup wire sign seed scalar candidate provider service codec route) work).run before =
      (simulateQ (RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route)
        ((simulateQ RegistrationNativeG2Trace.handler work).run before.1)).run before.2 := by
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route)
    RegistrationNativeG2Trace.handler work before.1 before.2
  simpa only [callback, Prod.mk.eta] using nested.symm

/-- The exact same runtime-supported result and trace remain possible in the original open chronological AST. -/
theorem open_support (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : Runtime n KemSK ProviderState Secret) (result : Value × Runtime n KemSK ProviderState Secret)
    (supported : result ∈ support ((simulateQ (callback setup wire sign seed scalar candidate provider service codec route) work).run before)) :
    (result.1, result.2.1) ∈ support ((simulateQ RegistrationNativeG2Trace.handler work).run before.1) := by
  have actual := Set.mem_image_of_mem (fun result => ((result.1, result.2.1), result.2.2)) supported
  rw [← support_map, program_source] at actual
  apply support_simulateQ_run'_subset
    (RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route) _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst actual

private theorem query_forget (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : Runtime n KemSK ProviderState Secret) :
    Prod.map id Prod.snd <$> (callback setup wire sign seed scalar candidate provider service codec route query).run before =
      (RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route query).run before.2 := by
  simp only [callback, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, RegistrationNativeG2Trace.handler,
    simulateQ_map, simulateQ_spec_query, StateT.run, StateT.mk, state_map_apply, Functor.map_map, Prod.map_def, id_eq, Prod.mk.eta, id_map']

/-- Erasing only chronology retains the exact original actual guarded execution and every private World poststate. -/
theorem forget_source (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : Runtime n KemSK ProviderState Secret) :
    Prod.map id Prod.snd <$> (simulateQ (callback setup wire sign seed scalar candidate provider service codec route) work).run before =
      (simulateQ (RegistrationNativeInstallRuntime.publicCallback setup wire sign seed scalar candidate provider service codec route) work).run before.2 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ Prod.snd
    (query_forget setup wire sign seed scalar candidate provider service codec route) work before

end BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.typed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.open_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.open_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.forget_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInstallRuntimeTrace.forget_source

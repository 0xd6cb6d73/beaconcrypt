-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
/-! Successful current native Init encoding retains the literal source serializer's vector. The joint native/platform state is packed without inspecting or discarding any private counter or allocator effect. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformNativeInitEncoder
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {KemSK Platform E Auxiliary A : Type} {source : RegistrationNativeMldsa.Source}
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))

noncomputable def writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E)
    (StateT (RegistrationNativeExperiment.State n KemSK source × Platform) ProbComp) :=
  fun query => pack (RegistrationNativePlatformExperiment.writer (RegistrationNativePlatformConcreteSource.writer reserve) query)

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value,before)) <$> work := by
  change (do let value ← work; pure (value,before)) = _
  rw [bind_pure_comp]
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem native_lift (implementation : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (AdapterRegistrationWriterRequestMonad.Spec E) A) :
    simulateQ (RegistrationNativePlatformExperiment.writer (n := n) (KemSK := KemSK) (source := source) implementation) work =
      StateT.lift (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
    apply StateT.ext
    intro before
    simp only [simulateQ_pure,StateT.run_pure,StateT.run_lift,pure_bind]
  | query_bind query next ih =>
    apply StateT.ext
    intro before
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformExperiment.writer,StateT.run_bind,StateT.run_lift,ih,
      bind_assoc,pure_bind]

/-- The actual native encoder is the same concrete writer with the entire native state carried unchanged. -/
theorem encoder_source (view : registration.InitView)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeExperiment.State n KemSK source × Platform) :
    (((RegistrationNativePlatformGenericBundle.encoderWith (writer reserve) view).run owners).run env).run before =
      (fun result => (((result.1,owners),env),(before.1,result.2))) <$>
        (simulateQ (RegistrationNativePlatformConcreteSource.writer reserve)
          (AdapterRegistrationWriterRequestExtraction.encodeInit
            (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
            (RegistrationNativePlatformWriter.initPacket view)).run).run before.2 := by
  unfold RegistrationNativePlatformGenericBundle.encoderWith
  simp only [StateT.run_lift,bind_pure_comp,StateT.run_map,Functor.map_map]
  rw [show writer (n := n) (KemSK := KemSK) (source := source) reserve =
      (fun query => pack (RegistrationNativePlatformExperiment.writer (RegistrationNativePlatformConcreteSource.writer reserve) query)) from rfl,
    ← RegistrationNativePlatformPackedState.simulate_pack,native_lift]
  simp only [StateT.run,pack,lift_apply,map_apply,Functor.map_map,Prod.map_def,id_eq]

/-- Any successful source-native Init vector has exact concrete bytes, including arbitrary prior private/platform state. -/
theorem encoder (view : registration.InitView)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeExperiment.State n KemSK source × Platform)
    (result : ((RustM (core.option.Option (alloc.vec.Vec U8)) × RegistrationNativeBeaconFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × (RegistrationNativeExperiment.State n KemSK source × Platform))
    (supported : result ∈ support ((((RegistrationNativePlatformGenericBundle.encoderWith (writer reserve) view).run owners).run env).run before))
    (bytes : alloc.vec.Vec U8) (returned : result.1.1.1 = .ok (.Some bytes)) :
    bytes = RegistrationNativeSourceWriterReadback.initVector view := by
  rw [encoder_source,support_map] at supported
  obtain ⟨actual,called,same⟩ := supported
  exact RegistrationNativePlatformPublicationConcrete.source_writer reserve view before.2 actual called bytes
    ((congrArg (fun output => output.1.1.1) same).trans returned)

end BeaconcryptCore.Computational.RegistrationNativePlatformNativeInitEncoder
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeInitEncoder.encoder_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeInitEncoder.encoder_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformNativeInitEncoder.encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformNativeInitEncoder.encoder

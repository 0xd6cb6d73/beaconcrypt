-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOwners
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete
open BeaconcryptCore.Refinement
variable {n : Nat} {KemSK Platform E : Type}

private theorem map_apply {S A B : Type} (f : A → B) (work : StateT S ProbComp A) (before : S) :
    (f <$> work) before = (fun result => (f result.1, result.2)) <$> work before := StateT.run_map f work before

/-- Every actual successful Init source writer returned the concrete source serializer's literal vector. -/
theorem source_writer (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.InitView) (before : Platform)
    (result : RustM (core.option.Option (alloc.vec.Vec U8)) × Platform)
    (supported : result ∈ support ((simulateQ (RegistrationNativePlatformConcreteSource.writer reserve)
      (AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run).run before))
    (bytes : alloc.vec.Vec U8) (returned : result.1 = .ok (.Some bytes)) :
    bytes = RegistrationNativeSourceWriterReadback.initVector view := by
  have encoded := congrFun (RegistrationNativePlatformConcreteSource.init_writer reserve view) before
  dsimp only [StateT.run] at supported
  rw [encoded] at supported
  rw [map_apply, support_map] at supported
  obtain ⟨allocation, _reserved, same⟩ := supported
  rcases allocation with ⟨allocation, after⟩
  cases allocation with
  | Err error =>
    have reply := congrArg Prod.fst same
    rw [returned] at reply
    cases reply
  | Ok value =>
    have reply := congrArg Prod.fst same
    rw [returned] at reply
    exact (Option.some.inj (RustM.ok.inj reply)).symm

/-- Public coin forwarding cannot change the concrete writer's successful returned vector or shared platform poststate. -/
theorem public_writer (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.InitView) (before : Platform)
    (result : RustM (core.option.Option (alloc.vec.Vec U8)) × Platform)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativePlatformPublicFrontend.writer (n := n) (KemSK := KemSK) (RegistrationNativePlatformConcreteSource.writer reserve))
      (AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run).run before))
    (bytes : alloc.vec.Vec U8) (returned : result.1 = .ok (.Some bytes)) :
    bytes = RegistrationNativeSourceWriterReadback.initVector view := by
  change result ∈ support ((simulateQ
    (RegistrationNativePlatformPublicFrontend.localCoin.mapStateTBase (RegistrationNativePlatformConcreteSource.writer reserve))
    (AdapterRegistrationWriterRequestExtraction.encodeInit
      (E := E) (m := AdapterRegistrationWriterRequestMonad.Program E)
      (RegistrationNativePlatformWriter.initPacket view)).run).run before) at supported
  rw [← QueryImpl.simulateQ_mapStateTBase_run] at supported
  exact source_writer reserve view before result
    (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ supported) bytes returned

variable {source : RegistrationNativeMldsa.Source} {Auxiliary : Type}

/-- The literal public bundle encoder retains the concrete source vector under the full owner/environment/platform state. -/
theorem encoder (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (view : registration.InitView) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (core.option.Option (alloc.vec.Vec U8)) × RegistrationNativeBeaconFrontend.State source) ×
      RegistrationWorldAgreementCompiler.EnvState Auxiliary) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformGenericBundle.encoderWith
      (RegistrationNativePlatformPublicFrontend.writer (n := n) (KemSK := KemSK) (RegistrationNativePlatformConcreteSource.writer reserve)) view).run owners).run env).run previous))
    (bytes : alloc.vec.Vec U8) (returned : result.1.1.1 = .ok (.Some bytes)) :
    bytes = RegistrationNativeSourceWriterReadback.initVector view := by
  simp only [RegistrationNativePlatformGenericBundle.encoderWith, StateT.run_lift, StateT.run_map,
    bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨actual, called, same⟩ := supported
  exact public_writer reserve view previous actual called bytes ((congrArg (fun output => output.1.1.1) same).trans returned)

/-- The actual concrete source vector and mathematical wire encoder have exactly the same bytes. -/
theorem init_encoding (view : registration.InitView) :
    RegistrationNativePlatformConcreteSource.wire.encodeInit view =
      .Some (TranscriptAuthParts.absSlice (RegistrationNativeSourceWriterReadback.initVector view)) := by
  exact RegistrationNativeConcreteCodec.init_bytes view

/-- Source serialization readback derives the packet directly; no caller-supplied codec property is used. -/
theorem decoded (view : registration.InitView) :
    RegistrationNativeWire.readInit RegistrationNativePlatformConcreteSource.wire
      (TranscriptAuthParts.absSlice (RegistrationNativeSourceWriterReadback.initVector view)) =
      some (RegistrationNativeWire.initPacket view) :=
  RegistrationNativePlatformConcreteSource.init_readback view _ (init_encoding view)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.source_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.source_writer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.public_writer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.public_writer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.encoder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.encoder

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.init_encoding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.init_encoding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.decoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete.decoded

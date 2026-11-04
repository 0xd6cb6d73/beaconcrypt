-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxProgram

/-! All original raw modes and their complete hidden-bit/fresh-message ledger execute through the current-runtime indexed joint-Ed client. Erasure restores the literal native dynamic-writer run with its original complete platform poststate. Ledger events remain executable without reconstructing a challenged Ed seed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityCtxMain (M Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned native)
open PqxdhDynamicIdentityPool (SourceState)
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before

variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "handler" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "target" => RegistrationNativePlatformIdentityCtxTyped.target setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

local notation "callback" => RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer


noncomputable def run (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    M n KemSK Platform source (Value × RegistrationNativeLedger.State) :=
  simulateQ handler (RegistrationNativeFullCompiler.compile setup.source.crypto
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) created.server.server.metadata.sender bounds mode work)

/-- The raw-CBOR compiler and original secrecy ledger retain every admitted callback, private bit/fresh value and actual native/P poststate. -/
theorem run_source (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : Full n KemSK Platform source) (owned : Owned setup.joint before) :
    Prod.map id native <$> (interpret setup.joint
      (run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work)).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work (native before).1).run (native before).2) := by
  rw [run, RegistrationNativePlatformIdentityCtxProgram.program_source setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer _ before owned]
  exact (congrFun (RegistrationNativePlatformPackedState.simulate_pack callback
    (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      created.server.server.metadata.sender bounds mode work)) (native before)).symm

/-- An original ledger-only event has its same complete raw-mode distribution in the executable indexed client, without inspecting private Ed seeds. -/
theorem run_event_source (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool)
    (before : Full n KemSK Platform source) (owned : Owned setup.joint before) :
    (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
      ((fun result => event (result.1.1, (result.1.2, ()))) <$>
        (run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work).run before.1)).run' before.2 =
      (fun result => event (result.1.1.1, (result.1.1.2, ()))) <$>
        ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work (native before).1).run (native before).2) := by
  have same := congrArg (fun distribution => (fun result => event (result.1.1, (result.1.2, ()))) <$> distribution)
    (run_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before owned)
  unfold RegistrationNativePlatformIdentityCtxMain.interpret at same
  simp only [StateT.run, simulateQ_map, StateT.run'_eq, map_apply, Functor.map_map,
    Prod.map, id_eq, native] at same ⊢
  exact same

/-- The exact same ledger event also retains the actual shared platform poststate in its joint source distribution. -/
theorem run_event_joint (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value Unit → Bool)
    (before : Full n KemSK Platform source) (owned : Owned setup.joint before) :
    (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation setup.joint)
      ((fun result => (event (result.1.1, (result.1.2, ())), result.2.2)) <$>
        (run setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work).run before.1)).run' before.2 =
      (fun result => (event (result.1.1.1, (result.1.1.2, ())), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryExperiment.run setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work (native before).1).run (native before).2) := by
  have same := congrArg (fun distribution => (fun result => (event (result.1.1, (result.1.2, ())), result.2.2)) <$> distribution)
    (run_source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode work before owned)
  unfold RegistrationNativePlatformIdentityCtxMain.interpret at same
  simp only [StateT.run, simulateQ_map, StateT.run'_eq, map_apply, Functor.map_map,
    Prod.map, id_eq, native] at same ⊢
  exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull.run_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull.run_event_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull.run_event_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull.run_event_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxFull.run_event_joint

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptAgreementObserver
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuthPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterConfiguredAccept
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
variable {n :Nat} {KemSK P A B R Error I :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)

private theorem lift_pure (value :A) :RegistrationNativePlatformPublicAdapterLeaves.lift (S:=Backend n KemSK)
    (pure value:RustT (StateT P ProbComp) A)=pure value :=by
  apply RustT.ext
  apply StateT.ext
  intro before
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_pure,StateT.run_lift,pure_bind,StateT.run_pure]

private theorem lift_bind (work :RustT (StateT P ProbComp) A) (next :A→RustT (StateT P ProbComp) B) :
    RegistrationNativePlatformPublicAdapterLeaves.lift (S:=Backend n KemSK) (work >>=next)=
      (RegistrationNativePlatformPublicAdapterLeaves.lift work >>=fun value=>RegistrationNativePlatformPublicAdapterLeaves.lift (next value)) :=by
  apply RustT.ext
  apply StateT.ext
  intro before
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_bind,StateT.run_lift,StateT.run_bind,bind_assoc]
  apply bind_congr
  intro result
  cases result <;>simp only [pure_bind,StateT.run_pure,StateT.run_lift]

variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable (containers :ContainerOperations (RustT (StateT P ProbComp)))

private theorem record_lift (self :beaconcrypt_public_wrapper.server.Server) (rng :R) (effect :agreement.AgreementEffect) :
    let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
    let :ContainerOperations (RustT (StateT P ProbComp)):=containers
    AdapterPublicServerAcceptBody.record (m:=PhysicalM) self rng effect=
      RegistrationNativePlatformPublicAdapterLeaves.lift (AdapterPublicServerAcceptBody.record (m:=StateT P ProbComp) self rng effect) :=by
  let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
  let :ContainerOperations (RustT (StateT P ProbComp)):=containers
  dsimp only
  cases effect <;>try exact (lift_pure _).symm
  case ServerComplete completed=>
    rw [AdapterPublicServerToken.record,AdapterPublicServerToken.record,lift_bind]
    apply bind_congr
    rintro ⟨inserted,history⟩
    exact (lift_pure _).symm

variable [original :CryptoOperations (RustT ProbComp)]
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
variable (generator :rand_core.TryCryptoRng R Error)
variable (model :AdapterPublicAgreementPrimitiveModel.Model (m:=ProbComp) generator setup checks view)
variable (coins :QueryImpl unifSpec (StateT P ProbComp))

def install (receipt :AdapterPublicServerAgreementReceipt.Receipt R) (before :Backend n KemSK) :Backend n KemSK :=
  match receipt with
  | .ok value=>RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.install view value.2 before
  | .fail _ | .div=>before

omit platform [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem capture_auxiliary (keys :AdapterPublicAgreementFields.Keys) (work :OracleComp RegistrationAgreementExecutor.Spec A)
    (rng :R) (before :Backend n KemSK) (auxiliary :RegistrationServerRoleBackend.State) (previous :P) :
    ((RegistrationNativePlatformPublicAdapterAcceptReceipt.capture coins generator keys work rng).run {before with auxiliary:=auxiliary}).run previous=
      (fun result=>((result.1.1,{result.1.2 with auxiliary:=auxiliary}),result.2)) <$>
        ((RegistrationNativePlatformPublicAdapterAcceptReceipt.capture coins generator keys work rng).run before).run previous :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptReceipt.capture
  rw [RegistrationNativePlatformPublicAdapterCrypto.captured_source]
  exact RegistrationNativePlatformPublicAdapterAcceptObserver.primitive_auxiliary coins _ before auxiliary previous

theorem program_auxiliary (keys :AdapterPublicAgreementFields.Keys) (self :beaconcrypt_public_wrapper.server.Server)
    (work :OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng :R)
    (before :Backend n KemSK) (auxiliary :RegistrationServerRoleBackend.State) (previous :P) :
    ((RegistrationNativePlatformPublicAdapterAcceptReceipt.program containers coins generator keys self work rng).run {before with auxiliary:=auxiliary}).run previous=
      (fun result=>((result.1.1,{result.1.2 with auxiliary:=auxiliary}),result.2)) <$>
        ((RegistrationNativePlatformPublicAdapterAcceptReceipt.program containers coins generator keys self work rng).run before).run previous :=by
  unfold RegistrationNativePlatformPublicAdapterAcceptReceipt.program
  simp only [StateT.run_bind,StateT.run_pure,map_pure,map_bind]
  rw [capture_auxiliary (generator:=generator) (coins:=coins) keys work rng before auxiliary previous,bind_map_left]
  apply bind_congr
  rintro ⟨⟨receipt,current⟩,post⟩
  simp only [StateT.run_lift,bind_pure_comp]
  simp only [StateT.run_map,Functor.map_map]

theorem installed_program (keys :AdapterPublicAgreementFields.Keys) (self :beaconcrypt_public_wrapper.server.Server)
    (work :OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng :R)
    (before :Backend n KemSK) (auxiliary :RegistrationServerRoleBackend.State) (previous :P) :
    (fun result=>((result.1.1.2,install view result.1.1.1 result.1.2),result.2)) <$>
      ((RegistrationNativePlatformPublicAdapterAcceptReceipt.program containers coins generator keys self work rng).run {before with auxiliary:=auxiliary}).run previous=
    (fun result=>((result.1.1.2,install view result.1.1.1 {result.1.2 with auxiliary:=auxiliary}),result.2)) <$>
      ((RegistrationNativePlatformPublicAdapterAcceptReceipt.program containers coins generator keys self work rng).run before).run previous :=by
  rw [program_auxiliary (containers:=containers) (generator:=generator) (coins:=coins) keys self work rng before auxiliary previous,Functor.map_map]

noncomputable def executeRecorded (keys :AdapterPublicAgreementFields.Keys) (self :beaconcrypt_public_wrapper.server.Server)
    (control :pqxdh.ServerState) (authenticated :registration.AuthenticatedInit) (rng :R) :RustT PhysicalM (AdapterPublicServerAgreementReceipt.Word R) :=
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
  do
    let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control .Fresh authenticated)
    let (effect,after)←beaconcrypt_public_request.pqxdh.execute_agreement (m:=RustT PhysicalM) generator phase keys rng
    AdapterPublicServerAcceptBody.record (m:=PhysicalM) self after effect

include model in
theorem execute_recorded (keys :AdapterPublicAgreementFields.Keys) (self :beaconcrypt_public_wrapper.server.Server)
    (control :pqxdh.ServerState) (authenticated :registration.AuthenticatedInit) (rng :R) (before :Backend n KemSK)
    (empty :before.auxiliary=RegistrationServerRoleBackend.empty) (previous :P) :
    ((executeRecorded containers view generator coins keys self control authenticated rng).run.run before).run previous=
      (fun result=>((result.1.1.2,install view result.1.1.1 result.1.2),result.2)) <$>
        ((RegistrationNativePlatformPublicAdapterAcceptReceipt.program containers coins generator keys self
          (RegistrationAgreementExecutor.server control .Fresh authenticated) rng).run before).run previous :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
  unfold executeRecorded
  have traced:=RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.execute_trace (n:=n) view generator coins keys control .Fresh authenticated rng
  dsimp only at traced
  rw [←bind_assoc,traced]
  simp only [RustT.run_bind,StateT.run_bind]
  rw [RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.captured setup checks view generator model coins keys
    (RegistrationAgreementExecutor.server control .Fresh authenticated) rng before empty previous]
  unfold RegistrationNativePlatformPublicAdapterAcceptReceipt.program
  simp only [StateT.run_bind,map_bind,bind_map_left,StateT.run_pure,map_pure,bind_assoc]
  apply bind_congr
  rintro ⟨⟨receipt,current⟩,post⟩
  cases receipt with
  | fail error | div=>simp only [RegistrationNativePlatformPublicAdapterAcceptReceipt.replay,StateT.run_lift,
      StateT.run_pure,pure_bind,install]
  | ok value=>
    rcases value with ⟨⟨effect,journal⟩,capture⟩
    cases effect with
    | fail error | div=>simp only [RegistrationNativePlatformPublicAdapterAcceptReceipt.replay,RustT.run_bind,
        RustT.run_liftRust,pure_bind,StateT.run_lift,StateT.run_pure,install]
    | ok effect=>
      dsimp only
      simp only [RustT.run_liftRust,pure_bind,RustT.run_pure,StateT.run_pure]
      rw [record_lift]
      simp only [RegistrationNativePlatformPublicAdapterAcceptReceipt.replay,RustT.run_bind,RustT.run_liftRust,
        pure_bind,RegistrationNativePlatformPublicAdapterLeaves.lift,StateT.run_lift,bind_pure_comp,install,
        RegistrationNativePlatformPublicAdapterAcceptAgreementObserver.install]
      simp only [StateT.run_map,Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore

/-- info: '_private.BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.0.BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.record_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.record_lift

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.capture_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.capture_auxiliary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.execute_recorded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.execute_recorded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.program_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.program_auxiliary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.installed_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.installed_program

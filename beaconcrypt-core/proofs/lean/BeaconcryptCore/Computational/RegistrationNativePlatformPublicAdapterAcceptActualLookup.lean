-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualSourceCore
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
variable {n :Nat} {KemSK P R Error I :Type} {base :OracleSpec I} {mlSource :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [original :CryptoOperations (RustT ProbComp)]
variable (containers :ContainerOperations (RustT (StateT P ProbComp)))
variable (setup :PqxdhServerAuthExperiment.Setup base KemSK) (checks :PqxdhServerAuthExperiment.Checks)
variable (view :AdapterPublicWrapperState.MaterialView mlSource KemSK)
variable (generator :rand_core.TryCryptoRng R Error)
variable (model :AdapterPublicAgreementPrimitiveModel.Model (m:=ProbComp) generator setup checks view)
variable (coins :QueryImpl unifSpec (StateT P ProbComp))
local notation "PhysicalM"=>StateT (Backend n KemSK) (StateT P ProbComp)

def mark (receipt :AdapterPublicServerReservationReceipt.Receipt R) (before :Backend n KemSK) :Backend n KemSK :=
  match receipt with
  | none=>before
  | some capture=>RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.install view capture
      {before with auxiliary:=RegistrationServerRoleBackend.empty}

omit ed original in
theorem reserve_run (history :AdapterPublicWrapperStorage.ReplaySet) (before :Backend n KemSK) (previous :P) :
    (let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
     ((AdapterPublicServerAcceptBody.setReserve (m:=PhysicalM) history).run.run before).run previous)=
      (fun result=>((result.1,RegistrationNativePlatformPublicAdapterAcceptObserver.reserved before result.1),result.2)) <$>
        (let :ContainerOperations (RustT (StateT P ProbComp)):=containers
         ((AdapterPublicServerAcceptBody.setReserve (m:=StateT P ProbComp) history).run.run previous)) :=by
  let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
  let :ContainerOperations (RustT (StateT P ProbComp)):=containers
  dsimp only
  change ((RegistrationNativePlatformPublicAdapterAcceptObserver.observe RegistrationNativePlatformPublicAdapterAcceptObserver.reserved
    (RegistrationNativePlatformPublicAdapterLeaves.lift (AdapterPublicServerAcceptBody.setReserve (m:=StateT P ProbComp) history))).run.run before).run previous=_
  rw [RegistrationNativePlatformPublicAdapterAcceptObserver.observe_run]
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,StateT.run_lift,bind_pure_comp,StateT.run_map,Functor.map_map]

include model in
theorem reservation (self :beaconcrypt_public_wrapper.server.Server) (control :pqxdh.ServerState)
    (authenticated :registration.AuthenticatedInit) (rng :R) (before :Backend n KemSK) (previous :P) :
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
     let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
     (((do let phase←AdapterRecordRequestMonad.liftRust (agreement.begin_server_agreement control .Fresh authenticated)
           AdapterPublicServerAcceptBody.reserved (m:=PhysicalM) generator self rng phase).run.run before).run previous))=
      (fun result=>((result.1.1.2,mark view result.1.1.1 result.1.2),result.2)) <$>
        ((RegistrationNativePlatformPublicAdapterAcceptLookup.reservation containers coins generator self control authenticated rng).run before).run previous :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
  dsimp only
  obtain ⟨phase,started⟩:=AdapterPublicServerReplayPrefix.begin_fresh control authenticated
  rw [started]
  simp only [RustT.run_bind,RustT.run_liftRust,pure_bind]
  unfold AdapterPublicServerAcceptBody.reserved RegistrationNativePlatformPublicAdapterAcceptLookup.reservation
  simp only [RustT.run_bind,StateT.run_bind,map_bind,StateT.run_lift,bind_pure_comp]
  rw [reserve_run containers self.consumed_registrations before previous,bind_map_left]
  simp only [StateT.run_map,bind_map_left]
  apply bind_congr
  rintro ⟨result,post⟩
  cases result with
  | fail error | div=>simp only [StateT.run_pure,map_pure,mark,RegistrationNativePlatformPublicAdapterAcceptObserver.reserved]
  | ok allocated=>
    rcases allocated with ⟨allocation,history⟩
    cases allocation with
    | Err failed=>simp only [StateT.run_pure,RustT.run_pure,map_pure,mark,RegistrationNativePlatformPublicAdapterAcceptObserver.reserved]
    | Ok unitValue=>
      dsimp only
      have getter:beaconcrypt_public_request.server.Server.identity_sk (m:=RustT PhysicalM)
          {self with consumed_registrations:=history}=pure (platform.arcView self.identity).identity_key.secret_key :=by
        change (do
          let identity←(AdapterRecordRequestMonad.liftRust (.ok (platform.arcView self.identity)):RustT PhysicalM _)
          AdapterRecordRequestMonad.liftRust (.ok identity.identity_key.secret_key))=_
        apply RustT.ext
        simp only [RustT.run_bind,RustT.run_liftRust,RustT.run_pure,pure_bind]
      rw [getter,pure_bind]
      have called:=RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.execute_recorded containers setup checks view generator model coins
        (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
        {self with consumed_registrations:=history} control authenticated rng
        {before with auxiliary:=RegistrationServerRoleBackend.empty} rfl post
      have moved:=RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.installed_program containers view generator coins
        (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
        {self with consumed_registrations:=history} (RegistrationAgreementExecutor.server control .Fresh authenticated) rng
        before RegistrationServerRoleBackend.empty post
      have law:=called.trans moved
      simpa only [RegistrationNativePlatformPublicAdapterAcceptActualSourceCore.executeRecorded,started,RustT.run_bind,
        RustT.run_liftRust,pure_bind,StateT.run_map,Functor.map_map,RegistrationNativePlatformPublicAdapterAcceptObserver.reserved,mark,AdapterPublicAgreementServerNative.keys] using law

omit ed original in
theorem member_run (history :AdapterPublicWrapperStorage.ReplaySet) (identifier :Std.Array U8 64#usize)
    (before :Backend n KemSK) (previous :P) :
    (let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
     ((AdapterPublicServerReplayPrefix.contains (m:=PhysicalM) history identifier).run.run before).run previous)=
      (fun result=>((result.1,before),result.2)) <$>
        (let :ContainerOperations (RustT (StateT P ProbComp)):=containers
         ((AdapterPublicServerReplayPrefix.contains (m:=StateT P ProbComp) history identifier).run.run previous)) :=by
  let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
  let :ContainerOperations (RustT (StateT P ProbComp)):=containers
  dsimp only
  change ((RegistrationNativePlatformPublicAdapterLeaves.lift
    (AdapterPublicServerReplayPrefix.contains (m:=StateT P ProbComp) history identifier)).run.run before).run previous=_
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,StateT.run_lift,bind_pure_comp,StateT.run_map]

include model in
theorem lookup (self :beaconcrypt_public_wrapper.server.Server) (pending :peer.RegistrationLookup)
    (rng :R) (before :Backend n KemSK) (previous :P) :
    (let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
     let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
     ((AdapterPublicServerAcceptBody.acceptLookup (m:=PhysicalM) generator self pending rng).run.run before).run previous)=
      (fun result=>((result.1.1.2,mark view result.1.1.1 result.1.2),result.2)) <$>
        ((RegistrationNativePlatformPublicAdapterAcceptLookup.lookup containers coins generator self pending rng).run before).run previous :=by
  let :CryptoOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography coins view
  let :ContainerOperations (RustT PhysicalM):=RegistrationNativePlatformPublicAdapterAcceptObserver.containers containers
  dsimp only
  unfold AdapterPublicServerAcceptBody.acceptLookup RegistrationNativePlatformPublicAdapterAcceptLookup.lookup
  rw [AdapterPublicServerLookupReceipt.requested]
  simp only [pqxdh.RegistrationId.as_bytes]
  change (((do
    let consumed←AdapterPublicServerReplayPrefix.contains (m:=PhysicalM) self.consumed_registrations
      (AdapterPublicServerLookupReceipt.identifier pending).bytes
    let effect←AdapterRecordRequestMonad.liftRust (pending.resume consumed)
    match effect with
    | .Rejected _=>pure (core.option.Option.None,self,rng)
    | _=>AdapterPublicServerAcceptBody.reserved (m:=PhysicalM) generator self rng effect).run.run before).run previous)=_
  simp only [RustT.run_bind,StateT.run_bind,map_bind,StateT.run_lift,bind_pure_comp]
  rw [member_run containers self.consumed_registrations (AdapterPublicServerLookupReceipt.identifier pending).bytes before previous,bind_map_left]
  simp only [StateT.run_map,bind_map_left]
  apply bind_congr
  rintro ⟨result,post⟩
  cases result with
  | fail error | div=>simp only [StateT.run_pure,map_pure,mark]
  | ok present=>cases present with
    | true=>simp only [PeerOwnership.registration_lookup_consumed,RustT.run_liftRust,pure_bind,
        RustT.run_pure,StateT.run_pure,map_pure,mark]
    | false=>
      dsimp only
      rw [PeerOwnership.registration_lookup_fresh]
      obtain ⟨phase,started⟩:=AdapterPublicServerReplayPrefix.begin_fresh pending.control pending.authenticated
      have law:=reservation containers setup checks view generator model coins self pending.control pending.authenticated rng before post
      simpa only [started,RustT.run_bind,RustT.run_liftRust,pure_bind] using law

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.reserve_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.reserve_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.reservation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.reservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.member_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.member_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptActualLookup.lookup

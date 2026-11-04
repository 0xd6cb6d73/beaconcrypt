-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerLookupReceipt
/-! The actual source replay lookup and fallible reservation prefix share the same persistent source container leaves with the backend agreement receipt. Opaque returned sets, Rust failures, source Self/RNG and the complete backend/platform state remain exact. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptLookup
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterLeaves (containerOperations)
variable {n : Nat} {KemSK P A B : Type} {source : RegistrationNativeMldsa.Source}
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "NativeM"=>StateT Native (StateT P ProbComp)
local notation "BackendM"=>StateT (Backend n KemSK) (StateT P ProbComp)
private theorem pure_source (value : A) (before : Native) :
    Prod.map id backend <$> (pure value : NativeM A).run before=(pure value : BackendM A).run (backend before) := by
  simp only [StateT.run_pure,map_pure]
  rfl
private theorem lift_source (work : StateT P ProbComp A) (before : Native) :
    Prod.map id backend <$> (StateT.lift work : NativeM A).run before=
      (StateT.lift work : BackendM A).run (backend before) := by
  simp only [StateT.run_lift,bind_pure_comp,Functor.map_map]
  rfl
private theorem bind_source (first : NativeM A) (other : BackendM A)
    (next : A→NativeM B) (later : A→BackendM B)
    (firstSource : ∀before,Prod.map id backend <$>first.run before=other.run (backend before))
    (nextSource : ∀value before,Prod.map id backend <$>(next value).run before=(later value).run (backend before))
    (before : Native) :
    Prod.map id backend <$>(first >>=next).run before=(other >>=later).run (backend before) := by
  rw [StateT.run_bind,map_bind,StateT.run_bind,←firstSource before,bind_map_left]
  apply bind_congr
  rintro ⟨value,current⟩
  exact nextSource value current
private theorem map_source (first : NativeM A) (other : BackendM A) (observe : A→B)
    (same : ∀before,Prod.map id backend <$>first.run before=other.run (backend before)) (before : Native) :
    Prod.map id backend <$>(observe <$>first).run before=(observe <$>other).run (backend before) := by
  have result:=congrArg (fun work=>(Prod.map observe id) <$>work) (same before)
  simp only [StateT.run_map,Functor.map_map,Prod.map,id_eq] at result ⊢
  exact result
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [original : CryptoOperations (RustT ProbComp)]
variable (containers : ContainerOperations (RustT (StateT P ProbComp)))

noncomputable def reservation {R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (rng : R) :
    StateT (Backend n KemSK) (StateT P ProbComp)
      (AdapterPublicServerReservationReceipt.Receipt R×RustM (AdapterPublicServerAgreementReceipt.Word R)) :=
  let : ContainerOperations (RustT (StateT P ProbComp)):=containers
  do
    let allocated←StateT.lift (AdapterPublicServerAcceptBody.setReserve (m:=StateT P ProbComp) self.consumed_registrations).run
    match allocated with
    | .fail error=>pure (none,.fail error)
    | .div=>pure (none,.div)
    | .ok (allocation,history)=>
      match allocation with
      | .Err _=>pure (none,.ok (.None,{self with consumed_registrations:=history},rng))
      | .Ok _=>
        (fun result=>(some result.1,result.2)) <$>
          (RegistrationNativePlatformPublicAdapterAcceptReceipt.program containers coins generator
            (AdapterPublicAgreementServerNative.keys (platform.arcView self.identity).identity_key.secret_key)
            {self with consumed_registrations:=history} (RegistrationAgreementExecutor.server control .Fresh authenticated) rng)

theorem reservation_source {R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (control : pqxdh.ServerState) (authenticated : registration.AuthenticatedInit) (rng : R) (before : Native) :
    let : ContainerOperations (RustT NativeM):=containerOperations containers
    Prod.map id backend <$>
      (AdapterPublicServerReservationReceipt.program coins generator self control authenticated rng).run before=
      (reservation containers coins generator self control authenticated rng).run (backend before) := by
  let : ContainerOperations (RustT NativeM):=containerOperations containers
  unfold AdapterPublicServerReservationReceipt.program reservation
  dsimp only
  apply bind_source
  · intro current
    exact lift_source _ current
  · intro result current
    cases result with
    | fail error | div=>exact pure_source _ _
    | ok allocated=>
      rcases allocated with ⟨allocation,history⟩
      cases allocation with
      | Err error=>exact pure_source _ _
      | Ok value=>
        apply map_source
        intro actual
        exact RegistrationNativePlatformPublicAdapterAcceptReceipt.program_source containers coins generator _ _ _ rng actual

noncomputable def lookup {R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.RegistrationLookup) (rng : R) :
    StateT (Backend n KemSK) (StateT P ProbComp)
      (AdapterPublicServerReservationReceipt.Receipt R×RustM (AdapterPublicServerAgreementReceipt.Word R)) :=
  let : ContainerOperations (RustT (StateT P ProbComp)):=containers
  do
    let observed←StateT.lift (AdapterPublicServerReplayPrefix.contains (m:=StateT P ProbComp)
      self.consumed_registrations (AdapterPublicServerLookupReceipt.identifier pending).bytes).run
    match observed with
    | .fail error=>pure (none,.fail error)
    | .div=>pure (none,.div)
    | .ok true=>pure (none,.ok (.None,self,rng))
    | .ok false=>reservation containers coins generator self pending.control pending.authenticated rng

theorem lookup_source {R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (self : beaconcrypt_public_wrapper.server.Server)
    (pending : peer.RegistrationLookup) (rng : R) (before : Native) :
    let : ContainerOperations (RustT NativeM):=containerOperations containers
    Prod.map id backend <$>
      (AdapterPublicServerLookupReceipt.program coins generator self pending rng).run before=
      (lookup containers coins generator self pending rng).run (backend before) := by
  let : ContainerOperations (RustT NativeM):=containerOperations containers
  unfold AdapterPublicServerLookupReceipt.program lookup
  dsimp only
  apply bind_source
  · intro current
    exact lift_source _ current
  · intro result current
    cases result with
    | fail error | div=>exact pure_source _ _
    | ok present=>cases present with
      | true=>exact pure_source _ _
      | false=>exact reservation_source containers coins generator self pending.control pending.authenticated rng current

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptLookup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptLookup.reservation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptLookup.reservation_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptLookup.lookup_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptLookup.lookup_source

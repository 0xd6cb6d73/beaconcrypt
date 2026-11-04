-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCryptoPlatform
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
/-! Acceptance observes only actual source leaf results. Successful replay reservation resets the local ephemeral observation before agreement starts, and actual key generation records the returned opaque pair's private view. All source results, RNG, container histories, reached primitive effects and persistent platform state are retained. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend)
private theorem map_apply {State X Y :Type} {m :Type→Type} [Monad m] [LawfulMonad m]
    (function :X→Y) (work :StateT State m X) (before :State) :
    (function <$>work) before=(fun result=>(function result.1,result.2)) <$>work before :=
  StateT.run_map _ _ _

variable {n :Nat} {KemSK P A R Error Collection :Type} {mlSource :RegistrationNativeMldsa.Source}

noncomputable def observe (mark :Backend n KemSK→RustM A→Backend n KemSK)
    (work :RustT (StateT (Backend n KemSK) (StateT P ProbComp)) A) :
    RustT (StateT (Backend n KemSK) (StateT P ProbComp)) A :=
  ⟨fun before=>(fun result=>(result.1,mark result.2 result.1)) <$>work.run.run before⟩

theorem observe_run (mark :Backend n KemSK→RustM A→Backend n KemSK)
    (work :RustT (StateT (Backend n KemSK) (StateT P ProbComp)) A) (before :Backend n KemSK) (previous :P) :
    ((observe mark work).run.run before).run previous=
      (fun result=>((result.1.1,mark result.1.2 result.1.1),result.2)) <$> (work.run.run before).run previous :=by
  change ((fun result=>(result.1,mark result.2 result.1)) <$>work.run.run before).run previous=_
  exact StateT.run_map _ _ _

 theorem primitive_auxiliary (coins :QueryImpl unifSpec (StateT P ProbComp)) (work :RustT ProbComp A)
    (before :Backend n KemSK) (auxiliary :RegistrationServerRoleBackend.State) (previous :P) :
    ((AdapterPublicAgreementOracleInterpretation.transform coins (RegistrationNativePlatformPublicAdapterCrypto.transform work)).run.run
      {before with auxiliary:=auxiliary}).run previous=
      (fun result=>((result.1.1,{result.1.2 with auxiliary:=auxiliary}),result.2)) <$>
        ((AdapterPublicAgreementOracleInterpretation.transform coins (RegistrationNativePlatformPublicAdapterCrypto.transform work)).run.run before).run previous :=by
  simp only [AdapterPublicAgreementOracleInterpretation.transform,RegistrationNativePlatformPublicAdapterCrypto.transform,
    RegistrationNativePlatformPublicAdapterCrypto.world,RegistrationNativePlatformInterpret.state,StateT.run,simulateQ_map]
  simp only [map_apply,Functor.map_map]

variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations]

def generated (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (before :Backend n KemSK)
    (result :RustM (core.result.Result beaconcrypt_crypto.crypto_kx.KeyPair ed.Error×R)) :Backend n KemSK :=
  match result with
  | .ok (.Ok pair,_)=>{before with auxiliary:=⟨some (view.kxSecret pair.secret_key)⟩}
  | .ok (.Err _,_)=>{before with auxiliary:=⟨none⟩}
  | .fail _ | .div=>before

def reserved (before :Backend n KemSK)
    (result :RustM (core.result.Result Unit platform.ReserveError×Collection)) :Backend n KemSK :=
  match result with
  | .ok (.Ok _,_)=>{before with auxiliary:=RegistrationServerRoleBackend.empty}
  | .ok (.Err _,_) | .fail _ | .div=>before

variable [PublicWrapperPlatform.Allocator]
variable [original :CryptoOperations (RustT ProbComp)]

@[instance_reducible] noncomputable def cryptography (coins :QueryImpl unifSpec (StateT P ProbComp))
    (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) :
    CryptoOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
  let previous:=RegistrationNativePlatformPublicAdapterCryptoPlatform.operations (n:=n) coins original
  {previous with kxGenerate:=fun generator rng=>observe (generated view) (previous.kxGenerate generator rng)}

@[instance_reducible] noncomputable def containers
    (original :ContainerOperations (RustT (StateT P ProbComp))) :
    ContainerOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))) :=
  let previous:=RegistrationNativePlatformPublicAdapterLeaves.containerOperations (S:=Backend n KemSK) original
  {previous with setReserve:=fun eq hash build allocate collection capacity=>observe reserved (previous.setReserve eq hash build allocate collection capacity)}

omit platform [PublicWrapperPlatform.Allocator] original in
theorem generated_failure (view :AdapterPublicWrapperState.MaterialView mlSource KemSK) (before :Backend n KemSK) (error :Aeneas.Std.Error) :
    generated (R:=R) view before (.fail error)=before ∧generated (R:=R) view before .div=before :=⟨rfl,rfl⟩

omit material ed [PublicWrapperPlatform.Allocator] original in
theorem reserved_failure (before :Backend n KemSK) (error :Aeneas.Std.Error) (failed :platform.ReserveError) (history :Collection) :
    reserved before (.ok (.Err failed,history))=before ∧
    reserved (Collection:=Collection) before (.fail error)=before ∧reserved (Collection:=Collection) before .div=before :=⟨rfl,rfl,rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.observe_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.observe_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.primitive_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.primitive_auxiliary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.cryptography

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.containers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.containers

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.generated_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.generated_failure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.reserved_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptObserver.reserved_failure

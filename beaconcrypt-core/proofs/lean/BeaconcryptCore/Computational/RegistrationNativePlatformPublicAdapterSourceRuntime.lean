-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterStore
/-! Actual adaptive source execution keeps returned objects only on normal Rust returns. Failure and divergence stop the source continuation while retaining the exact terminal primitive/platform state. No replacement source object is constructed. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterStore (Store)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R Platform A B : Type}

structure Objects (R : Type) where
  server : beaconcrypt_public_wrapper.server.Server
  beacons : Nat →Option beaconcrypt_public_wrapper.beacon.Beacon
  tokens : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput
  rng : R
  nextSession : Nat
  nextOwner : Nat

def objects (before : Store n KemSK R Platform) : Objects R :=
  ⟨before.server,before.beacons,before.tokens,before.rng,before.nextSession,before.nextOwner⟩

def join (before : Objects R) (backend : Backend n KemSK ×Platform) : Store n KemSK R Platform :=
  ⟨before.server,before.beacons,before.tokens,before.rng,before.nextSession,before.nextOwner,backend⟩

theorem join_objects (before : Store n KemSK R Platform) : join (objects before) before.backend=before := rfl

abbrev M (n : Nat) (KemSK R Platform : Type) :=
  StateT (Objects R) (RustT (StateT (Backend n KemSK ×Platform) ProbComp))

def run (work : M n KemSK R Platform A) (before : Store n KemSK R Platform) :
    ProbComp (RustM (A ×Objects R) ×(Backend n KemSK ×Platform)) :=
  (work.run (objects before)).run.run before.backend

def embed (result : A ×Store n KemSK R Platform) :
    RustM (A ×Objects R) ×(Backend n KemSK ×Platform) :=
  (.ok (result.1,objects result.2),result.2.backend)

noncomputable def raw (work : Store n KemSK R Platform →
    ProbComp (RustM (A ×Store n KemSK R Platform) ×(Backend n KemSK ×Platform))) : M n KemSK R Platform A :=
  fun before=>⟨fun backend=>(fun result=>(Prod.map id objects <$>result.1,result.2)) <$>work (join before backend)⟩

theorem run_raw (work : Store n KemSK R Platform →
    ProbComp (RustM (A ×Store n KemSK R Platform) ×(Backend n KemSK ×Platform)))
    (before : Store n KemSK R Platform) :
    run (raw work) before=(fun result=>(Prod.map id objects <$>result.1,result.2)) <$>work before := by
  change (fun result=>(Prod.map id objects <$>result.1,result.2)) <$>work (join (objects before) before.backend)=_
  rw [join_objects]

theorem run_pure (value : A) (before : Store n KemSK R Platform) :
    run (pure value : M n KemSK R Platform A) before=pure (embed (value,before)) := rfl

theorem run_bind (work : M n KemSK R Platform A) (next : A →M n KemSK R Platform B)
    (before : Store n KemSK R Platform) :
    run (work >>=next) before=(do
      let result ←run work before
      match result.1 with
      | .ok (value,after)=>run (next value) (join after result.2)
      | .fail error=>pure (.fail error,result.2)
      | .div=>pure (.div,result.2)) := by
  change ((work.run (objects before) >>=fun result=>((next result.1).run result.2)).run.run before.backend)=_
  rw [RustT.run_bind,StateT.run_bind]
  apply bind_congr
  rintro ⟨result,backend⟩
  cases result with
  | fail error | div=>rfl
  | ok pair=>rfl

theorem program {N I : Type} {spec : OracleSpec I}
    (model : QueryImpl spec (StateT N ProbComp))
    (source : QueryImpl spec (M n KemSK R Platform)) (physical : N →Store n KemSK R Platform)
    (queries : ∀query current,(fun result=>embed (result.1,physical result.2)) <$> (model query).run current=run (source query) (physical current))
    (work : OracleComp spec A) (before : N) :
    (fun result=>embed (result.1,physical result.2)) <$> (simulateQ model work).run before=run (simulateQ source work) (physical before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,map_pure,run_pure]
  | query_bind query next ih=>
    rw [simulateQ_bind,simulateQ_bind,simulateQ_spec_query,simulateQ_spec_query,StateT.run_bind,run_bind,map_bind]
    rw [←queries query before,bind_map_left]
    apply bind_congr
    rintro ⟨reply,after⟩
    change (fun result=>embed (result.1,physical result.2)) <$> (simulateQ model (next reply)).run after=
      run (simulateQ source (next reply)) (join (objects (physical after)) (physical after).backend)
    rw [join_objects]
    exact ih reply after

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.join_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.join_objects
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.run_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.run_raw
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.run_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.run_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime.program

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLeaves
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementReceipt
import BeaconcryptCore.Refinement.AdapterPublicServerToken
/-! The actual instrumented Server agreement and replay insertion execute on the retained physical backend. The same private source capture and query journal, returned SDK Self/RNG and every Rust outcome remain jointly visible to the source store. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformSdkReification (Backend backend)
open RegistrationNativePlatformPublicAdapterLeaves (containerOperations)
variable {S P A B : Type}

private theorem lift_pure (value : A) : RegistrationNativePlatformPublicAdapterLeaves.lift (S:=S) (pure value : RustT (StateT P ProbComp) A)=pure value := by
  apply RustT.ext
  apply StateT.ext
  intro before
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_pure,StateT.run_lift,pure_bind,StateT.run_pure]

private theorem lift_bind (work : RustT (StateT P ProbComp) A) (next : A→RustT (StateT P ProbComp) B) :
    RegistrationNativePlatformPublicAdapterLeaves.lift (S:=S) (work >>=next)=(RegistrationNativePlatformPublicAdapterLeaves.lift work >>=fun value=>RegistrationNativePlatformPublicAdapterLeaves.lift (next value)) := by
  apply RustT.ext
  apply StateT.ext
  intro before
  simp only [RegistrationNativePlatformPublicAdapterLeaves.lift,RustT.run_bind,StateT.run_lift,StateT.run_bind,bind_assoc]
  apply bind_congr
  intro result
  cases result <;> simp only [pure_bind,StateT.run_pure,StateT.run_lift]

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable (containers : ContainerOperations (RustT (StateT P ProbComp)))

private theorem record_lift {R : Type} (self : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (effect : agreement.AgreementEffect) :
    let : ContainerOperations (RustT (StateT P ProbComp)):=containers
    let : ContainerOperations (RustT (StateT S (StateT P ProbComp))):=containerOperations containers
    AdapterPublicServerAcceptBody.record (m:=StateT S (StateT P ProbComp)) self rng effect=
      RegistrationNativePlatformPublicAdapterLeaves.lift (AdapterPublicServerAcceptBody.record (m:=StateT P ProbComp) self rng effect) := by
  let : ContainerOperations (RustT (StateT P ProbComp)):=containers
  let : ContainerOperations (RustT (StateT S (StateT P ProbComp))):=containerOperations containers
  dsimp only
  cases effect <;> try {exact (lift_pure _).symm}
  case ServerComplete completed=>
    rw [AdapterPublicServerToken.record,AdapterPublicServerToken.record,lift_bind]
    apply bind_congr
    rintro ⟨inserted,history⟩
    exact (lift_pure _).symm

noncomputable def replay {R : Type} (self : beaconcrypt_public_wrapper.server.Server)
    (receipt : AdapterPublicServerAgreementReceipt.Receipt R) : StateT P ProbComp (RustM (AdapterPublicServerAgreementReceipt.Word R)) :=
  let : ContainerOperations (RustT (StateT P ProbComp)):=containers
  match receipt with
  | .fail error=>pure (.fail error)
  | .div=>pure .div
  | .ok ((effect,_journal),capture)=>
    (do let completed←AdapterRecordRequestMonad.liftRust effect
        AdapterPublicServerAcceptBody.record (m:=StateT P ProbComp) self capture.rng completed).run

private theorem replay_lift {n : Nat} {KemSK R : Type} {source : RegistrationNativeMldsa.Source}
    (self : beaconcrypt_public_wrapper.server.Server) (receipt : AdapterPublicServerAgreementReceipt.Receipt R) :
    let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=containerOperations containers
    AdapterPublicServerAgreementReceipt.replay (n:=n) (KemSK:=KemSK) (source:=source) (m:=StateT P ProbComp) self receipt=
      StateT.lift (replay containers self receipt) := by
  let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=containerOperations containers
  cases receipt with
  | fail error | div=>
    apply StateT.ext
    intro before
    simp only [AdapterPublicServerAgreementReceipt.replay,replay,StateT.run_lift,StateT.run_pure,pure_bind]
  | ok pair=>
    rcases pair with ⟨⟨effect,journal⟩,capture⟩
    cases effect with
    | fail error | div=>
      apply StateT.ext
      intro before
      simp only [AdapterPublicServerAgreementReceipt.replay,replay,RustT.run_bind,RustT.run_liftRust,pure_bind,
        StateT.run_lift,StateT.run_pure]
    | ok effect=>
      simp only [AdapterPublicServerAgreementReceipt.replay,replay,RustT.run_bind,RustT.run_liftRust,pure_bind]
      exact congrArg RustT.run (record_lift containers self capture.rng effect)

variable {n : Nat} {KemSK : Type} {source : RegistrationNativeMldsa.Source}
variable [original : CryptoOperations (RustT ProbComp)]

noncomputable def capture {R Error Value : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (keys : AdapterPublicAgreementFields.Keys)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) (rng : R) :
    StateT (Backend n KemSK) (StateT P ProbComp)
      (RustM ((Value×RegistrationAgreementQueryTrace.Trace)×AdapterPublicAgreementInterpreter.Capture R)) :=
  fun before=>simulateQ coins ((RegistrationNativePlatformPublicAdapterCrypto.captured generator keys work rng).run.run before)

noncomputable def program {R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (keys : AdapterPublicAgreementFields.Keys)
    (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng : R) :
    StateT (Backend n KemSK) (StateT P ProbComp)
      (AdapterPublicServerAgreementReceipt.Receipt R×RustM (AdapterPublicServerAgreementReceipt.Word R)) := do
  let receipt←capture coins generator keys work rng
  let returned←StateT.lift (replay containers self receipt)
  pure (receipt,returned)


theorem program_source {R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (keys : AdapterPublicAgreementFields.Keys)
    (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=containerOperations containers
    Prod.map id backend <$>
      (AdapterPublicServerAgreementReceipt.program (n:=n) (KemSK:=KemSK) (source:=source) coins generator keys self work rng).run before=
      (program containers coins generator keys self work rng).run (backend before) := by
  let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=containerOperations containers
  have capturedSource : Prod.map id backend <$>
      (AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run.run before=
      (capture coins generator keys work rng).run (backend before) := by
    apply StateT.ext
    intro previous
    rw [StateT.run_map]
    convert RegistrationNativePlatformPublicAdapterCrypto.captured_platform coins generator keys work rng before previous using 1 <;> rfl
  unfold AdapterPublicServerAgreementReceipt.program program
  simp only [StateT.run_bind,map_bind,StateT.run_pure,map_pure]
  rw [←capturedSource,bind_map_left]
  apply bind_congr
  rintro ⟨receipt,current⟩
  rw [replay_lift (n:=n) (KemSK:=KemSK) (source:=source) containers self receipt]
  simp only [StateT.run_lift,bind_assoc,pure_bind]
  rfl

theorem program_platform {R Error : Type} (coins : QueryImpl unifSpec (StateT P ProbComp))
    (generator : rand_core.TryCryptoRng R Error) (keys : AdapterPublicAgreementFields.Keys)
    (self : beaconcrypt_public_wrapper.server.Server)
    (work : OracleComp RegistrationAgreementExecutor.Spec (RustM agreement.AgreementEffect)) (rng : R)
    (before : RegistrationNativeExperiment.State n KemSK source) (previous : P) :
    let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=containerOperations containers
    Prod.map (Prod.map id backend) id <$>
      ((AdapterPublicServerAgreementReceipt.program (n:=n) (KemSK:=KemSK) (source:=source) coins generator keys self work rng).run before).run previous=
      ((program containers coins generator keys self work rng).run (backend before)).run previous := by
  let : ContainerOperations (RustT (StateT (RegistrationNativeExperiment.State n KemSK source) (StateT P ProbComp))):=containerOperations containers
  rw [←program_source containers coins generator keys self work rng before,StateT.run_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt.program_platform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAcceptReceipt.program_platform

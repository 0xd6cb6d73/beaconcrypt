-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativePlatformInterpreter
import BeaconcryptCore.Refinement.AdapterPublicServerAgreementMaterial
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual counted source SDK agreement retains live Server material before and after its private capture/journal projection. This follows from the original sampler's literal uniform-counter update, without primitive normality or a whole source-controller frame premise. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Keys)
open AdapterPublicAgreementInterpreter (Capture handler)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
variable {n : Nat} {Value KemSK : Type} {source : RegistrationNativeMldsa.Source}

theorem sampled_server (work : ProbComp Value) (before after : PqxdhRecordLiftWorld.State n) (reply : Value)
    (supported : (reply, after) ∈ support ((PqxdhRecordLiftWorld.sampled work).run before)) :
    after.server = before.server := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨result, _called, returned⟩ := supported
  have same := congrArg Prod.snd returned
  cases same
  rfl

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable [original : CryptoOperations (RustT ProbComp)]

omit platform in
theorem captured_server {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (rng : R)
    (before after : RegistrationNativeExperiment.State n KemSK source)
    (reply : RustM ((Value × RegistrationAgreementQueryTrace.Trace) × Capture R))
    (supported : (reply, after) ∈ support
      (((AdapterPublicAgreementNativeWorldInterpreter.captured generator keys work rng).run).run before)) :
    after.server.world.world.1.server = before.server.world.world.1.server := by
  rw [AdapterPublicAgreementNativeWorldInterpreter.captured_run] at supported
  simp only [support_map] at supported
  obtain ⟨⟨value, world⟩, called, returned⟩ := supported
  have same := congrArg Prod.snd returned
  cases same
  unfold AdapterPublicAgreementCountedNative.captured at called
  rw [AdapterPublicAgreementCountedInterpreter.program] at called
  change (value, world) ∈ support ((PqxdhRecordLiftWorld.sampled _).run before.server.world.world.1) at called
  exact sampled_server _ before.server.world.world.1 world value called

theorem captured_material {R E : Type} (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec Value) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before after : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (reply : RustM ((Value × RegistrationAgreementQueryTrace.Trace) × Capture R))
    (supported : (reply, after) ∈ support
      (((AdapterPublicAgreementNativeWorldInterpreter.captured generator keys work rng).run).run before)) :
    AdapterPublicWrapperState.Server view views created credential self after.server := by
  have unchanged := captured_server generator keys work rng before after reply supported
  rw [AdapterPublicAgreementNativeWorldInterpreter.captured_run] at supported
  simp only [support_map] at supported
  obtain ⟨⟨_value, _world⟩, _called, returned⟩ := supported
  have same := congrArg Prod.snd returned
  cases same
  rcases related.peers with ⟨records, reached, sender, identity, peers⟩
  exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa, related.replay,
    records, unchanged.trans reached, sender, identity, peers⟩

omit original in
theorem restored_material {R : Type} (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (views : AdapterPublicWrapperStorage.Views) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (self : beaconcrypt_public_wrapper.server.Server)
    (before current after : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (serverSame : current.server.world.world.1.server = before.server.world.world.1.server)
    (reply : RustM (((RustM agreement.AgreementEffect) × RegistrationAgreementQueryTrace.Trace) × Capture R))
    (effect : RustM agreement.AgreementEffect)
    (restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before (reply, current) = .ok (effect, after)) :
    AdapterPublicWrapperState.Server view views created credential self after.server := by
  cases reply with
  | fail error =>
    change RustM.fail error = .ok (effect, after) at restored
    cases restored
  | div =>
    change RustM.div = .ok (effect, after) at restored
    cases restored
  | ok pair =>
    rcases pair with ⟨⟨value, journal⟩, capture⟩
    let world := (RegistrationAgreementWorldTrace.restore before.server.world
      (((value, journal), AdapterPublicAgreementServerWorld.project view capture), current.server.world.world.1)).2
    have same : { before with server := { before.server with world := world } } = after := by
      exact congrArg Prod.snd (RustM.ok.inj restored)
    cases same
    rcases related.peers with ⟨records, reached, sender, identity, peers⟩
    exact ⟨related.identity, related.control, related.pinIdentity, related.pinIdentifier, related.pinMldsa, related.replay,
      records, serverSame.trans reached, sender, identity, peers⟩

omit platform in
theorem platform_server {Platform R E : Type}
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : Keys) (work : OracleComp Spec Value) (rng : R)
    (before after : RegistrationNativeExperiment.State n KemSK source)
    (reply : RustM ((Value × RegistrationAgreementQueryTrace.Trace) × Capture R)) (previous next : Platform)
    (supported : ((reply, after), next) ∈ support
      ((((AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run).run before).run previous)) :
    after.server.world.world.1.server = before.server.world.world.1.server := by
  rw [AdapterPublicAgreementNativePlatformInterpreter.captured_run] at supported
  apply captured_server generator keys work rng before after reply
  apply OracleComp.support_simulateQ_run'_subset coins _ previous
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

theorem platform_restored_material {Platform R E : Type}
    (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (generator : rand_core.TryCryptoRng R E) (keys : Keys)
    (work : OracleComp Spec (RustM agreement.AgreementEffect)) (rng : R)
    (view : AdapterPublicWrapperState.MaterialView source KemSK) (views : AdapterPublicWrapperStorage.Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) (before current after : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Server view views created credential self before.server)
    (reply : RustM (((RustM agreement.AgreementEffect) × RegistrationAgreementQueryTrace.Trace) × Capture R))
    (previous next : Platform)
    (supported : ((reply, current), next) ∈ support
      ((((AdapterPublicAgreementNativePlatformInterpreter.captured coins generator keys work rng).run).run before).run previous))
    (effect : RustM agreement.AgreementEffect)
    (restored : AdapterPublicAgreementNativeWorldInterpreter.restore view before (reply, current) = .ok (effect, after)) :
    AdapterPublicWrapperState.Server view views created credential self after.server :=
  restored_material view views created credential self before current after related
    (platform_server coins generator keys work rng before current reply previous next supported) reply effect restored

end BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.sampled_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.sampled_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.captured_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.captured_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.restored_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.restored_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.captured_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.captured_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.platform_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.platform_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.platform_restored_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeSourceFrame.platform_restored_material

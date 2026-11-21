-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishDispatchModel
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveFinishSupported
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish
/-! The complete Finish phase dispatcher uses the current coupled active runner and the existing missing/inactive source paths. Private material and returned source objects come from the same supported runner; no free agreement model, decapsulation law or whole callback correspondence is a caller premise. The active original-SDK physical marginal is a separate closed source theorem. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupledDispatch
open BeaconcryptCore.Refinement
open AdapterPublicFinishLifetime (packet)
open BeaconcryptCore.Computational

variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)


variable {Platform : Type}
variable [idleLocal : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleCrypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleChildren : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]
variable [idleCodecs : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (StateT (RegistrationNativeExperiment.State n KemSK source×Platform) ProbComp))]

omit idleLocal idleCrypto idleChildren idleCodecs [PublicWrapperPlatform.CryptoOperations] in
private noncomputable def absent {R : Type}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (current : RegistrationNativeExperiment.State n KemSK source×Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential current) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      (pure ((.ok none :RustM (Option Pqxdh.Bytes)),current)) := {
  step:={
    Packet:=Unit
    sample:=pure ()
    sourceType:=Option Pqxdh.Bytes
    sourceReply:=fun _=>.ok none
    sourceState:=fun _=>objects.base.objects.snapshot.committed
    sourceCall:=pure (.ok none,objects.base.objects.snapshot.committed)
    source_exact:=rfl
    native:=fun _=>(.ok none,current)
    native_exact:=rfl
    store:=fun _ _=>objects }
  observe:=RustM.ok
  normal:=fun _ _=>⟨none,rfl⟩
  reply:=by intro _packet _supported returned actual; cases actual; rfl }

noncomputable def step {R : Type} (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containersView : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)
    (before : RegistrationNativeExperiment.State n KemSK source) (index : Nat) (input : Slice U8) (previous : Platform)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential (before,previous)) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
      ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous) := by
  cases selected:before.beacons[index]? with
  | none=>
    rw [RegistrationNativePlatformSdkFinishDispatchModel.missing setup checks representation created wire index (packet input) before coins previous selected]
    exact absent containersView credential setup created view (before,previous) objects
  | some owner=>
    have prior:=objects.base.beacons index
    rw [selected] at prior
    let self:=Classical.choose prior
    have sourceSelected : objects.base.objects.beacons index=some self := (Classical.choose_spec prior).1
    have related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner
      before.server.world.world.1.owners[owner.worldOwner]? := (Classical.choose_spec prior).2
    cases stored:self.state with
    | InitSent pending prekey oneTime kem=>
      have phase : ∃scalar,owner.phase=.initSent pending scalar := by
        have matched:=related.phase
        cases phaseEq:owner.phase <;> simp only [AdapterPublicWrapperState.Phase,stored,phaseEq] at matched
        cases matched.1
        exact ⟨_,rfl⟩
      let scalar:=Classical.choose phase
      have phase:owner.phase=.initSent pending scalar:=Classical.choose_spec phase
      exact RegistrationNativePlatformSdkFinishCoupled.active coins setup checks representation created wire view containersView credential
        self pending prekey oneTime kem stored input owner scalar before index selected phase previous objects sourceSelected
    | Fresh control prekey kem | FreshWithCoins control prekey oneTime kem | Established control binding manager | Aborted control=>
      have idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state := by rw [stored]; trivial
      have inactive:=RegistrationNativePlatformExtractedSdkIdle.finish_phase view before.pool owner self.state
        before.server.world.world.1.owners[owner.worldOwner]? related.phase idle
      rw [RegistrationNativePlatformSdkFinishDispatchModel.idle setup checks representation created wire index (packet input) before coins previous owner selected inactive]
      exact RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish
        (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containersView created credential)
        (before,previous) objects.base.objects.snapshot.committed objects self input idle
end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupledDispatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupledDispatch.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupledDispatch.step

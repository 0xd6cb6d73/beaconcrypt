-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkPublic
import BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint
/-! Inactive SDK bundle and finish calls return their actual None reply, unchanged source Self and caller RNG. They instantiate the adaptive public interpreter without invoking an active source child or fabricating a moved object. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
variable {N : Type} (Private : N →Type) (current snapshot : N) (objects : Private current)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]
variable [LocalOperations (RustT (StateT N ProbComp))] [CryptoOperations (RustT (StateT N ProbComp))]
variable [ChildOperations (RustT (StateT N ProbComp))]
noncomputable def bundle {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state) :
    TotalStep Private (pure ((.ok none : RustM (Option Pqxdh.Bytes)),current)) := by
  let call:=RegistrationNativePlatformExtractedSdkAdaptiveIdle.bundle Private current snapshot objects generator self rng idle
  refine {step:=call,observe:=fun value=>RegistrationNativePlatformExtractedSdkAdaptiveBundle.bytes (.ok value),normal:=?_,reply:=?_}
  · intro packet supported
    exact ⟨_,rfl⟩
  · intro packet supported returned resultEq
    change RustM.ok (.None,self,rng)=.ok returned at resultEq
    have same:=RustM.ok.inj resultEq
    cases same
    rfl

variable [PublicWrapperPlatform.CryptoOperations] [Codecs (RustT (StateT N ProbComp))]
noncomputable def finish (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8)
    (idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state) :
    TotalStep Private (pure ((.ok none : RustM (Option Pqxdh.Bytes)),current)) := by
  let call:=RegistrationNativePlatformExtractedSdkAdaptiveIdle.finish Private current snapshot objects self input idle
  refine {step:=call,observe:=fun value=>AdapterPublicFinishEndpoint.bytes (.ok value),normal:=?_,reply:=?_}
  · intro packet supported
    exact ⟨_,rfl⟩
  · intro packet supported returned resultEq
    change RustM.ok (.None,self)=.ok returned at resultEq
    have same:=RustM.ok.inj resultEq
    cases same
    rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdlePublic.finish

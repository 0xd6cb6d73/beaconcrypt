-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive
/-! Pure SDK inactive branches form actual source-certified steps without replacing a moved object after a failed call. Source and model snapshots are separate and both remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdle
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open RegistrationNativePlatformExtractedSdkAdaptive (Step)
variable {N : Type} (Private : N →Type) (current snapshot : N) (objects : Private current)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]
variable [LocalOperations (RustT (StateT N ProbComp))] [CryptoOperations (RustT (StateT N ProbComp))]
variable [ChildOperations (RustT (StateT N ProbComp))]
noncomputable def bundle {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (rng : R)
    (idle : RegistrationNativePlatformExtractedSdkIdle.BundleIdle self.state) :
    Step Private (pure ((.ok none : RustM (Option Pqxdh.Bytes)),current)) := by
  refine {
    Packet:=Unit
    sample:=pure ()
    sourceType:=core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon ×R
    sourceReply:=fun _=>.ok (.None,self,rng)
    sourceState:=fun _=>snapshot
    sourceCall:=((beaconcrypt_public_request.beacon.Beacon.get_registration_bundle_with_rng
      (m:=RustT (StateT N ProbComp)) generator self rng).run).run snapshot
    source_exact:=?_
    native:=fun _=>(.ok none,current)
    native_exact:=rfl
    store:=fun _ _=>objects }
  rw [RegistrationNativePlatformExtractedSdkIdle.bundle_source generator self rng idle]
  rfl

variable [PublicWrapperPlatform.CryptoOperations] [Codecs (RustT (StateT N ProbComp))]
noncomputable def finish (self : beaconcrypt_public_wrapper.beacon.Beacon) (input : Slice U8)
    (idle : RegistrationNativePlatformExtractedSdkIdle.FinishIdle self.state) :
    Step Private (pure ((.ok none : RustM (Option Pqxdh.Bytes)),current)) := by
  refine {
    Packet:=Unit
    sample:=pure ()
    sourceType:=core.option.Option (alloc.vec.Vec U8) ×beaconcrypt_public_wrapper.beacon.Beacon
    sourceReply:=fun _=>.ok (.None,self)
    sourceState:=fun _=>snapshot
    sourceCall:=((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m:=RustT (StateT N ProbComp)) self input).run).run snapshot
    source_exact:=?_
    native:=fun _=>(.ok none,current)
    native_exact:=rfl
    store:=fun _ _=>objects }
  rw [RegistrationNativePlatformExtractedSdkIdle.finish_source self input idle]
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdle
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdle.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdle.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdle.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptiveIdle.finish

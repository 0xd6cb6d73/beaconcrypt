-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundlePhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleCallFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterReply
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterPhysicalOrdinary
/-! The actual Bundle driver reads only the stored source Self, caller RNG and physical backend. Returned source words update the same object and RNG; Rust failures retain the actual terminal backend without manufacturing a returned Self. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterStore (Store erase bundle)
open RegistrationNativePlatformSdkOrdinaryBeaconSelected (raw strongPhysical)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep returned store)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {I KemSK E P R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
open RegistrationNativePlatformPublicAdapterBundlePhysical (Word finish call run)
variable [original : CryptoOperations (RustT ProbComp)]
variable (coins : QueryImpl unifSpec (StateT P ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
variable (physicalLocal : LocalOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))
variable (failure : ed.Error) (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT P ProbComp))
variable (physicalChildren : ChildOperations (RustT (StateT (Backend n KemSK) (StateT P ProbComp))))

omit original in
theorem finish_source (before : Store n KemSK R P) (index : Nat) (result : RustM (Word R) ×(Backend n KemSK ×P)) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize (finish before index result)=
      finish (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index
        (result.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent result.2) :=by
  rcases result with ⟨reply,after⟩
  cases reply <;> rfl

theorem call_source {Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (before : Store n KemSK R P) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
      call coins setup checks representation created view physicalLocal failure writer physicalChildren generator before index self=
    call coins setup checks representation created view physicalLocal failure writer physicalChildren generator
      (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index self :=by
  have framed:=RegistrationNativePlatformPublicAdapterBundleCallFrame.call coins setup checks representation created view physicalLocal failure writer physicalChildren generator self before.rng before.backend.1
  have actual:=congrArg (fun work=>(work.run before.backend.2)) framed
  simp only [StateT.run_map] at actual
  have observed:=congrArg (fun tree=>(fun result=>finish (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index
    (result.1.1,(result.1.2,result.2))) <$>tree) actual
  unfold call
  simp only [Functor.map_map]
  have point : (fun result : (RustM (Word R) ×Backend n KemSK) ×P=>RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize (finish before index (result.1.1,(result.1.2,result.2))))=
      (fun result : (RustM (Word R) ×Backend n KemSK) ×P=>finish (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index
        (result.1.1,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent (result.1.2,result.2))) :=by
    funext result
    exact finish_source before index _
  rw [point]
  simpa only [Functor.map_map,Prod.map,id_eq,RegistrationNativePlatformPublicAdapterPhysicalBackend.persistent,
    RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize,Function.comp_def] using observed

theorem run_source {Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (before : Store n KemSK R P) (index : Nat) :
    RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$>
      run coins setup checks representation created view physicalLocal failure writer physicalChildren generator before index=
    run coins setup checks representation created view physicalLocal failure writer physicalChildren generator
      (RegistrationNativePlatformPublicAdapterPhysicalBackend.normalize before) index :=by
  unfold run
  change RegistrationNativePlatformPublicAdapterPhysicalOrdinary.normalize <$> (match before.beacons index with
    | none=>pure _ | some self=>_)=(match before.beacons index with | none=>pure _ | some self=>_)
  cases selected:before.beacons index with
  | none=>simp only [map_pure];rfl
  | some self=>exact call_source coins setup checks representation created view physicalLocal failure writer physicalChildren generator before index self

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization.call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization.call_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterBundleNormalization.run_source

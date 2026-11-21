-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterCreateDispatch
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativeConcreteReaders
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
/-! The selected raw public-adapter target fixes the actual codec and sender decoder, retains original raw bytes and uses the unchanged extracted dictionary. Its local equations connect the concrete wrapper factories without a caller-supplied callback law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawCreateModel
private theorem pure_apply {S A : Type} {m : Type →Type} [Monad m] (value : A) (state : S) :
    (pure value : StateT S m A) state=pure (value,state) := rfl
private theorem map_apply {S A B : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (observe : A →B) (work : StateT S m A) (state : S) :
    (observe <$>work) state=Prod.map observe id <$>work state := StateT.run_map observe work state
attribute [local irreducible] RegistrationNativePlatformExtractedExperiment.record
  RegistrationNativePlatformExtractedAuthentication.accept RegistrationNativePlatformExtractedBundle.bundle
  RegistrationNativePlatformExtractedFinish.finish RegistrationNativeConcreteCodec.wire
  RegistrationNativePlatformPublicAdapterRouting.route
open BeaconcryptCore.Refinement
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route

theorem create (keyId : U64) (identityKey mlKey : Slice U8)
    (current : RegistrationNativeExperiment.State n KemSK source ×Platform) :
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformPublicAdapterRawModel.raw setup checks representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer
          (.inr (.create (TranscriptAuthParts.absSlice identityKey) (TranscriptAuthParts.absSlice mlKey) keyId))) current=
    RegistrationNativePlatformPublicAdapterCreateDispatch.command coins setup checks representation created keyId identityKey mlKey current := by
  rw [RegistrationNativePlatformPublicAdapterRawModel.create]
  cases identity:PqxdhDeploymentInterface.parsePin (TranscriptAuthParts.absSlice identityKey) with
  | none=>simp only [RegistrationNativePlatformPublicAdapterCreateDispatch.command,identity,
      RegistrationNativePlatformPackedState.pure_pack,pure_apply]
  | some identityBytes=>
    cases ml:RegistrationNativeWire.parseMldsaPin (TranscriptAuthParts.absSlice mlKey) with
    | none=>simp only [RegistrationNativePlatformPublicAdapterCreateDispatch.command,identity,ml,
        RegistrationNativePlatformPackedState.pure_pack,pure_apply]
    | some mlBytes=>
      simp only [RegistrationNativePlatformPublicAdapterCreateDispatch.command,identity,ml,
        RegistrationNativePlatformPackedState.pack,StateT.run,map_apply,Functor.map_map]
      rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawCreateModel
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawCreateModel.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawCreateModel.create

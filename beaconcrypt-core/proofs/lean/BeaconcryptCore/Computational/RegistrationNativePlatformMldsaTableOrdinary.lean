-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableRestore
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata

/-! Actual non-signing corrected source callbacks preserve live owner handles and restore through the reached fixed private table. The verifier and public fields stay literal; source allocation and assigned-ID installation retain their complete shared platform poststates. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableOrdinary
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource restore)
open RegistrationNativeMldsaMap (nativeState)
open RegistrationNativeMldsaGlobalMap (NonML)
open RegistrationNativePlatformMldsaTableProgram (runState)
open RegistrationNativePlatformMldsaTableRestore (observe)
variable {n : Nat} {KemSK Platform E Value ι : Type} {base : OracleSpec ι}
variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "callback" => RegistrationNativePlatformExperiment.handler (n := n) RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$> work) before = Prod.map f id <$> work before := bind_pure_comp _ _

/-- Complete actual non-signing source callbacks restore only the private key representation, keeping the exact common platform result. -/
theorem restored (fallback : Credential source) (pool : Pool source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : NonML query)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (previous : Platform) :
    observe source fallback <$> runState source (RegistrationNativePlatformMldsaProgram.lift
      (callback (handleSource source) credential view failure allocation reserveRegistration reservePeer erased helper writer query)) before previous pool =
      (((callback source (RegistrationNativeMldsaMap.credential (restore source fallback pool) credential)
        view failure allocation reserveRegistration reservePeer erased helper writer query).run
          (nativeState (restore source fallback pool) before)).run previous) := by
  rw [RegistrationNativePlatformMldsaTableProgram.run_lift]
  have same := congrArg (fun action => action.run previous)
    (RegistrationNativePlatformMldsaOrdinaryMap.non_ml_natural (restore source fallback pool) rfl
      RegistrationNativePlatformMldsaProgram.coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query ordinary before)
  simp only [Functor.map_map, observe, StateT.run]
  simp only [StateT.run, map_apply] at same
  convert same using 1
  congr 1

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableOrdinary.restored' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableOrdinary.restored

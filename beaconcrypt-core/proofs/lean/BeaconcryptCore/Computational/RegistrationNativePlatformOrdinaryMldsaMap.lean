-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaOrdinaryMap
/-! The actual runtime terminal writer is independent of private ML credentials. Its complete Native and public platform effects commute with public-key-preserving credential replacement; no signing or generation law is needed. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaMap
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaMap (Map nativeState)
open RegistrationNativePlatformMldsaOrdinaryMap (Natural)
open RegistrationNativePlatformOrdinaryExperimentRouting (after terminal)
variable {left right : RegistrationNativeMldsa.Source} {n : Nat} {Platform E KemSK ι : Type} {base : OracleSpec ι}

/-- A public terminal publication gate retains exactly the same private credential map and common platform state. -/
theorem after_natural (mapping : Map left right)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (first : RegistrationNativePlatformOrdinaryExperiment.M n KemSK left Platform (Option RawCtxSourceSend.Encrypted))
    (second : RegistrationNativePlatformOrdinaryExperiment.M n KemSK right Platform (Option RawCtxSourceSend.Encrypted))
    (law : Natural mapping id first second) : Natural mapping id (after reserve first) (after reserve second) := by
  intro before
  simp only [after, StateT.run_bind, StateT.run_lift, map_bind]
  rw [← law before, bind_map_left]
  apply bind_congr
  intro result
  simp only [map_pure]
  rfl

/-- Actual non-ML runtime callbacks preserve source credential replacement through failed and successful dynamic frame writes. -/
theorem non_ml_natural [primitive : AdapterSealPrimitive.Operations]
    (mapping : Map left right) (sameVerify : left.verify = right.verify)
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential left)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (ordinary : RegistrationNativeMldsaGlobalMap.NonML query) :
    Natural (n := n) mapping id
      (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created left credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query)
      (RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created right
        (RegistrationNativeMldsaMap.credential mapping credential) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query) := by
  rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal,
    RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal]
  have original := RegistrationNativePlatformMldsaOrdinaryMap.non_ml_natural (n := n) mapping sameVerify
    RegistrationNativePlatformMldsaProgram.coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
    route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer query ordinary
  cases query with
  | inl coin => exact original
  | inr query => cases query with
    | serverSend keyId plaintext => exact after_natural mapping reserveFrame _ _ original
    | beaconSend owner plaintext => exact after_natural mapping reserveFrame _ _ original
    | _ => exact original

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaMap.after_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaMap.after_natural

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaMap.non_ml_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaMap.non_ml_natural

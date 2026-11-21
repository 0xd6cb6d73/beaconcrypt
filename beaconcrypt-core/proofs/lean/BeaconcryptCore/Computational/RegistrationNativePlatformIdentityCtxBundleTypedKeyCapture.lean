-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleKeyCapture
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
open RegistrationNativePlatformIdentityCtxSigningHistoryFrame (messages)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- The literal typed bundle callback has the same captured-handle/fixed-pair signing scope, with actual byte conversion and all private state retained. -/
theorem typed_new (index : Nat) (before : Full n KemSK Platform source)
    (result : RustM (Option Pqxdh.Bytes) × Full n KemSK Platform source)
    (reached : result ∈ support ((interpret setup.joint (frontend (.inr (.bundle index)))).run before))
    (identity : Nat) (message : Pqxdh.Bytes) (fresh : message ∉ messages identity before.2)
    (signed : message ∈ messages identity result.2.2) :
    ∃ owner, before.1.1.beacons[index]? = some owner ∧ owner.identity.handle = identity ∧
      RegistrationNativeEdKeyPolicy.Allowed (PqxdhPhase2InputBytes.word owner.prekeyPublic) owner.kemPublic message := by
  unfold RegistrationNativePlatformIdentityCtxTyped.handler RegistrationNativePlatformIdentityCtxLifecycle.bundle at reached
  have mapped {A B : Type} (change : A → B) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform source A) :
      interpret setup.joint (change <$> work) = change <$> interpret setup.joint work := by
    rw [map_eq_bind_pure_comp, RegistrationNativePlatformIdentityCtxOrdinary.interpret_bind]
    simp only [Function.comp_def, RegistrationNativePlatformIdentityCtxOrdinary.interpret_pure]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [mapped, StateT.run_map, support_map] at reached
  obtain ⟨inner, called, same⟩ := reached
  have post : inner.2 = result.2 := congrArg Prod.snd same
  exact RegistrationNativePlatformIdentityCtxBundleKeyCapture.bundle_new setup checks representation created index writer before
    inner called identity message fresh (by simpa only [post] using signed)
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture.typed_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxBundleTypedKeyCapture.typed_new

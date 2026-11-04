-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView
/-! The complete actual typed source tree depends on no prior raw Ed signature slot or Local ML receipt payload. Signed-message order, every current reply, full remaining native state, physical queries and P are retained. The named final observation masks stored signature slots, including current appended slots, and the ML receipt coordinate; current canonical-versus-placeholder reply coupling is separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxMain (M)
open PqxdhEd25519EufCma (Ed25519Signature)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

def view (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :=
  RegistrationNativePlatformIdentityCtxReceiptView.view
    (RegistrationNativePlatformIdentityCtxHistoryView.view placeholder before)
def Stable (placeholder : Ed25519Signature) (work : M n KemSK Platform source A) : Prop :=
  RegistrationNativePlatformViewStable.Stable (view placeholder) work

omit primitives in
/-- Independent raw-history and raw-receipt coordinates commute without changing other state. -/
theorem commute (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    RegistrationNativePlatformIdentityCtxHistoryView.view placeholder (RegistrationNativePlatformIdentityCtxReceiptView.view before) =
      RegistrationNativePlatformIdentityCtxReceiptView.view (RegistrationNativePlatformIdentityCtxHistoryView.view placeholder before) := rfl

omit primitives in
/-- The exact joint observation is idempotent. -/
theorem view_idempotent (placeholder : Ed25519Signature) (before : RegistrationNativeIdentityMain.State n KemSK source × Platform) :
    view placeholder (view placeholder before) = view placeholder before := by
  simp only [view]
  rw [commute, RegistrationNativePlatformIdentityCtxHistoryView.view_idempotent,
    RegistrationNativePlatformIdentityCtxReceiptView.view_idempotent]

omit primitives in
/-- Independently discharged source dependency laws compose through their two commuting observations. -/
theorem compose_stable {A : Type} (placeholder : Ed25519Signature) (work : M n KemSK Platform source A)
    (history : RegistrationNativePlatformIdentityCtxHistoryView.Stable placeholder work)
    (receipt : RegistrationNativePlatformIdentityCtxReceiptView.Stable work) : Stable placeholder work := by
  intro before
  have first := congrArg (fun distribution => Prod.map id RegistrationNativePlatformIdentityCtxReceiptView.view <$> distribution) (history before)
  have second := congrArg (fun distribution => Prod.map id (RegistrationNativePlatformIdentityCtxHistoryView.view placeholder) <$> distribution)
    (receipt (RegistrationNativePlatformIdentityCtxHistoryView.view placeholder before))
  simp only [Functor.map_map, Prod.map_def, id_eq, commute] at first second
  simp only [view, Prod.map_def, id_eq]
  exact first.trans second

local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

/-- Every actual corrected typed callback derives its joint old-log dependency law internally. -/
theorem handler_stable (placeholder : Ed25519Signature) (query : TypedSpec.Domain) : Stable placeholder (callback query) :=
  compose_stable placeholder _
    (RegistrationNativePlatformIdentityCtxTypedHistoryView.handler_stable setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer placeholder query)
    (RegistrationNativePlatformIdentityCtxTypedReceiptView.handler_stable setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query)

/-- The complete adaptive actual source tree preserves joint prior-log independence through every reply and failure. -/
theorem program_stable {A : Type} (placeholder : Ed25519Signature) (work : OracleComp TypedSpec A) :
    Stable placeholder (simulateQ callback work) :=
  RegistrationNativePlatformViewStable.program_stable (view placeholder) (view_idempotent placeholder) callback
    (handler_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder) work
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.commute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.commute

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.view_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.compose_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.compose_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.handler_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.handler_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView.program_stable

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkReceiptView
/-! Every leaf of the literal source SDK build discharges receipt-payload independence. Private cache, all remaining state and persistent platform effects are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
open RegistrationNativePlatformCtxRunner (M privateWork publicWork)
open RegistrationNativePlatformCtxSdkReceiptView (Stable view serverView world_stable)
variable {n : Nat} {I KemSK Reader Response Platform E : Type} {base : OracleSpec I}

private theorem local_pin (current : session.ServerAuthenticationPin) :
    RegistrationNativePlatformIdentityReceiptView.Stable (RegistrationNativePlatformCtxPin.pin (n := n) (Auxiliary := RegistrationServerRoleBackend.State) current) := by
  exact RegistrationNativePlatformViewStable.pure_stable
    RegistrationNativePlatformIdentityReceiptView.view (fun _ => rfl) _

/-- Pure pin selection has no input dependency on the private signing log and performs no hash. -/
theorem pin_stable : Stable (RegistrationNativePlatformCtxSdk.pin : M (State n) Platform _) := by
  rintro ⟨before, previous⟩
  have same := world_stable (privateWork (RegistrationNativePlatformCtxPin.pin before.pin))
    (RegistrationNativePlatformCtxReceiptView.private_stable _ (local_pin before.pin)) (before, previous)
  simpa only [RegistrationNativePlatformCtxSdk.pin, RegistrationNativePlatformPackedState.pack,
    StateT.run, view, serverView] using same

/-- The actual AD hash and owned resume ignore earlier raw signing receipts while retaining the complete hash cache and all other state. -/
theorem adHash_stable (pending : registration.ServerAdHash) :
    Stable (RegistrationNativePlatformCtxSdk.adHash pending : M (State n) Platform _) := by
  unfold RegistrationNativePlatformCtxSdk.adHash RegistrationServerAdHash.runWith
  cases pending.request with
  | fail error | div => exact RegistrationNativePlatformCtxSdkReceiptView.pure_stable _
  | ok request =>
    simp only [bind_assoc, pure_bind]
    apply RegistrationNativePlatformCtxSdkReceiptView.bind_stable _ _
      (world_stable _ (RegistrationNativePlatformCtxReceiptView.private_stable _
        (RegistrationNativePlatformIdentityReceiptView.effects _)))
    intro digest
    exact RegistrationNativePlatformCtxSdkReceiptView.pure_stable _

/-- The actual occupancy capability retains all projected server and external coordinates. -/
theorem present_stable (keyId : U64) : Stable (RegistrationNativePlatformCtxSdk.present keyId : M (State n) Platform Bool) :=
  world_stable _ (RegistrationNativePlatformCtxReceiptView.private_stable _ (RegistrationNativePlatformIdentityReceiptView.effects _))

/-- Actual public preflight reservations receive the same P and preserve the full native state. -/
theorem reserve_stable (reserve : StateT Platform ProbComp Bool) : Stable (publicWork reserve : M (State n) Platform Bool) := by
  rintro ⟨before, previous⟩
  simp only [RegistrationNativePlatformPackedState.pack, publicWork, StateT.run, Functor.map_map,
    view, serverView, RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- The complete literal SDK source build discharges every individual leaf law, including all moved-token, signing and writer failures. -/
theorem build_stable (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8)) :
    Stable (RegistrationNativePlatformCtxSdk.build (n := n) setup codec keys failure allocation erased sign helper writer reserve handle application) := by
  apply RegistrationNativePlatformCtxSdkReceiptView.build_stable
    (deriveAd := RegistrationNativePlatformCtxSdk.adHash) (ad_law := adHash_stable)
  · exact pin_stable
  · exact reserve_stable reserve
  · exact present_stable
  · intro control pending
    exact world_stable _ (RegistrationNativePlatformCtxCompletionReceiptView.completion_stable setup codec keys failure allocation erased sign helper writer control pending)
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.pin_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.pin_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.adHash_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.adHash_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.present_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.present_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.reserve_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.reserve_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.build_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkSourceReceiptView.build_stable

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorHashOutgoingSource
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedJointView

/-! The actual outgoing dictionary ignores only earlier raw Ed slots and compact ML receipts. Closing the source under the real or private-censored operational interpreter retains this exact input-independence law. Current replies, physical hash state, complete Mode and P remain in the observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}

def view (placeholder : Ed25519Signature)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :=
  ((RegistrationNativePlatformIdentityCtxTypedJointView.view placeholder before.1.1, before.1.2), before.2)

/-- The exact combined stored-log observation is idempotent; the private physical interpreter state is not changed. -/
theorem view_idempotent (placeholder : Ed25519Signature)
    (before : Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)) :
    view placeholder (view placeholder before) = view placeholder before := by
  simp only [view, RegistrationNativePlatformIdentityCtxTypedJointView.view_idempotent]

/-- Each literal outgoing Ed/hash/ML leaf derives both previous-log dependency laws from its actual body. -/
theorem native_query (placeholder : Ed25519Signature) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    RegistrationNativePlatformIdentityCtxTypedJointView.Stable placeholder
      (RegistrationNativePlatformIdentityCtxMain.beacon (Platform := Platform) setup checks representation created
        (RegistrationNativePlatformIdentityProgram.native
          (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner query))) := by
  apply RegistrationNativePlatformIdentityCtxTypedJointView.compose_stable
  · exact RegistrationNativePlatformIdentityCtxHistoryView.beacon placeholder setup checks representation created _
      (RegistrationNativePlatformIdentityHistoryView.native placeholder _
        (RegistrationNativeIdentityHistoryView.outgoing placeholder setup mlSource index owner query))
  · exact RegistrationNativePlatformIdentityCtxReceiptView.beacon setup checks representation created _
      (RegistrationNativeIdentityEnvReceiptView.platform_native _
        (RegistrationNativeIdentityEnvReceiptView.outgoing setup index owner query))

private def close (result : ((A × (RegistrationNativeIdentityMain.State n KemSK mlSource × Platform)) ×
    RegistrationNativeIdentityCensorCompiler.Mode) × RegistrationNativeIdentityCensorSource.State) :
    A × Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource) :=
  (result.1.1.1, ((result.1.1.2, result.1.2), result.2))

/-- The exact private operational realization transports a proved free source equation; neither interpreter state nor current reply is projected. -/
theorem interpreted (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (censored : Bool) (work : RegistrationNativePlatformIdentityCtxMain.M n KemSK Platform mlSource A)
    (law : RegistrationNativePlatformIdentityCtxTypedJointView.Stable placeholder work) :
    RegistrationNativePlatformViewStable.Stable (view placeholder) (interpret joint selected placeholder censored work) := by
  intro before
  have transported := congrArg (fun script => close <$>
    (simulateQ (if censored then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
      else RegistrationNativeIdentityCensorSource.implementation joint selected)
      ((simulateQ (RegistrationNativeIdentityCensorOperational.implementation selected placeholder) script).run before.1.2)).run before.2)
    (law before.1.1)
  simp only [simulateQ_map, StateT.run_map, Functor.map_map, close, Prod.map_def, id_eq] at transported
  simpa only [interpret, StateT.run, bind_pure_comp, Functor.map_map, close, view, Prod.map_def, id_eq] using transported

/-- The actual outgoing callbacks retain their derived old-log law through every optional source reply and physical CTX operation. -/
theorem query (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature) (censored : Bool)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner mlSource) (request : RegistrationBeaconInitExecutor.Spec.Domain) :
    RegistrationNativePlatformViewStable.Stable (view placeholder)
      (interpret joint selected placeholder censored
        (RegistrationNativePlatformIdentityCtxMain.beacon (Platform := Platform) setup checks representation created
          (RegistrationNativePlatformIdentityProgram.native
            (RegistrationNativeIdentityFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup mlSource index owner request)))) :=
  interpreted joint selected placeholder censored _
    (native_query placeholder setup checks representation created index owner request)

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.view_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.view_idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.native_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.native_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.interpreted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorOutgoingView.query

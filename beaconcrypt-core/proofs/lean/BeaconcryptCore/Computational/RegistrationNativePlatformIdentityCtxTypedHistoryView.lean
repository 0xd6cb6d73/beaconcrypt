-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxHistoryView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
/-! Actual public alias reports, owner lookup and every corrected typed callback ignore earlier raw Ed signature slots. The private source pool, physical backend and complete P remain separate and unchanged by this observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxHistoryView (Stable view)
open PqxdhEd25519EufCma (Ed25519Signature)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ambient" => RegistrationNativePlatformIdentityCtxDispatch.context (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

omit primitives in
private theorem reports (placeholder : Ed25519Signature) (packet : registration.InitPacket)
    (owners : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativeIdentityMain.reports packet (RegistrationNativeIdentityHistoryView.owners placeholder owners) =
      RegistrationNativeIdentityMain.reports packet owners := by
  simp only [RegistrationNativeIdentityMain.reports, RegistrationNativeIdentityHistoryView.owners,
    List.filterMap_map, Function.comp_def, RegistrationNativeIdentityHistoryView.owner]

omit primitives in
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl
omit primitives in
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit primitives in
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := by
  change (do let value ← work; pure (value, before)) = _
  rw [bind_pure_comp]

omit primitives in
/-- The complete actual public alias reporter retains its original requests after earlier raw-history replacement. -/
theorem report_stable (placeholder : Ed25519Signature) (packet : registration.InitPacket) :
    Stable placeholder (RegistrationNativePlatformIdentityCtxOrdinary.report (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) packet) := by
  intro before
  simp only [StateT.run, RegistrationNativePlatformIdentityCtxOrdinary.report, RegistrationNativeIdentityMain.report,
    bind_apply, get_apply, lift_apply, pure_bind, simulateQ_map,
    Functor.map_map, view, reports, Prod.map_def, id_eq, RegistrationNativeIdentityHistoryLifecycle.owners_idempotent]

private theorem context_history (placeholder : Ed25519Signature) (query : TypedSpec.Domain)
    (owners : RegistrationNativeIdentityFrontend.State source) :
    ambient query (RegistrationNativeIdentityHistoryView.owners placeholder owners) = ambient query owners := by
  have handles : (RegistrationNativeIdentityHistoryView.owners placeholder owners).map (fun selected => selected.worldOwner) =
      owners.map (fun selected => selected.worldOwner) := by
    simp only [RegistrationNativeIdentityHistoryView.owners, List.map_map, Function.comp_def,
      RegistrationNativeIdentityHistoryView.owner]
  cases query with
  | inl coin => simp only [RegistrationNativePlatformIdentityCtxDispatch.context, handles]
  | inr query => cases query <;> first
    | rfl
    | simp only [RegistrationNativePlatformIdentityCtxDispatch.context, handles]

/-- The literal non-Beacon dispatcher keeps full Context/P and depends only on public owner handles. -/
theorem ambient_stable (placeholder : Ed25519Signature) (query : TypedSpec.Domain) :
    Stable placeholder (RegistrationNativePlatformIdentityCtxDispatch.step (n := n) setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query) := by
  intro before
  have actual := RegistrationNativePlatformIdentityCtxHistoryView.ordinary placeholder (ambient query before.1.beacons) before
  simp only [StateT.run, RegistrationNativePlatformIdentityCtxDispatch.step, view, context_history] at actual ⊢
  exact actual

local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step

/-- Every actual corrected typed callback keeps the signed-message chronology and ignores only earlier raw signature slots. -/
theorem handler_stable (placeholder : Ed25519Signature) (query : TypedSpec.Domain) : Stable placeholder (callback query) := by
  cases query with
  | inl coin => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inl coin)
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityCtxHistoryView.create_stable placeholder setup checks representation created edPin mlPin keyId
    | bundle index => exact RegistrationNativePlatformIdentityCtxHistoryView.bundle_stable placeholder setup checks representation created writer index
    | finish index packet => exact RegistrationNativePlatformIdentityCtxHistoryView.finish_stable placeholder setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet
    | accept packet =>
        unfold RegistrationNativePlatformIdentityCtxTyped.handler
        exact RegistrationNativePlatformViewStable.bind_stable (view placeholder) _ _
          (report_stable placeholder packet)
          (fun _ => ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.accept packet)))
    | build session application => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.build session application))
    | hmac key message => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.hmac key message))
    | hash bytes => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.hash bytes))
    | serverSend keyId plaintext => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.serverSend keyId plaintext))
    | serverRaw raw => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.serverRaw raw))
    | beaconSend index plaintext => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.beaconSend index plaintext))
    | beaconRaw index raw => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder (.inr (.beaconRaw index raw))

/-- The full adaptive actual typed source tree preserves this exact dependency law on every reply. -/
theorem program_stable {A : Type} (placeholder : Ed25519Signature) (work : OracleComp TypedSpec A) :
    Stable placeholder (simulateQ callback work) :=
  RegistrationNativePlatformViewStable.program_stable (view placeholder)
    (RegistrationNativePlatformIdentityCtxHistoryView.view_idempotent placeholder) callback
    (handler_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer placeholder) work
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.report_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.report_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.ambient_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.ambient_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.handler_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.handler_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedHistoryView.program_stable

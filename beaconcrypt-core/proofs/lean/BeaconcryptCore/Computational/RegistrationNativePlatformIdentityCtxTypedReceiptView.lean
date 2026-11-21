-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptReceiptView
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
/-! Actual public alias reports, owner lookup and every corrected typed callback ignore earlier raw ML receipt payloads. The private source pool, physical backend and complete P remain separate and unchanged by this observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxReceiptView (Stable view)
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
theorem report_stable (packet : registration.InitPacket) :
    Stable (RegistrationNativePlatformIdentityCtxOrdinary.report (n := n) (KemSK := KemSK) (Platform := Platform) (source := source) packet) := by
  intro before
  simp only [StateT.run, RegistrationNativePlatformIdentityCtxOrdinary.report, RegistrationNativeIdentityMain.report,
    bind_apply, get_apply, lift_apply, pure_bind, simulateQ_map,
    Functor.map_map, view, RegistrationNativePlatformCtxBuildReceiptView.context, RegistrationNativePlatformCtxSdkReceiptView.serverView, RegistrationNativePlatformIdentityReceiptView.view, Prod.map_def, id_eq]

private theorem context_stable (query : TypedSpec.Domain) (owners : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativePlatformCtxBuildReceiptView.Stable (ambient query owners) := by
  cases query with
  | inl coin => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inl coin)
  | inr query => cases query with
    | accept packet => exact RegistrationNativePlatformCtxAcceptReceiptView.accept setup checks reserveRegistration source.verify representation created packet
    | build handle application => exact RegistrationNativePlatformCtxBuildReceiptView.build_stable setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) keys failure allocation erased (RegistrationNativeMldsa.owned source credential) helper writer reservePeer handle application
    | create edPin mlPin keyId => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.create edPin mlPin keyId))
    | bundle index => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.bundle index))
    | finish index packet => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.finish index packet))
    | hmac key message => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.hmac key message))
    | hash bytes => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.hash bytes))
    | serverSend keyId plaintext => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.serverSend keyId plaintext))
    | serverRaw raw => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.serverRaw raw))
    | beaconSend index plaintext => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.beaconSend index plaintext))
    | beaconRaw index raw => exact RegistrationNativePlatformCtxCommandReceiptView.command setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.beaconRaw index raw))

/-- The literal non-Beacon dispatcher keeps full Context/P and depends only on public owner handles. -/
theorem ambient_stable (query : TypedSpec.Domain) :
    Stable (RegistrationNativePlatformIdentityCtxDispatch.step (n := n) setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query) := by
  intro before
  have actual := RegistrationNativePlatformIdentityCtxReceiptView.ordinary (ambient query before.1.beacons)
    (context_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1.beacons) before
  simp only [StateT.run, RegistrationNativePlatformIdentityCtxDispatch.step, view] at actual ⊢
  exact actual

local notation "callback" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.step

/-- Every actual corrected typed callback keeps the full remaining source state and ignores only earlier raw signature slots. -/
theorem handler_stable (query : TypedSpec.Domain) : Stable (callback query) := by
  cases query with
  | inl coin => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin)
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativePlatformIdentityCtxReceiptView.create_stable setup checks representation created edPin mlPin keyId
    | bundle index => exact RegistrationNativePlatformIdentityCtxReceiptView.bundle_stable setup checks representation created writer index
    | finish index packet => exact RegistrationNativePlatformIdentityCtxReceiptView.finish_stable setup checks representation created (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) index packet
    | accept packet =>
        unfold RegistrationNativePlatformIdentityCtxTyped.handler
        exact RegistrationNativePlatformViewStable.bind_stable view _ _
          (report_stable packet)
          (fun _ => ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)))
    | build session application => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.build session application))
    | hmac key message => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hmac key message))
    | hash bytes => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.hash bytes))
    | serverSend keyId plaintext => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverSend keyId plaintext))
    | serverRaw raw => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.serverRaw raw))
    | beaconSend index plaintext => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconSend index plaintext))
    | beaconRaw index raw => exact ambient_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.beaconRaw index raw))

/-- The full adaptive actual typed source tree preserves this exact dependency law on every reply. -/
theorem program_stable {A : Type} (work : OracleComp TypedSpec A) :
    Stable (simulateQ callback work) :=
  RegistrationNativePlatformViewStable.program_stable view
    (RegistrationNativePlatformIdentityCtxReceiptView.view_idempotent) callback
    (handler_stable setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.report_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.report_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.ambient_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.ambient_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.handler_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.handler_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.program_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedReceiptView.program_stable

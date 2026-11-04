-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommands
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuildReceiptView
/-! All four actual ordinary record routes and public environment commands ignore prior Local raw ML receipts while retaining full native/P state and every physical query. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandReceiptView
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformCtxBuildReceiptView (Stable view)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

/-- Ordinary World work does not receive the enclosing prior ML receipt log. -/
theorem world (work : RegistrationNativePlatformCtxRunner.M (PqxdhRecordLiftWorld.State n) Platform A) :
    Stable (RegistrationNativePlatformCtxContext.world (KemSK := KemSK) work) := by
  intro before
  simp only [RegistrationNativePlatformCtxContext.world, StateT.run, Functor.map_map,
    view, RegistrationNativePlatformCtxBuildReceiptView.context, RegistrationNativePlatformCtxSdkReceiptView.serverView,
    RegistrationNativePlatformIdentityReceiptView.view, RegistrationNativePlatformCtxContext.attach, Prod.map_def, id_eq]

private theorem pure_stable (value : A) : Stable (pure value : RegistrationNativePlatformCtxContext.M n KemSK Platform A) :=
  RegistrationNativePlatformViewStable.pure_stable view RegistrationNativePlatformCtxBuildReceiptView.view_idempotent value

private theorem guarded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) :
    Stable (RegistrationNativePlatformCtxContext.guarded setup codec reserve route query) := world _

private theorem record (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : PqxdhRecordLiftInterface.RecordQuery) :
    Stable (RegistrationNativePlatformCtxCommands.record (n := n) setup codec reserve route owners query) := by
  cases query with
  | inl query => exact guarded setup codec reserve route (.inr (.inr (.inl query)))
  | inr pair =>
    rcases pair with ⟨index, query⟩
    cases query with
    | inl plaintext => cases selected : owners[index]? with
      | none => simpa only [RegistrationNativePlatformCtxCommands.record, selected] using (pure_stable (n := n) (KemSK := KemSK) (Platform := Platform) (none : Option RawCtxSourceSend.Encrypted))
      | some owner => simpa only [RegistrationNativePlatformCtxCommands.record, selected] using guarded (n := n) setup codec reserve route (.inr (.inr (.inr (owner, .inl plaintext))))
    | inr raw => cases selected : owners[index]? with
      | none => simpa only [RegistrationNativePlatformCtxCommands.record, selected] using (pure_stable (n := n) (KemSK := KemSK) (Platform := Platform) (core.option.Option.None : core.option.Option RawCtxWholeOwner.Decrypted))
      | some owner => simpa only [RegistrationNativePlatformCtxCommands.record, selected] using guarded (n := n) setup codec reserve route (.inr (.inr (.inr (owner, .inr raw))))

/-- Every literal auxiliary typed command derives its old-receipt independence from the actual World/P lens. -/
theorem command (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : TypedSpec.Domain) :
    Stable (RegistrationNativePlatformCtxCommands.command (n := n) setup codec reserve route owners query) := by
  cases query with
  | inl coin => exact guarded setup codec reserve route (.inr (.inl (.inl coin)))
  | inr query => cases query with
    | hash bytes => exact guarded setup codec reserve route (.inr (.inl (.inr (.hash bytes))))
    | serverSend keyId plaintext => exact record setup codec reserve route owners (.inl (.inl (plaintext, keyId)))
    | serverRaw raw => exact record setup codec reserve route owners (.inl (.inr raw))
    | beaconSend index plaintext => exact record setup codec reserve route owners (.inr (index, .inl plaintext))
    | beaconRaw index raw => exact record setup codec reserve route owners (.inr (index, .inr raw))
    | create edPin mlPin keyId | bundle index | finish index packet | accept packet | build handle application | hmac key message => exact pure_stable _
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandReceiptView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandReceiptView.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandReceiptView.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandReceiptView.command' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandReceiptView.command

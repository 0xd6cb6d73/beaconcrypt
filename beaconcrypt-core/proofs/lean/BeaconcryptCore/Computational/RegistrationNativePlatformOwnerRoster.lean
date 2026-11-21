-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishMetadata
import BeaconcryptCore.Computational.RegistrationNativeOwnerRoster

/-! Every corrected actual typed source callback retains all earlier owner metadata at the same slots and only appends newly created owners. Source writers and corrected assigned-ID finish may update history/phase, with immutable private credential, scalar, public tuple and pin fields retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOwnerRoster
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

attribute [local irreducible] RegistrationNativePlatformSourceAccept.accept
  RegistrationNativePlatformSourceSeal.build

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

omit primitive in
private theorem server_frame (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Value)
    (before after : Native) (previous next : Platform) (reply : Value)
    (supported : ((reply, after), next) ∈ support (((RegistrationNativePlatformExperiment.server work).run before).run previous)) :
    after.beacons = before.beacons ∧ after.pool = before.pool := by
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact ⟨(congrArg (fun result => result.1.2.beacons) same).symm, (congrArg (fun result => result.1.2.pool) same).symm⟩

/-- Every literal corrected callback preserves the complete earlier metadata prefix. -/
theorem handler (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : TypedSpec.Domain) (before after : Native) (previous next : Platform) (reply : TypedSpec.Range query)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure
        allocation reserveRegistration reservePeer erased helper writer query).run before).run previous)) :
    RegistrationNativeOwnerRoster.Prefix before.beacons after.beacons := by
  have ordinary (same : RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure
      allocation reserveRegistration reservePeer erased helper writer query =
      RegistrationNativePlatformExperiment.liftNative (n := n) coins (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)) :
      RegistrationNativeOwnerRoster.Prefix before.beacons after.beacons := by
    rw [same] at supported
    have actual := RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
    exact RegistrationNativeOwnerRoster.typed_prefix setup checks wire route representation created credential query before (reply, after) actual
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | bundle index =>
      refine ⟨[], ?_⟩
      simpa only [List.append_nil] using RegistrationNativePlatformBundleMetadata.native_bundle coins setup checks representation created source writer
        index before after previous next reply supported
    | finish index packet =>
      refine ⟨[], ?_⟩
      simpa only [List.append_nil] using RegistrationNativePlatformFinishMetadata.native_metadata coins setup checks representation created wire
        index packet before after previous next reply supported
    | accept packet =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at supported
      obtain ⟨owners, _pool⟩ := server_frame _ _ after previous next reply supported
      exact ⟨[], by rw [owners]; simp only [List.append_nil]⟩
    | build index application =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
      obtain ⟨⟨⟨result, current⟩, platform⟩, called, same⟩ := supported
      have afterEq : current = after := congrArg (fun result => result.1.2) same
      cases afterEq
      have platformEq : platform = next := congrArg Prod.snd same
      cases platformEq
      obtain ⟨owners, _pool⟩ := server_frame _ before after previous next result called
      exact ⟨[], by rw [owners]; simp only [List.append_nil]⟩
    | create _ _ _ | hmac _ _ | hash _ | serverSend _ _ | serverRaw _ | beaconSend _ _ | beaconRaw _ _ => exact ordinary rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOwnerRoster

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOwnerRoster.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOwnerRoster.handler

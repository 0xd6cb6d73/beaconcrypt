-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleCoherence
import BeaconcryptCore.Computational.RegistrationNativePlatformFinishCoherence
import BeaconcryptCore.Computational.RegistrationNativeBeaconCoherenceRun

/-! Actual corrected Platform execution derives pending control/server-pin coherence for every owner at every supported initialized cut. Effectful writer, authentication, copy/install and all failure prefixes are covered; the original raw compiler and fresh/test samples remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable [primitive : AdapterSealPrimitive.Operations]
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

open RegistrationNativeBeaconCoherence (Holds)

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

/-- Every complete corrected typed callback preserves pending coherence for every retained owner. -/
theorem handler (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : TypedSpec.Domain) (before after : Native) (previous next : Platform) (reply : TypedSpec.Range query)
    (prior : Holds before.beacons)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure
        allocation reserveRegistration reservePeer erased helper writer query).run before).run previous)) : Holds after.beacons := by
  have ordinary (same : RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure
      allocation reserveRegistration reservePeer erased helper writer query =
      RegistrationNativePlatformExperiment.liftNative (n := n) coins (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)) :
      Holds after.beacons := by
    rw [same] at supported
    have actual := RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
    exact RegistrationNativeBeaconCoherenceRun.handler_keeps setup checks wire route representation created credential
      query before (reply, after) prior actual
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | bundle index =>
      exact RegistrationNativePlatformBundleCoherence.native_bundle coins setup checks representation created source writer index
        before after previous next reply prior supported
    | finish index packet =>
      exact RegistrationNativePlatformFinishCoherence.native_finish coins setup checks representation created wire index packet
        before after previous next reply prior supported
    | accept packet =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at supported
      obtain ⟨owners, _pool⟩ := server_frame _ _ after previous next reply supported
      simpa only [owners] using prior
    | build index application =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
      obtain ⟨⟨⟨result, current⟩, platform⟩, called, same⟩ := supported
      have afterEq : current = after := congrArg (fun result => result.1.2) same
      cases afterEq
      have platformEq : platform = next := congrArg Prod.snd same
      cases platformEq
      obtain ⟨owners, _pool⟩ := server_frame _ before after previous next result called
      simpa only [owners] using prior
    | create _ _ _ | hmac _ _ | hash _ | serverSend _ _ | serverRaw _ | beaconSend _ _ | beaconRaw _ _ => exact ordinary rfl

/-- Arbitrary adaptive corrected typed work preserves every retained pending control/pin equation. -/
theorem program (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp TypedSpec Value) (before after : Native) (previous next : Platform) (reply : Value)
    (prior : Holds before.beacons)
    (supported : ((reply, after), next) ∈ support
      (((simulateQ (RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure
        allocation reserveRegistration reservePeer erased helper writer) work).run before).run previous)) : Holds after.beacons := by
  induction work using OracleComp.inductionOn generalizing before after previous next with
  | pure input =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at supported
    exact supported.1.2 ▸ prior
  | query_bind query continuation ih =>
    simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨value, middle⟩, platform⟩, called, continued⟩ := supported
    exact ih value middle after platform next
      (handler coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
        query before middle previous platform value prior called) continued

/-- All original raw modes retain the original private ledger and its original fresh/test samples. -/
theorem initialized (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : (Value × RegistrationNativeLedger.State) × Native) (previous next : Platform)
    (supported : (result, next) ∈ support
      ((RegistrationNativePlatformExperiment.run coins setup checks wire route representation initial.created source initial.credential view failure allocation
        reserveRegistration reservePeer erased helper writer bounds mode work initial.state).run previous)) : Holds result.2.beacons :=
  program coins setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire initial.created.server.server.metadata.sender bounds mode work)
    initial.state result.2 previous next result.1
    (RegistrationNativeBeaconCoherenceRun.start_holds setup source ensureInit identityIndex serverKeyId initial started) supported

end BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCoherenceRun.initialized

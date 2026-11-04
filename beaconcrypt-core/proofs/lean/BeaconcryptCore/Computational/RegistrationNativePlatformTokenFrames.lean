-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
import BeaconcryptCore.Computational.RegistrationNativeTokenCacheTrace

/-! Stateful source Init generation and every corrected callback outside accept cannot create private Server tokens. Actual source writer, allocation and reservation effects are retained, and build only consumes the original source-table entry. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeTokenSource (Present)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem step (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain)
    (before after : Native) (previous next : Platform)
    (reply : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Range query)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer query).run before).run previous)) :
    after.server.sessions = before.server.sessions := by
  cases query with
  | inl query =>
    exact RegistrationNativeTokenTrace.trusted setup checks representation created query before (reply, after)
      (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported)
  | inr query =>
    simp only [RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.writer,
      StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
    obtain ⟨inner, _called, same⟩ := supported
    exact (congrArg (fun value => value.1.2.server.sessions) same).symm

private theorem program (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) Value)
    (before after : Native) (previous next : Platform) (reply : Value)
    (supported : ((reply, after), next) ∈ support
      (((simulateQ (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before).run previous)) :
    after.server.sessions = before.server.sessions := by
  induction work using OracleComp.inductionOn generalizing before after previous next with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact congrArg (fun result => result.1.2.server.sessions) supported
  | query_bind query more ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨⟨value, current⟩, platform⟩, called, continued⟩ := supported
    exact (ih value current after platform next continued).trans
      (step coins setup checks representation created writer query before current previous platform value called)

/-- Complete actual source bundle generation retains the literal private Server token table through every writer outcome. -/
theorem bundle (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) (index : Nat)
    (before after : Native) (previous next : Platform) (reply : RustM (Option Pqxdh.Bytes))
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before).run previous)) :
    after.server.sessions = before.server.sessions := by
  simp only [RegistrationNativePlatformExperiment.bundle, StateT.run, bind_pure_comp, map_apply, support_map] at supported
  obtain ⟨⟨raw, platform⟩, called, same⟩ := supported
  cases same
  exact program coins setup checks representation created writer _ before raw.2 previous platform raw.1 called

variable [primitive : AdapterSealPrimitive.Operations]
attribute [local irreducible] RegistrationNativeExperiment.handler

/-- Every actual corrected callback outside accept only inherits live private tokens from its input. -/
theorem handler (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : RegistrationNativeTokenCacheTrace.NonAccept query)
    (before after : Native) (previous next : Platform) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before).run previous))
    (token : peer.ConsumedRegistration) (present : Present token after.server) : Present token before.server := by
  have ordinary (same : RegistrationNativePlatformExperiment.handler (n := n) coins setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer erased helper writer query = RegistrationNativePlatformExperiment.liftNative coins
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query)) : Present token before.server := by
    rw [same] at supported
    have called := RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported
    rcases RegistrationNativeTokenTrace.call_origin setup checks wire route representation created credential ⟨query, before, reply, after⟩ called token present with old | origin
    · exact old
    · obtain ⟨packet, _events, _authenticated, _checked, queryEq, _called, _born⟩ := origin
      change query = .inr (.accept packet) at queryEq
      rw [queryEq] at allowed
      exact False.elim allowed
  cases query with
  | inl coin => exact ordinary rfl
  | inr command => cases command with
    | accept packet => exact False.elim allowed
    | bundle index =>
      have same := bundle coins setup checks representation created writer index before after previous next reply supported
      simpa only [Present, same] using present
    | finish index packet =>
      have same := RegistrationNativeTokenTrace.beacon setup checks representation created _ before (reply, after)
        (RegistrationNativePlatformHashReceipt.native_support coins _ _ previous next supported)
      change after.server.sessions = before.server.sessions at same
      simpa only [Present, same] using present
    | build index application =>
      simp only [RegistrationNativePlatformExperiment.handler, StateT.run, bind_pure_comp, map_apply, support_map] at supported
      obtain ⟨⟨⟨raw, current⟩, platform⟩, called, same⟩ := supported
      have currentEq : current = after := congrArg (fun result => result.1.2) same
      cases currentEq
      simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at called
      obtain ⟨⟨⟨value, frontend⟩, finalPlatform⟩, reached, closed⟩ := called
      have serverEq : frontend = after.server := congrArg (fun result => result.1.2.server) closed
      apply RegistrationNativePlatformTokenBuild.build coins setup (RegistrationNativeWire.ledgerCodec wire) view failure allocation erased reservePeer
        (RegistrationNativeMldsa.owned source credential) helper writer index application before.server previous ((value, frontend), finalPlatform) reached token
      simpa only [serverEq] using present
    | _ => exact ordinary rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames.handler

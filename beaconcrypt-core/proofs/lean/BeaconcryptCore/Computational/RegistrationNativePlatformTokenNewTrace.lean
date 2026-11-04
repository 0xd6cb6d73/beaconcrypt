-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace

/-! The first appearance of a token in one chronological source path is an actual successful accept. This selects a source call from the execution's own ordered table changes; it does not select an independent supported Root computation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeTokenSource (Present)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

/-- Any token absent initially and present finally crosses a literal first table-insertion cut. -/
theorem first {implementation : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT Whole ProbComp)}
    {before after : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path implementation before calls after) (token : peer.ConsumedRegistration)
    (empty : ¬ Present token before.1.server) (present : Present token after.1.server) :
    ∃ call ∈ calls, ¬ Present token call.before.1.server ∧ Present token call.after.1.server := by
  induction reached with
  | nil => exact False.elim (empty present)
  | cons call called rest last following ih =>
    by_cases now : Present token call.after.1.server
    · exact ⟨call, List.mem_cons_self, empty, now⟩
    · obtain ⟨later, member, old, added⟩ := ih now present
      exact ⟨later, List.mem_cons_of_mem _ member, old, added⟩

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- A new token in an actual source callback forces its exact successful accept reply. -/
theorem callback (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (called : Executed impl call)
    (token : peer.ConsumedRegistration) (empty : ¬ Present token call.before.1.server)
    (present : Present token call.after.1.server) :
    ∃ packet handle before after, call = ⟨.inr (.accept packet), before, .ok (some handle), after⟩ := by
  have actual : ((call.reply, call.after.1), call.after.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer call.query).run call.before.1).run call.before.2) := by
    simp only [Executed, RegistrationNativePlatformInitPendingJournal.callback, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at called
    obtain ⟨⟨⟨value, native⟩, platform⟩, supported, same⟩ := called
    have replyEq : value = call.reply := congrArg Prod.fst same
    have nativeEq : native = call.after.1 := congrArg (fun result => result.2.1) same
    have platformEq : platform = call.after.2 := congrArg (fun result => result.2.2) same
    rw [replyEq, nativeEq, platformEq] at supported
    exact supported
  by_cases allowed : RegistrationNativeTokenCacheTrace.NonAccept call.query
  · exact False.elim (empty (RegistrationNativePlatformTokenFrames.handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query allowed call.before.1 call.after.1 call.before.2 call.after.2 call.reply actual token present))
  · rcases call with ⟨query, before, reply, after⟩
    cases query with
    | inl query => exact False.elim (allowed trivial)
    | inr query => cases query with
      | accept packet =>
        simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at actual
        simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at actual
        obtain ⟨⟨⟨result, current⟩, platform⟩, supported, same⟩ := actual
        have stateEq : current = after.1.server := congrArg (fun result => result.1.2.server) same
        have replyEq : result = reply := congrArg (fun result => result.1.1) same
        have currentPresent : Present token current := by simpa only [stateEq] using present
        rcases RegistrationNativePlatformTokenReply.accept coins setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration route source.verify
          representation created packet before.1.server before.2 ((result, current), platform) supported token currentPresent with old | ⟨handle, returned⟩
        · exact False.elim (empty old)
        · change result = .ok (some handle) at returned
          exact ⟨packet, handle, before, after, by rw [← replyEq, returned]⟩
      | _ => exact False.elim (allowed trivial)

/-- Every final token has an earlier actual successful accept at its first appearance in this same initialized table path. -/
theorem path {before after : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl before calls after) (token : peer.ConsumedRegistration)
    (empty : ¬ Present token before.1.server) (present : Present token after.1.server) :
    ∃ packet handle first last,
      (⟨.inr (.accept packet), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls ∧
      ¬ Present token first.1.server ∧ Present token last.1.server := by
  obtain ⟨call, member, absent, added⟩ := first reached token empty present
  obtain ⟨_leading, _trailing, _split, _before, executed, _after⟩ := reached.member call member
  obtain ⟨packet, handle, first, last, same⟩ := callback coins setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer call executed token absent added
  subst call
  exact ⟨packet, handle, first, last, member, absent, added⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace.first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace.first

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace.path

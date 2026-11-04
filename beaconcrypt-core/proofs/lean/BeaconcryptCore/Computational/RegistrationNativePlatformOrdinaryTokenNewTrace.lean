-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenReply
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenNewTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperimentRouting

/-! The first appearance of a token in one chronological source path is an actual successful accept. This selects a source call from the execution's own ordered table changes; it does not select an independent supported Root computation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativeTokenSource (Present)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

private theorem only_accept (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (absent : ¬ RegistrationNativeTokenCacheTrace.NonAccept query) :
    ∃ packet, query = .inr (.accept packet) := by
  cases query with
  | inl query => exact False.elim (absent trivial)
  | inr query => cases query with
    | accept packet => exact ⟨packet, rfl⟩
    | _ => exact False.elim (absent trivial)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin RegistrationNativePlatformOrdinaryExperiment.handler
  RegistrationNativePlatformOrdinaryExperiment.record RegistrationNativePlatformOrdinaryWorld.guarded
  RegistrationNativePlatformExperiment.handler RegistrationNativePlatformSourceSeal.build
  RegistrationNativePlatformOrdinaryKemClientJournal.actual RegistrationNativePlatformInitPendingJournal.callback

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem known_accept (packet : registration.InitPacket) (before after : Whole)
    (reply : RustM (Option Nat))
    (called : Executed impl (⟨.inr (.accept packet), before, reply, after⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (token : peer.ConsumedRegistration) (empty : ¬ Present token before.1.server) (present : Present token after.1.server) :
    ∃ actual handle first last,
      (⟨.inr (.accept packet), before, reply, after⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) =
        ⟨.inr (.accept actual), first, .ok (some handle), last⟩ := by
  have same : RegistrationNativePlatformOrdinaryKemClientJournal.actual (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.accept packet)) =
      RegistrationNativePlatformInitPendingJournal.callback (n := n) RegistrationNativePlatformMldsaProgram.coins setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
          reserveRegistration reservePeer erased helper writer (.inr (.accept packet)) := by
    have law := congrFun (RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal (n := n) setup checks wire route representation
      created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) (.inr (.accept packet))
    simp only [RegistrationNativePlatformOrdinaryExperimentRouting.terminal] at law
    unfold RegistrationNativePlatformOrdinaryKemClientJournal.actual RegistrationNativePlatformInitPendingJournal.callback
    exact congrArg RegistrationNativePlatformPackedState.pack law
  unfold Executed at called
  rw [same] at called
  exact RegistrationNativePlatformTokenNewTrace.callback RegistrationNativePlatformMldsaProgram.coins setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer _ called token empty present

/-- A new token in an actual source callback forces its exact successful accept reply. -/
theorem callback (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (called : Executed impl call)
    (token : peer.ConsumedRegistration) (empty : ¬ Present token call.before.1.server)
    (present : Present token call.after.1.server) :
    ∃ packet handle before after, call = ⟨.inr (.accept packet), before, .ok (some handle), after⟩ := by
  have actual : ((call.reply, call.after.1), call.after.2) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer call.query).run call.before.1).run call.before.2) := by
    simp only [Executed, RegistrationNativePlatformOrdinaryKemClientJournal.actual, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at called
    obtain ⟨⟨⟨value, native⟩, platform⟩, supported, same⟩ := called
    have replyEq : value = call.reply := congrArg Prod.fst same
    have nativeEq : native = call.after.1 := congrArg (fun result => result.2.1) same
    have platformEq : platform = call.after.2 := congrArg (fun result => result.2.2) same
    rw [replyEq, nativeEq, platformEq] at supported
    exact supported
  by_cases allowed : RegistrationNativeTokenCacheTrace.NonAccept call.query
  · exact False.elim (empty (RegistrationNativePlatformOrdinaryTokenFrames.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer call.query allowed call.before.1 call.after.1 call.before.2 call.after.2 call.reply actual token present))
  · obtain ⟨packet, queryEq⟩ := only_accept call.query allowed
    rcases call with ⟨query, before, reply, after⟩
    change query = .inr (.accept packet) at queryEq
    subst query
    exact known_accept setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer packet before after reply called token empty present

/-- Every final token has an earlier actual successful accept at its first appearance in this same initialized table path. -/
theorem path {before after : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl before calls after) (token : peer.ConsumedRegistration)
    (empty : ¬ Present token before.1.server) (present : Present token after.1.server) :
    ∃ packet handle first last,
      (⟨.inr (.accept packet), first, .ok (some handle), last⟩ : Call RegistrationNativeRawAdapter.TypedSpec Whole) ∈ calls ∧
      ¬ Present token first.1.server ∧ Present token last.1.server := by
  obtain ⟨call, member, absent, added⟩ := RegistrationNativePlatformTokenNewTrace.first reached token empty present
  obtain ⟨_leading, _trailing, _split, _before, executed, _after⟩ := reached.member call member
  obtain ⟨packet, handle, first, last, same⟩ := callback setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer call executed token absent added
  subst call
  exact ⟨packet, handle, first, last, member, absent, added⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace.callback' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace.callback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenNewTrace.path

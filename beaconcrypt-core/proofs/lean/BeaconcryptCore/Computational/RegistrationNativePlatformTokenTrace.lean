-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource
import BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal

/-! Every consumed token on an actual corrected initialized source path has an earlier mandatory Init authentication and actual agreement/replay-consume birth in that same path. Exact pin/hash, external-state and final authentication-cache cuts are retained; no final-history origin or completed-peer premise replaces this source chronology. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeTokenSource (Present Born)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

def SourceAt (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (token : peer.ConsumedRegistration) : Prop :=
  ∃ packet pin pinned pinPlatform events authenticated checked authPlatform,
    call.query = .inr (.accept packet) ∧
    ((.ok (.Some pin), pinned), pinPlatform) ∈ support
      (((RegistrationNativePlatformSourceBuild.pin coins).run call.before.1.server).run call.before.2) ∧
    ((.ok (events, .Accepted authenticated), checked), authPlatform) ∈ support
      (((RegistrationNativePlatformSourceAccept.authenticate coins setup (RegistrationNativeWire.ledgerCodec wire) route source.verify pin packet).run pinned).run pinPlatform) ∧
    Born setup checks representation created packet authenticated checked token ∧
    RegistrationNativeInitFinal.summary checked = RegistrationNativeInitFinal.summary call.after.1.server

variable [primitive : AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformInitPendingJournal.callback coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationServerNativeSource.authenticate
  RegistrationServerNativeSource.agree RegistrationWorldAuthentication.begin RegistrationAuthenticationShared.begin

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  simp only [RegistrationNativePlatformInitPendingJournal.callback, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem accept_origin (packet : registration.InitPacket) (before after : Whole) (reply : RustM (Option Nat))
    (called : ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer (.inr (.accept packet))).run before.1).run before.2))
    (token : peer.ConsumedRegistration) (present : Present token after.1.server) :
    Present token before.1.server ∨ SourceAt coins setup checks wire route representation created ⟨.inr (.accept packet), before, reply, after⟩ token := by
  simp only [RegistrationNativePlatformExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind] at called
  simp only [RegistrationNativePlatformExperiment.server, StateT.run, map_apply, support_map] at called
  obtain ⟨⟨⟨result, current⟩, platform⟩, supported, same⟩ := called
  have stateEq : current = after.1.server := congrArg (fun result => result.1.2.server) same
  have currentPresent : Present token current := by simpa only [stateEq] using present
  rcases RegistrationNativePlatformTokenSource.accept coins setup (RegistrationNativeWire.ledgerCodec wire) checks reserveRegistration route source.verify
      representation created packet before.1.server before.2 ((result, current), platform) supported token currentPresent with old | origin
  · exact Or.inl old
  · obtain ⟨pin, pinned, pinPlatform, events, authenticated, checked, authPlatform, pinCalled, authCalled, born, summaryEq⟩ := origin
    exact Or.inr ⟨packet, pin, pinned, pinPlatform, events, authenticated, checked, authPlatform, rfl, pinCalled, authCalled, born,
      summaryEq.trans (congrArg RegistrationNativeInitFinal.summary stateEq)⟩

/-- Every literal actual callback retains a prior token or supplies its own mandatory source authentication/agreement birth. -/
theorem call_origin (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (called : Executed impl call)
    (token : peer.ConsumedRegistration) (present : Present token call.after.1.server) :
    Present token call.before.1.server ∨ SourceAt coins setup checks wire route representation created call token := by
  have sourceCalled := actual coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
    call.query call.before call.after call.reply called
  by_cases allowed : RegistrationNativeTokenCacheTrace.NonAccept call.query
  · exact Or.inl (RegistrationNativePlatformTokenFrames.handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query allowed call.before.1 call.after.1 call.before.2 call.after.2 call.reply sourceCalled token present)
  · rcases call with ⟨query, before, reply, after⟩
    cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr query => cases query with
      | accept packet =>
        exact accept_origin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
          packet before after reply sourceCalled token present
      | _ => exact False.elim (allowed trivial)

/-- The actual chronological source path identifies the same earlier authentication cut of every surviving token. -/
theorem path_origin {first last : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls last) (token : peer.ConsumedRegistration) (present : Present token last.1.server) :
    Present token first.1.server ∨ ∃ call ∈ calls, SourceAt coins setup checks wire route representation created call token := by
  induction reached with
  | nil => exact Or.inl present
  | cons call called rest last following ih =>
    rcases ih present with old | ⟨earlier, member, origin⟩
    · rcases call_origin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
        call called token old with initial | born
      · exact Or.inl initial
      · exact Or.inr ⟨call, List.mem_cons_self, born⟩
    · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ member, origin⟩

/-- Moving an actual source table entry derives its earlier source authentication/birth cut and literal leading/trailing in the same execution. -/
theorem taken_origin {first beforeBuild : Whole} {calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole)}
    (reached : Path impl first calls beforeBuild) (empty : first.1.server.sessions = [])
    (index : Nat) (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (taken : RegistrationServerSdkSource.take index beforeBuild.1.server = (some token, current)) :
    ∃ call leading trailing, calls = leading ++ call :: trailing ∧ Path impl first leading call.before ∧ Executed impl call ∧
      Path impl call.after trailing beforeBuild ∧ SourceAt coins setup checks wire route representation created call token := by
  have found := (RegistrationNativeTokenSource.take_origin index beforeBuild.1.server current token taken).1
  have present : Present token beforeBuild.1.server := List.mem_of_getElem? found
  rcases path_origin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      reached token present with initial | ⟨call, member, origin⟩
  · simp only [Present, empty, List.not_mem_nil] at initial
  · obtain ⟨leading, trailing, split, earlier, called, later⟩ := reached.member call member
    exact ⟨call, leading, trailing, split, earlier, called, later, origin⟩

/-- A moved token in an actual initialized journal derives its same-run earlier source authentication, rather than requiring a caller-supplied origin history. -/
theorem initialized_taken (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (Whole × List (Call RegistrationNativeRawAdapter.TypedSpec Whole)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler impl) work).run ((initial.state, previous), [])))
    (index : Nat) (token : peer.ConsumedRegistration) (current : RegistrationServerFrontendCompiler.State n)
    (taken : RegistrationServerSdkSource.take index result.2.1.1.server = (some token, current)) :
    ∃ call leading trailing, result.2.2 = leading ++ call :: trailing ∧ Path impl (initial.state, previous) leading call.before ∧
      Executed impl call ∧ Path impl call.after trailing result.2.1 ∧ SourceAt coins setup checks wire route representation created call token := by
  exact taken_origin coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
    (RegistrationNativeStageTrace.path impl work (initial.state, previous) result supported)
    (RegistrationNativeTokenTrace.start_empty setup ensureInit identityIndex serverKeyId initial startup) index token current taken

omit primitive in
/-- The actual token's earlier source authentication leaves its original Init preimage at the actual returned acceptance cache. -/
theorem source_cache (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (token : peer.ConsumedRegistration)
    (origin : SourceAt coins setup checks wire route representation created call token) :
    ∃ packet authenticated, ∃ (checked : RegistrationServerFrontendCompiler.State n), ∃ digest,
      call.query = .inr (.accept packet) ∧ Born setup checks representation created packet authenticated checked token ∧
      call.after.1.server.world.world.1.primitive.2
        ((), RegistrationAuthentication.initPreimage call.before.1.server.pin packet) = some digest ∧
      authenticated.binding.init_hash = RegistrationAuthenticationShared.digestArray digest := by
  obtain ⟨packet, pin, pinned, pinPlatform, events, authenticated, checked, authPlatform, queryEq, pinCalled, authCalled, born, summaryEq⟩ := origin
  obtain ⟨digest, receipt, binding⟩ := RegistrationNativePlatformTokenCacheSource.authenticated_cache coins setup (RegistrationNativeWire.ledgerCodec wire) route source.verify
    created packet call.before.1.server pinned checked call.before.2 pinPlatform authPlatform pin events authenticated pinCalled authCalled
  have cacheEq : checked.world.world.1.primitive.2 = call.after.1.server.world.world.1.primitive.2 :=
    congrArg (fun value : RegistrationSigningShared.State => value.2) summaryEq
  rw [cacheEq] at receipt
  exact ⟨packet, authenticated, checked, digest, queryEq, born, receipt, binding⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.call_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.call_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.path_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.path_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.taken_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.taken_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.initialized_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.initialized_taken

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.source_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTokenTrace.source_cache

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! The literal current parsed-accept counter equals the original native ledger scan at every full chronological prefix under any persistent Word interpretation. Counter increments are derived from free source bodies and exact raw compilation, including malformed packets and all callback failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform E Private A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
abbrev State (source : RegistrationNativeMldsa.Source) (Platform Private : Type) :=
  RegistrationNativePlatformLorStatefulSupport.State (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformLorStatefulSupport.typed implementation controller


open RegistrationNativePlatformLorSourceRetainedControl (close)
open RegistrationNativePlatformLorSourcePlatform (extend)
open RegistrationNativePlatformLorIdealStateLift (interpret)
open RegistrationNativeSecretWordSessionSlots (Preserves)
omit primitive in
private theorem local_factor (routed : Bool) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (server : RegistrationNativeSecretWordMessage.ServerState) (env : RegistrationServerReferenceCompiler.Environment)
    (previous : Platform) (before : Private) :
    (close (RegistrationNativePlatformSecretWordOpen.accept
      (extend implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal routed)
      (interpret implementation (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration))
      setup checks verify packet)).run (server,(env,(previous,before))) =
      (fun result => (result.1.1.1.1,(result.1.1.1.2,(result.1.1.2,(result.1.2,result.2))))) <$>
        (simulateQ implementation
          ((((RegistrationNativePlatformSecretWordOpen.accept (RegistrationNativePlatformSecretWordFrontendView.wordLocal routed)
            (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) setup checks verify packet).run server).run env).run previous)).run before := by
  have natural := RegistrationNativePlatformSecretWordOpenMap.accept
    (RegistrationNativePlatformLorIdealStateLift.hom (P := Platform) implementation)
    (RegistrationNativePlatformSecretWordFrontendView.wordLocal routed)
    (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) setup checks verify packet server env
  rw [RegistrationNativePlatformLorSourcePlatform.local_source] at natural
  have ran := congrArg (fun action => action.run (previous,before)) natural
  have mapped := congrArg (Functor.map (fun result => (result.1.1.1,(result.1.1.2,(result.1.2,result.2))))) ran.symm
  simpa only [RegistrationNativePlatformLorSourceRetainedControl.close,RegistrationNativePlatformLorIdealStateLift.interpret,StateT.run,Functor.map_map] using mapped

omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$>work) before=Prod.map f id <$>work before := StateT.run_map _ _ _
omit primitive in
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl
omit primitive in
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before=pure (before,before) := rfl
omit primitive in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (f : S → S) (before : S) :
    (modify f : StateT S m Unit) before=pure ((),f before) := rfl

theorem accept_run (packet : registration.InitPacket) (before : State source Platform Private) :
    (typed (.inr (.accept packet))).run before =
      (fun result => (result.1,(({before.1.1 with server:=result.2.1,environment:=result.2.2.1,parsedAccepts:=before.1.1.parsedAccepts+1},result.2.2.2.1),result.2.2.2.2))) <$>
        (close (RegistrationNativePlatformSecretWordOpen.accept
          (extend implementation ∘ₛ RegistrationNativeSecretWordInterface.liftLocal (decide (before.1.1.parsedAccepts=selectedAccept)))
          (interpret implementation (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration)) setup checks source.verify packet)).run
          (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) := by
  rw [local_factor setup checks reserveRegistration implementation]
  rw [RegistrationNativePlatformLorStatefulSupport.typed_run]
  simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.accept,
    bind_apply,get_apply,modify_apply,pure_bind,RegistrationNativePlatformSecretWordFrontend.serverOpen,
    StateT.run,simulateQ_map,map_apply,Functor.map_map]
  rfl

theorem typed_fresh (packet : registration.InitPacket) (handle : Nat) (before after : State source Platform Private)
    (supported : (.ok (some handle),after) ∈ support ((typed (.inr (.accept packet))).run before)) :
    handle=before.1.1.server.sessions.length := by
  rw [accept_run,support_map] at supported
  obtain ⟨⟨reply,reached⟩,called,equal⟩ := supported
  have replyEq : reply=.ok (some handle) := congrArg Prod.fst equal
  subst reply
  exact RegistrationNativePlatformLorSourceSessionShape.fresh _ setup checks _ source.verify packet _ _ handle called

/-- Every actual current typed callback preserves each surviving earlier one-use session, including dynamic writer failures. -/
theorem typed_preserves (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform Private)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform Private)
    (supported : result ∈ support ((typed query).run before)) :
    Preserves before.1.1.server.sessions result.2.1.1.server.sessions := by
  have free := RegistrationNativePlatformLorStatefulSupport.typed_support implementation controller query before result supported
  by_cases accepts : RegistrationNativeRawAdapter.kind query = 3
  · cases query with
    | inl coin => cases accepts
    | inr command => cases command with
      | accept packet =>
        rw [accept_run,support_map] at supported
        obtain ⟨reached,called,equal⟩ := supported
        have shape := RegistrationNativePlatformLorSourceSessionShape.accept _ setup checks _ source.verify packet
          (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) reached called
        cases equal
        exact RegistrationNativeSecretWordSessionSlots.shape _ _ _ shape
      | _ => cases accepts
  · by_cases builds : RegistrationNativeRawAdapter.kind query = 4
    · cases query with
      | inl coin => cases builds
      | inr command => cases command with
        | build handle application =>
          have same := RegistrationNativePlatformSecretWordLiveBuild.sessions setup sign view failure allocation erased helper writer reservePeer
            source handle application before.1 (result.1,result.2.1) free
          rw [same]
          exact RegistrationNativeSecretWordSessionSlots.take handle before.1.1.server
        | _ => cases builds
    · have same := RegistrationNativePlatformSecretWordLiveState.quiet_server setup checks
        wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query ⟨accepts,builds⟩ before.1 (result.1,result.2.1) free
      rw [same]
      exact RegistrationNativeSecretWordSessionSlots.refl _

omit primitive in
private theorem program_preserves {Index : Type} {spec : OracleSpec Index}
    (localInterpreter : QueryImpl spec (StateT (State source Platform Private) ProbComp))
    (step : ∀ query before result, result ∈ support ((localInterpreter query).run before) →
      Preserves before.1.1.server.sessions result.2.1.1.server.sessions)
    (work : OracleComp spec A) (before : State source Platform Private) (result : A × State source Platform Private)
    (supported : result ∈ support ((simulateQ localInterpreter work).run before)) :
    Preserves before.1.1.server.sessions result.2.1.1.server.sessions := by
  apply OracleComp.simulateQ_run_preserves_inv_of_query localInterpreter
    (fun current => Preserves before.1.1.server.sessions current.1.1.server.sessions)
    (fun query current prior next reached => RegistrationNativeSecretWordSessionSlots.trans _ _ _ prior
      (step query current next reached)) work before _ result supported
  exact RegistrationNativeSecretWordSessionSlots.refl _

/-- Malformed raw requests and all decoded callbacks retain the same surviving stored session values. -/
theorem raw (query : RegistrationNativeInterface.Spec.Domain) (before : State source Platform Private)
    (result : RegistrationNativeInterface.Spec.Range query × State source Platform Private)
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler
      wire typed query).run before)) :
    Preserves before.1.1.server.sessions result.2.1.1.server.sessions :=
  program_preserves source typed
    (typed_preserves setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation)
    (RegistrationNativeRawAdapter.adapter wire query) before result supported

/-- Every complete original full-interface callback preserves those same old slots, including all secrecy coin/send continuations. -/
theorem full (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State source Platform Private)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State source Platform Private))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      wire serverKeyId bounds typed query).run before)) :
    Preserves before.2.1.1.server.sessions result.2.2.1.1.server.sessions := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  exact program_preserves source (RegistrationNativeRawAdapter.handler wire typed)
    (raw setup checks wire source sign
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation)
    _ before.2 reached called

/-- Actual later chronological calls can only consume an old capability or append a new slot, never replace its Ready. -/
theorem path (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    {before after : RegistrationNativeLedger.State × State source Platform Private}
    {entries : List RegistrationNativeInterface.Entry}
    (actual : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire
        serverKeyId bounds typed) before entries after) :
    Preserves before.2.1.1.server.sessions after.2.1.1.server.sessions := by
  apply RegistrationNativeSecretWordTargetPath.preserves _
    (fun current => Preserves before.2.1.1.server.sessions current.2.1.1.server.sessions)
    (fun query current result prior reached => RegistrationNativeSecretWordSessionSlots.trans _ _ _ prior
      (full setup checks wire source sign
        selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation
        serverKeyId bounds query current result reached)) actual
  exact RegistrationNativeSecretWordSessionSlots.refl _

/-- Successfully decoded original raw accepts return exactly that same fresh source slot. -/
private theorem raw_fresh (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit wire raw=some packet)
    (before after : State source Platform Private)
    (supported : (some handle,after) ∈ support ((RegistrationNativeRawAdapter.handler
      wire typed (.inr (.accept raw))).run before)) :
    handle=before.1.1.server.sessions.length := by
  simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,
    decoded,simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,returned⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual,RegistrationNativeRawAdapter.resultOption] at returned
  | ok reply =>
    simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at returned
    obtain ⟨rfl,rfl⟩ := returned
    exact typed_fresh setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation packet handle before _
      (by simpa only [actual] using reached)

/-- The original complete ledger callback retains its actual pre-call fresh index and all failure semantics. -/
theorem full_fresh (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (raw : Pqxdh.Bytes)
    (packet : registration.InitPacket) (handle : Nat)
    (decoded : RegistrationNativeWire.readInit wire raw=some packet)
    (before after : RegistrationNativeLedger.State × State source Platform Private)
    (supported : (some handle,after) ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto
      wire serverKeyId bounds typed (.inl (.inr (.accept raw)))).run before)) :
    handle=before.2.1.1.server.sessions.length := by
  rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
  obtain ⟨⟨reply,current⟩,reached,returned⟩ := supported
  have success : reply=some handle := congrArg Prod.fst returned
  subst reply
  exact raw_fresh setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation _ packet handle decoded before.2 current reached

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.accept_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.typed_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.typed_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.typed_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.typed_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.raw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.full

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.full_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions.full_fresh

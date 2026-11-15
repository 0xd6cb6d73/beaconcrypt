-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessions
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceSessionShape
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceAcceptFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordSessionSlotsSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
/-! Every Ready in the corrected source roster either survives an earlier slot or originates at the actual successful accept returning that same session handle. Parsed attempt counters remain a separate source coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions
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


def Creates (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (handle : Nat) : Prop :=
  match query with
  | .inr (.accept _) => reply=.ok (some handle)
  | _ => False

omit primitive in
private theorem appended (before : List (Option RegistrationNativeSecretWordMessage.ServerReady))
    (reply : RustM (Option Nat)) (after : List (Option RegistrationNativeSecretWordMessage.ServerReady))
    (shape : RegistrationNativeSecretWordAtomSessionShape.Shape before reply after)
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : after[handle]?=some (some ready)) :
    before[handle]?=some (some ready) ∨ reply=.ok (some handle) := by
  rcases shape with same | ⟨actual,same,returned⟩
  · exact Or.inl (same ▸ stored)
  · by_cases prior : handle<before.length
    · exact Or.inl (by simpa only [same,List.getElem?_append_left prior] using stored)
    · have bound := (List.getElem?_eq_some_iff.mp stored).1
      rw [same,List.length_append,List.length_singleton] at bound
      have index : handle=before.length := by omega
      exact Or.inr (index ▸ returned)

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

/-- A current typed callback can create a new surviving Ready only at its own successfully returned accept session. -/
theorem typed_origin (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source Platform Private)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source Platform Private)
    (supported : result ∈ support ((typed query).run before))
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : result.2.1.1.server.sessions[handle]?=some (some ready)) :
    before.1.1.server.sessions[handle]?=some (some ready) ∨ Creates query result.1 handle := by
  have free := RegistrationNativePlatformLorStatefulSupport.typed_support implementation controller query before result supported
  by_cases accepts : RegistrationNativeRawAdapter.kind query=3
  · cases query with
    | inl coin => cases accepts
    | inr command => cases command with
      | accept packet =>
        rw [RegistrationNativePlatformLorSourceSessions.accept_run,support_map] at supported
        obtain ⟨reached,called,equal⟩ := supported
        have shape := RegistrationNativePlatformLorSourceSessionShape.accept _ setup checks _ source.verify packet
          (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) reached called
        cases equal
        exact appended _ _ _ shape handle ready stored
      | _ => cases accepts
  · by_cases builds : RegistrationNativeRawAdapter.kind query=4
    · cases query with
      | inl coin => cases builds
      | inr command => cases command with
        | build session application =>
          have same := RegistrationNativePlatformSecretWordLiveBuild.sessions setup sign view failure allocation erased helper writer reservePeer
            source session application before.1 (result.1,result.2.1) free
          have slots := RegistrationNativeSecretWordSessionSlots.take session before.1.1.server
          have found : (RegistrationNativeSecretWordServerMaterial.take session before.1.1.server).2.sessions[handle]?=some (some ready) := same ▸ stored
          have below := (List.getElem?_eq_some_iff.mp found).1
          have size : (RegistrationNativeSecretWordServerMaterial.take session before.1.1.server).2.sessions.length=before.1.1.server.sessions.length := by
            unfold RegistrationNativeSecretWordServerMaterial.take
            split <;> simp only [List.length_set]
          exact Or.inl (slots.2 handle (by omega) ready found)
        | _ => cases builds
    · have same := RegistrationNativePlatformSecretWordLiveState.quiet_server setup checks
        wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query ⟨accepts,builds⟩ before.1 (result.1,result.2.1) free
      exact Or.inl (same ▸ stored)

omit primitive in
private theorem program_backwards {J S X : Type} {spec : OracleSpec J}
    (impl : QueryImpl spec (StateT S ProbComp))
    (sessions : S → List (Option RegistrationNativeSecretWordMessage.ServerReady)) (allowed : J → Prop)
    (step : ∀ query, allowed query → ∀ before result, result ∈ support ((impl query).run before) →
      ∀ (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady), (sessions result.2)[handle]?=some (some ready) → (sessions before)[handle]?=some (some ready))
    (work : OracleComp spec X) (permitted : work.AllQueriesSatisfy allowed)
    (before : S) (result : X × S) (supported : result ∈ support ((simulateQ impl work).run before))
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : (sessions result.2)[handle]?=some (some ready)) : (sessions before)[handle]?=some (some ready) := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact stored
  | query_bind query next ih =>
    rw [allQueriesSatisfy_query_bind_iff] at permitted
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨⟨reply,middle⟩,called,continued⟩ := supported
    have prior := ih reply (permitted.2 reply) middle result continued stored
    exact step query permitted.1 before (reply,middle) called handle ready prior

/-- A raw callback outside acceptance cannot create a new retained session. -/
theorem raw_old (query : RegistrationNativeInterface.Spec.Domain)
    (quiet : RegistrationNativeLedgerCaps.coreKind query≠3) (before : State source Platform Private)
    (result : RegistrationNativeInterface.Spec.Range query × State source Platform Private)
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler wire typed query).run before))
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : result.2.1.1.server.sessions[handle]?=some (some ready)) :
    before.1.1.server.sessions[handle]?=some (some ready) := by
  have bounded := RegistrationNativeRawAdapter.query_bound wire query 3
  simp only [quiet,ite_false] at bounded
  have permitted : (RegistrationNativeRawAdapter.adapter wire query).AllQueriesSatisfy
      (fun request => RegistrationNativeRawAdapter.kind request≠3) :=
    (isQueryBoundP_zero_iff _ _).mp (by simpa only [not_not] using bounded)
  apply program_backwards typed (fun current => current.1.1.server.sessions)
    (fun request => RegistrationNativeRawAdapter.kind request≠3) ?_
    (RegistrationNativeRawAdapter.adapter wire query) permitted before result supported handle ready stored
  intro request notAccept current reached called index actual found
  rcases typed_origin setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation request current reached called index actual found with old | created
  · exact old
  · cases request with
    | inl coin => cases created
    | inr command => cases command <;> first | cases notAccept rfl | cases created

variable (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "full" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
local notation "FullState" => RegistrationNativeLedger.State × State source Platform Private

/-- Secrecy wrappers and every other non-accept full callback cannot create a new retained session. -/
theorem full_old (query : RegistrationNativeInterface.FullSpec.Domain)
    (quiet : RegistrationNativeInterface.queryClass query≠3) (before : FullState)
    (result : RegistrationNativeInterface.FullSpec.Range query × FullState)
    (supported : result ∈ support ((full query).run before))
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : result.2.2.1.1.server.sessions[handle]?=some (some ready)) :
    before.2.1.1.server.sessions[handle]?=some (some ready) := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  have cost : PqxdhDeploymentCompileSecrecy.wrapCost bounds 3 (RegistrationNativeInterface.queryClass query)=0 := by
    have different : (RegistrationNativeInterface.queryClass query).val≠3 := by
      intro equal
      exact quiet (Fin.ext equal)
    simp only [PqxdhDeploymentCompileSecrecy.wrapCost]
    split_ifs <;> omega
  have bounded := RegistrationNativeLedgerCaps.step_bound setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds 3 query before.1
  rw [cost] at bounded
  have permitted : ((RegistrationNativeLedger.handler setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query).run before.1).AllQueriesSatisfy
      (fun request => RegistrationNativeLedgerCaps.coreKind request≠3) :=
    (isQueryBoundP_zero_iff _ _).mp (by simpa only [not_not] using bounded)
  apply program_backwards (RegistrationNativeRawAdapter.handler wire typed) (fun current => current.1.1.server.sessions)
    (fun request => RegistrationNativeLedgerCaps.coreKind request≠3) ?_ _ permitted before.2 reached called handle ready stored
  intro request notAccept current next possible index actual found
  exact raw_old setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation request notAccept current next possible index actual found

/-- A raw accept's only new Ready belongs to its actual successful returned session, regardless of earlier failures. -/
theorem raw_accept (raw : Pqxdh.Bytes) (before : State source Platform Private)
    (result : Option Nat × State source Platform Private)
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler wire typed (.inr (.accept raw))).run before))
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : result.2.1.1.server.sessions[handle]?=some (some ready)) :
    before.1.1.server.sessions[handle]?=some (some ready) ∨ result.1=some handle := by
  cases decoded : RegistrationNativeWire.readInit wire raw with
  | none =>
    simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,decoded,
      simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact Or.inl stored
  | some packet =>
    simp only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose,RegistrationNativeRawAdapter.adapter,decoded,
      simulateQ_map,simulateQ_spec_query,StateT.run_map,support_map] at supported
    obtain ⟨⟨reply,after⟩,called,equal⟩ := supported
    cases equal
    rcases typed_origin setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer implementation (.inr (.accept packet)) before (reply,after) called handle ready stored with prior | created
    · exact Or.inl prior
    · exact Or.inr (by rw [show reply=.ok (some handle) from created];rfl)

/-- A new stored Ready in any complete callback is owned by that exact successful public accept result. -/
theorem full_origin (query : RegistrationNativeInterface.FullSpec.Domain) (before : FullState)
    (result : RegistrationNativeInterface.FullSpec.Range query × FullState)
    (supported : result ∈ support ((full query).run before))
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : result.2.2.1.1.server.sessions[handle]?=some (some ready)) :
    before.2.1.1.server.sessions[handle]?=some (some ready) ∨
      ∃ raw, (⟨query,result.1⟩ : RegistrationNativeInterface.Entry)=⟨.inl (.inr (.accept raw)),some handle⟩ := by
  by_cases quiet : RegistrationNativeInterface.queryClass query≠3
  · exact Or.inl (full_old setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds query quiet before result supported handle ready stored)
  · cases query with
    | inr secrecy => cases secrecy <;> exact (quiet (by intro equal; cases equal)).elim
    | inl request => cases request with
      | inl coin => exact (quiet (by intro equal; cases equal)).elim
      | inr command => cases command with
        | accept raw =>
          rw [RegistrationNativeTargetLedgerCore.run,support_map] at supported
          obtain ⟨⟨reply,after⟩,called,equal⟩ := supported
          cases equal
          rcases raw_accept setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer implementation raw before.2 (reply,after) called handle ready stored with prior | created
          · exact Or.inl prior
          · exact Or.inr ⟨raw,by rw [created]⟩
        | _ => exact (quiet (by intro equal; cases equal)).elim

/-- Every surviving Ready has its own same-run successful accept, or was already in the supplied initial roster. -/
theorem path_origin {before after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full before entries after)
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : after.2.1.1.server.sessions[handle]?=some (some ready)) :
    before.2.1.1.server.sessions[handle]?=some (some ready) ∨
      ∃ (pre post : List RegistrationNativeInterface.Entry) (raw : Pqxdh.Bytes) (first last : FullState),
        entries=pre++⟨.inl (.inr (.accept raw)),some handle⟩::post ∧
        RegistrationNativeSecretWordTargetPath.Path full before pre first ∧
        (some handle,last) ∈ support ((full (.inl (.inr (.accept raw)))).run first) ∧
        last.2.1.1.server.sessions[handle]?=some (some ready) ∧
        RegistrationNativeSecretWordTargetPath.Path full last post after := by
  induction path with
  | nil before => exact Or.inl stored
  | cons query reply before middle after tail called later ih =>
    rcases ih stored with prior | ⟨pre,post,raw,first,last,recorded,earlierPath,birth,retained,suffix⟩
    · rcases full_origin setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds query before (reply,middle) called handle ready prior with original | ⟨raw,entry⟩
      · exact Or.inl original
      · cases entry
        exact Or.inr ⟨[],tail,raw,before,middle,rfl,.nil before,called,prior,later⟩
    · exact Or.inr ⟨⟨query,reply⟩::pre,post,raw,first,last,by rw [recorded];rfl,
        .cons query reply before middle first pre called earlierPath,birth,retained,suffix⟩

/-- Empty initial capabilities remove the initial-roster alternative without restricting failed accepts. -/
theorem initialized_origin {before after : FullState} {entries : List RegistrationNativeInterface.Entry}
    (path : RegistrationNativeSecretWordTargetPath.Path full before entries after)
    (empty : before.2.1.1.server.sessions=[])
    (handle : Nat) (ready : RegistrationNativeSecretWordMessage.ServerReady)
    (stored : after.2.1.1.server.sessions[handle]?=some (some ready)) :
    ∃ (pre post : List RegistrationNativeInterface.Entry) (raw : Pqxdh.Bytes) (first last : FullState),
      entries=pre++⟨.inl (.inr (.accept raw)),some handle⟩::post ∧
      RegistrationNativeSecretWordTargetPath.Path full before pre first ∧
      (some handle,last) ∈ support ((full (.inl (.inr (.accept raw)))).run first) ∧
      last.2.1.1.server.sessions[handle]?=some (some ready) ∧
      RegistrationNativeSecretWordTargetPath.Path full last post after := by
  rcases path_origin setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds path handle ready stored with old | origin
  · rw [empty] at old
    cases old
  · exact origin

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.typed_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.typed_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.raw_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.raw_old

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.full_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.full_old

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.raw_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.raw_accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.full_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.full_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.path_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.path_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.initialized_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSessions.initialized_origin

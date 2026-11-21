-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorStatefulSupport
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallMonotone
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTyped
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerPath
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! The literal current symbolic callbacks preserve exact installation counts and descriptor order under any persistent stateful Word interpretation. Full ledger paths retain all source/platform/private outcomes; no particular real or ideal record reply support is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall
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


local notation "Front" => RegistrationNativePlatformSecretWordOrdinary.State source Platform
local notation "traceState" => RegistrationNativePlatformLorStatefulSupport.TracedState Front Private
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks canonical source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
local notation "traceTyped" => RegistrationNativePlatformLorStatefulSupport.traced implementation controller

open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallStep (RoleStep)

def events {source : RegistrationNativeMldsa.Source} (candidate : MlKemSharedSecret)
    (before : RegistrationNativePlatformLorStatefulSupport.TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private) :=
  before.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)
private def slots {source : RegistrationNativeMldsa.Source}
    (_before : RegistrationNativePlatformLorStatefulSupport.TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) Private) (_handle : PqxdhDeploymentInterface.Handle) :
    Option (PqxdhRecordLiftInterface.Slot n) := none

/-- Arbitrary stateful closing preserves the exact count of the literal current callback and its own returned public reply. -/
theorem typed_count (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : traceState) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × traceState)
    (supported : result ∈ support ((traceTyped query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    ∃ added, RegistrationNativeSecretWordInstallOrdinals.messages role result.2.2.1.events =
      RegistrationNativeSecretWordInstallOrdinals.messages role before.2.1.events ++ added ∧
      added.length = (RegistrationNativeInstallOrdinals.handles role [entry query result.1]).length := by
  exact RegistrationNativePlatformSecretWordInstallTyped.count setup checks canonical sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query before.1 before.2.1
    ((result.1,result.2.1),result.2.2.1)
    (RegistrationNativePlatformLorStatefulSupport.traced_support implementation controller query before result supported) role

/-- The same actual public entry supplies the complete typed role-count receipt under the persistent interpretation. -/
theorem typed_receipts (candidate : MlKemSharedSecret) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : traceState) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × traceState)
    (_prior : True) (supported : result ∈ support ((traceTyped query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events candidate before) (events candidate result.2) (entry query result.1) ((slots (n := n)) result.2) (fun _ => False) := by
  obtain ⟨added,bill,counted⟩ := typed_count setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation query before result supported role
  refine ⟨added.map (RegistrationNativeSecretWordMessage.eval candidate),?_,?_,?_⟩
  · simp only [events,RegistrationNativeSecretWordInstallOrdinals.messages_eval,bill,List.map_append]
  · rw [List.length_map]
    exact counted
  · intro position message handle messageAt handleAt selected
    cases selected

private theorem typed_storage (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : traceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × traceState)
    (_prior : True) (_supported : result ∈ support ((traceTyped query).run before)) :
    RegistrationNativeInstallLedger.Storage (slots (n := n)) (fun _ => True) before result.2 :=
  ⟨trivial,fun _ present => present⟩

/-- Every full source prefix has its exact per-role successful handles and messages under arbitrary persistent private World state. -/
theorem path_counts (candidate : MlKemSharedSecret) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (before : traceState) (empty : before.2.1.events = [])
    {after : RegistrationNativeLedger.State × traceState} {entries : List RegistrationNativeInterface.Entry}
    (actual : Path (RegistrationNativeFullCompiler.handler setup.source.crypto canonical serverKeyId bounds traceTyped)
      (RegistrationNativeLedger.empty,before) entries after) :
    ∀ role, RegistrationNativeInstallOrdinals.Counts role (events candidate after.2) after.1.transcript := by
  have stored := RegistrationNativeInstallRawStorage.raw traceTyped canonical (slots (n := n)) (fun _ => True)
    (typed_storage setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation)
  have receipts := RegistrationNativeInstallRawStep.raw traceTyped canonical (events candidate) (slots (n := n)) (fun _ => True) (fun _ => False)
    (typed_receipts setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation candidate)
  have initial := RegistrationNativeInstallLedger.initial (events candidate) (slots (n := n)) (fun _ => True) (fun _ => False) before trivial
    (by simp only [events,empty,List.map_nil])
  exact (RegistrationNativeInstallLedger.path (RegistrationNativeRawAdapter.handler canonical traceTyped) (events candidate) (slots (n := n))
    (fun _ => True) (fun _ => False) stored receipts setup.source.crypto (RegistrationNativeWire.ledgerCodec canonical) serverKeyId bounds actual initial).2.1

omit primitive in
private theorem program_extension {Index Private Result : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT Private ProbComp)) (values : Private → List Message)
    (step : ∀ query before result, result ∈ support ((implementation query).run before) →
      ∃ added, values result.2 = values before ++ added)
    (work : OracleComp spec Result) (before : Private) (result : Result × Private)
    (supported : result ∈ support ((simulateQ implementation work).run before)) :
    ∃ added, values result.2 = values before ++ added := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
      cases supported
      exact ⟨[],(List.append_nil _).symm⟩
  | query_bind query next ih =>
      rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
      obtain ⟨middle,called,continued⟩ := supported
      obtain ⟨head,first⟩ := step query before middle called
      obtain ⟨tail,last⟩ := ih middle.1 middle.2 continued
      exact ⟨head ++ tail,by rw [last,first,List.append_assoc]⟩

omit primitive in
/-- The genuine trace algebra retains each descriptor at its prior ordinal through any persistent interpretation and adaptive suffix. -/
theorem trace_suffix {B : Type} (role : PqxdhRecordLiftInterface.Role)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) B)
    (before : RegistrationNativeSecretWordFrontendTrace.State × Private)
    (result : B × (RegistrationNativeSecretWordFrontendTrace.State × Private))
    (supported : result ∈ support ((simulateQ (RegistrationNativePlatformLorStatefulSupport.trace implementation) work).run before)) :
    ∃ added, RegistrationNativeSecretWordInstallOrdinals.messages role result.2.1.events =
      RegistrationNativeSecretWordInstallOrdinals.messages role before.1.events ++ added := by
  exact RegistrationNativeSecretWordInstallMonotone.program role work before.1 (result.1,result.2.1)
    (RegistrationNativePlatformLorStatefulSupport.trace_support implementation work before result supported)

private theorem raw_suffix (role : PqxdhRecordLiftInterface.Role) (query : RegistrationNativeInterface.Spec.Domain)
    (before : traceState) (result : RegistrationNativeInterface.Spec.Range query × traceState)
    (supported : result ∈ support ((RegistrationNativeRawAdapter.handler canonical traceTyped query).run before)) :
    ∃ added, RegistrationNativeSecretWordInstallOrdinals.messages role result.2.2.1.events =
      RegistrationNativeSecretWordInstallOrdinals.messages role before.2.1.events ++ added := by
  apply program_extension traceTyped (fun current => RegistrationNativeSecretWordInstallOrdinals.messages role current.2.1.events)
    (fun request first reached called => by
      exact RegistrationNativeSecretWordInstallMonotone.program role _ first.2.1
        ((reached.1,reached.2.1),reached.2.2.1)
        (RegistrationNativePlatformLorStatefulSupport.traced_support implementation controller request first reached called))
    (RegistrationNativeRawAdapter.adapter canonical query) before result
  simpa only [RegistrationNativeRawAdapter.handler,QueryImpl.apply_compose] using supported

/-- Every literal full-ledger callback retains the complete ordered descriptor prefix under arbitrary persistent private state. -/
theorem full_suffix (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (role : PqxdhRecordLiftInterface.Role) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × traceState)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × traceState))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto canonical serverKeyId bounds traceTyped query).run before)) :
    ∃ added, RegistrationNativeSecretWordInstallOrdinals.messages role result.2.2.2.1.events =
      RegistrationNativeSecretWordInstallOrdinals.messages role before.2.2.1.events ++ added := by
  rw [RegistrationNativeFullCompiler.handler,RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,support_map] at supported
  obtain ⟨reached,called,returned⟩ := supported
  cases returned
  exact program_extension (RegistrationNativeRawAdapter.handler canonical traceTyped)
    (fun current => RegistrationNativeSecretWordInstallOrdinals.messages role current.2.1.events)
    (raw_suffix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation role)
    _ before.2 reached called

/-- Any same-execution chronological suffix preserves every earlier descriptor's original role ordinal. -/
theorem path_suffix (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (role : PqxdhRecordLiftInterface.Role)
    {before after : RegistrationNativeLedger.State × traceState} {entries : List RegistrationNativeInterface.Entry}
    (actual : Path (RegistrationNativeFullCompiler.handler setup.source.crypto canonical serverKeyId bounds traceTyped) before entries after) :
    ∃ added, RegistrationNativeSecretWordInstallOrdinals.messages role after.2.2.1.events =
      RegistrationNativeSecretWordInstallOrdinals.messages role before.2.2.1.events ++ added := by
  apply RegistrationNativeSecretWordTargetPath.preserves
    (RegistrationNativeFullCompiler.handler setup.source.crypto canonical serverKeyId bounds traceTyped)
    (fun current => ∃ added, RegistrationNativeSecretWordInstallOrdinals.messages role current.2.2.1.events =
      RegistrationNativeSecretWordInstallOrdinals.messages role before.2.2.1.events ++ added)
    (fun query first result prior called => by
      obtain ⟨head,firstEq⟩ := prior
      obtain ⟨tail,lastEq⟩ := full_suffix setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer implementation serverKeyId bounds role query first result called
      exact ⟨head ++ tail,by rw [lastEq,firstEq,List.append_assoc]⟩) actual
  exact ⟨[],(List.append_nil _).symm⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.typed_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.typed_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.typed_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.typed_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.path_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.path_counts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.trace_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.trace_suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.full_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.full_suffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.path_suffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceInstall.path_suffix

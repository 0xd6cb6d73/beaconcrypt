import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinRoster
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinSummary
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPinPath
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinPrefix
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
import BeaconcryptCore.Computational.RegistrationNativeTargetLedgerCore
-- SPDX-License-Identifier: 0BSD
/-! The actual current common-state source preserves every prior configured owner Server-pin in roster order, through failed constructors and arbitrary later callbacks. Private provider state and persistent platform state are kept on the literal typed/raw/full execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordOwnerPins (key)
open RegistrationNativeOwnerPinSummaryStep (advance)
open RegistrationNativeSecretWordTargetPath (Path)
open RegistrationNativeInterface (Entry)
open PqxdhKemIndCca
open PqxdhDeploymentTranscript (summarize)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativePlatformSecretWordAliasAlignment (State)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup wire route sign input inside provider outer controller

private theorem typed_create (edPin : PqxdhBeaconPhase2Preparation.Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : State n KemSK source Platform) (reply : RustM (Option Nat)) (after : State n KemSK source Platform)
    (supported : (reply,after) ∈ support ((typed (.inr (.create edPin mlPin keyId))).run before)) :
    after.1.1.beacons.map key = match reply with | .ok (some _) => before.1.1.beacons.map key ++ [(edPin,keyId)] | _ => before.1.1.beacons.map key := by
  have free := RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller (.inr (.create edPin mlPin keyId)) before (reply,after) supported
  have pins := RegistrationNativePlatformSecretWordOwnerPinFields.word_create setup selectedOwner publicPrekey reserveFrame writer edPin mlPin keyId before.1 (reply,after.1) free
  cases reply with
  | fail error | div => exact pins
  | ok optional => cases optional <;> exact pins

private theorem typed_noncreate (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State n KemSK source Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source Platform)
    (supported : result ∈ support ((typed query).run before)) : result.2.1.1.beacons.map key=before.1.1.beacons.map key := by
  exact RegistrationNativePlatformSecretWordOwnerPinRoster.handler_keys setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    query quiet before.1 (result.1,result.2.1)
    (RegistrationNativePlatformSecretWordExecution.typed_support setup wire route sign input inside provider outer controller query before result supported)

private theorem typed_quiet (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (quiet : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) 0)
    (before : State n KemSK source Platform) (result : A × State n KemSK source Platform)
    (supported : result ∈ support ((simulateQ typed work).run before)) : result.2.1.1.beacons.map key = before.1.1.beacons.map key := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported; rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at quiet
      have absent : RegistrationNativeRawAdapter.kind query ≠ 1 := quiet.1.resolve_right (Nat.not_lt_zero _)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      have first := typed_noncreate setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query absent before middle reached
      exact (ih middle.1 (by simpa using quiet.2 middle.1) middle.2 result continued).trans first

local notation "rawImpl" => RegistrationNativeRawAdapter.handler wire typed
/-- Every original raw program without construction retains all immutable configured owner pins. -/
private theorem quiet (work : OracleComp RegistrationNativeInterface.Spec A)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeLedgerCaps.coreKind query = 1) 0)
    (before : State n KemSK source Platform) (result : A × State n KemSK source Platform)
    (supported : result ∈ support ((simulateQ rawImpl work).run before)) : result.2.1.1.beacons.map key = before.1.1.beacons.map key := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact typed_quiet setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    _ (RegistrationNativeRawAdapter.compile_bound wire work 1 0 bounded) before result supported

/-- Successful raw construction appends its same parsed configured pin; every malformed or rejected creation appends nothing. -/
private theorem create (edPin mlPin : Pqxdh.Bytes) (keyId : U64) (before : State n KemSK source Platform)
    (reply : Option Nat) (after : State n KemSK source Platform)
    (supported : (reply, after) ∈ support ((rawImpl (.inr (.create edPin mlPin keyId))).run before)) :
    after.1.1.beacons.map key = advance (before.1.1.beacons.map key) (.inr (.create edPin mlPin keyId)) reply := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter] at supported
  cases parsed : PqxdhDeploymentInterface.parsePin edPin with
  | none =>
      simp only [parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some word =>
      cases parsedMl : RegistrationNativeWire.parseMldsaPin mlPin with
      | none =>
          simp only [parsed, parsedMl, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
          cases supported
          rfl
      | some parsedPublic =>
          simp only [parsed, parsedMl, simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
          obtain ⟨⟨answer, current⟩, reached, equal⟩ := supported
          have actual := typed_create setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer word parsedPublic keyId before answer current reached
          cases answer with
          | fail error | div =>
              simp only [RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
              obtain ⟨rfl, rfl⟩ := equal
              exact actual
          | ok chosen =>
              simp only [RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
              obtain ⟨rfl, rfl⟩ := equal
              cases chosen <;> simpa only [advance, parsed] using actual

/-- Every original raw callback implements the literal public configured-pin summary update. -/
theorem step (query : RegistrationNativeInterface.Spec.Domain) (before : State n KemSK source Platform)
    (reply : RegistrationNativeInterface.Spec.Range query) (after : State n KemSK source Platform)
    (supported : (reply, after) ∈ support ((rawImpl query).run before)) :
    after.1.1.beacons.map key = advance (before.1.1.beacons.map key) query reply := by
  by_cases counted : RegistrationNativeLedgerCaps.coreKind query = 1
  · cases query with
    | inl coin => cases counted
    | inr command => cases command with
      | create edPin mlPin keyId => exact create setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer edPin mlPin keyId before reply after supported
      | _ => cases counted
  · have bounded : OracleComp.IsQueryBoundP (RegistrationNativeInterface.Spec.query query : OracleComp RegistrationNativeInterface.Spec _)
        (fun request => RegistrationNativeLedgerCaps.coreKind request = 1) 0 := by
      rw [isQueryBoundP_query_iff]
      intro contrary
      exact False.elim (counted contrary)
    have preserved := quiet setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (RegistrationNativeInterface.Spec.query query : OracleComp RegistrationNativeInterface.Spec _) bounded before (reply, after)
      (by simpa only [simulateQ_spec_query] using supported)
    cases query with
    | inl coin => exact preserved
    | inr command => cases command <;> first
      | exact (counted rfl).elim
      | exact preserved
variable (serverKeyId : U64)
omit primitive in
private theorem summary_append (transcript : List PqxdhDeploymentInterface.Entry) (entry : PqxdhDeploymentInterface.Entry) :
    (PqxdhDeploymentTranscript.summarize (transcript ++ [entry])).owners = (PqxdhDeploymentTranscript.step (PqxdhDeploymentTranscript.summarize transcript) entry).owners := by
  simp only [PqxdhDeploymentTranscript.summarize, List.foldl_append, List.foldl_cons, List.foldl_nil]

omit primitive in
private theorem step_advance (summary : PqxdhDeploymentTranscript.Summary)
    (query : RegistrationNativeInterface.Spec.Domain) (reply : RegistrationNativeInterface.Spec.Range query) :
    (PqxdhDeploymentTranscript.step summary (Entry.erase ⟨.inl query, reply⟩)).owners = advance summary.owners query reply := by
  cases query with
  | inl coin => rfl
  | inr command => cases command with
    | create edPin mlPin keyId =>
        cases reply with
        | none => rfl
        | some index =>
            cases parsed : PqxdhDeploymentInterface.parsePin edPin <;>
              simp only [Entry.erase, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentTranscript.step,
                PqxdhDeploymentTranscript.stepCommand, advance, parsed]
    | bundle owner =>
        cases reply <;> simp only [Entry.erase, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentTranscript.step,
          PqxdhDeploymentTranscript.stepCommand, advance]
        all_goals split <;> rfl
    | finish owner raw =>
        cases reply <;> simp only [Entry.erase, RegistrationNativeInterface.eraseCommand, PqxdhDeploymentTranscript.step,
          PqxdhDeploymentTranscript.stepCommand, advance]
        all_goals split <;> rfl
    | _ => rfl



private theorem secrecy_pins (bounds : PqxdhDeploymentInterface.FreshBounds) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (before : RegistrationNativeLedger.State × State n KemSK source Platform)
    (result : RegistrationNativeInterface.FullSpec.Range (.inr secrecy) × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed (.inr secrecy)).run before)) :
    result.2.2.1.1.beacons.map key = before.2.1.1.beacons.map key := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨current, reached, rfl⟩ := supported
  exact quiet setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _
    (RegistrationNativeOwnerPinSummaryCore.secrecy_quiet setup.source.crypto wire serverKeyId bounds secrecy before.1) before.2 current reached

def Holds {source : RegistrationNativeMldsa.Source} (transcript : List Entry) (owners : RegistrationNativePublicOwners.State source) : Prop :=
  (summarize (transcript.map Entry.erase)).owners = owners.map key

/-- Every actual complete original ledger call implements the exact configured-pin summary update. -/
private theorem full (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source Platform) (prior : Holds before.1.transcript before.2.1.1.beacons)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source Platform))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed query).run before)) :
    Holds result.2.1.transcript result.2.2.1.1.beacons := by
  have trace := RegistrationNativeLedgerJournal.handler_records _ setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query before result supported
  change (summarize (result.2.1.transcript.map Entry.erase)).owners = result.2.2.1.1.beacons.map key
  rw [trace, List.map_append, List.map_cons, List.map_nil, summary_append]
  cases query with
  | inr secrecy =>
      change (summarize (before.1.transcript.map Entry.erase)).owners = result.2.2.1.1.beacons.map key
      exact prior.trans (secrecy_pins setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds secrecy before result supported).symm
  | inl query =>
      rw [RegistrationNativeTargetLedgerCore.run, support_map] at supported
      obtain ⟨⟨reply, after⟩, reached, equal⟩ := supported
      cases equal
      rw [step_advance]
      change advance (summarize (before.1.transcript.map Entry.erase)).owners query reply = after.1.1.beacons.map key
      rw [prior]
      exact (step setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.2 reply after reached).symm


variable (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "fullImpl" => RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
/-- Every actual original prefix from the empty roster has its own exact original public configured-pin summary. -/
theorem summary (before : State n KemSK source Platform) (empty : before.1.1.beacons = [])
    {entries : List Entry} {after : RegistrationNativeLedger.State × State n KemSK source Platform}
    (path : Path fullImpl (RegistrationNativeLedger.empty, before) entries after) :
    Holds after.1.transcript after.2.1.1.beacons := by
  apply RegistrationNativeSecretWordTargetPath.preserves fullImpl
    (fun current => Holds current.1.transcript current.2.1.1.beacons)
    (fun query current result prior called => full setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds query current prior result called) path
  simp only [Holds, RegistrationNativeLedger.empty,
    List.map_nil, PqxdhDeploymentTranscript.summarize, PqxdhDeploymentTranscript.Summary.empty, List.foldl_nil, empty]

/-- The exact configured owner pin at an actual earlier source cut equals the original final public designation binding at that index. -/
theorem owner (before : State n KemSK source Platform) (empty : before.1.1.beacons = [])
    (pre post : List Entry) (cut : RegistrationNativeLedger.State × State n KemSK source Platform)
    (path : Path fullImpl (RegistrationNativeLedger.empty, before) pre cut)
    (index : Nat) (current : RegistrationNativePublicOwners.Owner source)
    (found : cut.2.1.1.beacons[index]? = some current)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : U64)
    (retained : (PqxdhDeploymentTranscript.summarize ((pre ++ post).map Entry.erase)).owners[index]? = some (pin, keyId)) :
    current.view.pin.binding = ⟨pin, keyId⟩ := by
  have actual := summary setup checks wire source route sign input inside selected pairs publicKey challenge outer selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds before empty path
  have recorded := RegistrationNativeSecretWordTargetPath.records fullImpl (fun reached => reached.1.transcript)
    (fun query first result called => RegistrationNativeLedgerJournal.handler_records _ setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query first result called) path
  simp only [RegistrationNativeLedger.empty, List.nil_append] at recorded
  change (PqxdhDeploymentTranscript.summarize (cut.1.transcript.map Entry.erase)).owners = cut.2.1.1.beacons.map key at actual
  have pinned : (PqxdhDeploymentTranscript.summarize (pre.map Entry.erase)).owners[index]? = some (key current) := by
    rw [← recorded, actual, List.getElem?_map, found, Option.map_some]
  rw [List.map_append] at retained
  have equal := RegistrationNativeOwnerPinPrefix.lookup (pre.map Entry.erase) (post.map Entry.erase) index (key current) (pin, keyId) pinned retained
  have identity := congrArg Prod.fst equal
  have assigned := congrArg Prod.snd equal
  cases binding : current.view.pin.binding
  simp only [key, binding] at identity assigned
  cases identity
  cases assigned
  rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath.summary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath.summary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinPath.owner

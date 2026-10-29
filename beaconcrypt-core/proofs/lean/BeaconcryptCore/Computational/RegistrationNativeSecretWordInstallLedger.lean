-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallTyped
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOrdinalBase
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerPath

/-! Exact open Word callback counts lift through their actual private interpreter and the original raw and full ledger compilers. Thus every actual monitored prefix has equal installation and successful-handle lengths, without a native source equality or caller-supplied prefix invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option quotPrecheck false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetTracedSource (State)
open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallStep (RoleStep)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "actual" => RegistrationNativeSecretWordTargetTracedSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
local notation "native" => RegistrationNativeRawAdapter.handler wire actual

def events (candidate : PqxdhKemIndCca.MlKemSharedSecret) (before : State n KemSK source) :=
  before.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)

private def slots (_before : State n KemSK source) (_handle : PqxdhDeploymentInterface.Handle) :
    Option (PqxdhRecordLiftInterface.Slot n) := none

/-- Closing the actual private interpreter preserves the complete same-reply Word callback count. -/
theorem typed_receipts (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (_prior : True) (supported : result ∈ support ((actual query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events candidate before) (events candidate result.2) (entry query result.1) (slots result.2) (fun _ => False) := by
  simp only [RegistrationNativeSecretWordTargetTracedSource.typed, StateT.run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  have possible : reached.1 ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before.1.1)).run before.1.2) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  obtain ⟨added, bill, counted⟩ := RegistrationNativeSecretWordInstallTyped.count setup checks wire sign selectedOwner selectedAccept publicPrekey
    query before.1.1 before.1.2 reached.1 possible role
  have replyEq : reached.1.1.1 = result.1 := congrArg Prod.fst returned
  have traceEq : reached.1.2 = result.2.1.2 := congrArg (fun output => output.2.1.2) returned
  refine ⟨added.map (RegistrationNativeSecretWordMessage.eval candidate), ?_, ?_, ?_⟩
  · simp only [events, RegistrationNativeSecretWordInstallOrdinals.messages_eval, ← traceEq, bill, List.map_append]
  · rw [List.length_map]
    simpa only [replyEq] using counted
  · intro position message handle messageAt handleAt selected
    cases selected

private theorem typed_storage (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (_prior : True) (_supported : result ∈ support ((actual query).run before)) :
    RegistrationNativeInstallLedger.Storage slots (fun _ => True) before result.2 := by
  exact ⟨trivial, fun _ present => present⟩

/-- Every actual monitored Word prefix has equal per-role installation and original successful-handle counts. -/
theorem path (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (before : State n KemSK source)
    (empty : before.1.2.events = [])
    {after : RegistrationNativeLedger.State × State n KemSK source} {entries : List RegistrationNativeInterface.Entry}
    (actualPath : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds actual)
      (RegistrationNativeLedger.empty, before) entries after) :
    ∀ role, RegistrationNativeInstallOrdinals.Counts role (events candidate after.2) after.1.transcript := by
  have stored := RegistrationNativeInstallRawStorage.raw actual wire slots (fun _ => True)
    (typed_storage setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey)
  have receipts := RegistrationNativeInstallRawStep.raw actual wire (events candidate) slots (fun _ => True) (fun _ => False)
    (typed_receipts setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey candidate)
  have initial := RegistrationNativeInstallLedger.initial (events candidate) slots (fun _ => True) (fun _ => False) before trivial
    (by simp only [events, empty, List.map_nil])
  exact (RegistrationNativeInstallLedger.path native (events candidate) slots (fun _ => True) (fun _ => False) stored receipts
    setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds actualPath initial).2.1

/-- Empty original chronology discharges the exact target prefix-count premise on every actual supported Word prefix. -/
theorem prefix_counts (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (before : State n KemSK source)
    (empty : before.1.2.events = []) :
    RegistrationNativeSecretWordTargetOrdinalBase.PrefixCounts setup checks wire route sign input inside provider outer
      selectedOwner selectedAccept publicPrekey serverKeyId bounds candidate before := by
  intro role pre cut prior
  exact path setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey candidate serverKeyId bounds before empty prior role

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger.typed_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger.typed_receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger.path
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger.prefix_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInstallLedger.prefix_counts

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTyped
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStorage
import BeaconcryptCore.Computational.RegistrationNativeInstallRawStep
import BeaconcryptCore.Computational.RegistrationNativeInstallLedgerPath
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPhase
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! Actual current symbolic callbacks attach their exact ordered installation messages to the original successful raw handles. The complete original ledger and every interpreted source prefix retain the same per-role counts, including all failed allocation and writer branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetAlignment (Aligned)
open RegistrationNativeSecretWordTargetPublication (key)
open PqxdhKemIndCca
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
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer
local notation "controller" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "typed" => RegistrationNativePlatformSecretWordExecution.typed (n := n) setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller



open RegistrationNativePlatformSecretWordExecution (TracedState drop)
open RegistrationNativeSecretWordTargetPath (Path)
local notation "traceState" => TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK
local notation "traceTyped" => RegistrationNativePlatformSecretWordExecution.traced (n := n) setup
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller

open RegistrationNativeInstallTypedEntry (entry)
open RegistrationNativeInstallStep (RoleStep)

def events {source : RegistrationNativeMldsa.Source} (candidate : MlKemSharedSecret) (before : TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK) :=
  before.2.1.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate)
private def slots {source : RegistrationNativeMldsa.Source} (_before : TracedState (RegistrationNativePlatformSecretWordOrdinary.State source Platform) n KemSK) (_handle : PqxdhDeploymentInterface.Handle) :
    Option (PqxdhRecordLiftInterface.Slot n) := none

/-- The current actual source interpreter preserves the exact same-reply typed installation count. -/
theorem typed_receipts (candidate : MlKemSharedSecret) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : traceState) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × traceState)
    (_prior : True) (supported : result ∈ support ((traceTyped query).run before)) (role : PqxdhRecordLiftInterface.Role) :
    RoleStep role (events candidate before) (events candidate result.2) (entry query result.1) (slots result.2) (fun _ => False) := by
  have possible := RegistrationNativePlatformSecretWordExecution.traced_support setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside provider outer controller query before result supported
  obtain ⟨added,bill,counted⟩ := RegistrationNativePlatformSecretWordInstallTyped.count setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) sign selectedOwner selectedAccept publicPrekey view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query before.1 before.2.1
    ((result.1,result.2.1),result.2.2.1) possible role
  refine ⟨added.map (RegistrationNativeSecretWordMessage.eval candidate),?_,?_,?_⟩
  · simp only [events,RegistrationNativeSecretWordInstallOrdinals.messages_eval,bill,List.map_append]
  · rw [List.length_map]
    exact counted
  · intro position message handle messageAt handleAt selected
    cases selected

private theorem typed_storage (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : traceState)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × traceState)
    (_prior : True) (_supported : result ∈ support ((traceTyped query).run before)) :
    RegistrationNativeInstallLedger.Storage slots (fun _ => True) before result.2 :=
  ⟨trivial,fun _ present => present⟩

/-- Every actual current-source prefix counts its precise original successful handles and same ordered descriptor list. -/
theorem path (candidate : MlKemSharedSecret) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (before : traceState) (empty : before.2.1.events = [])
    {after : RegistrationNativeLedger.State × traceState} {entries : List RegistrationNativeInterface.Entry}
    (actual : Path (RegistrationNativeFullCompiler.handler setup.source.crypto
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) serverKeyId bounds traceTyped)
      (RegistrationNativeLedger.empty,before) entries after) :
    ∀ role, RegistrationNativeInstallOrdinals.Counts role (events candidate after.2) after.1.transcript := by
  have stored := RegistrationNativeInstallRawStorage.raw traceTyped
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) slots (fun _ => True)
    (typed_storage setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
  have receipts := RegistrationNativeInstallRawStep.raw traceTyped
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (events candidate) slots (fun _ => True) (fun _ => False)
    (typed_receipts setup checks wire source route sign input inside selected pairs publicKey challenge outer
      selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer candidate)
  have initial := RegistrationNativeInstallLedger.initial (events candidate) slots (fun _ => True) (fun _ => False) before trivial
    (by simp only [events,empty,List.map_nil])
  exact (RegistrationNativeInstallLedger.path (RegistrationNativeRawAdapter.handler
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) traceTyped) (events candidate) slots
    (fun _ => True) (fun _ => False) stored receipts setup.source.crypto
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) serverKeyId bounds actual initial).2.1

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger.typed_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger.typed_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallLedger.path

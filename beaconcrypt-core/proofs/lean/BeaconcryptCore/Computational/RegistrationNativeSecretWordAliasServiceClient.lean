-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceHistory
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand

/-! The exact complete alias client derives its demanded-literal recovery receipts from cold startup. Every literal at an actual installation or installation attempt has its earlier descriptor demand in the same trace; the derived prefix preparation certificate makes that valid protected demand a real key query. No successful-demand or log-correspondence certificate is supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceClient
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordRecoveryCompiler (closed literals)
open RegistrationNativeSecretWordFrontendTrace (Event)
open RegistrationNativeSuffixKeyPrf (Secret)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (source : RegistrationNativeMldsa.Source) (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
  (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
  (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (front : RegistrationNativeSecretWordMessage.State source) (empty : front.server.sessions = [])
  (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
  (candidate : Secret)
  (result : RegistrationNativeSecretWordAliasClient.Result source n KemSK Value × RegistrationNativeSecretWordRecoveryCompiler.State)
  (supported : result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
    (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign input inside provider
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem)))

include supported empty

/-- The original full-ledger client derives recovery evidence for every valid protected literal demand in its actual final chronology. -/
theorem demands_logged :
    RegistrationNativeSecretWordAliasServiceHistory.Holds input inside candidate result.1.1.2 result.2.2 := by
  apply RegistrationNativeSecretWordAliasServiceHistory.program setup wire route sign input inside provider candidate
    (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front)
    (RegistrationNativeSecretWordInterpreter.initial ordinary kem) RegistrationNativeSecretWordFrontendTrace.initial (∅, [])
  · intro message key member
    cases member
  · exact RegistrationNativeSecretWordPreparedTransfer.program setup wire route sign input inside provider _ _
      (RegistrationNativeSecretWordLiveFrontendSafety.run setup wire route sign input inside provider checks source selectedOwner selectedAccept
        publicPrekey serverKeyId bounds mode work front empty ordinary kem)
  · exact supported

/-- Installation exposure of a valid protected literal is an actual earlier demand and therefore appears in the concrete final recovery log. -/
theorem install_logged (role : PqxdhRecordLiftInterface.Role) (message : Message) (key : Key)
    (member : Event.install role message ∈ result.1.1.2.events ∨ Event.installAttempt role message ∈ result.1.1.2.events)
    (realized : input message = some key) (protectedInput : inside key.head = true)
    (literal : key.word = .literal candidate) : candidate ∈ result.2.2 := by
  let bare := RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
    serverKeyId bounds mode work front
  have actual : result.1 ∈ support (RegistrationNativeSecretWordAliasClient.client setup checks wire source route sign input inside provider
      selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front ordinary kem) := by
    apply OracleComp.support_simulateQ_run'_subset (RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals) _ (∅, [])
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have observed : result.1.1 ∈ support (RegistrationNativeSecretWordFrontendTrace.program bare) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeSecretWordInterpreter.handler setup wire route sign input inside provider)
      _ (RegistrationNativeSecretWordInterpreter.initial ordinary kem)
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst actual
  have trace := RegistrationNativeSecretWordAtomTraceDemand.program bare RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [RegistrationNativeSecretWordAtomTraceDemand.Holds, RegistrationNativeSecretWordFrontendTrace.initial]) result.1.1 observed
  have demanded : Event.demand message ∈ result.1.1.2.events := by
    rcases member with installed | attempted
    · exact trace.2 (.install role message) installed message (List.mem_singleton_self _)
    · exact trace.2 (.installAttempt role message) attempted message (List.mem_singleton_self _)
  exact demands_logged setup checks wire source route sign input inside provider selectedOwner selectedAccept publicPrekey
    serverKeyId bounds mode work front empty ordinary kem candidate result supported message key demanded realized protectedInput literal

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceClient
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceClient.demands_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceClient.demands_logged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceClient.install_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceClient.install_logged

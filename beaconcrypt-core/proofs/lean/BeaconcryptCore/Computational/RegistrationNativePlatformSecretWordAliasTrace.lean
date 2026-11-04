-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceOrder
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand
/-! The literal observer of the complete corrected Word client retains chronological order and every installation attempt’s actual earlier material demand. These are derived from the same supported result under arbitrary outer table interpretation; no lifecycle cap or alias conclusion is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
variable {n : Nat} {I KemSK Platform E A Observation : Type} {base : OracleSpec I}

open RegistrationNativePlatformSecretWordAliasClient (Result)

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

variable (route : RawCtxServerRouting.SenderDecoder) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)

variable (outer : QueryImpl Combined ProbComp) (result : Result source n KemSK A Platform)
local notation "bare" => RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  serverKeyId bounds mode work before
local notation "actual" => RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  route input inside provider serverKeyId bounds mode work before ordinary kem

omit primitive in
private theorem closed_support {V : Type} (work : OracleComp Combined V) (value : V)
    (supported : value ∈ support (simulateQ outer work)) : value ∈ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure, mem_support_pure_iff] using supported
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported ⊢
    obtain ⟨reply, _possible, later⟩ := supported
    exact ⟨reply, mem_support_query query reply, ih reply later⟩

/-- The exact complete closed client retains the same chronological pure observer and complete source frontend/platform result. -/
theorem observed_support (supported : result ∈ support (simulateQ outer actual)) :
    result.1 ∈ support (RegistrationNativeSecretWordFrontendTrace.program bare) := by
  have possible := closed_support outer _ result supported
  apply OracleComp.support_simulateQ_run'_subset
    (RegistrationNativeSecretWordInterpreter.handler setup (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      route sign input inside provider) _ (RegistrationNativeSecretWordInterpreter.initial ordinary kem)
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst possible

/-- Same-run order follows for both roles, including refused material and failed installation callbacks. -/
theorem client_order (supported : result ∈ support (simulateQ outer actual)) :
    ∀ role, RegistrationNativeSecretWordAtomTraceOrder.Good role result.1.2.events := by
  have observed := observed_support setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem outer result supported
  intro role
  exact RegistrationNativeSecretWordAtomTraceOrder.program_good role bare RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [RegistrationNativeSecretWordAtomTraceOrder.Good, RegistrationNativeSecretWordAtomTraceOrder.stream,
      RegistrationNativeSecretWordFrontendTrace.initial]) result.1 observed

/-- Every actual install or install-attempt receipt has its descriptor demand in that same final chronology. -/
theorem client_demand (supported : result ∈ support (simulateQ outer actual))
    (role : PqxdhRecordLiftInterface.Role) (message : Message)
    (member : RegistrationNativeSecretWordFrontendTrace.Event.install role message ∈ result.1.2.events ∨
      RegistrationNativeSecretWordFrontendTrace.Event.installAttempt role message ∈ result.1.2.events) :
    RegistrationNativeSecretWordFrontendTrace.Event.demand message ∈ result.1.2.events := by
  have observed := observed_support setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route input inside provider serverKeyId bounds mode work before ordinary kem outer result supported
  have trace := RegistrationNativeSecretWordAtomTraceDemand.program bare RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [RegistrationNativeSecretWordAtomTraceDemand.Holds, RegistrationNativeSecretWordFrontendTrace.initial]) result.1 observed
  rcases member with installed | attempted
  · exact trace.2 (.install role message) installed message (List.mem_singleton_self _)
  · exact trace.2 (.installAttempt role message) attempted message (List.mem_singleton_self _)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace.observed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace.observed_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace.client_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace.client_order

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace.client_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace.client_demand

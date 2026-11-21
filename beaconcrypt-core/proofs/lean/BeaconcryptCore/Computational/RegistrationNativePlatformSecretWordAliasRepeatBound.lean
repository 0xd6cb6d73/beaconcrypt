-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomOwnerAttempts
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerAttempts
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasTrace
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasServiceClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomRepeatMap
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound
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

open PqxdhKemIndCca
open RegistrationNativeSuffixKeyPrf (Secret)
local instance : ∀ query : Combined.Domain, SampleableType (Combined.Range query) := by
  intro query
  rcases query with (coin | key) | head <;> infer_instance
variable (route : RawCtxServerRouting.SenderDecoder)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (kem : RegistrationNativeSecretWordKemProvider.State KemSK)
local notation "interpret" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selectedOwner pairs publicKey challenge
local notation "actual" => RegistrationNativePlatformSecretWordAliasClient.client setup checks wire source sign
  selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
  route interpret inside provider serverKeyId bounds mode work before ordinary kem

omit primitive in
def Event (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : Secret) (result : Result source n KemSK A Platform) : Prop :=
  RegistrationNativeG2Trace.RepeatedRoleAttempt (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeSelectiveHiddenService.selected
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate)
    (result.1.2.events.map (RegistrationNativeSecretWordCheckedTrace.event candidate))

/-- Repetition in this actual complete new client exposes a candidate-equal literal in that same chronological result. -/
theorem client_literal (outer : QueryImpl Combined ProbComp)
    (sessions : before.1.server.sessions = []) (parsed : before.1.parsedAccepts = 0)
    (owners : before.1.beacons = []) (keys : kem.1.keys = [])
    (result : Result source n KemSK A Platform) (supported : result ∈ support (simulateQ outer actual))
    (candidate : Secret) (repeated : Event source setup seed scalar candidate result) :
    RegistrationNativeSecretWordAtomRepeatLiteral.LiteralHit candidate setup.joint setup.dh seed scalar
      (setup.joint.staticDh seed (setup.dh.publicKey scalar)) result.1.2.events := by
  have ordered := RegistrationNativePlatformSecretWordAliasTrace.client_order setup checks wire source sign
    selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    route interpret inside provider serverKeyId bounds mode work before ordinary kem outer result supported
  have bounded : ∀ role, RegistrationNativeSecretWordAtomInstallTrace.count role result.1.2 ≤ 1 := by
    intro role
    cases role with
    | server =>
      exact RegistrationNativePlatformSecretWordAtomServerAttempts.client_one setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route interpret inside selectedOwner pairs publicKey challenge outer
        serverKeyId bounds mode work before ordinary kem sessions parsed result supported
    | beacon =>
      exact RegistrationNativePlatformSecretWordAtomOwnerAttempts.client_one setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route interpret inside pairs publicKey challenge outer
        serverKeyId bounds mode work before ordinary kem owners keys result supported
  exact RegistrationNativeSecretWordAtomRepeatMap.repeated_literal setup.joint setup.dh seed scalar candidate
    (setup.joint.staticDh seed (setup.dh.publicKey scalar)) result.1.2.events ordered bounded repeated

/-- The same actual logged execution records that protected literal, with all source failures and platform state retained. -/
theorem logged_hit (sessions : before.1.server.sessions = []) (parsed : before.1.parsedAccepts = 0)
    (owners : before.1.beacons = []) (keys : kem.1.keys = [])
    (candidate : Secret) (result : Result source n KemSK A Platform × RegistrationNativeSecretWordRecoveryCompiler.State)
    (supported : result ∈ support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate actual))
    (repeated : Event source setup seed scalar candidate result.1) : candidate ∈ result.2.2 := by
  have reached : result.1 ∈ support actual := by
    apply OracleComp.support_simulateQ_run'_subset
      (RawCtxSelectedQueryTrace.recorded (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate)
        RegistrationNativeSecretWordRecoveryCompiler.literals) actual (∅, [])
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have uniformReached : result.1 ∈ support (simulateQ (uniformSampleImpl (spec := Combined)) actual) := by
    rw [uniformSampleImpl.support_simulateQ]
    exact reached
  obtain ⟨role, message, key, member, formed, protectedInput, _message, literal⟩ :=
    client_literal setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer route seed scalar pairs publicKey challenge serverKeyId bounds mode work before ordinary kem
      uniformSampleImpl sessions parsed owners keys result.1 uniformReached candidate repeated
  exact RegistrationNativePlatformSecretWordAliasServiceClient.install_logged setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route interpret inside provider serverKeyId bounds mode work
    before ordinary kem sessions candidate result supported role message key member formed protectedInput literal

/-- The actual corrected all-mode raw byte experiment pays twice one whole-client recovery advantage and the original material allowances. -/
theorem bytes_bound (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (sessions : before.1.server.sessions = []) (parsed : before.1.parsedAccepts = 0)
    (owners : before.1.beacons = []) (keys : kem.1.keys = []) :
    Pr{let pair ← (RegistrationNativeSecretWordRecoveryBound.bytesView setup.source
      (fun candidate result => (candidate, result.1)) actual)}[Event source setup seed scalar pair.1 pair.2] ≤
      2 * (ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
        (RegistrationNativeSuffixKeyRecovery.adversary setup.source (RegistrationNativeSecretWordRecoveryCompiler.guesses actual))) +
        (budget.cap 4 + budget.cap 5) * (256 ^ 160 : ℝ≥0∞)⁻¹ + (budget.cap 4 + budget.cap 5) * (256 ^ 32 : ℝ≥0∞)⁻¹) := by
  simpa only [Nat.cast_add] using RegistrationNativeSecretWordAliasPriorBound.bytes_bound setup.source actual (budget.cap 4 + budget.cap 5)
    (RegistrationNativePlatformSecretWordAliasClient.client_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route interpret inside provider serverKeyId bounds mode work before ordinary kem budget bounded .suffix)
    (RegistrationNativePlatformSecretWordAliasClient.client_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route interpret inside provider serverKeyId bounds mode work before ordinary kem budget bounded .key)
    (Event source setup seed scalar)
    (logged_hit setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer route seed scalar pairs publicKey challenge serverKeyId bounds mode work before ordinary kem sessions parsed owners keys)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound.client_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound.client_literal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound.logged_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound.logged_hit

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound.bytes_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasRepeatBound.bytes_bound

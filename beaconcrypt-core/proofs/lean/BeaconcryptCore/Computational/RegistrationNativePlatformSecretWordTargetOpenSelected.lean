-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRootMetadata
/-! The actual selected corrected OPEN accept stores the descriptor of its own successful matching collector. Repeated pin hashing, mandatory authentication and stateful reservation preserve the unspent marker before that collector; the returned Ready, challenge ciphertext and original verified tuple are derived from the same run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenSelected
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomSessionCredit (count)
open RegistrationNativePlatformSecretWordAtomOpenRun (State Base close)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "impl" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer

local notation "localImpl" => RegistrationNativeSecretWordTargetServerExecution.localImpl
  (n := n) setup wire route sign input inside provider outer true

attribute [local irreducible] RegistrationAuthenticationCompiler.program
  PqxdhDeploymentTranscript.acceptedKeys RegistrationRootInput.candidate

/-- The same selected corrected accept retains its own matching atom collector, actual challenge ciphertext and original verified key tuple. -/
theorem accept_retained (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (reserve : StateT Platform ProbComp Bool) (packet : registration.InitPacket)
    (before after : State n KemSK Platform) (handle : Nat)
    (initial : before.2.2.2.kem.2 = none)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet)).map
      (fun keys => keys.2.pqKey) = some publicKey)
    (supported : (.ok (some handle),after) ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.accept (wordLocal true)
        (RegistrationNativePlatformSecretWordOrdinary.platform reserve) setup checks verify packet)).run before)) :
    ∃ (ready : ServerReady) (authenticated : registration.AuthenticatedInit)
      (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding),
      after.1.sessions[handle]? = some (some ready) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧
      ready.agreement = ⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain,authenticated.binding⟩ ∧
      collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
      collected.kem = Word.atom ∧ ready.reference.kem = Word.atom ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
        some (collected.plain.verified.identity,collected.plain.verified.keys) := by
  obtain ⟨pinned,pinAt,afterPinAt⟩ := RegistrationNativePlatformSecretWordTargetOpenOrigin.accept impl setup checks true
    (RegistrationNativePlatformSecretWordOrdinary.platform reserve) packet verify before after handle supported
  have pinMarker := RegistrationNativePlatformSecretWordTargetOpenLeaves.pin_phase setup wire route sign input inside
    selected pairs publicKey challenge outer before.1.pin before pinned pinAt
  obtain ⟨pin,events,authenticated,checked,_pinReply,authenticatedAt,checkedReply,afterAuthenticationAt⟩ :=
    RegistrationNativePlatformSecretWordTargetOpenOrigin.after_pin impl setup checks true
      (RegistrationNativePlatformSecretWordOrdinary.platform reserve) packet verify pinned.1 pinned.2 after handle afterPinAt
  have authMarker := RegistrationNativePlatformSecretWordTargetOpenLeaves.environment_phase setup wire route sign input inside
    selected pairs publicKey challenge outer (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)
    pinned.2 checked authenticatedAt
  have authSource := RegistrationNativePlatformSecretWordTargetOpenLeaves.environment_source setup wire route sign input inside
    selected pairs publicKey challenge outer (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)
    pinned.2 checked authenticatedAt
  rw [checkedReply] at authSource
  have acceptedKeys := RegistrationNativeSecretWordTargetServerEffects.accepted_keys localImpl setup.source.crypto verify pin packet
    (pinned.2.2.1,pinned.2.2.2.2) (checked.2.2.1,checked.2.2.2.2) events authenticated authSource
  have actualKey : (RegistrationRootInput.keys authenticated.registration).pqKey = publicKey := by
    rw [acceptedKeys,Option.map_some,Option.some.injEq] at matching
    exact matching
  obtain ⟨reserved,ready,agreed,reservedAt,_admitted,agreedAt,agreedReply,_retainedAt,stored⟩ :=
    RegistrationNativePlatformSecretWordTargetOpenOrigin.after_authentication impl setup checks true
      (RegistrationNativePlatformSecretWordOrdinary.platform reserve) packet authenticated checked.2 after handle afterAuthenticationAt
  have reserveMarker := RegistrationNativePlatformSecretWordTargetOpenLeaves.platform_phase setup wire route sign input inside
    selected pairs publicKey challenge outer reserve checked.2 reserved reservedAt
  obtain ⟨collected,middle,collectedAt,rooted,echo⟩ :=
    RegistrationNativePlatformSecretWordTargetOpenLeaves.agreement setup wire route sign input inside
      selected pairs publicKey challenge outer checks packet authenticated reserved.2 agreed agreedAt ready agreedReply
  have fields := RegistrationNativeSecretWordTargetCollectAtom.collect_atom setup checks wire route sign input inside
    selected pairs publicKey challenge outer packet authenticated (reserved.2.2.1,reserved.2.2.2.2) middle collected
    (reserveMarker.trans (authMarker.trans (pinMarker.trans initial))) actualKey collectedAt
  have agreement := RegistrationNativeSecretWordTargetRootMetadata.rooted localImpl authenticated.binding collected ready middle
    (agreed.2.2.1,agreed.2.2.2.2) rooted
  refine ⟨ready,authenticated,collected,stored,echo,agreement,fields.1,fields.2.1,fields.2.2,?_,?_⟩
  · rw [echo]
    exact fields.2.2
  · rw [fields.1]
    exact acceptedKeys

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenSelected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenSelected.accept_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenSelected.accept_retained

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRootMetadata

/-! The matching selected accept stores the descriptor of the same actual collector whose KEM reply is the challenge atom. The native session lookup, actual authentication, collector and pure root echo all come from one supported execution; an unrelated existential collector is never used to identify a retained root. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetainedPublic
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
open RegistrationNativeSecretWordServerCollect (Input)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordInterpreter.handler
  RegistrationNativeSecretWordServerCompiler.accept RegistrationAuthenticationCompiler.program

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer true
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

/-- The actual stored session reference contains the atom of its same successful collector and actual challenge ciphertext. -/
theorem accept_retained (packet : registration.InitPacket) (before after : State n KemSK source) (session : Nat)
    (selectedCall : before.1.parsedAccepts = selectedAccept) (initial : before.2.kem.2 = none)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet)).map
      (fun keys => keys.2.pqKey) = some publicKey)
    (supported : (.ok (some session), after) ∈ support ((typed (.inr (.accept packet))).run before)) :
    ∃ (ready : RegistrationNativeSecretWordMessage.ServerReady) (authenticated : registration.AuthenticatedInit)
      (collected : Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding),
      after.1.server.sessions[session]? = some (some ready) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧
      ready.agreement = ⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain, authenticated.binding⟩ ∧
      collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
      collected.kem = Word.atom ∧ ready.reference.kem = Word.atom ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
        some (collected.plain.verified.identity, collected.plain.verified.keys) := by
  rw [RegistrationNativeSecretWordTargetServerExecution.accept_run setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey packet before selectedCall, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  have success : reached.1.1 = .ok (some session) := congrArg Prod.fst returned
  rcases reached with ⟨⟨reply, server⟩, reached⟩
  dsimp only at success
  subst reply
  obtain ⟨events, authenticated, afterAuthentication, ready, collected, middle, authenticatedAt, stored, collectedAt, rooted, echo⟩ :=
    RegistrationNativeSecretWordLiveServerOriginOuter.accept setup wire route sign input inside provider outer true checks source.verify packet
      before.1.server server (before.1.environment, before.2) reached session called
  have acceptedKeys := RegistrationNativeSecretWordTargetServerEffects.accepted_keys localImplementation setup.source.crypto source.verify
    before.1.server.pin packet (before.1.environment, before.2) afterAuthentication events authenticated authenticatedAt
  have actualKey : (RegistrationRootInput.keys authenticated.registration).pqKey = publicKey := by
    rw [acceptedKeys, Option.map_some, Option.some.injEq] at matching
    exact matching
  have authenticationMarker := RegistrationNativeSecretWordTargetServerPhase.effect_phase setup wire route sign input inside
    selected pairs publicKey challenge outer
    (RegistrationAuthenticationCompiler.program setup.source.crypto source.verify before.1.server.pin packet)
    (before.1.environment, before.2) (.ok (events, .Accepted authenticated), afterAuthentication) authenticatedAt
  have fields := RegistrationNativeSecretWordTargetCollectAtom.collect_atom setup checks wire route sign input inside
    selected pairs publicKey challenge outer packet authenticated afterAuthentication middle collected
    (authenticationMarker.trans initial) actualKey collectedAt
  have agreement := RegistrationNativeSecretWordTargetRootMetadata.rooted localImplementation authenticated.binding
    collected ready middle reached rooted
  have serverEq : server = after.1.server := congrArg (fun result => result.2.1.server) returned
  refine ⟨ready, authenticated, collected, ?_, echo, agreement, fields.1, fields.2.1, fields.2.2, ?_, ?_⟩
  · rw [← serverEq]
    exact stored
  · rw [echo]
    exact fields.2.2
  · rw [fields.1]
    exact acceptedKeys

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetainedPublic
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetainedPublic.accept_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetainedPublic.accept_retained

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerReceipt

/-! A successful selected typed accept whose actual authenticated PQ key is the reserved challenge key reaches its literal first getter and carries that getter's atom and ciphertext into the same successful collector. Every authentication, prefix and suffix state is taken from this actual execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAcceptAtom
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl prefixImpl)
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

/-- The selected successful callback reaches a same-execution collector containing exactly the challenge ciphertext and atom; authenticated-key matching is the explicit local input to be discharged by original target/birth provenance. -/
theorem accept_atom (packet : registration.InitPacket) (before after : State n KemSK source) (session : Nat)
    (selectedCall : before.1.parsedAccepts = selectedAccept) (initial : before.2.kem.2 = none)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet)).map
      (fun keys => keys.2.pqKey) = some publicKey)
    (supported : (.ok (some session), after) ∈ support ((typed (.inr (.accept packet))).run before)) :
    ∃ events authenticated afterAuthentication collected afterCollection,
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((lower localImplementation (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
          (RegistrationAuthenticationCompiler.program setup.source.crypto source.verify before.1.server.pin packet)))).run
            (before.1.environment, before.2)) ∧
      (some collected, afterCollection) ∈ support
        ((lower localImplementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run afterAuthentication) ∧
      collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧ collected.kem = Word.atom := by
  rw [RegistrationNativeSecretWordTargetServerExecution.accept_run setup checks wire route sign input inside provider outer
    selectedOwner selectedAccept publicPrekey packet before selectedCall, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  have success : reached.1.1 = .ok (some session) := congrArg Prod.fst returned
  rcases reached with ⟨⟨reply, server⟩, reached⟩
  dsimp only at success
  subst reply
  obtain ⟨events, authenticated, afterAuthentication, collected, afterCollection, authenticatedAt, collectedAt, acceptedKeys⟩ :=
    RegistrationNativeSecretWordTargetServerReceipt.accept_collected localImplementation setup checks source.verify packet
      before.1.server (before.1.environment, before.2) reached session server called
  have actualKey : (RegistrationRootInput.keys authenticated.registration).pqKey = publicKey := by
    rw [acceptedKeys, Option.map_some, Option.some.injEq] at matching
    exact matching
  have authenticationMarker := RegistrationNativeSecretWordTargetServerPhase.effect_phase setup wire route sign input inside
    selected pairs publicKey challenge outer
    (RegistrationAuthenticationCompiler.program setup.source.crypto source.verify before.1.server.pin packet)
    (before.1.environment, before.2) (.ok (events, .Accepted authenticated), afterAuthentication) authenticatedAt
  have fields := RegistrationNativeSecretWordTargetCollectAtom.collect_atom setup checks wire route sign input inside
    selected pairs publicKey challenge outer packet authenticated afterAuthentication afterCollection collected
    (authenticationMarker.trans initial) actualKey collectedAt
  exact ⟨events, authenticated, afterAuthentication, collected, afterCollection, authenticatedAt, collectedAt, fields⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAcceptAtom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAcceptAtom.accept_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAcceptAtom.accept_atom

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasAlignment
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenSelected
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCounter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetPath
/-! The actual current typed frontend retains the same successful selected OPEN collector and Ready through exact four-coordinate state reassociation. All dynamic source dictionaries, mutable reservation outcomes and original parsed counter effects remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained
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



omit primitive in
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (work before >>= fun reached => next reached.1 reached.2) := rfl
omit primitive in
private theorem get_apply {S : Type} {m : Type → Type} [Monad m]
    (before : S) : (get : StateT S m S) before = pure (before,before) := rfl
omit primitive in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (before : S) : (modify change : StateT S m Unit) before = pure ((),change before) := rfl
omit primitive in
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.accept

/-- Literal source state reassociation exposes the actual corrected OPEN controller and preserves its complete platform/private poststate. -/
theorem accept_run (packet : registration.InitPacket) (before : State n KemSK source Platform) :
    (typed (.inr (.accept packet))).run before =
      (fun result => (result.1, (({ before.1.1 with server := result.2.1, environment := result.2.2.1, parsedAccepts := before.1.1.parsedAccepts + 1 }, result.2.2.2.1), result.2.2.2.2))) <$>
        (RegistrationNativePlatformSecretWordAtomOpenRun.close implementation
          (RegistrationNativePlatformSecretWordOpen.accept
            (RegistrationNativePlatformSecretWordFrontendView.wordLocal (decide (before.1.1.parsedAccepts=selectedAccept)))
            (RegistrationNativePlatformSecretWordOrdinary.platform reserveRegistration) setup checks source.verify packet)).run
          (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) := by
  rw [RegistrationNativePlatformSecretWordExecution.typed_run]
  simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.accept,
    bind_apply,get_apply,modify_apply,pure_bind,RegistrationNativePlatformSecretWordFrontend.serverOpen,
    RegistrationNativePlatformSecretWordAtomOpenRun.close,StateT.run,simulateQ_map,map_apply,Functor.map_map]
  rfl

/-- The actual selected typed callback stores its same successful matching collector, preserving all corrected source reserve and failure semantics. -/
theorem accept_retained (packet : registration.InitPacket) (before after : State n KemSK source Platform) (session : Nat)
    (selectedCall : before.1.1.parsedAccepts = selectedAccept) (initial : before.2.kem.2 = none)
    (matching : (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet)).map
      (fun keys => keys.2.pqKey) = some publicKey)
    (supported : (.ok (some session),after) ∈ support ((typed (.inr (.accept packet))).run before)) :
    ∃ (ready : RegistrationNativeSecretWordMessage.ServerReady) (authenticated : registration.AuthenticatedInit)
      (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding),
      after.1.1.server.sessions[session]? = some (some ready) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧
      ready.agreement = ⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain,authenticated.binding⟩ ∧
      collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
      collected.kem = RegistrationNativeSecretWord.Word.atom ∧ ready.reference.kem = RegistrationNativeSecretWord.Word.atom ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) =
        some (collected.plain.verified.identity,collected.plain.verified.keys) := by
  rw [accept_run,support_map] at supported
  obtain ⟨⟨reply,reached⟩,called,returned⟩ := supported
  have success : reply = .ok (some session) := congrArg Prod.fst returned
  subst reply
  have selectedBool : decide (before.1.1.parsedAccepts=selectedAccept)=true := decide_eq_true selectedCall
  rw [selectedBool] at called
  have retained := RegistrationNativePlatformSecretWordTargetOpenSelected.accept_retained setup
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route sign input inside selected pairs publicKey challenge outer
    checks source.verify reserveRegistration packet (before.1.1.server,(before.1.1.environment,(before.1.2,before.2))) reached session
    initial matching called
  cases returned
  exact retained

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained.accept_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained.accept_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained.accept_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetRetained.accept_retained

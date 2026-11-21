-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCanonicalKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetained
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCall

/-! The original canonical APP target stores the atom descriptor of its same actual successful collector in the selected session. Original raw-prefix/session metadata, broad designation and all native failure paths are retained; no separate key-matching, activation, root-echo or whole-source assumption is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCanonicalRetained
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetCall (Call)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
/-- Actual canonical APP success chooses a successful typed call at the same target and its genuinely absent reached getter marker. -/
theorem selected_retained (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity)
    (bounded : RegistrationNativeInterface.Respects budget work) (reserved : budget.create ≤ pairs.length)
    (chosenAt : pairs[target.2.val]? = some chosen) (readback : RegistrationNativeWire.InitReadBack wire) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (before : State n KemSK source) (initialCounter : before.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (ownersEmpty : before.1.beacons = []) (keysEmpty : before.2.kem.1.keys = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
        outer target.2.val target.1.val publicPrekey) mode work before))
    (winning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire serverKeyId budget target claim observed) :
    ∃ index guess entry session,
      ∃ call : Call (State n KemSK source)
        (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
          outer target.2.val target.1.val publicPrekey) (fun current => current.1.parsedAccepts) wire target.1.val
        observed.2.1.transcript session.val,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
      entry.message = guess ∧ call.first.2.kem.2 = none ∧
      (PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet)).map
        (fun keys => keys.2.pqKey) = some chosen.1 ∧
      ∃ (ready : RegistrationNativeSecretWordMessage.ServerReady) (authenticated : registration.AuthenticatedInit)
        (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding),
        call.last.1.server.sessions[session.val]? = some (some ready) ∧
        ready.reference = RegistrationNativeSecretWordServerRoot.message collected ∧
        collected.plain.verified = RegistrationRootInput.verified call.packet authenticated ∧
        collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
        collected.kem = RegistrationNativeSecretWord.Word.atom ∧ ready.reference.kem = RegistrationNativeSecretWord.Word.atom ∧
        PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet) =
          some (collected.plain.verified.identity, collected.plain.verified.keys) := by
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, matching⟩ :=
    RegistrationNativeSecretWordTargetCanonicalKey.selected_call setup checks wire route sign input inside pairs chosen challenge
      outer publicPrekey serverKeyId bounds mode work budget target bounded reserved chosenAt readback claim before initialCounter initialMarker
      ownersEmpty keysEmpty observed supported winning
  have retained := RegistrationNativeSecretWordTargetRetained.accept_retained setup checks wire route sign input inside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey call.packet call.first call.last session.val
    call.selected marker matching call.reached
  exact ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, matching, retained⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCanonicalRetained
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCanonicalRetained.selected_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCanonicalRetained.selected_retained

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRetainedPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBuildChronology

/-! The original canonical APP target stores the atom descriptor of its same actual successful collector in the selected session. Original raw-prefix/session metadata, broad designation and all native failure paths are retained; no separate key-matching, activation, root-echo or whole-source assumption is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetResponse
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
        ready.agreement = ⟨PqxdhServerClearedRoot.pending authenticated.binding.server_pin.binding collected.plain, authenticated.binding⟩ ∧
        collected.plain.verified = RegistrationRootInput.verified call.packet authenticated ∧
        collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
        collected.kem = RegistrationNativeSecretWord.Word.atom ∧ ready.reference.kem = RegistrationNativeSecretWord.Word.atom ∧
        PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet) =
          some (collected.plain.verified.identity, collected.plain.verified.keys) ∧
      ∃ firstLedger lastLedger,
        RegistrationNativeSecretWordTargetPath.Path
          (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
            (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
              (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
              outer target.2.val target.1.val publicPrekey))
          (RegistrationNativeLedger.empty, before) call.pre (firstLedger, call.first) ∧
        (some session.val, (lastLedger, call.last)) ∈ support
          ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
            (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
              (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
              outer target.2.val target.1.val publicPrekey) (.inl (.inr (.accept call.raw)))).run (firstLedger, call.first)) ∧
        RegistrationNativeSecretWordTargetPath.Path
          (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
            (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
              (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
              outer target.2.val target.1.val publicPrekey))
          (lastLedger, call.last) call.post observed.2 ∧
        ∀ response, PqxdhDeploymentTranscript.buildOf observed.2.1.ledger.transcript session.val = some response →
          ∃ (payload : Option Pqxdh.Bytes) (buildFirst buildLast : RegistrationNativeLedger.State × State n KemSK source)
            (left right : List RegistrationNativeInterface.Entry),
            call.post = left ++ ⟨.inl (.inr (.build session.val payload)), some response⟩ :: right ∧
            RegistrationNativeSecretWordTargetPath.Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
              (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
                (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
                outer target.2.val target.1.val publicPrekey)) (lastLedger, call.last) left buildFirst ∧
            (some response, buildLast) ∈ support (((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
              (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
                (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
                outer target.2.val target.1.val publicPrekey)) (.inl (.inr (.build session.val payload)))).run buildFirst) ∧
            RegistrationNativeSecretWordTargetPath.Path (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
              (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
                (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
                outer target.2.val target.1.val publicPrekey)) buildLast right observed.2 ∧
            RegistrationNativeResponseCiphertext.EncodedFrom wire.encodeResponse
              (PqxdhAcceptedRegistration.ciphertextArray challenge) response.serialized ∧
            RegistrationNativeResponseIdentity.EncodedFrom wire.encodeResponse
              buildFirst.2.1.server.pin.binding.identity_public_key response.serialized := by
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, matching,
      firstLedger, lastLedger, prior, called, later⟩ :=
    RegistrationNativeSecretWordTargetChronologicalKey.selected_call setup checks wire route sign input inside pairs chosen challenge
      outer publicPrekey serverKeyId bounds mode work budget target bounded reserved chosenAt readback claim before initialCounter initialMarker
      ownersEmpty keysEmpty observed supported winning
  obtain ⟨ready, authenticated, collected, stored, echo, agreement, verified, ciphertext, atom, referenceAtom, acceptedKeys⟩ :=
    RegistrationNativeSecretWordTargetRetainedPublic.accept_retained setup checks wire route sign input inside
      target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey call.packet call.first call.last session.val
      call.selected marker matching call.reached
  refine ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, matching,
    ready, authenticated, collected, stored, echo, agreement, verified, ciphertext, atom, referenceAtom, acceptedKeys,
    firstLedger, lastLedger, prior, called, later, ?_⟩
  intro response found
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds
    (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
      outer target.2.val target.1.val publicPrekey) mode work before observed supported
  rw [projected] at found
  obtain ⟨payload, member⟩ := RegistrationNativeSecretWordBuildChronology.original_build observed.2.1.transcript session.val response found
  rw [call.recorded] at member
  obtain ⟨buildFirst, buildLast, left, right, recorded, beforeBuild, built, afterBuild, encoded⟩ :=
    RegistrationNativeSecretWordBuildChronology.response setup checks wire route sign input inside
      (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
      outer target.2.val target.1.val publicPrekey serverKeyId bounds call.raw call.packet session.val call.decoded
      prior called later ready stored payload response member
  have original : ready.agreement.pending.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge := by
    rw [agreement]
    exact ciphertext
  exact ⟨payload, buildFirst, buildLast, left, right, recorded, beforeBuild, built, afterBuild,
    original ▸ encoded.1, encoded.2⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetResponse

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetResponse.selected_retained' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetResponse.selected_retained

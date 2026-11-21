-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetBornKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPublic
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalCall

/-! Original canonical APP designation identifies the exact reserved KEM public key for the same parsed-accept and owner target. Actual bundle publication, current roster/private-pair alignment and the original create budget discharge key provenance; no activation, unchanged-bundle or event-simulation premise is supplied. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalKey
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
theorem selected_call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
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
          (lastLedger, call.last) call.post observed.2 := by
  let provider := RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, paths⟩ :=
    RegistrationNativeSecretWordTargetChronologicalCall.selected_call setup checks wire route sign input inside pairs chosen.1 challenge
      outer publicPrekey serverKeyId bounds mode work budget target claim before initialCounter initialMarker observed supported winning
  obtain ⟨owner, raw, packet, keys, found, accepted, parsed, acceptedKeys, publicMatches⟩ :=
    RegistrationNativeSecretWordTargetPublic.designated_public setup checks wire route sign input inside provider outer
      target.2.val target.1.val publicPrekey serverKeyId readback bounds mode work before observed supported budget
      entry.handle (session, target.2) designated
  obtain ⟨pair, pairAt, _handle, ownerKey⟩ := RegistrationNativeSecretWordTargetBornKey.full_born_key setup checks wire route sign input inside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey serverKeyId bounds mode work budget
    bounded reserved before ownersEmpty keysEmpty observed supported target.2.val owner found
  have samePair : pair = chosen := Option.some.inj (pairAt.symm.trans chosenAt)
  have chosenKey : owner.view.kemPublic = chosen.1 := ownerKey.trans (congrArg Prod.fst samePair)
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds
    (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
      target.2.val target.1.val publicPrekey) mode work before observed supported
  rw [projected, call.canonical] at accepted
  have sameRaw : call.raw = raw := Option.some.inj accepted
  rw [← sameRaw, call.decoded] at parsed
  have samePacket : call.packet = packet := Option.some.inj parsed
  refine ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, ?_, paths⟩
  rw [samePacket, acceptedKeys, Option.map_some, publicMatches, chosenKey]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalKey
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalKey.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalKey.selected_call

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCanonicalKey
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetAcceptAtom

/-! The original broad canonical APP target activates the same parsed accept's actual matching private KEM getter and collector. This endpoint derives the reserved public-key match, reached first-getter marker and actual challenge/atom collector receipt while retaining original session/raw-prefix metadata and the unchanged native ledger. It does not identify a later installation root or bound a root-alias event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetActive
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetServerExecution (lower localImpl)
open RegistrationNativeSecretWordTargetCall (Call)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordInterpreter.handler
  RegistrationNativeSecretWordServerCompiler.accept RegistrationAuthenticationCompiler.program

section Receipt
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer true

def CollectedAtom (packet : registration.InitPacket) (before : State n KemSK source) : Prop :=
    ∃ events authenticated afterAuthentication collected afterCollection,
      (.ok (events, .Accepted authenticated), afterAuthentication) ∈ support
        ((lower localImplementation (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
          (RegistrationAuthenticationCompiler.program setup.source.crypto source.verify before.1.server.pin packet)))).run
            (before.1.environment, before.2)) ∧
      (some collected, afterCollection) ∈ support
        ((lower localImplementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run afterAuthentication) ∧
      collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧ collected.kem = Word.atom
end Receipt

/-- Actual canonical APP success chooses a successful typed call at the same target and its genuinely absent reached getter marker. -/
theorem selected_collector (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
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
      CollectedAtom setup checks wire route sign input inside target.2.val pairs chosen.1 challenge outer call.packet call.first := by
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, matching⟩ :=
    RegistrationNativeSecretWordTargetCanonicalKey.selected_call setup checks wire route sign input inside pairs chosen challenge
      outer publicPrekey serverKeyId bounds mode work budget target bounded reserved chosenAt readback claim before initialCounter initialMarker
      ownersEmpty keysEmpty observed supported winning
  have atom := RegistrationNativeSecretWordTargetAcceptAtom.accept_atom setup checks wire route sign input inside
    target.2.val pairs chosen.1 challenge outer target.2.val target.1.val publicPrekey call.packet call.first call.last session.val
    call.selected marker matching call.reached
  exact ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, marker, matching, atom⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetActive
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetActive.selected_collector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetActive.selected_collector

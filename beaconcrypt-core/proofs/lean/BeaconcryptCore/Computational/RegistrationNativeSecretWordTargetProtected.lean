-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPrekeyTarget
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCanonicalRetained
import BeaconcryptCore.Computational.RegistrationNativeSecretWordProtection
import BeaconcryptCore.Computational.RegistrationNativeProtectedInputs

/-! The canonical selected Server root is protected because the complementary real-source public prekey equality remains in the current event. The proof uses that same original successful call, its actual authenticated collector and stored reference. Matching only the accepted PQ key is insufficient and is never used to infer the prekey. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode Budget)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetCall (Call)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The exact successful symbolic collector is inside the native first-DH protected slice whenever its actual verified prekey is the selected public prekey. -/
theorem server_inside (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : MlKemSharedSecret)
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (prekey : collected.plain.verified.keys.prekey = setup.dh.publicKey scalar)
    (key : Key) (realized : RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
      (RegistrationNativeSecretWordServerRoot.message collected) = some key) :
    RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)) key.head = true := by
  have input := congrArg (Option.map (RegistrationNativeSecretWord.eval candidate)) realized
  rw [RegistrationNativeSecretWordMessage.input_eval] at input
  have peer : (RegistrationNativeSecretWordMessage.eval candidate
      (RegistrationNativeSecretWordServerRoot.message collected)).staticPeer = setup.dh.publicKey scalar := by
    change PqxdhPhase2GapDhSource.peer (PqxdhRootTableInitialization.rootArray collected.plain.verified.keys.prekey) = setup.dh.publicKey scalar
    rw [← prekey]
    apply Subtype.ext
    simp [PqxdhPhase2GapDhSource.peer, PqxdhRootTableInitialization.rootArray, PqxdhRefinement.absBytes,
      List.map_map, Function.comp_def, BeaconcryptCore.Refinement.ProtocolComposition.absByte_concreteByte]
  have protectedInput := RegistrationNativeProtectedInputs.server setup.joint setup.dh seed scalar
    (RegistrationNativeSecretWordMessage.eval candidate (RegistrationNativeSecretWordServerRoot.message collected))
    (PqxdhPhase2InputBytes.word collected.plain.third) (RegistrationNativeSecretWord.eval candidate key) rfl peer input
  rw [RegistrationNativeSecretWordProtection.inside_eval]
  exact decide_eq_true protectedInput

/-- The current canonical peer target's same original accepted bytes identify its verified prekey from the transported public conjunct and actual Word publication. -/
theorem call_prekey (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (readback : RegistrationNativeWire.InitReadBack wire)
    (before : State n KemSK source) (empty : before.1.beacons = [])
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
        outer target.2.val target.1.val publicPrekey) mode work before))
    (session : Fin budget.accept)
    (call : Call (State n KemSK source)
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge)
        outer target.2.val target.1.val publicPrekey) (fun current => current.1.parsedAccepts) wire target.1.val observed.2.1.transcript session.val)
    (keyId : U64)
    (pinned : RegistrationNativePrekeyEvents.Pinned setup.source.crypto (RegistrationNativeWire.ledgerCodec wire) serverKeyId observed.2.1.ledger.transcript (.peer keyId))
    (designated : PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget observed.2.1.ledger.transcript (.peer keyId) = some (session, target.2))
    (collected : RegistrationNativeSecretWordServerCollect.Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (keysFound : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet) =
      some (collected.plain.verified.identity, collected.plain.verified.keys)) :
    collected.plain.verified.keys.prekey = publicPrekey := by
  have consistent := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire serverKeyId bounds _ mode work before observed supported
  have accepted := call.canonical
  rw [← consistent] at accepted
  have plain := PqxdhDeploymentKemTransfer.designateIn_some setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId budget observed.2.1.ledger.transcript (.peer keyId) (session, target.2) designated
  exact RegistrationNativeSecretWordPrekeyTarget.peer_prekey setup checks wire route sign input inside
    (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs chosen.1 challenge) outer
    target.2.val target.1.val publicPrekey serverKeyId readback bounds mode work before observed empty supported
    keyId session.val call.raw (RegistrationRootInput.candidate call.packet) (collected.plain.verified.identity, collected.plain.verified.keys)
    pinned plain accepted (RegistrationNativeKemPublicTarget.candidate_read wire call.raw call.packet call.decoded) keysFound
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected.server_inside' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected.server_inside

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected.call_prekey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetProtected.call_prekey

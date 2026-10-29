-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetGetter

/-! Every supported successful collector at the matching first selected getter contains the same challenge ciphertext and atom. This universal local receipt can be applied to the exact collector retained by a later root/session origin theorem, without choosing an unrelated supported collection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl prefixImpl)
open RegistrationNativeSecretWordServerCollect (Input)
open PqxdhKemIndCca
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.implementation
  RegistrationNativeSecretWordInterpreter.handler RegistrationNativeSecretWordServerCompiler.collect
  RegistrationAuthenticationCompiler.program

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
  (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "localImplementation" => localImpl (n := n) setup wire route sign input inside provider outer true

/-- The exact successful collected input, not an independently selected witness, carries the matching challenge and atom. -/
theorem collect_atom (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : Auxiliary n KemSK) (collected : Input registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)
    (initial : before.2.kem.2 = none)
    (matching : (RegistrationRootInput.keys authenticated.registration).pqKey = publicKey)
    (supported : (some collected, after) ∈ support
      ((lower localImplementation (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run before)) :
    collected.plain.verified = RegistrationRootInput.verified packet authenticated ∧
      collected.plain.ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧ collected.kem = Word.atom := by
  have verifiedKey : (RegistrationRootInput.verified packet authenticated).keys.pqKey = publicKey := matching
  rw [RegistrationNativeSecretWordTargetServerExecution.collect_run] at supported
  obtain ⟨ephemeral, first, second, pair, earlier, getter, later, verified, ciphertext, word⟩ :=
    RegistrationNativeSecretWordTargetCollector.collect_receipt
      (prefixImpl setup checks wire route sign input inside provider outer)
      (RegistrationRootInput.verified packet authenticated) before after collected supported
  have prefixSource : (some ephemeral, first) ∈ support
      ((lower localImplementation (simulateQ (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks)
        (RegistrationNativeSecretWordTargetCollector.beforeGetter (RegistrationRootInput.verified packet authenticated)))).run before) := by
    rw [RegistrationNativeSecretWordTargetServerExecution.lower_program]
    convert earlier using 1; rfl
  have prefixMarker := RegistrationNativeSecretWordTargetBeforeGetter.before_phase setup checks wire route sign input inside
    selected pairs publicKey challenge outer (RegistrationRootInput.verified packet authenticated) before (some ephemeral, first) prefixSource
  have firstMarker : first.2.kem.2 = none := prefixMarker.trans initial
  have getterSource : (some pair, second) ∈ support
      ((lower localImplementation (RegistrationNativeSecretWordServerCompiler.prefixImpl setup checks (.encapsulate publicKey))).run first) := by
    simp only [prefixImpl] at getter
    rw [verifiedKey] at getter
    exact getter
  have pairValue := RegistrationNativeSecretWordTargetGetter.getter_atom setup wire route sign input inside
    selected pairs publicKey challenge outer checks first firstMarker second pair getterSource
  exact ⟨verified, ciphertext.trans (congrArg Prod.fst pairValue), word.trans (congrArg Prod.snd pairValue)⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom.collect_atom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom.collect_atom

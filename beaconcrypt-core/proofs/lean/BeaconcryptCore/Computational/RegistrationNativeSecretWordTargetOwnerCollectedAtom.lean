-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAtom
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerProtected

/-! A successful actual selected-owner ordered preparation retains the selected challenge atom and the same native public conversion of the authenticated Server pin. The original optional metadata-admission equation is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectedAtom
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower localImpl)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

attribute [local irreducible] RegistrationNativeSecretWordTargetOwnerCollect.compiler
  RegistrationNativeSecretWordKemEarly.early RegistrationNativeSecretWordTargetServerExecution.localImpl
  RegistrationNativeSecretWordTargetSource.implementation

/-- The actual successful selected-handle collector reaches its forward atom getter and preserves the authenticated packet's real pin conversion. -/
theorem collect (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp) (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before after : Auxiliary n KemSK)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse)
    (handle : owner.kemHandle = selected)
    (ciphertext : authenticated.packet.public.kem_cipher_text = PqxdhAcceptedRegistration.ciphertextArray challenge)
    (supported : (some pending, after) ∈ support
      ((lower (localImpl setup wire route sign input inside
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge) outer false)
        (RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated)).run before)) :
    pending.collected.kem = Word.atom ∧ pending.collected.plain.response = authenticated ∧
      pending.collected.plain.ciphertext = authenticated.packet.public.kem_cipher_text ∧
      pending.collected.plain.server = authenticated.packet.public.identity_key ∧
      setup.source.crypto.xpkConv (absBytes pending.collected.plain.server) = some (absBytes pending.collected.plain.serverConverted) ∧
      PqxdhPhase2DhMetadata.admitted authenticated.pending.control pending.collected.plain = some pending.metadata := by
  rw [RegistrationNativeSecretWordTargetOwnerCollect.collect_run] at supported
  simp only [RegistrationNativeSecretWordBeaconPrepare.prepare, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨collected, middle⟩, called, supported⟩ := supported
  cases collected with
  | none => simp only [simulateQ_pure, StateT.run_pure, Option.bind_none, mem_support_pure_iff] at supported; cases supported
  | some collected =>
      cases admitted : PqxdhPhase2DhMetadata.admitted authenticated.pending.control collected.plain with
      | none => simp only [Option.bind_some, admitted, Option.map_none, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported; cases supported
      | some metadata =>
          simp only [Option.bind_some, admitted, Option.map_some, simulateQ_pure, StateT.run_pure,
            mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
          obtain ⟨rfl, rfl⟩ := supported
          obtain ⟨header, first, reached, prepared, getter, response, ciphertextField, server, converted⟩ :=
            RegistrationNativeSecretWordTargetOwnerCollectReceipt.receipt _ () () () [] before after collected called
          have actual := RegistrationNativeSecretWordTargetOwnerCollect.header setup wire route sign input inside
            (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge) outer owner oneTime authenticated
            before first header prepared
          have headerCiphertext := actual.2.1.trans ciphertext
          have atom : collected.kem = Word.atom := by
            apply RegistrationNativeSecretWordTargetOwnerAtom.getter setup wire route sign input inside selected pairs publicKey challenge outer owner oneTime authenticated
              first reached collected.kem handle
            rw [← headerCiphertext]
            exact getter
          exact ⟨atom, response.trans actual.1, ciphertextField.trans actual.2.1,
            server.trans actual.2.2.1, by rw [server, converted]; exact actual.2.2.2, admitted⟩
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectedAtom
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectedAtom.collect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerCollectedAtom.collect

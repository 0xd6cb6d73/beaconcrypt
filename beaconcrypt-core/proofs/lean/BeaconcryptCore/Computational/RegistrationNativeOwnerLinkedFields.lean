-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseCiphertext
import BeaconcryptCore.Computational.RegistrationNativeResponseIdentity
import BeaconcryptCore.Computational.PqxdhDeploymentKemTransfer

/-! Original owner designation recovers its literal finish packet fields from the same designated session's actual encoded response. The readback equalities identify both the challenge ciphertext and configured owner pin; they do not infer signed-prekey equality from PQ equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields
open PqxdhDeploymentInterface (Budget)

/-- A designated owner's linked response fixes the ciphertext of its original finish input and its original configured pin. -/
theorem owner (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (readback : RegistrationNativeWire.ResponseReadBack wire) (serverKeyId : U64)
    (budget : Budget) (transcript : List PqxdhDeploymentInterface.Entry)
    (index : Nat) (session : Fin budget.accept) (selected : Fin budget.capacity)
    (designated : PqxdhDeploymentTranscript.designateIn crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId budget transcript (.owner index) = some (session, selected))
    (ciphertext : Std.Array U8 1088#usize) (identity : Std.Array U8 32#usize)
    (encoded : ∀ response, PqxdhDeploymentTranscript.buildOf transcript session.val = some response →
      RegistrationNativeResponseCiphertext.EncodedFrom wire.encodeResponse ciphertext response.serialized ∧
      RegistrationNativeResponseIdentity.EncodedFrom wire.encodeResponse identity response.serialized) :
    selected.val = index ∧ ∃ raw,
      (PqxdhDeploymentTranscript.summarize transcript).owners[index]? = some (identity, serverKeyId) ∧
      PqxdhDeploymentTranscript.finishOf transcript index = some raw ∧
      ∃ packet, RegistrationNativeWire.readResponse wire raw = some packet ∧ packet.public.kem_cipher_text = ciphertext := by
  have plain := PqxdhDeploymentKemTransfer.designateIn_some crypto (RegistrationNativeWire.ledgerCodec wire)
    serverKeyId budget transcript (.owner index) (session, selected) designated
  obtain ⟨sameIndex, _established, pin, raw, originalCiphertext, published, pqKey,
      ownerPin, finished, originalRead, _published, _pqKey, _sessionBound, linked⟩ :=
    PqxdhDeploymentTranscript.designate_owner crypto (RegistrationNativeWire.ledgerCodec wire)
      serverKeyId transcript index session.val selected.val plain
  obtain ⟨response, _accepted, _keys, built, responseCiphertext, responseIdentity, _rest⟩ := linked
  obtain ⟨actualCiphertext, actualIdentity⟩ := encoded response built
  have sameCiphertext := Option.some.inj (responseCiphertext.symm.trans
    (RegistrationNativeResponseCiphertext.readback_ciphertext wire readback ciphertext response.serialized actualCiphertext))
  have sameIdentity := Option.some.inj (responseIdentity.symm.trans
    (RegistrationNativeResponseIdentity.readback_identity wire readback identity response.serialized actualIdentity))
  subst originalCiphertext pin
  refine ⟨sameIndex, raw, ownerPin, finished, ?_⟩
  simp only [RegistrationNativeWire.ledgerCodec, Option.bind_eq_some_iff] at originalRead
  obtain ⟨packet, decoded, fields⟩ := originalRead
  exact ⟨packet, decoded, Option.some.inj fields⟩
end BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields.owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOwnerLinkedFields.owner

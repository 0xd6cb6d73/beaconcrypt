-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemCollected

/-! The exact source acceptance after a resumed encapsulation supplies the root builder's actual bytes. This records the supplied candidate in its original fifth secret coordinate without any claim about independence, freshness or the existing restricted-ROM backend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes
open PqxdhServerRootPreparation PqxdhServerRelatedRootInput
open PqxdhBeaconPhase2Preparation (Word32)
variable {Reader E : Type}

/-- Literal successful core acceptance contains exactly the root input built from all five collected source secrets. -/
theorem accepted_input (input : Inputs Reader E Word32) (control after : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (pending : pqxdh.PendingServerRegistration)
    (accepted : accept control binding input = ok (.Ok (after, pending))) :
    pqxdh.build_root_key_input (secrets input) = ok (.Ok pending.root_key_input) := by
  obtain ⟨result, rid, built, _, shape⟩ :=
    BeaconcryptCore.Refinement.PqxdhSurface.server_fresh_acceptance_shape control
      (PqxdhProtocolAcceptance.verified input.verified.identity input.verified.keys) binding
      ⟨input.ephemeral.publicKey, input.ciphertext⟩ (secrets input)
  change pqxdh.server_accept control _ .Fresh binding _ _ = _ at accepted
  rw [shape] at accepted
  cases result <;> simp only [RustM.ok.injEq, core.result.Result.Ok.injEq,
    Prod.mk.injEq, reduceCtorEq] at accepted
  rw [← accepted.2]
  exact built


/-- A successful resumed collector uses the ordinary candidate bytes as its fifth source secret and the ordinary ciphertext as its public output. -/
theorem challenge_fields (verified : Verified Reader) (ephemeral : Ephemeral E)
    (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Inputs Reader E Word32)
    (reached : some input ∈ support (PqxdhRegistrationJointKemCollected.afterEncapsulation
      verified ephemeral (PqxdhRegistrationJointKemResume.reply ciphertext candidate))) :
    input.verified = verified ∧ input.ephemeral = ephemeral ∧
      PqxdhPhase2InputBytes.ciphertext input.ciphertext = ciphertext ∧
      PqxdhPhase2InputBytes.word input.kem = candidate := by
  obtain ⟨sameVerified, sameEphemeral, pair⟩ :=
    PqxdhRegistrationJointKemCollected.after_fields verified ephemeral _ input reached
  have same := Option.some.inj pair
  change (PqxdhAcceptedRegistration.ciphertextArray ciphertext,
    PqxdhRootTableInitialization.rootArray candidate) = (input.ciphertext, input.kem) at same
  refine ⟨sameVerified, sameEphemeral, ?_, ?_⟩
  · rw [← (Prod.mk.inj same).1]
    exact (PqxdhPhase2InputBytes.ciphertext_roundtrip input.ciphertext ciphertext).2
  · rw [← (Prod.mk.inj same).2]
    exact PqxdhPhase2InputBytes.word_rootArray candidate

/-- Actual acceptance after the literal resumed callback feeds the exact four actual DH outputs and the challenger candidate into the source's192-byte root layout. It assumes neither coordinate independence nor a successful callback in advance. -/
theorem challenge_input (verified : Verified Reader) (ephemeral : Ephemeral E)
    (ciphertext : PqxdhKemIndCca.MlKem768Ciphertext) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : Inputs Reader E Word32)
    (reached : some input ∈ support (PqxdhRegistrationJointKemCollected.afterEncapsulation
      verified ephemeral (PqxdhRegistrationJointKemResume.reply ciphertext candidate)))
    (control after : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (pending : pqxdh.PendingServerRegistration)
    (accepted : accept control binding input = ok (.Ok (after, pending))) :
    absBytes pending.root_key_input.bytes = PqxdhHiddenRoot.hiddenRootIKM
      (PqxdhPhase2InputBytes.coordinates input.first input.second input.third input.fourth) candidate := by
  have actual := PqxdhPhase2InputBytes.root_input (secrets input) pending.root_key_input
    (accepted_input input control after binding pending accepted)
  simpa only [secrets, (challenge_fields verified ephemeral ciphertext candidate input reached).2.2.2] using actual

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes.accepted_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes.accepted_input

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes.challenge_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes.challenge_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes.challenge_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootBytes.challenge_input

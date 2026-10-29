-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseCandidate
import BeaconcryptCore.Computational.RegistrationWorldServerCompletion

/-! Actual known-kernel World record execution, mandatory signing and native peer insertion retain the public response identity. The proof uses the reached extracted controller paths and the actual shared World, independently of its cached primitive replies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseWorld
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationWorldAgreement (State)
variable {n : Nat} {Auxiliary Encoded Index Target Value ι KemSK Reader Response : Type}
variable {base : OracleSpec ι} {source : OracleSpec Index}

private theorem interpreted_support (implementation : QueryImpl source (StateT Target ProbComp))
    (work : OracleComp source Value) (before : Target) (result : Value × Target)
    (supported : result ∈ support ((simulateQ implementation work).run before)) : result.1 ∈ support work := by
  apply OracleComp.support_simulateQ_run'_subset implementation work before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

/-- Native peer insertion retains the exact encoded response bytes on every successful installation. -/
theorem install_encoded (control : pqxdh.ServerState) (published : registration.PublishedServerResponse Encoded)
    (before after : State n Auxiliary) (peer : peer.PublishedPeer Encoded)
    (supported : (.ok (.Ok peer), after) ∈ support ((RegistrationWorldServerCompletion.install control published).run before)) :
    peer.encoded = published.encoded := by
  obtain ⟨result, prepared, retained⟩ := BeaconcryptCore.Refinement.PeerOwnership.peer_insert_begin_retains control published
  cases result with
  | Err previous =>
      simp only [RegistrationWorldServerCompletion.install, prepared] at supported
      cases supported
  | Ok pending =>
      rw [RegistrationWorldServerCompletion.install_native control published pending prepared] at supported
      simp only [StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨inserted, _reached, returned⟩ := supported
      rcases inserted with ⟨inserted, current⟩
      cases inserted <;> simp [BeaconcryptCore.Refinement.PeerOwnership.publication_finish] at returned
      obtain ⟨same, _sameState⟩ := returned
      exact (congrArg (fun value : beaconcrypt_core.peer.PublishedPeer Encoded => value.encoded) same).trans retained.2.2.2.2.1

/-- Actual World signing and encoding retain the current candidate identity, with every shared hash/signature effect in place. -/
theorem signing_identity (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) (published : registration.PublishedServerResponse Encoded)
    (before after : State n Auxiliary)
    (supported : (.ok (.Ok published), after) ∈ support ((RegistrationWorldServerCompletion.signing sign encode pending).run before)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode pending.candidate.server_identity_public_key published.encoded := by
  simp only [RegistrationWorldServerCompletion.signing, StateT.run, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have actual := interpreted_support (RegistrationWorldSigning.outgoing sign)
    (RegistrationWorldServerPublication.program encode pending) before.world inner reached
  have value : inner.1 = .ok (.Ok published) := congrArg Prod.fst returned
  rw [value] at actual
  exact RegistrationNativeResponseIdentity.program_identity encode pending published actual

/-- The actual record, hash, mandatory ML signature and peer installation retain the admitted Server identity. -/
theorem fromInitial_identity (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (control : pqxdh.ServerState)
    (pending : registration.ServerInitialKdf) (published : peer.PublishedPeer Encoded)
    (before after : State n Auxiliary)
    (supported : (.ok (.Ok published), after) ∈ support
      ((RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending).run before)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode pending.candidate.server_identity_public_key published.encoded := by
  simp only [RegistrationWorldServerCompletion.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨record, reached, continued⟩ := supported
  have actual := interpreted_support (RegistrationWorldRecords.handler setup codec)
    (RegistrationServerRecordExecutor.fromInitial pending) before record reached
  cases result : record.1 with
  | fail error | div => simp only [result] at continued; cases continued
  | ok value => cases value with
    | Err previous => simp only [result] at continued; cases continued
    | Ok completed =>
      rw [result] at actual continued
      have candidate := RegistrationNativeResponseCandidate.record_identity pending completed actual
      change (.ok (.Ok published), after) ∈ support
        ((RegistrationWorldServerCompletion.publish sign encode control completed).run record.2) at continued
      simp only [RegistrationWorldServerCompletion.publish, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨signed, signedSupport, inserted⟩ := continued
      rcases signed with ⟨signed, signedState⟩
      cases signing : signed with
      | fail error | div => simp only [signing] at inserted; cases inserted
      | ok reply => cases reply with
        | Err previous => simp only [signing] at inserted; cases inserted
        | Ok response =>
          rw [signing] at inserted
          rw [signing] at signedSupport
          have encoded := signing_identity sign encode completed response record.2 signedState signedSupport
          have same := install_encoded control response signedState after published inserted
          rw [same, ← candidate]
          exact encoded

end BeaconcryptCore.Computational.RegistrationNativeResponseWorld
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseWorld.install_encoded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseWorld.install_encoded
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseWorld.signing_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseWorld.signing_identity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseWorld.fromInitial_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseWorld.fromInitial_identity

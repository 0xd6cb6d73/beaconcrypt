-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponsePaired
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerMaterial

/-! Successful actual Word Server builds retain the original stored registration ciphertext and current Server identity through one-use consumption, lookup admission, material choice, raw publication, mandatory signing and native installation. All callback replies remain arbitrary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open RegistrationNativeSecretWordServerMaterial (Spec)
variable {n : Nat}

private theorem finish_success (result : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before after : ServerState) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationNativeSecretWordServerMaterial.finish (n := n) result).run before)) :
    ∃ published, result = .ok (.Ok published) ∧ published.encoded = bytes := by
  cases result with
  | fail error | div => simp [StateT.run, RegistrationNativeSecretWordServerMaterial.finish] at supported
  | ok result => cases result with
    | Err previous => simp [StateT.run, RegistrationNativeSecretWordServerMaterial.finish] at supported
    | Ok published =>
        simp only [StateT.run, RegistrationNativeSecretWordServerMaterial.finish, mem_support_pure_iff,
          Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at supported
        exact ⟨published, rfl, supported.1.2.symm⟩

/-- Arbitrary paired material replies preserve the actual admitted candidate's public fields. -/
theorem admitted (wire : RegistrationNativeWire.Wire) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (reference : Message)
    (published : peer.PublishedPeer Pqxdh.Bytes)
    (supported : .ok (.Ok published) ∈ support
      (RegistrationNativeSecretWordServerMaterial.admitted (n := n) wire.encodeResponse control initial reference)) :
    RegistrationNativeResponsePaired.EncodedFrom wire.encodeResponse initial published.encoded := by
  simp only [RegistrationNativeSecretWordServerMaterial.admitted, mem_support_bind_iff] at supported
  obtain ⟨choice, _requested, continued⟩ := supported
  cases choice with
  | none => cases continued
  | some choice =>
      exact RegistrationNativeResponsePaired.branch wire.encodeResponse control initial choice published
        (RegistrationNativeResponsePaired.simulation_support RegistrationNativeSecretWordServerMaterial.commonLift _ _ continued)

def EncodedFrom (wire : RegistrationNativeWire.Wire) (ready : ServerReady)
    (pin : session.ServerAuthenticationPin) (bytes : Pqxdh.Bytes) : Prop :=
  RegistrationNativeResponseCiphertext.EncodedFrom wire.encodeResponse ready.agreement.pending.kem_ciphertext bytes ∧
    RegistrationNativeResponseIdentity.EncodedFrom wire.encodeResponse pin.binding.identity_public_key bytes

private theorem hash_receipt (pending : registration.ServerAdHash) (initial : registration.ServerInitialKdf)
    (supported : .ok (.Ok initial) ∈ support (RegistrationNativeSecretWordServerMaterial.adHash (n := n) pending)) :
    ∃ digest, pending.resume (.Some digest) = .ok (.Ok initial) := by
  cases requested : pending.request with
  | fail error | div => simp [RegistrationNativeSecretWordServerMaterial.adHash, requested] at supported
  | ok request =>
      simp only [RegistrationNativeSecretWordServerMaterial.adHash, requested, mem_support_bind_iff] at supported
      obtain ⟨digest, _, returned⟩ := supported
      simp only [mem_support_pure_iff] at returned
      exact ⟨RegistrationAuthenticationShared.digestArray digest, returned.symm⟩

/-- Every successful one-use completion encodes the same stored token ciphertext and current lookup pin. -/
theorem complete (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (ready : ServerReady) (application : Slice U8) (before after : ServerState)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationNativeSecretWordServerMaterial.complete (n := n) wire reservePeer ready application).run before)) :
    EncodedFrom wire ready before.pin bytes := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok before.control
  cases next with
  | Err previous =>
      simp [StateT.run, RegistrationNativeSecretWordServerMaterial.complete, peer.begin_completion_lookup,
        nextRun] at supported
  | Ok allocated =>
      have looked := BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_begin_next
        before.control before.pin (RegistrationNativeSecretWordServerMaterial.token ready) application allocated nextRun
      simp only [StateT.run, RegistrationNativeSecretWordServerMaterial.complete, looked,
        BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_request] at supported
      split at supported
      · simp only [mem_support_bind_iff] at supported
        obtain ⟨occupied, _requested, continued⟩ := supported
        cases resumed : (peer.CompletionLookup.mk before.control before.pin
            (RegistrationNativeSecretWordServerMaterial.token ready) application allocated).resume occupied with
        | fail error | div => simp only [resumed] at continued; cases continued
        | ok result => cases result with
          | Err previous => simp only [resumed] at continued; cases continued
          | Ok selected =>
              simp only [resumed, mem_support_bind_iff] at continued
              obtain ⟨hashed, hashCalled, continued⟩ := continued
              cases hashed with
              | fail error | div => simp at continued
              | ok answer => cases answer with
                | Err previous => simp at continued
                | Ok initial =>
                    obtain ⟨digest, hashResumed⟩ := hash_receipt selected initial hashCalled
                    dsimp only at continued
                    split at continued
                    · simp only [mem_support_bind_iff] at continued
                      obtain ⟨published, reached, finished⟩ := continued
                      obtain ⟨actual, successful, encoded⟩ := finish_success published before after keyId bytes finished
                      rw [successful] at reached
                      have fields := admitted wire before.control (RegistrationBoundKeySchedule.publicInitial initial)
                        ready.reference actual reached
                      have initialized : BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission before.control before.pin
                          (if (show Bool from occupied) then .Occupied else .Available)
                          (RegistrationNativeSecretWordServerMaterial.token ready).agreement application initial := by
                        refine ⟨selected, digest, ?_, hashResumed⟩
                        exact (BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_resume
                          (peer.CompletionLookup.mk before.control before.pin
                            (RegistrationNativeSecretWordServerMaterial.token ready) application allocated) occupied).symm.trans resumed
                      have ct := RegistrationNativeResponseCipherCandidate.initial_ciphertext _ _ _ _ _ _ initialized
                      have identity := RegistrationNativeResponseCandidate.initial_identity _ _ _ _ _ _ initialized
                      change RegistrationNativeResponseCiphertext.EncodedFrom wire.encodeResponse
                          initial.candidate.kem_ciphertext actual.encoded ∧
                        RegistrationNativeResponseIdentity.EncodedFrom wire.encodeResponse
                          initial.candidate.server_identity_public_key actual.encoded at fields
                      rw [ct, identity, encoded] at fields
                      exact fields
                    · simp only [mem_support_pure_iff] at continued
                      cases continued
      · simp only [mem_support_pure_iff] at supported
        cases supported

/-- Actual successful build returns a response of the exact one-use stored session. -/
theorem build (wire : RegistrationNativeWire.Wire) (reservePeer : Bool)
    (handle : Nat) (application : Option (Slice U8)) (before after : ServerState)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationNativeSecretWordServerMaterial.build (n := n) wire reservePeer handle application).run before)) :
    ∃ ready, before.sessions[handle]? = some (some ready) ∧ EncodedFrom wire ready before.pin bytes := by
  unfold StateT.run RegistrationNativeSecretWordServerMaterial.build RegistrationNativeSecretWordServerMaterial.take at supported
  cases found : before.sessions[handle]? with
  | none => simp [found] at supported
  | some entry => cases entry with
    | none => simp [found] at supported
    | some ready =>
        rw [found] at supported
        dsimp only at supported
        cases application with
        | none => simp at supported
        | some application =>
            exact ⟨ready, rfl, complete wire reservePeer ready application
              { before with sessions := before.sessions.set handle none } after keyId bytes supported⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse.admitted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordResponse.build

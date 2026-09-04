import BeaconcryptCore.Refinement.ServerTransactionRefinement
import BeaconcryptCore.Refinement.ProtocolComposition
import BeaconcryptCore.Refinement.PqxdhSurface
import BeaconcryptCore.Refinement.RatchetTraceRefinement

/-! The extracted candidate publication transaction refines an explicit optional-publication closure of the unchanged ideal server operation. The core allocation state and emitted values are related field by field; the ideal peer map and consumed-registration set are external context. This is not atomic serverRespond refinement on failed sealing. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Refinement.RepresentationBridge
open BeaconcryptCore.Refinement.ProtocolComposition
open BeaconcryptCore.Refinement.ServerTransactionRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.ServerPublicationRefinement

/-- The candidate's concrete fields represent the allocation and response inputs. No execution or desired publication result is assumed. -/
structure CandidateRefines (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (identity kemCipher ephemeral : Pqxdh.Bytes) (candidate : pqxdh.ServerRegistrationCandidate) : Prop where
  previousCounter : candidate.previous_state.last_key_id.val = entry.n
  nextCounter : candidate.next_state.last_key_id.val = entry.n + 1
  assignedId : candidate.key_id.val = entry.n + 1
  beaconIdentity : absBytes candidate.beacon_identity_public_key = identity
  serverIdentity : absBytes candidate.server_identity_public_key = c.edPub entry.ikSk
  serverId : candidate.server_identity_key_id.val = entry.sid
  ephemeralKey : absBytes candidate.ephemeral_public_key = ephemeral
  kemCiphertext : absBytes candidate.kem_ciphertext = kemCipher
  associatedData : absBytes candidate.associated_data = Pqxdh.assocData (c.edPub entry.ikSk) identity

/-- Available preparation derives every candidate field from extracted allocation and associated-data construction. -/
theorem prepare_candidate_refines (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (identity kemCipher ephemeral : Pqxdh.Bytes)
    (hcounter : state.last_key_id.val = entry.n) (hbinding : pending.server_binding = binding)
    (hserverIdentity : absBytes binding.identity_public_key = c.edPub entry.ikSk)
    (hserverId : binding.identity_key_id.val = entry.sid)
    (hidentity : absBytes pending.beacon_identity_public_key = identity)
    (hkem : absBytes pending.kem_ciphertext = kemCipher)
    (hephem : absBytes pending.ephemeral_public_key = ephemeral)
    (hmax : entry.n ≠ Pqxdh.maxKeyId) :
    ∃ candidate, pqxdh.server_prepare_commit state pending binding .Available = ok (.Ok candidate) ∧
      CandidateRefines c entry identity kemCipher ephemeral candidate := by
  have hne : state.last_key_id ≠ core.num.U64.MAX :=
    fun heq => hmax (hcounter.symm.trans (congrArg UScalar.val heq))
  obtain ⟨next, ad, _, hnext, had, hprepare⟩ :=
    BeaconcryptCore.Refinement.PqxdhSurface.available_server_key_id_candidate_shape
      state pending binding hne hbinding
  obtain ⟨canonical, hcanonical, hbytes⟩ :=
    build_associated_data_abs binding.identity_public_key pending.beacon_identity_public_key
  have heq : canonical = ad := RustM.ok.inj (hcanonical.symm.trans had)
  exact ⟨_, hprepare, ⟨hcounter, by simpa only [hcounter] using hnext,
    by simpa only [hcounter] using hnext, hidentity, hserverIdentity, hserverId, hephem, hkem,
    by simpa only [heq, hserverIdentity, hidentity] using hbytes⟩⟩

/-- Reconstruct the complete response from the candidate's actual fields and the first send's actual message index and ciphertext. Wire serialization remains an external boundary. -/
def candidateResponse (candidate : pqxdh.ServerRegistrationCandidate)
    (message : Ratchet.Msg Pqxdh.Bytes) : Pqxdh.KexResponse :=
  ⟨absBytes candidate.server_identity_public_key, absBytes candidate.ephemeral_public_key,
    absBytes candidate.kem_ciphertext,
    ⟨candidate.server_identity_key_id.val, message.idx + 1, message.ct⟩, candidate.key_id.val⟩

/-- Exact candidate transaction observations and externally owned publication context. Failure preserves the entire context; success inserts exactly the emitted peer and represented kernel. -/
def PublicationRefines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (entry : Pqxdh.ServerState) (root : Pqxdh.Bytes) (candidate : pqxdh.ServerRegistrationCandidate)
    (result : CandidateResult (Ratchet.Msg Pqxdh.Bytes))
    (publication : PublicationObservation × Pqxdh.ServerState) : Prop :=
  match result with
  | .sealFailed state =>
      state = candidate.previous_state ∧ state.last_key_id.val = entry.n ∧
      publication = (.sealFailed, entry)
  | .published state peer kernel message =>
      state = candidate.next_state ∧ peer.key_id = candidate.key_id ∧
      peer.identity_public_key = candidate.beacon_identity_public_key ∧
      peer.associated_data = candidate.associated_data ∧
      ∃ send receive,
        ByteKernelRefines c execute (Pqxdh.rootChains c root).2 send receive kernel ∧
        publication = (.published (candidateResponse candidate message),
          { entry with
            n := state.last_key_id.val
            peers := (peer.key_id.val, ⟨absBytes peer.identity_public_key,
              absBytes peer.associated_data, send, receive⟩) :: entry.peers })

/-- Identity changes are rejected by extracted preparation before any allocation or publication. This is an explicit core admission abort, outside atomic serverEmit's fixed-binding input domain. -/
theorem prepare_binding_changed (state : pqxdh.ServerState)
    (pending : pqxdh.PendingServerRegistration) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability)
    (hmismatch : pending.server_binding.identity_key_id ≠ binding.identity_key_id ∨
      pending.server_binding.identity_public_key ≠ binding.identity_public_key) :
    pqxdh.server_prepare_commit state pending binding availability = ok (.Err .IdentityMismatch) :=
  BeaconcryptCore.Refinement.PqxdhSurface.server_binding_mismatch_is_rejected
    state pending binding availability hmismatch

/-- An actual failed first seal and extracted abort match optional publication exactly, including the unchanged external context and absence of a peer or response. -/
theorem finish_candidate_failure_refines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (initial : InitialKdfInterpreter) (entry : Pqxdh.ServerState)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : Std.Array Std.U8 32#usize)
    (identity kemCipher ephemeral application : Pqxdh.Bytes)
    (h : CandidateRefines c entry identity kemCipher ephemeral candidate)
    (hmax : entry.n ≠ Pqxdh.maxKeyId)
    (hfree : ¬ (entry.peers.lookup (entry.n + 1)).isSome) :
    ∃ result, finishCandidate candidate root initial execute
        (fun _ _ _ => (core.option.Option.None : core.option.Option (Ratchet.Msg Pqxdh.Bytes))) = ok result ∧
      PublicationRefines c execute entry (absBytes root) candidate result
        (idealPublication c entry identity (absBytes root) kemCipher ephemeral application false) :=
  ⟨.sealFailed candidate.previous_state,
    finishCandidate_failed (recordCrypto c) candidate root initial execute,
    rfl, h.previousCounter,
    idealPublication_failed c entry identity (absBytes root) kemCipher ephemeral application hmax hfree⟩

/-- Exhaustion and collision are actual preparation rejections and exactly the existing ideal allocation errors; neither publishes a peer or advances allocation. -/
theorem prepare_allocation_rejections_refine (c : Pqxdh.Crypto) (entry : Pqxdh.ServerState)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (identity root kemCipher ephemeral application : Pqxdh.Bytes) (sealed : Bool)
    (hcounter : state.last_key_id.val = entry.n) (hbinding : pending.server_binding = binding)
    (hserverIdentity : absBytes binding.identity_public_key = c.edPub entry.ikSk)
    (havail : availability = .Occupied ↔ (entry.peers.lookup (entry.n + 1)).isSome) :
    (entry.n = Pqxdh.maxKeyId →
      pqxdh.server_prepare_commit state pending binding availability = ok (.Err .KeyIdExhausted) ∧
      idealPublication c entry identity root kemCipher ephemeral application sealed =
        (.rejected .keyIdExhausted, entry)) ∧
    (entry.n ≠ Pqxdh.maxKeyId → (entry.peers.lookup (entry.n + 1)).isSome →
      pqxdh.server_prepare_commit state pending binding availability = ok (.Err .KeyIdCollision) ∧
      idealPublication c entry identity root kemCipher ephemeral application sealed =
        (.rejected .keyIdCollision, entry)) := by
  obtain ⟨hexhausted, hcollision, _⟩ := server_prepare_commit_refines c entry state pending
    binding availability hcounter hbinding hserverIdentity havail
  exact ⟨fun hmax => ⟨hexhausted hmax, by simp [idealPublication, Pqxdh.serverEmit, hmax]⟩,
    fun hmax hoccupied => ⟨hcollision hmax hoccupied,
      by simp [idealPublication, Pqxdh.serverEmit, hmax, hoccupied]⟩⟩

/-- Publishing the actual candidate fields and an already-refined first record constructs exactly the ideal response and peer insertion. The first-send relation is discharged by the complete transaction theorem below. -/
theorem CandidateRefines.published_fields_refine (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (entry : Pqxdh.ServerState) (candidate : pqxdh.ServerRegistrationCandidate)
    (identity root kemCipher ephemeral application : Pqxdh.Bytes)
    (h : CandidateRefines c entry identity kemCipher ephemeral candidate)
    (hmax : entry.n ≠ Pqxdh.maxKeyId)
    (hfree : ¬ (entry.peers.lookup (entry.n + 1)).isSome)
    (kernel : ConcreteRatchetKernel)
    (hkernel : ByteKernelRefines c execute (Pqxdh.rootChains c root).2
      (Pqxdh.serverRecord c entry identity root application).2
      ⟨(Pqxdh.rootChains c root).2, 0, []⟩ kernel) :
    PublicationRefines c execute entry root candidate
      (.published candidate.next_state
        ⟨candidate.key_id, candidate.beacon_identity_public_key, candidate.associated_data⟩ kernel
        (Pqxdh.serverRecord c entry identity root application).1)
      (idealPublication c entry identity root kemCipher ephemeral application true) := by
  refine ⟨rfl, rfl, rfl, rfl, _, _, hkernel, ?_⟩
  simp [idealPublication, Pqxdh.serverEmit, hmax, hfree, candidateResponse,
    h.serverIdentity, h.ephemeralKey, h.kemCiphertext, h.serverId, h.assignedId,
    h.nextCounter, h.beaconIdentity, h.associatedData]

/-- The first-record boundary uses the candidate's actual association bytes, server identifier, and assigned-ID plaintext prefix. Sealing may independently fail. -/
noncomputable def candidateSealReply (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (candidate : pqxdh.ServerRegistrationCandidate) (application : Pqxdh.Bytes) (sealed : Bool)
    (material : ratchet.RatchetMaterial) (sequence : Std.U64) (context : Unit) :
    core.option.Option (Ratchet.Msg Pqxdh.Bytes) :=
  if sealed then recordSealReply c execute
    ⟨absBytes candidate.associated_data, 1, candidate.server_identity_key_id.val⟩
    (Pqxdh.LE64 candidate.key_id.val ++ application) material sequence context
  else .None

/-- The complete successful candidate transaction initializes concrete key material, executes the first send, and commits the exact response and fully represented peer. -/
theorem finish_candidate_success_refines (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (entry : Pqxdh.ServerState) (candidate : pqxdh.ServerRegistrationCandidate)
    (root : Std.Array Std.U8 32#usize) (identity kemCipher ephemeral application : Pqxdh.Bytes)
    (h : CandidateRefines c entry identity kemCipher ephemeral candidate)
    (hmax : entry.n ≠ Pqxdh.maxKeyId)
    (hfree : ¬ (entry.peers.lookup (entry.n + 1)).isSome) :
    ∃ result, finishCandidate candidate root initial execute
        (candidateSealReply c execute candidate application true) = ok result ∧
      PublicationRefines c execute entry (absBytes root) candidate result
        (idealPublication c entry identity (absBytes root) kemCipher ephemeral application true) := by
  obtain ⟨initialized, next, send, receive, hinit, hsendRun, hpost, hsend, hreceive⟩ :=
    initialize_serverRecord_refines c initial execute hinitial hstep root entry identity
      (absBytes root) application rfl
  have hzero : receive.n = 0 := congrArg Ratchet.RecvState.n hreceive
  have hchain : receive.ck = initialized.refined.receive_chain := by
    simpa only [hzero, Ratchet.chainAt, Function.iterate_zero_apply] using hpost.receiveControl.chain
  have horigin : absChain initialized.refined.receive_chain = (Pqxdh.rootChains c (absBytes root)).2 := by
    simpa only [mapRecv, hchain] using congrArg Ratchet.RecvState.ck hreceive
  have hbyte : ByteKernelRefines c execute (Pqxdh.rootChains c (absBytes root)).2
      (Pqxdh.serverRecord c entry identity (absBytes root) application).2
      ⟨(Pqxdh.rootChains c (absBytes root)).2, 0, []⟩ next :=
    ⟨initialized.refined.receive_chain, send, receive, horigin, hsend, hreceive, hpost⟩
  refine ⟨.published candidate.next_state
      ⟨candidate.key_id, candidate.beacon_identity_public_key, candidate.associated_data⟩ next
      (Pqxdh.serverRecord c entry identity (absBytes root) application).1, ?_,
    h.published_fields_refine c execute entry candidate identity (absBytes root) kemCipher
      ephemeral application hmax hfree next hbyte⟩
  have hreply : candidateSealReply c execute candidate application true =
      recordSealReply c execute ⟨Pqxdh.assocData (c.edPub entry.ikSk) identity, 1, entry.sid⟩
        (Pqxdh.LE64 (entry.n + 1) ++ application) := by
    funext material sequence context
    simp [candidateSealReply, h.associatedData, h.serverId, h.assignedId]
  simp! only [finishCandidate, initializeCandidate_eq, hinit, bind_tc_ok, hreply,
    hsendRun, pqxdh.server_commit]

/-- Both seal outcomes execute the actual full candidate transaction and preserve exact optional-publication observations and state. -/
theorem finish_candidate_refines (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (entry : Pqxdh.ServerState) (candidate : pqxdh.ServerRegistrationCandidate)
    (root : Std.Array Std.U8 32#usize) (identity kemCipher ephemeral application : Pqxdh.Bytes)
    (h : CandidateRefines c entry identity kemCipher ephemeral candidate)
    (hmax : entry.n ≠ Pqxdh.maxKeyId)
    (hfree : ¬ (entry.peers.lookup (entry.n + 1)).isSome) (sealed : Bool) :
    ∃ result, finishCandidate candidate root initial execute
        (candidateSealReply c execute candidate application sealed) = ok result ∧
      PublicationRefines c execute entry (absBytes root) candidate result
        (idealPublication c entry identity (absBytes root) kemCipher ephemeral application sealed) :=
  match sealed with
  | false => finish_candidate_failure_refines c execute initial entry candidate root identity
      kemCipher ephemeral application h hmax hfree
  | true => finish_candidate_success_refines c initial execute hinitial hstep entry candidate root
      identity kemCipher ephemeral application h hmax hfree

/-- The result of preparation followed by the complete candidate transaction. -/
inductive PreparedPublicationResult where
  | rejected (error : pqxdh.RegistrationError)
  | finished (result : CandidateResult (Ratchet.Msg Pqxdh.Bytes))

/-- Sequence actual extracted preparation with candidate-bound initialization, first sealing, and commit or abort. -/
noncomputable def prepareAndFinish (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (root : Std.Array Std.U8 32#usize) (application : Pqxdh.Bytes) (sealed : Bool) :
    RustM PreparedPublicationResult := do
  let prepared ← pqxdh.server_prepare_commit state pending binding availability
  match prepared with
  | .Err error => ok (.rejected error)
  | .Ok candidate =>
      let result ← finishCandidate candidate root initial execute
        (candidateSealReply c execute candidate application sealed)
      ok (.finished result)

/-- Preparation errors retain their exact error classification and unchanged context; completed candidates retain the complete publication relation and preparation-derived fields. -/
def PreparedPublicationRefines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (entry : Pqxdh.ServerState) (root identity kemCipher ephemeral : Pqxdh.Bytes)
    (result : PreparedPublicationResult) (publication : PublicationObservation × Pqxdh.ServerState) : Prop :=
  match result with
  | .rejected error => ∃ idealError, genServerError idealError = some error ∧
      publication = (.rejected idealError, entry)
  | .finished result => ∃ candidate, CandidateRefines c entry identity kemCipher ephemeral candidate ∧
      PublicationRefines c execute entry root candidate result publication

/-- Every fixed-binding preparation outcome is covered: exhausted or occupied allocation, failed first sealing, and complete successful publication. Candidate representation is derived from the actual preparation, never assumed. -/
theorem prepareAndFinish_refines (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (entry : Pqxdh.ServerState) (state : pqxdh.ServerState)
    (pending : pqxdh.PendingServerRegistration) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability) (root : Std.Array Std.U8 32#usize)
    (identity kemCipher ephemeral application : Pqxdh.Bytes) (sealed : Bool)
    (hcounter : state.last_key_id.val = entry.n) (hbinding : pending.server_binding = binding)
    (hserverIdentity : absBytes binding.identity_public_key = c.edPub entry.ikSk)
    (hserverId : binding.identity_key_id.val = entry.sid)
    (hidentity : absBytes pending.beacon_identity_public_key = identity)
    (hkem : absBytes pending.kem_ciphertext = kemCipher)
    (hephem : absBytes pending.ephemeral_public_key = ephemeral)
    (havail : availability = .Occupied ↔ (entry.peers.lookup (entry.n + 1)).isSome) :
    ∃ result, prepareAndFinish c initial execute state pending binding availability root application sealed = ok result ∧
      PreparedPublicationRefines c execute entry (absBytes root) identity kemCipher ephemeral result
        (idealPublication c entry identity (absBytes root) kemCipher ephemeral application sealed) := by
  obtain ⟨hexhausted, hcollision⟩ := prepare_allocation_rejections_refine c entry state pending binding
    availability identity (absBytes root) kemCipher ephemeral application sealed hcounter hbinding hserverIdentity havail
  by_cases hmax : entry.n = Pqxdh.maxKeyId
  · exact ⟨.rejected .KeyIdExhausted, by simp [prepareAndFinish, (hexhausted hmax).1],
      .keyIdExhausted, rfl, (hexhausted hmax).2⟩
  · by_cases hoccupied : (entry.peers.lookup (entry.n + 1)).isSome
    · exact ⟨.rejected .KeyIdCollision, by simp [prepareAndFinish, (hcollision hmax hoccupied).1],
        .keyIdCollision, rfl, (hcollision hmax hoccupied).2⟩
    · have havailable : availability = .Available := by
        cases availability with
        | Available => rfl
        | Occupied => exact False.elim (hoccupied (havail.mp rfl))
      obtain ⟨candidate, hprepare, hcandidate⟩ := prepare_candidate_refines c entry state pending binding
        identity kemCipher ephemeral hcounter hbinding hserverIdentity hserverId hidentity hkem hephem hmax
      obtain ⟨result, hfinish, hresult⟩ := finish_candidate_refines c initial execute hinitial hstep
        entry candidate root identity kemCipher ephemeral application hcandidate hmax hoccupied sealed
      exact ⟨.finished result, by simp [prepareAndFinish, havailable, hprepare, hfinish],
        candidate, hcandidate, hresult⟩

/-- Successful arbitrary callbacks preserve the actual extracted sequence and full encrypted record. Failure remains unrestricted. -/
def CandidateSealCorrect (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (candidate : pqxdh.ServerRegistrationCandidate) (application : Pqxdh.Bytes)
    (reply : ratchet.RatchetMaterial → Std.U64 → Unit → core.option.Option (Ratchet.Msg Pqxdh.Bytes)) : Prop :=
  ∀ material sequence context message, reply material sequence context = .Some message →
    message = ⟨sequence.val - 1, (concreteCrypto c execute).enc material
      ⟨absBytes candidate.associated_data, 1, candidate.server_identity_key_id.val⟩
      (Pqxdh.LE64 candidate.key_id.val ++ application)⟩

/-- Every actual optional first-seal callback has an outcome annotation reproducing the complete extracted candidate transaction. -/
theorem finishCandidate_callback_covered (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : Std.Array Std.U8 32#usize)
    (application : Pqxdh.Bytes)
    (reply : ratchet.RatchetMaterial → Std.U64 → Unit → core.option.Option (Ratchet.Msg Pqxdh.Bytes))
    (hcorrect : CandidateSealCorrect c execute candidate application reply) :
    ∃ sealed, finishCandidate candidate root initial execute reply =
      finishCandidate candidate root initial execute (candidateSealReply c execute candidate application sealed) := by
  obtain ⟨beaconOrigin, serverOrigin, _, server, _, hinit, _, _, _, hkernel⟩ :=
    initial_kernels_refine (concreteCrypto c execute) root initial
  obtain ⟨sealed, hcovered⟩ := hkernel.sealNext_optional_callback_covered (recordCrypto c) execute
    beaconOrigin ⟨⟨serverOrigin, 0⟩, ⟨beaconOrigin, 0, []⟩⟩ server
    (fun material sequence _ => (⟨sequence.val - 1, (concreteCrypto c execute).enc material
      ⟨absBytes candidate.associated_data, 1, candidate.server_identity_key_id.val⟩
      (Pqxdh.LE64 candidate.key_id.val ++ application)⟩ : Ratchet.Msg Pqxdh.Bytes)) reply hcorrect
  have hcovered' : sealNext execute server () reply =
      sealNext execute server () (candidateSealReply c execute candidate application sealed) := hcovered
  exact ⟨sealed, by simp only [finishCandidate, initializeCandidate_eq, hinit, bind_tc_ok, hcovered']⟩

/-- The complete preparation/publication driver with actual external optional callbacks, selected from the actual prepared candidate. -/
noncomputable def prepareAndFinishWith
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (root : Std.Array Std.U8 32#usize)
    (reply : pqxdh.ServerRegistrationCandidate → ratchet.RatchetMaterial → Std.U64 → Unit →
      core.option.Option (Ratchet.Msg Pqxdh.Bytes)) : RustM PreparedPublicationResult := do
  let prepared ← pqxdh.server_prepare_commit state pending binding availability
  match prepared with
  | .Err error => ok (.rejected error)
  | .Ok candidate =>
      let result ← finishCandidate candidate root initial execute (reply candidate)
      ok (.finished result)

/-- Actual optional callbacks are covered for every preparation outcome; only the actual seal outcome is selected, and no invocation field is changed. -/
theorem prepareAndFinishWith_covered (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (root : Std.Array Std.U8 32#usize) (application : Pqxdh.Bytes)
    (reply : pqxdh.ServerRegistrationCandidate → ratchet.RatchetMaterial → Std.U64 → Unit →
      core.option.Option (Ratchet.Msg Pqxdh.Bytes))
    (hcorrect : ∀ candidate, CandidateSealCorrect c execute candidate application (reply candidate)) :
    ∃ sealed, prepareAndFinishWith initial execute state pending binding availability root reply =
      prepareAndFinish c initial execute state pending binding availability root application sealed := by
  obtain ⟨prepared, hprepare⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok state pending binding availability
  cases prepared with
  | Err error => exact ⟨false, by simp [prepareAndFinishWith, prepareAndFinish, hprepare]⟩
  | Ok candidate =>
      obtain ⟨sealed, hcovered⟩ := finishCandidate_callback_covered c initial execute candidate root
        application (reply candidate) (hcorrect candidate)
      exact ⟨sealed, by simp only [prepareAndFinishWith, prepareAndFinish, hprepare, bind_tc_ok, hcovered]⟩

/-- The plaintext prefix used by the first-seal driver is exactly the extracted candidate binding accessor's bytes. -/
theorem candidate_binding_prefix_exact (candidate : pqxdh.ServerRegistrationCandidate)
    (application : Pqxdh.Bytes) :
    ∃ binding, candidate.key_id_binding = ok binding ∧
      absBytes binding.bytes ++ application = Pqxdh.LE64 candidate.key_id.val ++ application := by
  obtain ⟨binding, hbinding, hbytes⟩ := registration_key_id_binding_abs candidate.key_id
  exact ⟨binding, hbinding, congrArg (· ++ application) hbytes⟩

/-- The actual callback driver retains changed-binding rejection before initialization and sealing. -/
theorem prepareAndFinishWith_binding_changed
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability)
    (root : Std.Array Std.U8 32#usize)
    (reply : pqxdh.ServerRegistrationCandidate → ratchet.RatchetMaterial → Std.U64 → Unit →
      core.option.Option (Ratchet.Msg Pqxdh.Bytes))
    (hmismatch : pending.server_binding.identity_key_id ≠ binding.identity_key_id ∨
      pending.server_binding.identity_public_key ≠ binding.identity_public_key) :
    prepareAndFinishWith initial execute state pending binding availability root reply =
      ok (.rejected .IdentityMismatch) := by
  simp only [prepareAndFinishWith, prepare_binding_changed state pending binding availability hmismatch, bind_tc_ok]

/-- Every actual boundary-compliant preparation/publication execution after successful extracted acceptance has an optional-publication witness. The root is computed from that same pending transcript under the root KDF law; no protocol-root equality is assumed. The entry peer/replay context is the externally supplied already-consumed prefix. -/
theorem accepted_prepareAndFinishWith_refines (c : Pqxdh.Crypto)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize) (hrootLaw : RootKdfLaw c derive)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (originalState state : pqxdh.ServerState)
    (registration : pqxdh.VerifiedInitKex) (status : pqxdh.RegistrationStatus)
    (acceptedBinding : pqxdh.ServerBinding) (coins : pqxdh.ServerCoins)
    (secrets : pqxdh.PqxdhSharedSecrets) (pending : pqxdh.PendingServerRegistration)
    (haccept : pqxdh.server_accept originalState registration status acceptedBinding coins secrets =
      ok (.Ok (state, pending)))
    (entry : Pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability)
    (identity kemCipher ephemeral application : Pqxdh.Bytes)
    (reply : pqxdh.ServerRegistrationCandidate → ratchet.RatchetMaterial → Std.U64 → Unit →
      core.option.Option (Ratchet.Msg Pqxdh.Bytes))
    (hcorrect : ∀ candidate, CandidateSealCorrect c execute candidate application (reply candidate))
    (hcounter : state.last_key_id.val = entry.n) (hbinding : pending.server_binding = binding)
    (hserverIdentity : absBytes binding.identity_public_key = c.edPub entry.ikSk)
    (hserverId : binding.identity_key_id.val = entry.sid)
    (hidentity : absBytes pending.beacon_identity_public_key = identity)
    (hkem : absBytes pending.kem_ciphertext = kemCipher)
    (hephem : absBytes pending.ephemeral_public_key = ephemeral)
    (havail : availability = .Occupied ↔ (entry.peers.lookup (entry.n + 1)).isSome) :
    ∃ sealed result, prepareAndFinishWith initial execute state pending binding availability
        (derive pending.root_key_input) reply = ok result ∧
      PreparedPublicationRefines c execute entry
        (Pqxdh.rootSecret c (Pqxdh.ikmOf (absDHs secrets) (absBytes secrets.kem_shared_secret)))
        identity kemCipher ephemeral result
        (idealPublication c entry identity
          (Pqxdh.rootSecret c (Pqxdh.ikmOf (absDHs secrets) (absBytes secrets.kem_shared_secret)))
          kemCipher ephemeral application sealed) := by
  have hroot := accepted_root_refines c derive hrootLaw originalState state registration status
    acceptedBinding coins secrets pending haccept
  obtain ⟨sealed, hcovered⟩ := prepareAndFinishWith_covered c initial execute state pending binding
    availability (derive pending.root_key_input) application reply hcorrect
  obtain ⟨result, hrun, hresult⟩ := prepareAndFinish_refines c initial execute hinitial hstep entry
    state pending binding availability (derive pending.root_key_input) identity kemCipher ephemeral
    application sealed hcounter hbinding hserverIdentity hserverId hidentity hkem hephem havail
  exact ⟨sealed, result, hcovered.trans hrun, by simpa only [hroot] using hresult⟩

/-- The accepted-transcript theorem applies to any actual completed evaluation, by injectivity of the extracted computation's result. -/
theorem accepted_prepareAndFinishWith_observed (c : Pqxdh.Crypto)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize) (hrootLaw : RootKdfLaw c derive)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (originalState state : pqxdh.ServerState)
    (registration : pqxdh.VerifiedInitKex) (status : pqxdh.RegistrationStatus)
    (acceptedBinding : pqxdh.ServerBinding) (coins : pqxdh.ServerCoins)
    (secrets : pqxdh.PqxdhSharedSecrets) (pending : pqxdh.PendingServerRegistration)
    (haccept : pqxdh.server_accept originalState registration status acceptedBinding coins secrets =
      ok (.Ok (state, pending)))
    (entry : Pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (availability : pqxdh.KeyIdAvailability)
    (identity kemCipher ephemeral application : Pqxdh.Bytes)
    (reply : pqxdh.ServerRegistrationCandidate → ratchet.RatchetMaterial → Std.U64 → Unit →
      core.option.Option (Ratchet.Msg Pqxdh.Bytes))
    (hcorrect : ∀ candidate, CandidateSealCorrect c execute candidate application (reply candidate))
    (hcounter : state.last_key_id.val = entry.n) (hbinding : pending.server_binding = binding)
    (hserverIdentity : absBytes binding.identity_public_key = c.edPub entry.ikSk)
    (hserverId : binding.identity_key_id.val = entry.sid)
    (hidentity : absBytes pending.beacon_identity_public_key = identity)
    (hkem : absBytes pending.kem_ciphertext = kemCipher)
    (hephem : absBytes pending.ephemeral_public_key = ephemeral)
    (havail : availability = .Occupied ↔ (entry.peers.lookup (entry.n + 1)).isSome)
    (result : PreparedPublicationResult)
    (hactual : prepareAndFinishWith initial execute state pending binding availability
      (derive pending.root_key_input) reply = ok result) :
    ∃ sealed, PreparedPublicationRefines c execute entry
        (Pqxdh.rootSecret c (Pqxdh.ikmOf (absDHs secrets) (absBytes secrets.kem_shared_secret)))
        identity kemCipher ephemeral result
        (idealPublication c entry identity
          (Pqxdh.rootSecret c (Pqxdh.ikmOf (absDHs secrets) (absBytes secrets.kem_shared_secret)))
          kemCipher ephemeral application sealed) := by
  obtain ⟨sealed, covered, hrun, hrelated⟩ := accepted_prepareAndFinishWith_refines c derive hrootLaw
    initial execute hinitial hstep originalState state registration status acceptedBinding coins secrets
    pending haccept entry binding availability identity kemCipher ephemeral application reply hcorrect
    hcounter hbinding hserverIdentity hserverId hidentity hkem hephem havail
  have heq : covered = result := RustM.ok.inj (hrun.symm.trans hactual)
  exact ⟨sealed, heq ▸ hrelated⟩

/--
info: 'BeaconcryptCore.Refinement.ServerPublicationRefinement.accepted_prepareAndFinishWith_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms accepted_prepareAndFinishWith_refines

/--
info: 'BeaconcryptCore.Refinement.ServerPublicationRefinement.accepted_prepareAndFinishWith_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms accepted_prepareAndFinishWith_observed

end BeaconcryptCore.Refinement.ServerPublicationRefinement

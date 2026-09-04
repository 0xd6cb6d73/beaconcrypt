import BeaconcryptCore.Refinement.PqxdhConcreteSession
import BeaconcryptCore.Refinement.PqxdhProtocol
import BeaconcryptCore.Model.Pqxdh.Acceptance
import BeaconcryptCore.Refinement.RatchetReceiveIdeal
import BeaconcryptCore.Refinement.RatchetRoleReachability
import BeaconcryptCore.Refinement.RepresentationBridge

/-! Composition of extracted registration preparation, role initialization, and first-record processing. The drivers in this module sequence the public extracted phases; they do not assert that the surrounding Rust adapter implements this sequencing. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet.concrete
open PqxdhRefinement
open BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Refinement.RepresentationBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.ProtocolComposition

/-- The initial primitive returns the 64-byte HKDF result for the exact root and label requested by the extracted core. -/
def InitialKdfLaw (c : Pqxdh.Crypto) (execute : InitialKdfInterpreter) : Prop :=
  ∀ root, absBytes (execute { input := root, info := ratchet.SYM_RATCHET_INFO }).bytes =
    c.hkdf (absBytes root) Pqxdh.INFO_R 64

/-- Root derivation interprets the exact validated transcript assembled by the extracted PQXDH core. -/
def RootKdfLaw (c : Pqxdh.Crypto)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize) : Prop :=
  ∀ input, absBytes (derive input) = Pqxdh.rootSecret c (absBytes input.bytes)

/-- Initialization returns the concrete kernel, its exact byte origins, and the full concrete ratchet state relation. -/
theorem initializeBeacon_refines {AD PT CT : Type}
    (c : Pqxdh.Crypto)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter)
    (hlaw : InitialKdfLaw c execute) :
    ∃ kernel,
      initializeBeacon root execute = ok kernel ∧
      ChainBytesRefines kernel.refined.send_chain (Pqxdh.rootChains c (absBytes root)).2 ∧
      ChainBytesRefines kernel.refined.receive_chain (Pqxdh.rootChains c (absBytes root)).1 ∧
      KernelRefines cr kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  obtain ⟨pending, kernel, hstart, hresume, _, _, hsend, hreceive, hkernel⟩ :=
    beaconStartResume_refines c cr root (absBytes root)
      (execute { input := root, info := ratchet.SYM_RATCHET_INFO }) rfl
      (by simpa only [InitialResponseRefines, beaconPending, absBytes_ratchetSymmetricInfo] using hlaw root)
  have hpending : pending = beaconPending root :=
    RustM.ok.inj (hstart.symm.trans (pqxdh.concrete.start_beacon_ratchet_kdf_exact root))
  exact ⟨kernel, by simpa only [initializeBeacon_eq, hpending] using hresume, hsend, hreceive, hkernel⟩

/-- Initialization returns the concrete kernel, its exact byte origins, and the full concrete ratchet state relation. -/
theorem initializeServer_refines {AD PT CT : Type}
    (c : Pqxdh.Crypto)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (root : Std.Array Std.U8 32#usize) (execute : InitialKdfInterpreter)
    (hlaw : InitialKdfLaw c execute) :
    ∃ kernel,
      initializeServer root execute = ok kernel ∧
      ChainBytesRefines kernel.refined.send_chain (Pqxdh.rootChains c (absBytes root)).1 ∧
      ChainBytesRefines kernel.refined.receive_chain (Pqxdh.rootChains c (absBytes root)).2 ∧
      KernelRefines cr kernel.refined.receive_chain
        ⟨kernel.refined.send_chain, 0⟩ ⟨kernel.refined.receive_chain, 0, []⟩ kernel := by
  obtain ⟨pending, kernel, hstart, hresume, _, _, hsend, hreceive, hkernel⟩ :=
    serverStartResume_refines c cr root (absBytes root)
      (execute { input := root, info := ratchet.SYM_RATCHET_INFO }) rfl
      (by simpa only [InitialResponseRefines, serverPending, absBytes_ratchetSymmetricInfo] using hlaw root)
  have hpending : pending = serverPending root :=
    RustM.ok.inj (hstart.symm.trans (pqxdh.concrete.start_server_ratchet_kdf_exact root))
  exact ⟨kernel, by simpa only [initializeServer_eq, hpending] using hresume, hsend, hreceive, hkernel⟩

/-- Successful preparation constructs the exact transcript, association bytes, binding, and identifier consumed by later initialization and authentication. -/
theorem prepareBeacon_refines (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (hidentity : absBytes state.expected_server_binding.identity_public_key =
      absBytes inputs.response_server_identity)
    (hnonzero : Pqxdh.dhNonZero (absDHs inputs.shared_secrets)) :
    ∃ candidate,
      pqxdh.beacon_prepare_finish state inputs = ok (core.result.Result.Ok candidate) ∧
      candidate.server_binding = state.expected_server_binding ∧
      candidate.assigned_key_id = inputs.assigned_key_id ∧
      absBytes candidate.associated_data = Pqxdh.assocData
        (absBytes state.expected_server_binding.identity_public_key) (absBytes state.beacon_identity_public_key) ∧
      absBytes candidate.root_key_input.bytes = Pqxdh.ikmOf (absDHs inputs.shared_secrets)
        (absBytes inputs.shared_secrets.kem_shared_secret) := by
  obtain ⟨root, hroot, hrootBytes⟩ := (build_root_key_input_abs inputs.shared_secrets).1 hnonzero
  obtain ⟨ad, had, hadBytes⟩ := build_associated_data_abs
    state.expected_server_binding.identity_public_key state.beacon_identity_public_key
  exact ⟨⟨state.expected_server_binding, inputs.assigned_key_id, root, ad⟩,
    by simp [pqxdh.beacon_prepare_finish, array_eq_abs, hidentity, hroot, had],
    rfl, rfl, hadBytes, hrootBytes⟩

/-- Exact conversion back to an extracted byte, used only by the driver to pass authenticated plaintext bytes to the extracted binding check. -/
def concreteByte (byte : UInt8) : Std.U8 := ⟨byte.toBitVec⟩

@[simp] theorem absByte_concreteByte (byte : UInt8) : absByte (concreteByte byte) = byte := by
  exact UInt8.ofNat_toNat

/-- The binding parser retains the first eight authenticated plaintext bytes. -/
def plaintextBinding (plaintext : Pqxdh.Bytes) (hlength : 8 < plaintext.length) : Std.Array Std.U8 8#usize :=
  ⟨(plaintext.take 8).map concreteByte, by simp only [List.length_map, List.length_take, usize_val_8]; omega⟩

theorem plaintextBinding_bytes (plaintext : Pqxdh.Bytes) (hlength : 8 < plaintext.length) :
    absBytes (plaintextBinding plaintext hlength) = plaintext.take 8 := by
  simp [absBytes, plaintextBinding, List.map_map, Function.comp_def]

/-- Continue only from authenticated plaintext, invoking the extracted key-identifier binding check and extracted commit. -/
def commitPlaintext (candidate : pqxdh.BeaconRegistrationCandidate) (sender : Std.U64)
    (plaintext : Pqxdh.Bytes) : RustM (Except Pqxdh.BeaconError pqxdh.BeaconEstablished) :=
  if hlength : 8 < plaintext.length then do
    let checked ← pqxdh.authenticate_registration_key_id_binding candidate sender
      (plaintextBinding plaintext hlength)
    match checked with
    | .Err .IdentityMismatch => ok (.error .badSender)
    | .Err _ => ok (.error .keyIdMismatch)
    | .Ok authenticated =>
        let established ← pqxdh.beacon_commit authenticated
        ok (.ok established)
  else ok (.error .badPlaintext)

/-- The extracted authentication and commit give exactly the ideal plaintext checks when the first-record sender guard has succeeded. -/
theorem commitPlaintext_eq (candidate : pqxdh.BeaconRegistrationCandidate) (sender : Std.U64)
    (plaintext : Pqxdh.Bytes) (hsender : sender = candidate.server_binding.identity_key_id) :
    commitPlaintext candidate sender plaintext = ok
      (if plaintext.length ≤ 8 then .error .badPlaintext
       else if plaintext.take 8 ≠ Pqxdh.LE64 candidate.assigned_key_id.val then .error .keyIdMismatch
       else .ok ⟨candidate.server_binding, candidate.assigned_key_id⟩) := by
  by_cases hlength : 8 < plaintext.length
  · obtain ⟨binding, hbinding, hbytes⟩ := registration_key_id_binding_abs candidate.assigned_key_id
    by_cases hbound : plaintext.take 8 = Pqxdh.LE64 candidate.assigned_key_id.val <;>
      simp [commitPlaintext, hlength, Nat.not_le.mpr hlength, hbound,
      pqxdh.authenticate_registration_key_id_binding, hsender,
      pqxdh.BeaconRegistrationCandidate.key_id_binding, hbinding, array_eq_abs,
      plaintextBinding_bytes, hbytes, pqxdh.beacon_commit]
  · simp [commitPlaintext, hlength, Nat.le_of_not_gt hlength]

/-- The complete core registration driver: extracted candidate preparation, model-ordered sender/sequence guards, extracted initial KDF phases, actual receive phases, extracted binding authentication, and extracted commitment. Every failure discards registration-local key state. -/
def completeBeacon
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial Pqxdh.RecordAD Pqxdh.Bytes Pqxdh.Bytes)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (sender target : Std.U64) (ciphertext : Pqxdh.Bytes) :
    RustM (Except Pqxdh.BeaconError (pqxdh.BeaconEstablished × ConcreteRatchetKernel)) := do
  let prepared ← pqxdh.beacon_prepare_finish state inputs
  match prepared with
  | .Err .IdentityMismatch => ok (.error .identityMismatch)
  | .Err _ => ok (.error .zeroDH)
  | .Ok candidate =>
      if sender ≠ candidate.server_binding.identity_key_id then ok (.error .badSender)
      else if target.val = 0 then ok (.error .badRecord)
      else
        let initialized ← initializeBeaconCandidate candidate (derive candidate.root_key_input) initial
        let (next, plaintext) ← receiveNext execute initialized target ()
          (receiveIdealOpenReply cr ⟨absBytes candidate.associated_data, target.val, sender.val⟩ ciphertext)
        match plaintext with
        | .None => ok (.error .badRecord)
        | .Some plaintext =>
            let committed ← commitPlaintext candidate sender plaintext
            match committed with
            | .error error => ok (.error error)
            | .ok established => ok (.ok (established, next))

/-- The typed core inputs are the primitive outputs and wire fields of the chosen ideal registration input. Decapsulation and public-key conversion execute outside the core; their failures are adapter outcomes rather than inhabitants of this boundary. -/
structure BeaconBoundary (c : Pqxdh.Crypto) (state : pqxdh.BeaconInitSent)
    (inputs : pqxdh.BeaconFinishInputs) (sender target : Std.U64) (response : Pqxdh.KexResponse)
    (ikSk preSk otSk kemSk ikSX : Pqxdh.Bytes) : Prop where
  decapsulation : c.decap kemSk response.kemCipherText = some (absBytes inputs.shared_secrets.kem_shared_secret)
  conversion : c.xpkConv response.identityKey = some ikSX
  beaconIdentity : absBytes state.beacon_identity_public_key = c.edPub ikSk
  responseIdentity : absBytes inputs.response_server_identity = response.identityKey
  sharedDH : absDHs inputs.shared_secrets = Pqxdh.beaconDHs c ikSk preSk otSk ikSX response.ephemeralKey
  assignedId : inputs.assigned_key_id.val = response.keyId
  senderId : sender.val = response.appFrame.keyId
  sequence : target.val = response.appFrame.seq

/-- Actual initialization followed by actual first-record reception, with exact byte-model output and full represented poststate. Authentication and admission failure require no successful-receive premise. -/
theorem initialize_receive_refines (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (root : Std.Array Std.U8 32#usize) (target : Std.U64) (hpositive : 0 < target.val)
    (ad : Pqxdh.RecordAD) (ciphertext : Pqxdh.Bytes) :
    ∃ initialized next send receive,
      initializeBeacon root initial = ok initialized ∧
      receiveNext execute initialized target () (receiveIdealOpenReply (concreteCrypto c execute) ad ciphertext) =
        ok (next, receiveIdealPlaintext (Ratchet.recvStep (Pqxdh.ratchetCrypto c)
          ⟨(Pqxdh.rootChains c (absBytes root)).1, 0, []⟩ ad ⟨target.val - 1, ciphertext⟩).1) ∧
      KernelRefines (concreteCrypto c execute) initialized.refined.receive_chain send receive next ∧
      mapSend send = ⟨(Pqxdh.rootChains c (absBytes root)).2, 0⟩ ∧
      mapRecv receive = (Ratchet.recvStep (Pqxdh.ratchetCrypto c)
          ⟨(Pqxdh.rootChains c (absBytes root)).1, 0, []⟩ ad ⟨target.val - 1, ciphertext⟩).2 := by
  obtain ⟨initialized, hinit, hsend, hreceive, hkernel⟩ :=
    initializeBeacon_refines c (concreteCrypto c execute) root initial hinitial
  obtain ⟨next, hrun, hpost, _⟩ := hkernel.receive_ideal (recordCrypto c) execute
    initialized.refined.receive_chain ⟨initialized.refined.send_chain, 0⟩
    ⟨initialized.refined.receive_chain, 0, []⟩ initialized () target hpositive ad ciphertext
  have hcommute := recvStep_commutes c execute hstep
    ⟨initialized.refined.receive_chain, 0, []⟩ ad ⟨target.val - 1, ciphertext⟩
  simp only [mapRecv, List.map_nil, show absChain initialized.refined.receive_chain =
    (Pqxdh.rootChains c (absBytes root)).1 from hreceive] at hcommute
  exact ⟨initialized, next, _, _, hinit,
    by simpa only [concreteCrypto, ← congrArg Prod.fst hcommute] using hrun, hpost,
    by simpa only [mapSend, Ratchet.SendState.mk.injEq, and_true] using
      (show absChain initialized.refined.send_chain = (Pqxdh.rootChains c (absBytes root)).2 from hsend),
    congrArg Prod.snd hcommute⟩

/-- Registration preserves the precise failure code, or the assigned identity and the complete established ratchet state. -/
def BeaconResultRefines (c : Pqxdh.Crypto) (execute : KdfInterpreter) (ikSk : Pqxdh.Bytes)
    (result : Except Pqxdh.BeaconError (pqxdh.BeaconEstablished × ConcreteRatchetKernel))
    (ideal : Except Pqxdh.BeaconError Nat × Pqxdh.BeaconState) : Prop :=
  match result with
  | .error error => ideal = (.error error, .aborted)
  | .ok (established, kernel) =>
      ∃ origin send receive,
        KernelRefines (concreteCrypto c execute) origin send receive kernel ∧
        ideal = (.ok established.assigned_key_id.val,
          .established (absBinding established.server_binding) ikSk established.assigned_key_id.val
            (Pqxdh.assocData (absBytes established.server_binding.identity_public_key) (c.edPub ikSk))
            (mapSend send) (mapRecv receive))


/-- The suffix of the unchanged ideal transition after its sender and sequence guards. This is a named expression, not an added model transition. -/
def idealFinishRecord (binding : Pqxdh.ServerBinding) (ikSk : Pqxdh.Bytes) (kid : Nat)
    (ad : Pqxdh.Bytes) (send : Ratchet.SendState Pqxdh.Bytes)
    (opened : Except Ratchet.RecvError Pqxdh.Bytes × Ratchet.RecvState Pqxdh.Bytes (Pqxdh.Bytes × Pqxdh.Bytes)) :
    Except Pqxdh.BeaconError Nat × Pqxdh.BeaconState :=
  match opened with
  | (.error _, _) => (.error .badRecord, .aborted)
  | (.ok plaintext, receive) =>
      if plaintext.length ≤ 8 then (.error .badPlaintext, .aborted)
      else if plaintext.take 8 ≠ Pqxdh.LE64 kid then (.error .keyIdMismatch, .aborted)
      else (.ok kid, .established binding ikSk kid ad send receive)

/-- Every included beacon registration outcome matches the existing atomic ideal transition. Primitive assumptions are local request/response laws; no registration or successful receive equation is assumed. -/
theorem completeBeacon_refines (c : Pqxdh.Crypto)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hrootLaw : RootKdfLaw c derive) (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (sender target : Std.U64) (response : Pqxdh.KexResponse)
    (ikSk preSk otSk kemSk ikSX : Pqxdh.Bytes)
    (hboundary : BeaconBoundary c state inputs sender target response ikSk preSk otSk kemSk ikSX) :
    ∃ result,
      completeBeacon (concreteCrypto c execute) derive initial execute state inputs sender target
        response.appFrame.cipherText = ok result ∧
      BeaconResultRefines c execute ikSk result
        (Pqxdh.beaconFinish c (.initSent (absBinding state.expected_server_binding) ikSk preSk otSk kemSk) response) := by
  by_cases hidentity : absBytes state.expected_server_binding.identity_public_key =
      absBytes inputs.response_server_identity
  · have hid : response.identityKey = absBytes state.expected_server_binding.identity_public_key :=
      hboundary.responseIdentity.symm.trans hidentity.symm
    by_cases hnonzero : Pqxdh.dhNonZero (absDHs inputs.shared_secrets)
    · obtain ⟨candidate, hprepare, hbinding, hkid, had, htranscript⟩ :=
        prepareBeacon_refines state inputs hidentity hnonzero
      by_cases hsender : sender = candidate.server_binding.identity_key_id
      · have hsenderModel : response.appFrame.keyId = state.expected_server_binding.identity_key_id.val := by
          rw [← hboundary.senderId, hsender, hbinding]
        by_cases hzero : target.val = 0
        · exact ⟨.error .badRecord,
            by simp only [completeBeacon, hprepare, bind_tc_ok, hsender, ne_self_iff_false, if_false, if_pos hzero],
            by simp [BeaconResultRefines, Pqxdh.beaconFinish, hboundary.decapsulation, absBinding,
              ← hid, hboundary.conversion, ← hboundary.sharedDH, hnonzero, hsenderModel,
              ← hboundary.sequence, hzero]⟩
        · have hroot : absBytes (derive candidate.root_key_input) = Pqxdh.beaconRoot c ikSk preSk otSk ikSX
              response.ephemeralKey (absBytes inputs.shared_secrets.kem_shared_secret) := by
            rw [hrootLaw, htranscript, hboundary.sharedDH]
            rfl
          obtain ⟨initialized, next, send, receive, hinit, hrecv, hpost, hsend, hreceive⟩ :=
            initialize_receive_refines c initial execute hinitial hstep (derive candidate.root_key_input)
              target (Nat.pos_of_ne_zero hzero)
              ⟨absBytes candidate.associated_data, target.val, sender.val⟩ response.appFrame.cipherText
          have hadModel : absBytes candidate.associated_data =
              Pqxdh.assocData (absBytes state.expected_server_binding.identity_public_key) (c.edPub ikSk) := by
            rw [had, hboundary.beaconIdentity]
          have hmodel : Pqxdh.beaconFinish c
                (.initSent (absBinding state.expected_server_binding) ikSk preSk otSk kemSk) response =
              idealFinishRecord (absBinding state.expected_server_binding) ikSk response.keyId
                (absBytes candidate.associated_data) (mapSend send)
                (Ratchet.recvStep (Pqxdh.ratchetCrypto c)
                  ⟨(Pqxdh.rootChains c (absBytes (derive candidate.root_key_input))).1, 0, []⟩
                  ⟨absBytes candidate.associated_data, target.val, sender.val⟩
                  ⟨target.val - 1, response.appFrame.cipherText⟩) := by
            simp only [Pqxdh.beaconFinish, hboundary.decapsulation, absBinding,
              if_neg (not_ne_iff.mpr hid), hboundary.conversion,
              if_neg (not_not_intro (hboundary.sharedDH ▸ hnonzero)),
              if_neg (not_ne_iff.mpr (hboundary.senderId.trans hsenderModel)), if_false,
              ← hboundary.sequence, hzero, ← hroot, ← hadModel, ← hboundary.senderId, hsend, idealFinishRecord]
            rfl
          cases hopened : Ratchet.recvStep (Pqxdh.ratchetCrypto c)
              ⟨(Pqxdh.rootChains c (absBytes (derive candidate.root_key_input))).1, 0, []⟩
              ⟨absBytes candidate.associated_data, target.val, sender.val⟩
              ⟨target.val - 1, response.appFrame.cipherText⟩ with
          | mk result received =>
            cases result with
            | error error =>
                exact ⟨.error .badRecord,
                  by simp only [completeBeacon, hprepare, bind_tc_ok, if_neg (not_not_intro hsender),
                    if_neg hzero, initializeBeaconCandidate_eq, hinit, hrecv, hopened, receiveIdealPlaintext, core.option.Option.None]
                     rfl,
                  by simp only [BeaconResultRefines, hmodel, hopened, idealFinishRecord]⟩
            | ok plaintext =>
                have hactual : completeBeacon (concreteCrypto c execute) derive initial execute state inputs
                      sender target response.appFrame.cipherText =
                    (do let committed ← commitPlaintext candidate sender plaintext
                        match committed with
                        | .error error => ok (.error error)
                        | .ok established => ok (.ok (established, next))) := by
                  simp only [completeBeacon, hprepare, bind_tc_ok, if_neg (not_not_intro hsender),
                    if_neg hzero, initializeBeaconCandidate_eq, hinit, hrecv, hopened, receiveIdealPlaintext,
                    core.option.Option.Some]
                  rfl
                by_cases hlength : plaintext.length ≤ 8
                · exact ⟨.error .badPlaintext,
                    by simp only [hactual, commitPlaintext_eq candidate sender plaintext hsender, if_pos hlength, bind_tc_ok],
                    by simp only [BeaconResultRefines, hmodel, hopened, idealFinishRecord, if_pos hlength]⟩
                · have hkey : candidate.assigned_key_id.val = response.keyId := by
                    rw [hkid, hboundary.assignedId]
                  by_cases hbound : plaintext.take 8 ≠ Pqxdh.LE64 response.keyId
                  · exact ⟨.error .keyIdMismatch,
                      by simp only [hactual, commitPlaintext_eq candidate sender plaintext hsender, hkey,
                        if_neg hlength, if_pos hbound, bind_tc_ok],
                      by simp only [BeaconResultRefines, hmodel, hopened, idealFinishRecord,
                        if_neg hlength, if_pos hbound]⟩
                  · refine ⟨.ok (⟨candidate.server_binding, candidate.assigned_key_id⟩, next), ?_,
                      initialized.refined.receive_chain, send, receive, hpost, ?_⟩
                    · simp only [hactual, commitPlaintext_eq candidate sender plaintext hsender, hkey,
                        if_neg hlength, if_neg hbound, bind_tc_ok]
                    · rw [hmodel, hopened]
                      simp only [idealFinishRecord, if_neg hlength, if_neg hbound,
                        hbinding, hkey, hadModel, show mapRecv receive = received by simpa only [hopened] using hreceive]

      · have hsenderModel : response.appFrame.keyId ≠ state.expected_server_binding.identity_key_id.val := by
          intro heq
          exact hsender (Std.UScalar.eq_of_val_eq (by simpa only [hbinding, hboundary.senderId] using heq))
        exact ⟨.error .badSender, by simp only [completeBeacon, hprepare, bind_tc_ok, if_pos hsender],
          by simp [BeaconResultRefines, Pqxdh.beaconFinish, hboundary.decapsulation, absBinding,
            ← hid, hboundary.conversion, ← hboundary.sharedDH, hnonzero, hsenderModel]⟩
    · refine ⟨.error .zeroDH, ?_, ?_⟩
      · simp [completeBeacon, pqxdh.beacon_prepare_finish, array_eq_abs, hidentity,
          (build_root_key_input_abs inputs.shared_secrets).2 hnonzero]
      · simp [BeaconResultRefines, Pqxdh.beaconFinish, hboundary.decapsulation, absBinding,
          ← hid, hboundary.conversion, ← hboundary.sharedDH, hnonzero]
  · refine ⟨.error .identityMismatch, ?_, ?_⟩
    · simp [completeBeacon, pqxdh.beacon_prepare_finish, array_eq_abs, hidentity]
    · simp [BeaconResultRefines, Pqxdh.beaconFinish, hboundary.decapsulation, absBinding,
        ← hboundary.responseIdentity, Ne.symm hidentity]


/-- The record boundary returns the full encoded record and preserves the actual extracted wire sequence as the ideal zero-based index. -/
noncomputable def recordSealReply (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (ad : Pqxdh.RecordAD) (plaintext : Pqxdh.Bytes)
    (material : ratchet.RatchetMaterial) (sequence : Std.U64) (_ : Unit) :
    core.option.Option (Ratchet.Msg Pqxdh.Bytes) :=
  .Some ⟨sequence.val - 1, (concreteCrypto c execute).enc material ad plaintext⟩

/-- The actual server initializer and first send produce the exact byte-model record and advanced send state, retaining the complementary empty receive state. -/
theorem initialize_send_refines (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (root : Std.Array Std.U8 32#usize) (ad : Pqxdh.RecordAD) (plaintext : Pqxdh.Bytes) :
    ∃ initialized next send receive,
      initializeServer root initial = ok initialized ∧
      sealNext execute initialized () (recordSealReply c execute ad plaintext) =
        ok (next, .Some (Ratchet.sendStep (Pqxdh.ratchetCrypto c)
          ⟨(Pqxdh.rootChains c (absBytes root)).1, 0⟩ ad plaintext).1) ∧
      KernelRefines (concreteCrypto c execute) initialized.refined.receive_chain send receive next ∧
      mapSend send = (Ratchet.sendStep (Pqxdh.ratchetCrypto c)
          ⟨(Pqxdh.rootChains c (absBytes root)).1, 0⟩ ad plaintext).2 ∧
      mapRecv receive = ⟨(Pqxdh.rootChains c (absBytes root)).2, 0, []⟩ := by
  obtain ⟨initialized, hinit, hsend, hreceive, hkernel⟩ :=
    initializeServer_refines c (concreteCrypto c execute) root initial hinitial
  have hmax : initialized.refined.control.send_sequence ≠ core.num.U64.MAX := by
    intro heq
    have hv := hkernel.sendSequence
    rw [heq, u64_max_val] at hv
    norm_num at hv
  obtain ⟨pending, hbegin, hpending⟩ := begin_send_refines (concreteCrypto c execute)
    initialized.refined.receive_chain ⟨initialized.refined.send_chain, 0⟩
    ⟨initialized.refined.receive_chain, 0, []⟩ initialized () hkernel hmax
  obtain ⟨ready, hresume, hready⟩ := SendKdf.resume_refines (concreteCrypto c execute)
    initialized.refined.receive_chain ⟨initialized.refined.send_chain, 0⟩
    ⟨initialized.refined.receive_chain, 0, []⟩ initialized () pending hpending
    (execute pending.request) (interpreter_request_refines (recordCrypto c) execute
      initialized.refined.send_chain pending.request hpending.requestInput hpending.requestInfo)
  have hcommute := sendStep_commutes c execute hstep ⟨initialized.refined.send_chain, 0⟩ ad plaintext
  simp only [mapSend, show absChain initialized.refined.send_chain =
    (Pqxdh.rootChains c (absBytes root)).1 from hsend] at hcommute
  refine ⟨initialized, ready.advanced, _, _, hinit, ?_, hready.advanced,
    congrArg Prod.snd hcommute, ?_⟩
  · rw [← congrArg Prod.fst hcommute]
    simp only [sealNext, hbegin, bind_tc_ok, hresume, SendSeal.finish_returns_interpreter_result,
      recordSealReply, hready.sequence, hready.material, Ratchet.sendStep]
  · simpa only [mapRecv, List.map_nil, Ratchet.RecvState.mk.injEq, and_true] using
      (show absChain initialized.refined.receive_chain = (Pqxdh.rootChains c (absBytes root)).2 from hreceive)

/-- Specialize actual first sending to the unchanged PQXDH `serverRecord`, including its bound identifier prefix and server wire metadata. -/
theorem initialize_serverRecord_refines (c : Pqxdh.Crypto)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hinitial : InitialKdfLaw c initial) (hstep : KdfLaw c execute)
    (root : Std.Array Std.U8 32#usize) (S : Pqxdh.ServerState) (ikB ds app : Pqxdh.Bytes)
    (hroot : absBytes root = ds) :
    ∃ initialized next send receive,
      initializeServer root initial = ok initialized ∧
      sealNext execute initialized () (recordSealReply c execute
        ⟨Pqxdh.assocData (c.edPub S.ikSk) ikB, 1, S.sid⟩ (Pqxdh.LE64 (S.n + 1) ++ app)) =
        ok (next, .Some (Pqxdh.serverRecord c S ikB ds app).1) ∧
      KernelRefines (concreteCrypto c execute) initialized.refined.receive_chain send receive next ∧
      mapSend send = (Pqxdh.serverRecord c S ikB ds app).2 ∧
      mapRecv receive = ⟨(Pqxdh.rootChains c ds).2, 0, []⟩ := by
  simpa only [Pqxdh.serverRecord, hroot] using initialize_send_refines c initial execute hinitial hstep root
    ⟨Pqxdh.assocData (c.edPub S.ikSk) ikB, 1, S.sid⟩ (Pqxdh.LE64 (S.n + 1) ++ app)

/-- An actually accepted core registration inherits the existing PQXDH model's authenticated-record admission property. The incoming frame is arbitrary, so the statement covers relabelled and foreign records rather than assuming honest delivery. -/
theorem completeBeacon_success_admits_record (h : Pqxdh.HonestRun) (hok : h.Ok)
    (derive : pqxdh.RootKeyInput → Std.Array Std.U8 32#usize)
    (initial : InitialKdfInterpreter) (execute : KdfInterpreter)
    (hrootLaw : RootKdfLaw h.c derive) (hinitial : InitialKdfLaw h.c initial) (hstep : KdfLaw h.c execute)
    (state : pqxdh.BeaconInitSent) (inputs : pqxdh.BeaconFinishInputs)
    (sender target : Std.U64) (frame : Pqxdh.CryptoFrame)
    (hpin : absBinding state.expected_server_binding = h.binding)
    (hboundary : BeaconBoundary h.c state inputs sender target { h.response with appFrame := frame }
      h.ikSkB h.preSkB h.otSkB h.kemSkB (h.c.xpub (h.c.xsk h.ikSkS)))
    (established : pqxdh.BeaconEstablished) (kernel : ConcreteRatchetKernel)
    (hactual : completeBeacon (concreteCrypto h.c execute) derive initial execute state inputs sender target
      frame.cipherText = ok (.ok (established, kernel))) :
    frame.keyId = h.sid ∧ frame.seq ≠ 0 ∧
      ∃ plaintext, Pqxdh.openRecord h.c
        (Ratchet.msgKeyAt (Pqxdh.ratchetCrypto h.c) h.chains.1 (frame.seq - 1))
        ⟨h.ad, frame.seq, frame.keyId⟩ frame.cipherText = some plaintext := by
  obtain ⟨result, hrun, hrelated⟩ := completeBeacon_refines h.c derive initial execute hrootLaw hinitial hstep
    state inputs sender target { h.response with appFrame := frame }
    h.ikSkB h.preSkB h.otSkB h.kemSkB (h.c.xpub (h.c.xsk h.ikSkS)) hboundary
  have hresult : result = .ok (established, kernel) := RustM.ok.inj (hrun.symm.trans hactual)
  subst result
  obtain ⟨origin, send, receive, _, hideal⟩ := hrelated
  apply h.beaconRecordAdmitted_elim hok frame
  simp only [Pqxdh.HonestRun.beaconInitSent, ← hpin, hideal, Pqxdh.BeaconRecordAdmitted]

end BeaconcryptCore.Refinement.ProtocolComposition

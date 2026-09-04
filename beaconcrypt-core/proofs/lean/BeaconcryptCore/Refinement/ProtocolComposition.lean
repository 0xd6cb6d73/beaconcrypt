import BeaconcryptCore.Refinement.PqxdhConcreteSession
import BeaconcryptCore.Refinement.PqxdhProtocol
import BeaconcryptCore.Refinement.RatchetReceiveIdeal
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

end BeaconcryptCore.Refinement.ProtocolComposition

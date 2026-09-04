import BeaconcryptCore.Refinement.RatchetByteSurface
import BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

/-! Representation change between the extracted ratchet types and the existing byte-based PQXDH ratchet. The only primitive premise is the fixed-label, 76-byte HKDF response law; ciphertexts, plaintexts, associated data, sequence indices, and receive errors are unchanged. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open ratchet.concrete PqxdhRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BeaconcryptCore.Refinement.RepresentationBridge

/-- Preserve all 32 chain bytes. -/
def absChain (chain : ratchet.RatchetChain) : Pqxdh.Bytes := absBytes chain.bytes

/-- Preserve the full AEAD key and nonce. -/
def absMaterial (material : ratchet.RatchetMaterial) : Pqxdh.Bytes × Pqxdh.Bytes :=
  (absBytes material.key.bytes, absBytes material.nonce.bytes)

/-- No chain information is erased by the byte representation. -/
theorem absChain_injective : Function.Injective absChain := by
  intro left right h
  exact Computational.PqxdhInitialRatchetComplementarity.chain_eq_of_refines h rfl

/-- No key or nonce information is erased by the byte representation. -/
theorem absMaterial_injective : Function.Injective absMaterial := by
  intro left right h
  have hkey : left.key.bytes = right.key.bytes :=
    Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Prod.fst h))
  have hnonce : left.nonce.bytes = right.nonce.bytes :=
    Subtype.ext ((absBytes_inj_iff _ _).mp (congrArg Prod.snd h))
  cases left with
  | mk leftKey leftNonce =>
    cases right with
    | mk rightKey rightNonce =>
      cases leftKey; cases rightKey; cases leftNonce; cases rightNonce
      cases hkey; cases hnonce; rfl

/-- The record interpretation uses exactly the PQXDH model's record encoding and authentication, on the represented key and nonce. -/
def recordCrypto (c : Pqxdh.Crypto) :
    Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial Pqxdh.RecordAD Pqxdh.Bytes Pqxdh.Bytes where
  kdfChain := id
  kdfMsg := fun chain => ⟨⟨chain.bytes⟩, ⟨Std.Array.make 12#usize (List.replicate 12 0#u8)⟩⟩
  enc material := (Pqxdh.ratchetCrypto c).enc (absMaterial material)
  dec material := (Pqxdh.ratchetCrypto c).dec (absMaterial material)
  dec_enc material := (Pqxdh.ratchetCrypto c).dec_enc (absMaterial material)

/-- The concrete KDF is decoded by the extracted splitter; the record boundary retains the byte model's full operations. -/
noncomputable def concreteCrypto (c : Pqxdh.Crypto) (execute : KdfInterpreter) :=
  withInterpreter (recordCrypto c) execute

/-- A boundary law for precisely the 76-byte HKDF requests issued by the extracted ongoing ratchet. No transition or refinement conclusion is assumed. -/
def KdfLaw (c : Pqxdh.Crypto) (execute : KdfInterpreter) : Prop :=
  ∀ chain : ratchet.RatchetChain,
    absBytes (execute { input := chain.bytes, info := ratchet.SYM_RATCHET_INFO }).bytes =
      c.hkdf (absChain chain) Pqxdh.INFO_R 76

/-- Preserve the sender's current chain and logical message index. -/
def mapSend (send : Ratchet.SendState ratchet.RatchetChain) : Ratchet.SendState Pqxdh.Bytes :=
  ⟨absChain send.ck, send.n⟩

/-- Preserve the receiver's current chain, logical index, and every skipped key and nonce. -/
def mapRecv (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial) :
    Ratchet.RecvState Pqxdh.Bytes (Pqxdh.Bytes × Pqxdh.Bytes) :=
  ⟨absChain receive.ck, receive.n, receive.skipped.map (fun p => (p.1, absMaterial p.2))⟩

private theorem absBytes_slice {n m : Std.Usize} (source : Std.Array Std.U8 m)
    (slice : Std.Array Std.U8 n) (offset : Nat) (hbound : offset + n.val ≤ m.val)
    (hbytes : slice.val = (List.range n.val).map (fun i => source.val[i + offset]!)) :
    absBytes slice = ((absBytes source).drop offset).take n.val := by
  apply List.ext_getElem
  · simp only [absBytes_length, List.length_take, List.length_drop]
    omega
  · intro i h₁ h₂
    simp only [absBytes, hbytes, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    simp only [Nat.add_comm i offset, getElem!_pos source.val (offset + i) (by have hi := h₁; rw [absBytes_length] at hi; have hs := source.property; omega)]

/-- The extracted response parser selects the same full chain, key, and nonce byte regions as the byte model. -/
theorem interpretedStep_bytes (execute : KdfInterpreter) (chain : ratchet.RatchetChain) :
    absChain (interpretedStep execute chain).chain =
      ((absBytes (interpretedResponse execute chain).bytes).drop 32).take 32 ∧
    absMaterial (interpretedStep execute chain).material =
      ((absBytes (interpretedResponse execute chain).bytes).take 32,
       (absBytes (interpretedResponse execute chain).bytes).drop 64) := by
  obtain ⟨split, hsplit, hkey, hchain, hnonce⟩ :=
    PanicFreedom.split_ratchet_kdf_output_exact (interpretedResponse execute chain).bytes
  have hdecode : ratchet_step_from_response (interpretedResponse execute chain) =
      ok { chain := split.next_chain, material := { key := split.key, nonce := split.nonce } } := by
    simp [ratchet_step_from_response, ratchet.RatchetKdfResponse.as_bytes, hsplit]
  rw [RustM.ok.inj ((interpretedStep_spec execute chain).symm.trans hdecode)]
  refine ⟨absBytes_slice _ _ 32 (by decide) hchain, Prod.ext ?_ ?_⟩
  · simpa only [absMaterial, Nat.add_zero, usize_val_32, List.drop_zero] using
      absBytes_slice (interpretedResponse execute chain).bytes split.key.bytes 0 (by decide) (by simpa using hkey)
  · simpa only [absMaterial, List.take_of_length_le (by simp :
        ((absBytes (interpretedResponse execute chain).bytes).drop 64).length ≤ (12#usize).val)] using
      absBytes_slice (interpretedResponse execute chain).bytes split.nonce.bytes 64 (by decide) hnonce

/-- Ongoing chain derivation commutes with the exact byte representation. -/
theorem kdfChain_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (chain : ratchet.RatchetChain) :
    absChain ((concreteCrypto c execute).kdfChain chain) =
      (Pqxdh.ratchetCrypto c).kdfChain (absChain chain) := by
  simpa only [concreteCrypto, withInterpreter, Pqxdh.ratchetCrypto_kdfChain,
    Pqxdh.nextChain, Pqxdh.ratchetOut, interpretedResponse, hlaw chain] using
    (interpretedStep_bytes execute chain).1

/-- Ongoing message-key and nonce derivation commutes with the exact byte representation. -/
theorem kdfMsg_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (chain : ratchet.RatchetChain) :
    absMaterial ((concreteCrypto c execute).kdfMsg chain) =
      (Pqxdh.ratchetCrypto c).kdfMsg (absChain chain) := by
  simpa only [concreteCrypto, withInterpreter, Pqxdh.ratchetCrypto_kdfMsg,
    Pqxdh.msgMaterial, Pqxdh.ratchetOut, interpretedResponse, hlaw chain] using
    (interpretedStep_bytes execute chain).2

/-- The represented ongoing chains agree at every logical position. -/
theorem chainAt_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (chain : ratchet.RatchetChain) (n : Nat) :
    absChain (Ratchet.chainAt (concreteCrypto c execute) chain n) =
      Ratchet.chainAt (Pqxdh.ratchetCrypto c) (absChain chain) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [Ratchet.chainAt, Function.iterate_succ_apply', kdfChain_commutes c execute hlaw] using
      congrArg (Pqxdh.ratchetCrypto c).kdfChain ih

/-- The represented ongoing key and nonce streams agree at every logical position. -/
theorem msgKeyAt_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (chain : ratchet.RatchetChain) (n : Nat) :
    absMaterial (Ratchet.msgKeyAt (concreteCrypto c execute) chain n) =
      Ratchet.msgKeyAt (Pqxdh.ratchetCrypto c) (absChain chain) n := by
  simp only [Ratchet.msgKeyAt, kdfMsg_commutes c execute hlaw, chainAt_commutes c execute hlaw]

/-- Every skipped message index retains the full corresponding key and nonce. -/
theorem skipKeys_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (chain : ratchet.RatchetChain) (base count : Nat) :
    (Ratchet.skipKeys (concreteCrypto c execute) chain base count).map
        (fun p => (p.1, absMaterial p.2)) =
      Ratchet.skipKeys (Pqxdh.ratchetCrypto c) (absChain chain) base count := by
  induction count generalizing chain base with
  | zero => rfl
  | succ count ih =>
    simp only [Ratchet.skipKeys, List.map_cons, ih, kdfMsg_commutes c execute hlaw,
      kdfChain_commutes c execute hlaw]

/-- Sealing preserves the complete encoded record, including tag and commitment. -/
theorem enc_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (material : ratchet.RatchetMaterial) (ad : Pqxdh.RecordAD) (plaintext : Pqxdh.Bytes) :
    (concreteCrypto c execute).enc material ad plaintext =
      (Pqxdh.ratchetCrypto c).enc (absMaterial material) ad plaintext := rfl

/-- Opening preserves both authentication failure and the complete plaintext. -/
theorem dec_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (material : ratchet.RatchetMaterial) (ad : Pqxdh.RecordAD) (ciphertext : Pqxdh.Bytes) :
    (concreteCrypto c execute).dec material ad ciphertext =
      (Pqxdh.ratchetCrypto c).dec (absMaterial material) ad ciphertext := rfl

/-- The byte model sends exactly the same logical index and encoded ciphertext, and its poststate is the representation of the concrete-type model's poststate. -/
theorem sendStep_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute) (send : Ratchet.SendState ratchet.RatchetChain)
    (ad : Pqxdh.RecordAD) (plaintext : Pqxdh.Bytes) :
    ((Ratchet.sendStep (concreteCrypto c execute) send ad plaintext).1,
      mapSend (Ratchet.sendStep (concreteCrypto c execute) send ad plaintext).2) =
      Ratchet.sendStep (Pqxdh.ratchetCrypto c) (mapSend send) ad plaintext := by
  simp only [Ratchet.sendStep, mapSend, enc_commutes, kdfMsg_commutes c execute hlaw,
    kdfChain_commutes c execute hlaw]

private theorem lookup_mapMaterial (skipped : List (Nat × ratchet.RatchetMaterial)) (idx : Nat) :
    List.lookup idx (skipped.map (fun p => (p.1, absMaterial p.2))) =
      (List.lookup idx skipped).map absMaterial := by
  induction skipped with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨key, material⟩
    simp only [List.map_cons, List.lookup_cons, ih]
    split <;> rfl

/-- Both models return exactly the same plaintext or receive error, and every branch preserves the complete represented poststate. -/
theorem recvStep_commutes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (hlaw : KdfLaw c execute)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (ad : Pqxdh.RecordAD) (message : Ratchet.Msg Pqxdh.Bytes) :
    ((Ratchet.recvStep (concreteCrypto c execute) receive ad message).1,
      mapRecv (Ratchet.recvStep (concreteCrypto c execute) receive ad message).2) =
      Ratchet.recvStep (Pqxdh.ratchetCrypto c) (mapRecv receive) ad message := by
  simp only [Ratchet.recvStep, mapRecv, lookup_mapMaterial, List.length_map, dec_commutes,
    msgKeyAt_commutes c execute hlaw]
  cases hlookup : List.lookup message.idx receive.skipped with
  | some material =>
    simp only [Option.map_some]
    cases (Pqxdh.ratchetCrypto c).dec (absMaterial material) ad message.ct <;>
      simp only [List.filter_map, Function.comp_def]
  | none =>
    simp only [Option.map_none]
    by_cases hlt : message.idx < receive.n <;> simp only [hlt, if_true, if_false]
    by_cases hskip : Ratchet.maxSkip < message.idx - receive.n + receive.skipped.length <;>
      simp only [hskip, if_true, if_false]
    cases (Pqxdh.ratchetCrypto c).dec
        (Ratchet.msgKeyAt (Pqxdh.ratchetCrypto c) (absChain receive.ck) (message.idx - receive.n)) ad message.ct <;>
      simp only [chainAt_commutes c execute hlaw, List.map_append, skipKeys_commutes c execute hlaw]

/-- The implementation's full kernel relation, followed by an exact byte representation of its origin, both chains and counters, and every live skipped key and nonce. The existential witnesses retain the soundness/completeness and empty-tail clauses of `KernelRefines`. -/
def ByteKernelRefines (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (origin : Pqxdh.Bytes) (send : Ratchet.SendState Pqxdh.Bytes)
    (receive : Ratchet.RecvState Pqxdh.Bytes (Pqxdh.Bytes × Pqxdh.Bytes))
    (kernel : ConcreteRatchetKernel) : Prop :=
  ∃ concreteOrigin concreteSend concreteReceive,
    absChain concreteOrigin = origin ∧ mapSend concreteSend = send ∧ mapRecv concreteReceive = receive ∧
      KernelRefines (concreteCrypto c execute) concreteOrigin concreteSend concreteReceive kernel

/-- Any established concrete kernel relation gives the corresponding byte-model relation without additional assumptions. -/
theorem kernelRefines_toBytes (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (origin : ratchet.RatchetChain) (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ConcreteRatchetKernel)
    (h : KernelRefines (concreteCrypto c execute) origin send receive kernel) :
    ByteKernelRefines c execute (absChain origin) (mapSend send) (mapRecv receive) kernel :=
  ⟨origin, send, receive, rfl, rfl, rfl, h⟩

/-- The byte relation fixes both concrete chain bytes and both counters. -/
theorem ByteKernelRefines.chainsAndCounters (c : Pqxdh.Crypto) (execute : KdfInterpreter)
    (origin : Pqxdh.Bytes) (send : Ratchet.SendState Pqxdh.Bytes)
    (receive : Ratchet.RecvState Pqxdh.Bytes (Pqxdh.Bytes × Pqxdh.Bytes))
    (kernel : ConcreteRatchetKernel) (h : ByteKernelRefines c execute origin send receive kernel) :
    absChain kernel.refined.send_chain = send.ck ∧
      absChain kernel.refined.receive_chain = receive.ck ∧
      kernel.refined.control.send_sequence.val = send.n ∧
      kernel.refined.control.receive_sequence.val = receive.n := by
  rcases h with ⟨_, concreteSend, concreteReceive, _, rfl, rfl, h⟩
  exact ⟨congrArg absChain h.sendChain, congrArg absChain h.receiveChain,
    h.sendSequence, h.receiveControl.seq⟩

/--
info: 'BeaconcryptCore.Refinement.RepresentationBridge.sendStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sendStep_commutes

/--
info: 'BeaconcryptCore.Refinement.RepresentationBridge.recvStep_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms recvStep_commutes

end BeaconcryptCore.Refinement.RepresentationBridge

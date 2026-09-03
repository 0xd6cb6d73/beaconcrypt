import BeaconcryptCore.Computational.PqxdhJointKdf
import BeaconcryptCore.Refinement.PqxdhCore
import BeaconcryptCore.Refinement.RatchetEffectRefinement

/-!
# Initial PQXDH ratchet complementarity

HB-67 connects the extracted 64-byte initial-ratchet request, response split, and zero-counter kernel constructor to the handwritten ratchet refinement boundary.
It treats the adapter response equation as an explicit representation and primitive-correctness premise; the response type alone does not establish that equation.
The Server consumes the first 32 bytes as its send chain and the second 32 bytes as its receive chain, while the Beacon uses the opposite orientation.
Separate concrete roots and separate response objects are allowed, and concrete cross-role chain equality follows only when both roots represent one model root and both local responses satisfy their own pending-request equation.
The reusable kernel lemma is parametric in a concrete-chain Ratchet.Crypto and does not identify that crypto with the byte-list Pqxdh.ratchetCrypto.
The joint-stream corollary additionally assumes ProductionHkdfPrefixConsistent and exposes the two canonical projections at ratchetAddress root.
This module proves no root agreement or provenance, HKDF implementation or security property, adapter execution or provenance, ongoing 76-byte step semantics, AEAD/CTX/nonce property, source-to-Lean or compiler refinement, schedule, persistence, multi-user statement, crash property, erasure property, or probability bound.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

open beaconcrypt_core

/-- The model-byte view of offsets `[0, 32)` in an extracted 64-byte response. -/
def firstHalf (output : Std.Array Std.U8 64#usize) : Pqxdh.Bytes :=
  (PqxdhRefinement.absBytes output).take 32

/-- The model-byte view of offsets `[32, 64)` in an extracted 64-byte response. -/
def secondHalf (output : Std.Array Std.U8 64#usize) : Pqxdh.Bytes :=
  (PqxdhRefinement.absBytes output).drop 32

/-- Representation-only equality between an extracted chain wrapper and model bytes. -/
def ChainBytesRefines (chain : ratchet.RatchetChain) (bytes : Pqxdh.Bytes) : Prop :=
  PqxdhRefinement.absBytes chain.bytes = bytes

theorem chain_eq_of_refines {left right : ratchet.RatchetChain} {bytes : Pqxdh.Bytes}
    (hleft : ChainBytesRefines left bytes) (hright : ChainBytesRefines right bytes) :
    left = right := by
  have harray : left.bytes = right.bytes := by
    apply Subtype.ext
    exact (PqxdhRefinement.absBytes_inj_iff left.bytes right.bytes).mp
      (hleft.trans hright.symm)
  cases left
  cases right
  cases harray
  rfl

/-- Representation-only equality between an extracted root array and model bytes. -/
def RootArrayRefines (rootArray : Std.Array Std.U8 32#usize) (root : Pqxdh.Bytes) : Prop :=
  PqxdhRefinement.absBytes rootArray = root

/-- The external adapter/interpreter returned the exact 64-byte HKDF value requested by this pending phase. -/
def InitialResponseRefines (c : Pqxdh.Crypto)
    (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse) : Prop :=
  PqxdhRefinement.absBytes response.bytes =
    c.hkdf (PqxdhRefinement.absBytes pending.request.input)
      (PqxdhRefinement.absBytes pending.request.info) 64

/-- Re-express a response premise after its pending input and label have been related to model values. -/
theorem InitialResponseRefines.modelOutput (c : Pqxdh.Crypto)
    (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (root : Pqxdh.Bytes)
    (hresponse : InitialResponseRefines c pending response)
    (hinput : PqxdhRefinement.absBytes pending.request.input = root)
    (hinfo : PqxdhRefinement.absBytes pending.request.info = Pqxdh.INFO_R) :
    PqxdhRefinement.absBytes response.bytes = c.hkdf root Pqxdh.INFO_R 64 := by
  simpa [InitialResponseRefines, hinput, hinfo] using hresponse

@[simp] theorem absBytes_ratchetSymmetricInfo :
    PqxdhRefinement.absBytes ratchet.SYM_RATCHET_INFO = Pqxdh.INFO_R := by
  simpa [pqxdh.SYM_RATCHET_INFO] using PqxdhRefinement.absBytes_SYM_RATCHET_INFO

/-- The exact pending value returned by the extracted Server start phase. -/
def serverPending (root : Std.Array Std.U8 32#usize) :
    pqxdh.concrete.InitialRatchetKdfPending := {
  request := { input := root, info := ratchet.SYM_RATCHET_INFO }
  initialization := { send_offset := 0#u8, receive_offset := 32#u8 }
}

/-- The exact pending value returned by the extracted Beacon start phase. -/
def beaconPending (root : Std.Array Std.U8 32#usize) :
    pqxdh.concrete.InitialRatchetKdfPending := {
  request := { input := root, info := ratchet.SYM_RATCHET_INFO }
  initialization := { send_offset := 32#u8, receive_offset := 0#u8 }
}

theorem serverStartRequest_refines (rootArray : Std.Array Std.U8 32#usize)
    (root : Pqxdh.Bytes) (hroot : RootArrayRefines rootArray root) :
    pqxdh.concrete.start_server_ratchet_kdf rootArray = ok (serverPending rootArray) ∧
    pqxdh.concrete.InitialRatchetKdfPending.impl.request (serverPending rootArray) =
      ok (serverPending rootArray).request ∧
    RootArrayRefines (serverPending rootArray).request.input root ∧
    PqxdhRefinement.absBytes (serverPending rootArray).request.info = Pqxdh.INFO_R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [serverPending] using
      beaconcrypt_core.pqxdh.concrete.start_server_ratchet_kdf_exact rootArray
  · exact beaconcrypt_core.pqxdh.concrete.initial_request_accessor_exact _
  · simpa [serverPending] using hroot
  · simp [serverPending]

theorem beaconStartRequest_refines (rootArray : Std.Array Std.U8 32#usize)
    (root : Pqxdh.Bytes) (hroot : RootArrayRefines rootArray root) :
    pqxdh.concrete.start_beacon_ratchet_kdf rootArray = ok (beaconPending rootArray) ∧
    pqxdh.concrete.InitialRatchetKdfPending.impl.request (beaconPending rootArray) =
      ok (beaconPending rootArray).request ∧
    RootArrayRefines (beaconPending rootArray).request.input root ∧
    PqxdhRefinement.absBytes (beaconPending rootArray).request.info = Pqxdh.INFO_R := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [beaconPending] using
      beaconcrypt_core.pqxdh.concrete.start_beacon_ratchet_kdf_exact rootArray
  · exact beaconcrypt_core.pqxdh.concrete.initial_request_accessor_exact _
  · simpa [beaconPending] using hroot
  · simp [beaconPending]

/-- One completed extracted initial phase together with its zero/empty ideal refinement witness. -/
def InitialKernelResult {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (start : Std.Array Std.U8 32#usize → RustM pqxdh.concrete.InitialRatchetKdfPending)
    (rootArray : Std.Array Std.U8 32#usize)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (root modelSend modelReceive : Pqxdh.Bytes)
    (pending : pqxdh.concrete.InitialRatchetKdfPending)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) : Prop :=
  start rootArray = ok pending ∧
  pqxdh.concrete.resume_initial_ratchet_kdf pending response = ok kernel ∧
  RootArrayRefines pending.request.input root ∧
  PqxdhRefinement.absBytes pending.request.info = Pqxdh.INFO_R ∧
  ChainBytesRefines kernel.refined.send_chain modelSend ∧
  ChainBytesRefines kernel.refined.receive_chain modelReceive ∧
  ratchet.concrete.KernelRefines cr kernel.refined.receive_chain
    ({ ck := kernel.refined.send_chain, n := 0 } : Ratchet.SendState ratchet.RatchetChain)
    ({ ck := kernel.refined.receive_chain, n := 0, skipped := [] } :
      Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    kernel

/-- Existential packaging of a completed initial phase. -/
def InitialKernelWitness {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (start : Std.Array Std.U8 32#usize → RustM pqxdh.concrete.InitialRatchetKdfPending)
    (rootArray : Std.Array Std.U8 32#usize)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (root modelSend modelReceive : Pqxdh.Bytes) : Prop :=
  ∃ pending : pqxdh.concrete.InitialRatchetKdfPending,
    ∃ kernel : ratchet.concrete.ConcreteRatchetKernel,
      InitialKernelResult cr start rootArray response root modelSend modelReceive pending kernel

/-- The two generated `from_fn` calls compute precisely the first and second 32-byte halves. -/
theorem initialHalves_exact (output : Std.Array Std.U8 64#usize) :
    ∃ left right : Std.Array Std.U8 32#usize,
      core.array.from_fn 32#usize
          pqxdh.split_initial_ratchet_kdf_output.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
          output = ok left ∧
      core.array.from_fn 32#usize
          pqxdh.split_initial_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8
          output = ok right ∧
      PqxdhRefinement.absBytes left = firstHalf output ∧
      PqxdhRefinement.absBytes right = secondHalf output := by
  obtain ⟨left, hleft, hleftAbs⟩ :=
    PqxdhRefinement.from_fn_absBytes (F := pqxdh.split_initial_ratchet_kdf_output.closure)
      32#usize
      pqxdh.split_initial_ratchet_kdf_output.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8
      output (fun i => output.val[i]!) (firstHalf output) (by simp [firstHalf]) (by
        intro i hi
        rw [PqxdhRefinement.usize_val_32] at hi
        have hval : (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i :=
          PqxdhRefinement.usize_mk_val i (by omega)
        change (Std.Array.index_usize output (⟨BitVec.ofNat _ i⟩ : Std.Usize) >>= fun b =>
          ok (b, output)) = _
        rw [PqxdhRefinement.index_usize_eq output _ (by rw [hval]; simp; omega), hval]
        rfl) (by
          intro i hi
          rw [PqxdhRefinement.usize_val_32] at hi
          rw [firstHalf, List.getElem!_take_of_lt _ _ _ hi]
          exact (PqxdhRefinement.absBytes_getElem! output i (by simp; omega)).symm)
  obtain ⟨right, hright, hrightAbs⟩ :=
    PqxdhRefinement.drop_from_fn (F := pqxdh.split_initial_ratchet_kdf_output.closure_1)
      (N := 32#usize)
      pqxdh.split_initial_ratchet_kdf_output.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU8
      output output 32 (by simp) (by
        intro i hi
        rw [PqxdhRefinement.usize_val_32] at hi
        have hval : (⟨BitVec.ofNat _ i⟩ : Std.Usize).val = i :=
          PqxdhRefinement.usize_mk_val i (by omega)
        change (((⟨BitVec.ofNat _ i⟩ : Std.Usize) + pqxdh.RATCHET_CHAIN_SIZE) >>= fun j =>
          Std.Array.index_usize output j >>= fun b => ok (b, output)) = _
        have hsize : pqxdh.RATCHET_CHAIN_SIZE = 32#usize := by
          simp [pqxdh.RATCHET_CHAIN_SIZE, ratchet.RATCHET_CHAIN_SIZE]
        obtain ⟨z, hz, hzv⟩ := PqxdhRefinement.usize_add_val
          (⟨BitVec.ofNat _ i⟩ : Std.Usize) pqxdh.RATCHET_CHAIN_SIZE
          (by rw [hval, hsize, PqxdhRefinement.usize_val_32];
              exact PqxdhRefinement.lt_numBits _ (by omega))
        rw [hz]
        simp only [bind_tc_ok]
        have hzv' : z.val = i + 32 := by
          rw [hzv, hval, hsize, PqxdhRefinement.usize_val_32]
        rw [PqxdhRefinement.index_usize_eq output z (by rw [hzv']; simp; omega), hzv']
        rfl)
  exact ⟨left, right, hleft, hright, hleftAbs, hrightAbs⟩

/-- The extracted Server split uses the left half for sending and the right half for receiving. -/
theorem splitInitialServer_exact (output : Std.Array Std.U8 64#usize) :
    ∃ sendChain receiveChain : ratchet.RatchetChain,
      pqxdh.split_initial_ratchet_kdf_output output
          { send_offset := 0#u8, receive_offset := 32#u8 } =
        ok { send_chain := sendChain, receive_chain := receiveChain } ∧
      ChainBytesRefines sendChain (firstHalf output) ∧
      ChainBytesRefines receiveChain (secondHalf output) := by
  obtain ⟨left, right, hleft, hright, hleftAbs, hrightAbs⟩ := initialHalves_exact output
  refine ⟨{ bytes := left }, { bytes := right }, ?_, hleftAbs, hrightAbs⟩
  simp [pqxdh.split_initial_ratchet_kdf_output, hleft, hright,
    ratchet.RatchetChain.from_bytes]

/-- The extracted Beacon split uses the right half for sending and the left half for receiving. -/
theorem splitInitialBeacon_exact (output : Std.Array Std.U8 64#usize) :
    ∃ sendChain receiveChain : ratchet.RatchetChain,
      pqxdh.split_initial_ratchet_kdf_output output
          { send_offset := 32#u8, receive_offset := 0#u8 } =
        ok { send_chain := sendChain, receive_chain := receiveChain } ∧
      ChainBytesRefines sendChain (secondHalf output) ∧
      ChainBytesRefines receiveChain (firstHalf output) := by
  obtain ⟨left, right, hleft, hright, hleftAbs, hrightAbs⟩ := initialHalves_exact output
  refine ⟨{ bytes := right }, { bytes := left }, ?_, hrightAbs, hleftAbs⟩
  simp [pqxdh.split_initial_ratchet_kdf_output, hleft, hright,
    ratchet.RatchetChain.from_bytes]

/-- `ConcreteRatchetKernel.new` installs the supplied chains with zero counters, an empty receive cache, and 50 empty material slots. -/
theorem concreteKernelNew_exact
    (sendChain receiveChain : ratchet.RatchetChain) :
    ∃ kernel : ratchet.concrete.ConcreteRatchetKernel,
      ratchet.concrete.ConcreteRatchetKernel.new sendChain receiveChain = ok kernel ∧
      kernel.refined.control.send_sequence.val = 0 ∧
      kernel.refined.control.receive_sequence.val = 0 ∧
      kernel.refined.control.receive_cache.len.val = 0 ∧
      ratchet.control.cacheSeqs kernel.refined.control.receive_cache = [] ∧
      kernel.refined.send_chain = sendChain ∧
      kernel.refined.receive_chain = receiveChain ∧
      (∀ i, i < 50 →
        kernel.refined.receive_slots.val[i]! = core.option.Option.None) := by
  simp [ratchet.concrete.ConcreteRatchetKernel.new,
    ratchet.concrete.ConcreteRatchetKernel.from_counters,
    ratchet.refined.RefinedRatchet.from_counters,
    ratchet.control.RatchetState.from_counters,
    ratchet.control.SequenceCache.empty,
    ratchet.refined.empty_material_slots]
  constructor
  · rfl
  · intro i hi
    unfold Std.Array.make
    interval_cases i <;> rfl

/-- The new kernel refines zero/empty ideal states for every crypto over the extracted chain and material types. -/
theorem concreteKernelNew_refines_initial {AD PT CT : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (sendChain receiveChain : ratchet.RatchetChain) :
    ∃ kernel : ratchet.concrete.ConcreteRatchetKernel,
      ratchet.concrete.ConcreteRatchetKernel.new sendChain receiveChain = ok kernel ∧
      ratchet.concrete.KernelRefines cr receiveChain
        ({ ck := sendChain, n := 0 } : Ratchet.SendState ratchet.RatchetChain)
        ({ ck := receiveChain, n := 0, skipped := [] } :
          Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
        kernel := by
  obtain ⟨kernel, hkernel, hsendSeq, hreceiveSeq, hcacheLen, hcacheEmpty, hsendChain,
      hreceiveChain, hslots⟩ := concreteKernelNew_exact sendChain receiveChain
  refine ⟨kernel, hkernel, ?_⟩
  refine {
    receiveControl := ?_
    sendSequence := hsendSeq
    sendLt := by norm_num
    sendChain := hsendChain
    receiveChain := hreceiveChain
    slotSound := ?_
    slotComplete := ?_
    slotsAboveLenEmpty := ?_
  }
  · refine {
      wf := ?_
      seq := hreceiveSeq
      lt := by norm_num
      chain := by simp [Ratchet.chainAt]
      keys := by simp
      keys_lt := by simp
      nodup := by simp
      cache := ?_
    }
    · simp only [ratchet.control.RatchetState.Wf, ratchet.control.SequenceCache.Wf]
      omega
    · simp [hcacheEmpty]
  · intro i hi
    omega
  · intro p hp
    simp at hp
  · intro i _ hi
    exact hslots i hi

theorem serverStartResume_refines {AD PT CT : Type}
    (c : Pqxdh.Crypto)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (rootArray : Std.Array Std.U8 32#usize) (root : Pqxdh.Bytes)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (hroot : RootArrayRefines rootArray root)
    (hresponse : InitialResponseRefines c (serverPending rootArray) response) :
    InitialKernelWitness cr pqxdh.concrete.start_server_ratchet_kdf rootArray response root
      (Pqxdh.rootChains c root).1 (Pqxdh.rootChains c root).2 := by
  have hrootAbs : PqxdhRefinement.absBytes rootArray = root := hroot
  have hresponseModel : PqxdhRefinement.absBytes response.bytes =
      c.hkdf root Pqxdh.INFO_R 64 := by
    simpa [InitialResponseRefines, serverPending, hrootAbs] using hresponse
  obtain ⟨sendChain, receiveChain, hsplit, hsend, hreceive⟩ :=
    splitInitialServer_exact response.bytes
  have hsendModel : ChainBytesRefines sendChain (Pqxdh.rootChains c root).1 := by
    simpa [ChainBytesRefines, firstHalf, Pqxdh.rootChains, hresponseModel] using hsend
  have hreceiveModel : ChainBytesRefines receiveChain (Pqxdh.rootChains c root).2 := by
    simpa [ChainBytesRefines, secondHalf, Pqxdh.rootChains, hresponseModel] using hreceive
  obtain ⟨kernel, hkernel, hrefines⟩ :=
    concreteKernelNew_refines_initial cr sendChain receiveChain
  refine ⟨serverPending rootArray, kernel, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [serverPending] using
      beaconcrypt_core.pqxdh.concrete.start_server_ratchet_kdf_exact rootArray
  · rw [beaconcrypt_core.pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition]
    rw [show (serverPending rootArray).initialization =
        ({ send_offset := 0#u8, receive_offset := 32#u8 } : pqxdh.RatchetInitialization)
      from rfl, hsplit]
    simpa using hkernel
  · simpa [RootArrayRefines, serverPending] using hroot
  · simp [serverPending]
  · simpa only [hrefines.sendChain] using hsendModel
  · simpa only [hrefines.receiveChain] using hreceiveModel
  · simpa only [hrefines.sendChain, hrefines.receiveChain] using hrefines

theorem beaconStartResume_refines {AD PT CT : Type}
    (c : Pqxdh.Crypto)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (rootArray : Std.Array Std.U8 32#usize) (root : Pqxdh.Bytes)
    (response : pqxdh.concrete.InitialRatchetKdfResponse)
    (hroot : RootArrayRefines rootArray root)
    (hresponse : InitialResponseRefines c (beaconPending rootArray) response) :
    InitialKernelWitness cr pqxdh.concrete.start_beacon_ratchet_kdf rootArray response root
      (Pqxdh.rootChains c root).2 (Pqxdh.rootChains c root).1 := by
  have hrootAbs : PqxdhRefinement.absBytes rootArray = root := hroot
  have hresponseModel : PqxdhRefinement.absBytes response.bytes =
      c.hkdf root Pqxdh.INFO_R 64 := by
    simpa [InitialResponseRefines, beaconPending, hrootAbs] using hresponse
  obtain ⟨sendChain, receiveChain, hsplit, hsend, hreceive⟩ :=
    splitInitialBeacon_exact response.bytes
  have hsendModel : ChainBytesRefines sendChain (Pqxdh.rootChains c root).2 := by
    simpa [ChainBytesRefines, secondHalf, Pqxdh.rootChains, hresponseModel] using hsend
  have hreceiveModel : ChainBytesRefines receiveChain (Pqxdh.rootChains c root).1 := by
    simpa [ChainBytesRefines, firstHalf, Pqxdh.rootChains, hresponseModel] using hreceive
  obtain ⟨kernel, hkernel, hrefines⟩ :=
    concreteKernelNew_refines_initial cr sendChain receiveChain
  refine ⟨beaconPending rootArray, kernel, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [beaconPending] using
      beaconcrypt_core.pqxdh.concrete.start_beacon_ratchet_kdf_exact rootArray
  · rw [beaconcrypt_core.pqxdh.concrete.resume_initial_ratchet_kdf_is_core_partition]
    rw [show (beaconPending rootArray).initialization =
        ({ send_offset := 32#u8, receive_offset := 0#u8 } : pqxdh.RatchetInitialization)
      from rfl, hsplit]
    simpa using hkernel
  · simpa [RootArrayRefines, beaconPending] using hroot
  · simp [beaconPending]
  · simpa only [hrefines.sendChain] using hsendModel
  · simpa only [hrefines.receiveChain] using hreceiveModel
  · simpa only [hrefines.sendChain, hrefines.receiveChain] using hrefines

/-- Two local response premises for one abstract root yield complementary zero-state Server and Beacon kernels without requiring a shared concrete response object. -/
theorem initialRatchetComplementarity {AD PT CT : Type}
    (c : Pqxdh.Crypto)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (serverRoot beaconRoot : Std.Array Std.U8 32#usize) (root : Pqxdh.Bytes)
    (serverResponse beaconResponse : pqxdh.concrete.InitialRatchetKdfResponse)
    (hserverRoot : RootArrayRefines serverRoot root)
    (hbeaconRoot : RootArrayRefines beaconRoot root)
    (hserverResponse : InitialResponseRefines c (serverPending serverRoot) serverResponse)
    (hbeaconResponse : InitialResponseRefines c (beaconPending beaconRoot) beaconResponse) :
    ∃ serverPendingResult beaconPendingResult : pqxdh.concrete.InitialRatchetKdfPending,
      ∃ serverKernel beaconKernel : ratchet.concrete.ConcreteRatchetKernel,
        InitialKernelResult cr pqxdh.concrete.start_server_ratchet_kdf serverRoot
          serverResponse root (Pqxdh.rootChains c root).1 (Pqxdh.rootChains c root).2
          serverPendingResult serverKernel ∧
        InitialKernelResult cr pqxdh.concrete.start_beacon_ratchet_kdf beaconRoot
          beaconResponse root (Pqxdh.rootChains c root).2 (Pqxdh.rootChains c root).1
          beaconPendingResult beaconKernel ∧
        serverKernel.refined.send_chain = beaconKernel.refined.receive_chain ∧
        serverKernel.refined.receive_chain = beaconKernel.refined.send_chain := by
  obtain ⟨serverPendingResult, serverKernel, hserver⟩ :=
    serverStartResume_refines c cr serverRoot root serverResponse hserverRoot hserverResponse
  obtain ⟨beaconPendingResult, beaconKernel, hbeacon⟩ :=
    beaconStartResume_refines c cr beaconRoot root beaconResponse hbeaconRoot hbeaconResponse
  have hserverCopy := hserver
  have hbeaconCopy := hbeacon
  rcases hserver with ⟨_, _, _, _, hserverSend, hserverReceive, _⟩
  rcases hbeacon with ⟨_, _, _, _, hbeaconSend, hbeaconReceive, _⟩
  exact ⟨serverPendingResult, beaconPendingResult, serverKernel, beaconKernel,
    hserverCopy, hbeaconCopy,
    chain_eq_of_refines hserverSend hbeaconReceive,
    chain_eq_of_refines hserverReceive hbeaconSend⟩

/-- Under the production prefix law, the two directional model chains are the canonical first32 and second32 projections at one ratchet address. -/
theorem initialRatchetComplementarity_jointStream {AD PT CT : Type}
    (c : Pqxdh.Crypto)
    (hprefix : BeaconcryptCore.Computational.PqxdhJointKdf.ProductionHkdfPrefixConsistent c)
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (serverRoot beaconRoot : Std.Array Std.U8 32#usize) (root : Pqxdh.Bytes)
    (serverResponse beaconResponse : pqxdh.concrete.InitialRatchetKdfResponse)
    (hserverRoot : RootArrayRefines serverRoot root)
    (hbeaconRoot : RootArrayRefines beaconRoot root)
    (hserverResponse : InitialResponseRefines c (serverPending serverRoot) serverResponse)
    (hbeaconResponse : InitialResponseRefines c (beaconPending beaconRoot) beaconResponse) :
    let projections := BeaconcryptCore.Computational.PqxdhJointKdf.initialProjection
      (BeaconcryptCore.Computational.PqxdhJointKdf.productionStream c
        (BeaconcryptCore.Computational.PqxdhJointKdf.ratchetAddress root))
    ∃ serverPendingResult beaconPendingResult : pqxdh.concrete.InitialRatchetKdfPending,
      ∃ serverKernel beaconKernel : ratchet.concrete.ConcreteRatchetKernel,
        InitialKernelResult cr pqxdh.concrete.start_server_ratchet_kdf serverRoot
          serverResponse root projections.1 projections.2 serverPendingResult serverKernel ∧
        InitialKernelResult cr pqxdh.concrete.start_beacon_ratchet_kdf beaconRoot
          beaconResponse root projections.2 projections.1 beaconPendingResult beaconKernel ∧
        serverKernel.refined.send_chain = beaconKernel.refined.receive_chain ∧
        serverKernel.refined.receive_chain = beaconKernel.refined.send_chain := by
  have hchains := BeaconcryptCore.Computational.PqxdhJointKdf.rootChains_eq_initialProjection
    c hprefix root
  simpa only [hchains] using initialRatchetComplementarity c cr serverRoot beaconRoot root
    serverResponse beaconResponse hserverRoot hbeaconRoot hserverResponse hbeaconResponse

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.concreteKernelNew_refines_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms concreteKernelNew_refines_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.initialRatchetComplementarity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms initialRatchetComplementarity

/--
info: 'BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity.initialRatchetComplementarity_jointStream' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms initialRatchetComplementarity_jointStream

end BeaconcryptCore.Computational.PqxdhInitialRatchetComplementarity

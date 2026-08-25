import BeaconcryptCore.Model.RatchetEffect

/-!
# Refinement of the first-order ratchet effect phases

This file connects the affine request/response phases extracted from the production
Rust implementation to the handwritten symmetric-ratchet model.  In particular,
`KernelRefines` relates both chains and counters and records a bidirectional
correspondence between live concrete material slots and the ideal skipped-key store.

The external KDF is represented by `ResponseRefines`: the untrusted interpreter may
compute the response, but the refinement theorem assumes that parsing that response
produces exactly the chain and message material selected by the ideal crypto model.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace beaconcrypt_core.ratchet.concrete

variable {AD PT CT Context : Type}

/-- A production kernel represents one ideal send state and one ideal receive state.

The final three fields make the material cache relation explicit.  Every live slot is
aligned with its control-plane sequence and denotes an ideal skipped key; conversely,
every ideal skipped key occurs in a live slot; slots above the live prefix are empty. -/
structure KernelRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) : Prop where
  receiveControl : ratchet.control.Refines cr receiveOrigin receive kernel.refined.control
  sendSequence : kernel.refined.control.send_sequence.val = send.n
  sendLt : send.n < 2 ^ 64
  sendChain : kernel.refined.send_chain = send.ck
  receiveChain : kernel.refined.receive_chain = receive.ck
  slotSound : ∀ i, i < kernel.refined.control.receive_cache.len.val →
    ∃ (p : ℕ × ratchet.RatchetMaterial) (cached : ratchet.refined.CachedReceiveKey
        ratchet.RatchetMaterial),
      p ∈ receive.skipped ∧
      kernel.refined.receive_slots.val[i]! = core.option.Option.Some cached ∧
      cached.sequence = kernel.refined.control.receive_cache.entries.val[i]! ∧
      cached.sequence.val = p.1 + 1 ∧ cached.material = p.2
  slotComplete : ∀ p ∈ receive.skipped,
    ∃ (i : ℕ), i < kernel.refined.control.receive_cache.len.val ∧
      ∃ (cached : ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial),
        kernel.refined.receive_slots.val[i]! = core.option.Option.Some cached ∧
        cached.sequence = kernel.refined.control.receive_cache.entries.val[i]! ∧
        cached.sequence.val = p.1 + 1 ∧ cached.material = p.2
  slotsAboveLenEmpty : ∀ i,
    kernel.refined.control.receive_cache.len.val ≤ i → i < 50 →
      kernel.refined.receive_slots.val[i]! = core.option.Option.None

/-- The concrete KDF reply realizes one ideal chain step. This is the KDF-specific
semantic obligation; sealing, opening, and driver fidelity require separate laws. -/
def ResponseRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (chain : ratchet.RatchetChain) (response : ratchet.RatchetKdfResponse) : Prop :=
  ratchet.concrete.ratchet_step_from_response response =
    ok {
      chain := cr.kdfChain chain,
      material := cr.kdfMsg chain
    }

/-- The send-KDF phase carries exactly the entry state, context, logical advance, and
KDF request required for the next ideal send step. -/
structure SendKdfRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (pending : ratchet.concrete.SendKdf Context) : Prop where
  entry : pending.entry = kernel
  savedContext : pending.context = context
  entryRefines : KernelRefines cr receiveOrigin send receive kernel
  sequence : pending.sequence.val = send.n + 1
  committedSend : pending.committed_control.send_sequence.val = send.n + 1
  committedReceiveSequence :
    pending.committed_control.receive_sequence = kernel.refined.control.receive_sequence
  committedReceiveCache :
    pending.committed_control.receive_cache = kernel.refined.control.receive_cache
  key : pending.logical = { sequence := pending.sequence, available := true }
  requestInput : pending.request.input = send.ck.bytes
  requestInfo : pending.request.info = ratchet.SYM_RATCHET_INFO

/-- The seal phase contains the ideal message material and an advanced kernel refining
the ideal post-send state. -/
structure SendSealRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (context : Context) (pending : ratchet.concrete.SendSeal Context) : Prop where
  advanced : KernelRefines cr receiveOrigin
    { ck := cr.kdfChain send.ck, n := send.n + 1 } receive pending.advanced
  savedContext : pending.context = context
  sequence : pending.sequence.val = send.n + 1
  material : pending.material = cr.kdfMsg send.ck
  key : pending.logical = { sequence := pending.sequence, available := true }

/-! ## Rollback preserves the represented ideal state -/

theorem SendKdf.cancel_preserves_refinement
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (pending : ratchet.concrete.SendKdf Context)
    (h : SendKdfRefines cr receiveOrigin send receive kernel context pending) :
    pending.cancel = ok (kernel, context) ∧
      KernelRefines cr receiveOrigin send receive kernel := by
  constructor
  · rw [ratchet.concrete.SendKdf.cancel_exact, h.entry, h.savedContext]
  · exact h.entryRefines

theorem ReceiveKdf.cancel_preserves_refinement
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveKdf Context)
    (h : KernelRefines cr receiveOrigin send receive pending.entry) :
    pending.cancel = ok (pending.entry, pending.context) ∧
      KernelRefines cr receiveOrigin send receive pending.entry := by
  exact ⟨ratchet.concrete.ReceiveKdf.cancel_exact pending, h⟩

theorem ReceiveOpen.reject_preserves_refinement
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context)
    (h : KernelRefines cr receiveOrigin send receive pending.entry) :
    pending.reject = ok (pending.entry, pending.context) ∧
      KernelRefines cr receiveOrigin send receive pending.entry := by
  exact ⟨ratchet.concrete.ReceiveOpen.reject_exact pending, h⟩

theorem ReceiveOpen.failure_preserves_refinement
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context)
    (h : KernelRefines cr receiveOrigin send receive pending.entry) :
    pending.finish (core.option.Option.None : core.option.Option PT) =
        ok (pending.entry, core.option.Option.None) ∧
      KernelRefines cr receiveOrigin send receive pending.entry := by
  exact ⟨ratchet.concrete.ReceiveOpen.finish_failure_restores_entry pending, h⟩

/-! ## Send-phase refinement -/

theorem begin_send_refines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (h : KernelRefines cr receiveOrigin send receive kernel)
    (hmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX) :
    ∃ pending,
      ratchet.concrete.begin_send kernel context =
        ok (ratchet.concrete.SendStart.SendKdfRequested pending) ∧
      SendKdfRefines cr receiveOrigin send receive kernel context pending := by
  obtain ⟨advanced, hadv, hsend, hreceiveSequence, hreceiveCache, hsequence, hkey⟩ :=
    ratchet.control.advance_send_ok kernel.refined.control hmax
  have hbegin : ratchet.concrete.begin_send kernel context =
      ok (ratchet.concrete.SendStart.SendKdfRequested {
        entry := kernel,
        context := context,
        committed_control := advanced.state,
        logical := advanced.key,
        sequence := advanced.state.send_sequence,
        request := {
          input := kernel.refined.send_chain.bytes,
          info := ratchet.SYM_RATCHET_INFO
        }
      }) := by
    simp [ratchet.concrete.begin_send, hadv, hsequence, hkey,
      ratchet.control.SendKey.impl.sequence,
      ratchet.control.RatchetState.impl.send_sequence,
      ratchet.RatchetChain.as_bytes,
      ratchet.SymmetricRatchetKdfRequest.new,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64]
  refine ⟨{
    entry := kernel,
    context := context,
    committed_control := advanced.state,
    logical := advanced.key,
    sequence := advanced.state.send_sequence,
    request := {
      input := kernel.refined.send_chain.bytes,
      info := ratchet.SYM_RATCHET_INFO
    }
  }, hbegin, ?_⟩
  refine {
    entry := rfl,
    savedContext := rfl,
    entryRefines := h,
    sequence := ?_,
    committedSend := ?_,
    committedReceiveSequence := hreceiveSequence,
    committedReceiveCache := hreceiveCache,
    key := hkey,
    requestInput := ?_,
    requestInfo := rfl
  }
  · rw [hsend, h.sendSequence]
  · rw [hsend, h.sendSequence]
  · simpa only using congrArg ratchet.RatchetChain.bytes h.sendChain

theorem SendKdf.resume_refines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (pending : ratchet.concrete.SendKdf Context)
    (h : SendKdfRefines cr receiveOrigin send receive kernel context pending)
    (response : ratchet.RatchetKdfResponse)
    (hresponse : ResponseRefines cr send.ck response) :
    ∃ sealedPhase,
      pending.resume response = ok sealedPhase ∧
      SendSealRefines cr receiveOrigin send receive context sealedPhase := by
  have hresume := ratchet.concrete.SendKdf.resume_exact pending response
    {
      chain := cr.kdfChain send.ck,
      material := cr.kdfMsg send.ck
    } hresponse
  refine ⟨{
    advanced := {
      refined := {
        pending.entry.refined with
        control := pending.committed_control,
        send_chain := cr.kdfChain send.ck
      }
    },
    context := pending.context,
    logical := pending.logical,
    sequence := pending.sequence,
    material := cr.kdfMsg send.ck
  }, hresume, ?_⟩
  refine {
    advanced := ?_,
    savedContext := h.savedContext,
    sequence := h.sequence,
    material := rfl,
    key := h.key
  }
  rw [h.entry]
  refine {
    receiveControl := ?_,
    sendSequence := h.committedSend,
    sendLt := ?_,
    sendChain := rfl,
    receiveChain := h.entryRefines.receiveChain,
    slotSound := ?_,
    slotComplete := ?_,
    slotsAboveLenEmpty := ?_
  }
  · let hr := h.entryRefines.receiveControl
    refine {
      wf := ?_,
      seq := ?_,
      lt := hr.lt,
      chain := hr.chain,
      keys := hr.keys,
      keys_lt := hr.keys_lt,
      nodup := hr.nodup,
      cache := ?_
    }
    · change pending.committed_control.Wf
      simp only [ratchet.control.RatchetState.Wf, ratchet.control.SequenceCache.Wf]
      rw [h.committedReceiveCache]
      exact hr.wf
    · rw [h.committedReceiveSequence]
      exact hr.seq
    · rw [h.committedReceiveCache]
      exact hr.cache
  · change send.n + 1 < 2 ^ 64
    rw [← h.sequence]
    exact pending.sequence.hmax
  · simpa only [h.committedReceiveCache] using h.entryRefines.slotSound
  · simpa only [h.committedReceiveCache] using h.entryRefines.slotComplete
  · simpa only [h.committedReceiveCache] using h.entryRefines.slotsAboveLenEmpty

theorem SendSeal.finish_refines_ideal_send
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (context : Context) (pending : ratchet.concrete.SendSeal Context)
    (h : SendSealRefines cr receiveOrigin send receive context pending)
    (ad : AD) (plaintext : PT) :
    pending.finish (core.option.Option.Some (cr.enc pending.material ad plaintext)) =
        ok (pending.advanced,
          core.option.Option.Some (Ratchet.sendStep cr send ad plaintext).1.ct) ∧
      pending.sequence.val = (Ratchet.sendStep cr send ad plaintext).1.idx + 1 ∧
      KernelRefines cr receiveOrigin (Ratchet.sendStep cr send ad plaintext).2 receive
        pending.advanced := by
  constructor
  · rw [ratchet.concrete.SendSeal.finish_returns_interpreter_result, h.material]
    rfl
  constructor
  · simpa only [Ratchet.sendStep] using h.sequence
  · simpa only [Ratchet.sendStep] using h.advanced

/-! ## Represented finite failed receive traces are state neutral -/

/-- A finite receive interaction that ends without accepting plaintext.  `resume`
records any number of KDF request/response transitions; the other constructors record
the possible non-committing exits.  Every phase is tied to the same entry ownership
token and context. -/
inductive ReceiveFailureTrace (entry : ratchet.concrete.ConcreteRatchetKernel)
    (context : Context) :
    ratchet.concrete.ReceiveEffect Context →
      ratchet.concrete.ConcreteRatchetKernel → Prop where
  | rejected : ReceiveFailureTrace entry context
      (ratchet.concrete.ReceiveEffect.ReceiveRejected entry context) entry
  | cancel (pending : ratchet.concrete.ReceiveKdf Context)
      (hentry : pending.entry = entry) (hcontext : pending.context = context)
      (result : ratchet.concrete.ConcreteRatchetKernel) (resultContext : Context)
      (hcancel : pending.cancel = ok (result, resultContext)) :
      ReceiveFailureTrace entry context
        (ratchet.concrete.ReceiveEffect.ReceiveKdfRequested pending) result
  | resume (pending : ratchet.concrete.ReceiveKdf Context)
      (hentry : pending.entry = entry) (hcontext : pending.context = context)
      (response : ratchet.RatchetKdfResponse)
      (next : ratchet.concrete.ReceiveEffect Context)
      (result : ratchet.concrete.ConcreteRatchetKernel)
      (hresume : pending.resume response = ok next)
      (tail : ReceiveFailureTrace entry context next result) :
      ReceiveFailureTrace entry context
        (ratchet.concrete.ReceiveEffect.ReceiveKdfRequested pending) result
  | reject (pending : ratchet.concrete.ReceiveOpen Context)
      (hentry : pending.entry = entry) (hcontext : pending.context = context)
      (result : ratchet.concrete.ConcreteRatchetKernel) (resultContext : Context)
      (hreject : pending.reject = ok (result, resultContext)) :
      ReceiveFailureTrace entry context
        (ratchet.concrete.ReceiveEffect.ReceiveOpenRequested pending) result
  | openFailure {Plaintext : Type} (pending : ratchet.concrete.ReceiveOpen Context)
      (hentry : pending.entry = entry) (hcontext : pending.context = context)
      (result : ratchet.concrete.ConcreteRatchetKernel)
      (hfinish : pending.finish
        (core.option.Option.None : core.option.Option Plaintext) =
          ok (result, core.option.Option.None)) :
      ReceiveFailureTrace entry context
        (ratchet.concrete.ReceiveEffect.ReceiveOpenRequested pending) result

theorem ReceiveFailureTrace.result_eq_entry
    {entry : ratchet.concrete.ConcreteRatchetKernel} {context : Context}
    {effect : ratchet.concrete.ReceiveEffect Context}
    {result : ratchet.concrete.ConcreteRatchetKernel}
    (trace : ReceiveFailureTrace entry context effect result) : result = entry := by
  induction trace with
  | rejected => rfl
  | cancel pending hentry hcontext result resultContext hcancel =>
      rw [ratchet.concrete.ReceiveKdf.cancel_exact] at hcancel
      cases hcancel
      exact hentry
  | resume pending hentry hcontext response next result hresume tail ih =>
      exact ih
  | reject pending hentry hcontext result resultContext hreject =>
      rw [ratchet.concrete.ReceiveOpen.reject_exact] at hreject
      cases hreject
      exact hentry
  | openFailure pending hentry hcontext result hfinish =>
      rw [ratchet.concrete.ReceiveOpen.finish_failure_restores_entry] at hfinish
      cases hfinish
      exact hentry

theorem ReceiveFailureTrace.preserves_refinement
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    {entry : ratchet.concrete.ConcreteRatchetKernel} {context : Context}
    {effect : ratchet.concrete.ReceiveEffect Context}
    {result : ratchet.concrete.ConcreteRatchetKernel}
    (trace : ReceiveFailureTrace entry context effect result)
    (h : KernelRefines cr receiveOrigin send receive entry) :
    KernelRefines cr receiveOrigin send receive result := by
  rw [trace.result_eq_entry]
  exact h

/-! ## Successful open replies -/

/-- Convert the ideal AEAD decryption result to the extracted core option returned to
the production effect machine. -/
def idealOpenReply
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (material : ratchet.RatchetMaterial) (ad : AD) (ciphertext : CT) :
    core.option.Option PT :=
  match cr.dec material ad ciphertext with
  | some plaintext => core.option.Option.Some plaintext
  | none => core.option.Option.None

/-- An open reply is valid when it extensionally agrees with ideal AEAD decryption
under the material exposed by the pending phase. This does not prove computation
provenance for the external interpreter. -/
def OpenReplyRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (pending : ratchet.concrete.ReceiveOpen Context) (ad : AD) (ciphertext : CT)
    (opened : core.option.Option PT) : Prop :=
  ∃ material : ratchet.RatchetMaterial,
    pending.material = ok (core.option.Option.Some material) ∧
    opened = idealOpenReply cr material ad ciphertext

theorem OpenReplyRefines.some_implies_ideal_decryption
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (pending : ratchet.concrete.ReceiveOpen Context) (ad : AD) (ciphertext : CT)
    (plaintext : PT)
    (h : OpenReplyRefines cr pending ad ciphertext
      (core.option.Option.Some plaintext)) :
    ∃ material, pending.material = ok (core.option.Option.Some material) ∧
      cr.dec material ad ciphertext = some plaintext := by
  obtain ⟨material, hpending, hopened⟩ := h
  refine ⟨material, hpending, ?_⟩
  cases hdec : cr.dec material ad ciphertext with
  | none => simp [idealOpenReply, hdec] at hopened
  | some opened =>
      simp [idealOpenReply, hdec] at hopened
      exact congrArg some hopened.symm

/-- The invariant carried by a cached-key open phase.  It identifies the concrete live
slot with the exact ideal skipped key selected by `List.lookup`. -/
def CachedOpenRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ) (material : ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context) : Prop :=
  ∃ (prepared : ratchet.refined.PreparedCachedReceive)
      (cached : ratchet.refined.CachedReceiveKey ratchet.RatchetMaterial),
    pending.prepared =
        ratchet.refined.PreparedReceive.PreparedReceiveCachedCase prepared ∧
    ratchet.refined.prepare_cached_receive pending.entry.refined prepared.sequence =
      ok (core.option.Option.Some prepared) ∧
    prepared.last_slot.val =
      pending.entry.refined.control.receive_cache.len.val - 1 ∧
    ratchet.control.finish_receive_with_removal pending.entry.refined.control
        prepared.sequence prepared.target_slot true =
      ok {
        state := prepared.committed_control,
        disposition := ratchet.control.ReceiveDisposition.Consumed,
        removal := core.option.Option.Some {
          target_slot := prepared.target_slot,
          last_slot := prepared.last_slot
        }
      } ∧
    KernelRefines cr receiveOrigin send receive pending.entry ∧
    List.lookup index receive.skipped = some material ∧
    prepared.sequence.val = index + 1 ∧
    prepared.target_slot.val < pending.entry.refined.control.receive_cache.len.val ∧
    pending.entry.refined.receive_slots.val[prepared.target_slot.val]! =
      core.option.Option.Some cached ∧
    cached.sequence = pending.entry.refined.control.receive_cache.entries.val[
      prepared.target_slot.val]! ∧
    cached.sequence = prepared.sequence ∧ cached.material = material

/-- A cached ideal key determines an exact generated cached-open request.  In
particular, the prepared value is not supplied by the interpreter: it is the value
returned by the extracted `prepare_cached_receive` implementation. -/
theorem begin_receive_cached_refines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : Context)
    (target : Std.U64) (index : ℕ) (material : ratchet.RatchetMaterial)
    (hkernel : KernelRefines cr receiveOrigin send receive kernel)
    (htarget : target.val = index + 1)
    (hlookup : List.lookup index receive.skipped = some material) :
    ∃ pending : ratchet.concrete.ReceiveOpen Context,
      ratchet.concrete.begin_receive kernel target context =
        ok (ratchet.concrete.ReceiveEffect.ReceiveOpenRequested pending) ∧
      CachedOpenRefines cr receiveOrigin send receive index material pending := by
  have hmem : (index, material) ∈ receive.skipped :=
    ratchet.control.mem_of_lookup_eq_some hlookup
  have hindexLt : index < receive.n := hkernel.receiveControl.keys_lt _ hmem
  have htargetLe : target.val ≤ kernel.refined.control.receive_sequence.val := by
    rw [htarget, hkernel.receiveControl.seq]
    omega
  have hplan := ratchet.control.plan_receive_until_replay
    kernel.refined.control target htargetLe
  have htargetMem : target.val ∈
      ratchet.control.cacheSeqs kernel.refined.control.receive_cache :=
    hkernel.receiveControl.cache.mem_iff.2
      (List.mem_map.2 ⟨(index, material), hmem, by simp only []; omega⟩)
  obtain ⟨targetSlot, hfind, htargetSlot, htargetEntry⟩ :=
    ratchet.control.lookup_receive_key_of_mem kernel.refined.control target
      hkernel.receiveControl.wf htargetMem
  obtain ⟨⟨storedIndex, storedMaterial⟩, cached, hstored, htargetCached,
      hcachedSequence, hcachedSequenceVal, hcachedMaterial⟩ :=
    hkernel.slotSound targetSlot.val htargetSlot
  have hcachedSequenceTarget : cached.sequence = target :=
    hcachedSequence.trans htargetEntry
  have hstoredIndex : storedIndex = index := by
    rw [hcachedSequenceTarget, htarget] at hcachedSequenceVal
    omega
  have hstoredMaterial : storedMaterial = material := by
    have hstoredKey := hkernel.receiveControl.keys (storedIndex, storedMaterial) hstored
    have htargetKey := hkernel.receiveControl.keys (index, material) hmem
    rw [hstoredIndex] at hstoredKey
    exact hstoredKey.trans htargetKey.symm
  have hcachedMaterialExact : cached.material = material :=
    hcachedMaterial.trans hstoredMaterial
  have hlenPositive : 1 ≤ kernel.refined.control.receive_cache.len.val := by omega
  obtain ⟨lastSlot, hlastSub, hlastSlotVal⟩ :=
    ratchet.control.uscalar_sub_eq_ok kernel.refined.control.receive_cache.len 1#u8
      (by scalar_tac)
  have hlastSlotLt : lastSlot.val <
      kernel.refined.control.receive_cache.len.val := by
    have hlastSlotVal' : lastSlot.val =
        kernel.refined.control.receive_cache.len.val - 1 := by
      simpa using hlastSlotVal
    omega
  obtain ⟨lastPair, lastCached, hlastStored, hlastCached,
      hlastCachedSequence, hlastCachedSequenceVal, hlastCachedMaterial⟩ :=
    hkernel.slotSound lastSlot.val hlastSlotLt
  have htargetSlot50 : targetSlot.val < 50 := by
    have hwf := hkernel.receiveControl.wf
    simp only [ratchet.control.RatchetState.Wf,
      ratchet.control.SequenceCache.Wf] at hwf
    omega
  have hlastSlot50 : lastSlot.val < 50 := by
    have hwf := hkernel.receiveControl.wf
    simp only [ratchet.control.RatchetState.Wf,
      ratchet.control.SequenceCache.Wf] at hwf
    omega
  have htargetEntryBound : targetSlot.val <
      kernel.refined.control.receive_cache.entries.val.length := by
    simpa using htargetSlot50
  have htargetEntryGet := htargetEntry
  rw [List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem htargetEntryBound] at htargetEntryGet
  have htargetEntryGet' :
      kernel.refined.control.receive_cache.entries.val[targetSlot.val] = target := by
    simpa using htargetEntryGet
  have hlastEntryBound : lastSlot.val <
      kernel.refined.control.receive_cache.entries.val.length := by
    simpa using hlastSlot50
  have hlastCachedSequenceGet := hlastCachedSequence
  rw [List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem hlastEntryBound] at hlastCachedSequenceGet
  have hlastCachedSequenceGet' : lastCached.sequence =
      kernel.refined.control.receive_cache.entries.val[lastSlot.val] := by
    simpa using hlastCachedSequenceGet
  have htargetReceiveKey :
      ratchet.control.RatchetState.receive_key_at kernel.refined.control targetSlot =
        ok (core.option.Option.Some target) := by
    simp [ratchet.control.RatchetState.receive_key_at,
      ratchet.control.SequenceCache.entry, lift,
      ratchet.control.capacity_eq_ok, htargetSlot, htargetSlot50,
      ratchet.control.entries_index_eq_ok]
    exact htargetEntryGet'
  have hlastReceiveKey :
      ratchet.control.RatchetState.receive_key_at kernel.refined.control lastSlot =
        ok (core.option.Option.Some
          kernel.refined.control.receive_cache.entries.val[lastSlot.val]!) := by
    simp [ratchet.control.RatchetState.receive_key_at,
      ratchet.control.SequenceCache.entry, lift,
      ratchet.control.capacity_eq_ok, hlastSlotLt, hlastSlot50,
      ratchet.control.entries_index_eq_ok]
  have htargetArrayRead :
      Array.index_usize kernel.refined.receive_slots
          (UScalar.cast UScalarTy.Usize targetSlot) =
        ok (core.option.Option.Some cached) := by
    have htargetSlotsBound : targetSlot.val <
        kernel.refined.receive_slots.val.length := by
      simpa using htargetSlot50
    have htargetCachedGet := htargetCached
    rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem htargetSlotsBound] at htargetCachedGet
    rw [ratchet.control.array_index_eq_ok]
    · simpa using htargetCachedGet
    · simp_scalar
  have hlastArrayRead :
      Array.index_usize kernel.refined.receive_slots
          (UScalar.cast UScalarTy.Usize lastSlot) =
        ok (core.option.Option.Some lastCached) := by
    have hlastSlotsBound : lastSlot.val <
        kernel.refined.receive_slots.val.length := by
      simpa using hlastSlot50
    have hlastCachedGet := hlastCached
    rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hlastSlotsBound] at hlastCachedGet
    rw [ratchet.control.array_index_eq_ok]
    · simpa using hlastCachedGet
    · simp_scalar
  obtain ⟨finished, hfinish, hdisposition, hfinishedLen, hfinishedSend,
      hfinishedReceive, hremoval, hfinishedEntries⟩ :=
    ratchet.control.finish_receive_consumed kernel.refined.control target targetSlot
      hkernel.receiveControl.wf htargetSlot htargetEntry
  have hfinishedLast : finished.state.receive_cache.len = lastSlot := by
    apply UScalar.eq_of_val_eq
    rw [hfinishedLen]
    simpa using hlastSlotVal.symm
  have hremoval' : finished.removal = core.option.Option.Some
      { target_slot := targetSlot, last_slot := lastSlot } := by
    simpa only [hfinishedLast] using hremoval
  let prepared : ratchet.refined.PreparedCachedReceive := {
    sequence := target
    target_slot := targetSlot
    last_slot := lastSlot
    committed_control := finished.state
  }
  have hprepared : ratchet.refined.prepare_cached_receive kernel.refined target =
      ok (core.option.Option.Some prepared) := by
    have htargetNot50 : ¬50 ≤ targetSlot.val := by omega
    have hlastNot50 : ¬50 ≤ lastSlot.val := by omega
    have hlenNe : kernel.refined.control.receive_cache.len ≠ 0#u8 := by
      intro hzero
      have hzeroVal : kernel.refined.control.receive_cache.len.val = 0 := by
        simpa using congrArg UScalar.val hzero
      omega
    simp [ratchet.refined.prepare_cached_receive, hfind, lift,
      ratchet.control.capacity_eq_ok, htargetNot50, htargetReceiveKey,
      htargetArrayRead,
      ratchet.control.RatchetState.receive_cache_len, hlenNe,
      hlastSub, hlastNot50, hlastReceiveKey, hlastArrayRead,
      hfinish, hdisposition, hremoval', hcachedSequenceTarget,
      hlastCachedSequence, List.getElem!_eq_getElem?_getD,
      core.option.Option.as_ref,
      core.option.Option.Insts.CoreCmpPartialEqOption.eq,
      core.U64.Insts.CoreCmpPartialEqU64, prepared]
  have hbegin := ratchet.concrete.begin_receive_cached_exact kernel target target context
    prepared hplan hprepared
  have hpreparedLast : prepared.last_slot.val =
      kernel.refined.control.receive_cache.len.val - 1 := by
    simpa [prepared] using hlastSlotVal
  have hpreparedFinish : ratchet.control.finish_receive_with_removal
      kernel.refined.control prepared.sequence prepared.target_slot true =
      ok {
        state := prepared.committed_control,
        disposition := ratchet.control.ReceiveDisposition.Consumed,
        removal := core.option.Option.Some {
          target_slot := prepared.target_slot,
          last_slot := prepared.last_slot
        }
      } := by
    simp only [prepared]
    rw [hfinish]
    cases finished with
    | mk finishedState finishedDisposition finishedRemoval =>
        simp only at hdisposition hremoval' ⊢
        rw [hdisposition, hremoval']
  refine ⟨{
      entry := kernel,
      context := context,
      prepared := ratchet.refined.PreparedReceive.PreparedReceiveCachedCase prepared
    }, hbegin, ?_⟩
  refine ⟨prepared, cached, rfl, hprepared, hpreparedLast, hpreparedFinish,
    hkernel, hlookup, ?_, htargetSlot,
    htargetCached, hcachedSequence, ?_, hcachedMaterialExact⟩
  · exact htarget
  · exact hcachedSequenceTarget

theorem CachedOpenRefines.material_exact
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ) (material : ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context)
    (h : CachedOpenRefines cr receiveOrigin send receive index material pending) :
    pending.material = ok (core.option.Option.Some material) := by
  obtain ⟨prepared, cached, hphase, hprepared, hlast, hfinish, hkernel, hlookup,
    hsequence, hslot,
    hcached, hcachedControlSequence, hcachedSequence, hcachedMaterial⟩ := h
  have hslot50 : prepared.target_slot.val < 50 := by
    have hwf := hkernel.receiveControl.wf
    simp only [ratchet.control.RatchetState.Wf, ratchet.control.SequenceCache.Wf] at hwf
    omega
  have hlen : prepared.target_slot.val <
      pending.entry.refined.receive_slots.val.length := by
    simpa using hslot50
  have hcached' :
      pending.entry.refined.receive_slots.val[prepared.target_slot.val]'hlen =
      core.option.Option.Some cached := by
    rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem hlen] at hcached
    simpa using hcached
  simp [ratchet.concrete.ReceiveOpen.material, hphase,
    ratchet.control.RECEIVE_CACHE_CAPACITY, lift, Array.index_usize,
    core.option.Option.as_ref, hslot50, hcached', hcachedSequence, hcachedMaterial]

theorem CachedOpenRefines.openReply_some
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ) (material : ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context)
    (h : CachedOpenRefines cr receiveOrigin send receive index material pending)
    (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hdecrypt : cr.dec material ad ciphertext = some plaintext) :
    OpenReplyRefines cr pending ad ciphertext
      (core.option.Option.Some plaintext) := by
  refine ⟨material, h.material_exact, ?_⟩
  simp [idealOpenReply, hdecrypt]

/-- Cached-key success agrees directly with the handwritten receive step. -/
theorem CachedOpenRefines.ideal_success
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ) (material : ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context)
    (h : CachedOpenRefines cr receiveOrigin send receive index material pending)
    (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hdecrypt : cr.dec material ad ciphertext = some plaintext) :
    Ratchet.recvStep cr receive ad ⟨index, ciphertext⟩ =
      (.ok plaintext,
        { receive with
          skipped := receive.skipped.filter (fun p => !(p.1 == index)) }) := by
  obtain ⟨prepared, cached, hphase, hprepared, hlast, hfinish, hkernel, hlookup,
    hsequence, hslot,
    hcached, hcachedControlSequence, hcachedSequence, hcachedMaterial⟩ := h
  simp [Ratchet.recvStep, hlookup, hdecrypt]

/-- The remaining publication obligation for cached success, stated separately from
the cryptographic reply: swap-removing the live material slot must re-establish the
full `KernelRefines` relation for the ideal filtered skipped-key store. -/
def CachedPublicationRefines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain
      ratchet.RatchetChain ratchet.RatchetMaterial) : Prop :=
  KernelRefines cr receiveOrigin send
    { receive with
      skipped := receive.skipped.filter (fun p => !(p.1 == index)) }
    { refined := published }

/-- Consuming one live control-cache entry refines filtering the corresponding ideal
skipped key.  This is the control-plane half of cached publication; the material-array
swap is handled separately below. -/
theorem ratchet.control.Refines.finish_receive_with_removal_consumed_refines
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (state : ratchet.control.RatchetState)
    (h : ratchet.control.Refines cr receiveOrigin receive state)
    (target : Std.U64) (index : ℕ) (slot : Std.U8)
    (htarget : target.val = index + 1)
    (hslot : slot.val < state.receive_cache.len.val)
    (hentry : state.receive_cache.entries.val[slot.val]! = target)
    (finished : ratchet.control.ReceiveFinishWithRemoval)
    (hfinish : ratchet.control.finish_receive_with_removal state target slot true =
      ok finished) :
    ratchet.control.Refines cr receiveOrigin
      { receive with
        skipped := receive.skipped.filter (fun p => !(p.1 == index)) }
      finished.state := by
  obtain ⟨result, hresult, hdisposition, hsend, hreceive, hlen, hperm⟩ :=
    ratchet.control.finish_receive_consumed_cacheSeqs state target slot h.wf hslot hentry
  have hresult' : ratchet.control.finish_receive state target slot true =
      ok { state := finished.state, disposition := finished.disposition } := by
    simp [ratchet.control.finish_receive, hfinish]
  rw [hresult'] at hresult
  have hstate : result.state = finished.state := by
    simpa using congrArg (fun value => value.state) (Result.ok.inj hresult.symm)
  rw [hstate] at hsend hreceive hlen hperm
  refine ⟨?_, ?_, h.lt, h.chain, ?_, ?_, ?_, ?_⟩
  · show finished.state.receive_cache.len.val ≤ 50
    have hwf := h.wf
    simp only [ratchet.control.RatchetState.Wf,
      ratchet.control.SequenceCache.Wf] at hwf
    omega
  · rw [hreceive]
    exact h.seq
  · intro p hp
    exact h.keys p (List.mem_of_mem_filter hp)
  · intro p hp
    exact h.keys_lt p (List.mem_of_mem_filter hp)
  · exact h.nodup.sublist (List.Sublist.map _ List.filter_sublist)
  · rw [ratchet.control.filter_map_eq_erase receive.skipped index h.nodup, ← htarget]
    exact hperm.trans (List.Perm.erase target.val h.cache)

/-- Genuine (unconditional on the post-state relation) cached success result: the
production phase publishes the supplied refined state and returns the same plaintext,
while the ideal step delivers that plaintext and removes the skipped key. -/
theorem CachedOpenRefines.finish_success_matches_ideal
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ) (material : ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context)
    (h : CachedOpenRefines cr receiveOrigin send receive index material pending)
    (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hdecrypt : cr.dec material ad ciphertext = some plaintext)
    (prepared : ratchet.refined.PreparedCachedReceive)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain
      ratchet.RatchetChain ratchet.RatchetMaterial)
    (hphase : pending.prepared =
      ratchet.refined.PreparedReceive.PreparedReceiveCachedCase prepared)
    (hpublish : ratchet.refined.publish_cached_receive pending.entry.refined prepared =
      ok published) :
    pending.finish (core.option.Option.Some plaintext) =
        ok ({ refined := published }, core.option.Option.Some plaintext) ∧
      Ratchet.recvStep cr receive ad ⟨index, ciphertext⟩ =
        (.ok plaintext,
          { receive with
            skipped := receive.skipped.filter (fun p => !(p.1 == index)) }) := by
  constructor
  · simp [ratchet.concrete.ReceiveOpen.finish, hphase, hpublish]
  · exact CachedOpenRefines.ideal_success cr receiveOrigin send receive index material
      pending h ad ciphertext plaintext hdecrypt

/-- Conditional capstone for cached receive success.  All cryptographic and ideal-step
facts are proved here; `hpublication` is exactly the isolated array swap-remove
invariant that a subsequent proof must discharge. -/
theorem CachedOpenRefines.finish_success_refines_of_publication
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (receiveOrigin : ratchet.RatchetChain)
    (send : Ratchet.SendState ratchet.RatchetChain)
    (receive : Ratchet.RecvState ratchet.RatchetChain ratchet.RatchetMaterial)
    (index : ℕ) (material : ratchet.RatchetMaterial)
    (pending : ratchet.concrete.ReceiveOpen Context)
    (h : CachedOpenRefines cr receiveOrigin send receive index material pending)
    (ad : AD) (ciphertext : CT) (plaintext : PT)
    (hdecrypt : cr.dec material ad ciphertext = some plaintext)
    (prepared : ratchet.refined.PreparedCachedReceive)
    (published : ratchet.refined.RefinedRatchet ratchet.RatchetChain
      ratchet.RatchetChain ratchet.RatchetMaterial)
    (hphase : pending.prepared =
      ratchet.refined.PreparedReceive.PreparedReceiveCachedCase prepared)
    (hpublish : ratchet.refined.publish_cached_receive pending.entry.refined prepared =
      ok published)
    (hpublication : CachedPublicationRefines cr receiveOrigin send receive index published) :
    pending.finish (core.option.Option.Some plaintext) =
        ok ({ refined := published }, core.option.Option.Some plaintext) ∧
      Ratchet.recvStep cr receive ad ⟨index, ciphertext⟩ =
        (.ok plaintext,
          { receive with
            skipped := receive.skipped.filter (fun p => !(p.1 == index)) }) ∧
      KernelRefines cr receiveOrigin send
        { receive with
          skipped := receive.skipped.filter (fun p => !(p.1 == index)) }
        { refined := published } := by
  obtain ⟨hfinish, hideal⟩ :=
    CachedOpenRefines.finish_success_matches_ideal cr receiveOrigin send receive index
      material pending h ad ciphertext plaintext hdecrypt prepared published hphase hpublish
  exact ⟨hfinish, hideal, hpublication⟩

end beaconcrypt_core.ratchet.concrete

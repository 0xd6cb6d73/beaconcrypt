import BeaconcryptCore.Refinement.RatchetStructural
import BeaconcryptCore.Refinement.RatchetRoleReachability

/-! Complete send operations preserve structural validity without canonical chain or material assumptions. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.control

/-- Structural receive validity is independent of the sending counter. -/
theorem ValidControl.of_receive_eq {state : RatchetState} (h : ValidControl state)
    (other : RatchetState) (hsequence : other.receive_sequence = state.receive_sequence)
    (hcache : other.receive_cache = state.receive_cache) : ValidControl other := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [RatchetState.Wf, SequenceCache.Wf, hcache] using h.capacity
  · simpa only [hcache] using h.positive
  · simpa only [hsequence, hcache] using h.past
  · simpa only [hcache] using h.unique

end beaconcrypt_core.ratchet.control

namespace beaconcrypt_core.ratchet.refined

/-- Replacing send data while preserving receive control preserves structural validity. -/
theorem ValidRefined.send_update {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material) (h : ValidRefined state)
    (control : ratchet.control.RatchetState) (sendChain : SendChain)
    (hsequence : control.receive_sequence = state.control.receive_sequence)
    (hcache : control.receive_cache = state.control.receive_cache) :
    ValidRefined { state with control, send_chain := sendChain } := by
  exact ⟨h.control.of_receive_eq control hsequence hcache, by simpa only [hcache] using h.slots⟩

end beaconcrypt_core.ratchet.refined

namespace beaconcrypt_core.ratchet.concrete

/-- Admitted send phases retain all receive control and the original entry kernel. -/
theorem begin_send_receive_structure {Context : Type}
    (entry : ConcreteRatchetKernel) (context : Context)
    (hmax : entry.refined.control.send_sequence ≠ core.num.U64.MAX) :
    ∃ pending : SendKdf Context, begin_send entry context = ok (SendStart.SendKdfRequested pending) ∧
      pending.entry = entry ∧
      pending.committed_control.receive_sequence = entry.refined.control.receive_sequence ∧
      pending.committed_control.receive_cache = entry.refined.control.receive_cache := by
  obtain ⟨advanced, hadvance, _, hreceive, hcache, hsequence, hkey⟩ := ratchet.control.advance_send_ok entry.refined.control hmax
  let pending : SendKdf Context := {
    entry, context, committed_control := advanced.state, logical := advanced.key,
    sequence := advanced.state.send_sequence,
    request := { input := entry.refined.send_chain.bytes, info := ratchet.SYM_RATCHET_INFO }
  }
  refine ⟨pending, ?_, rfl, hreceive, hcache⟩
  simp [begin_send, hadvance, hsequence, hkey, ratchet.control.SendKey.impl.sequence,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
    ratchet.control.RatchetState.impl.send_sequence, ratchet.RatchetChain.as_bytes,
    ratchet.SymmetricRatchetKdfRequest.new, pending]

/-- Every complete send preserves structural validity for arbitrary chains, material bytes, and optional seal results. -/
theorem sealNext_preserves_validity {Context Output : Type} (execute : KdfInterpreter)
    (entry : ConcreteRatchetKernel) (context : Context)
    (sealReply : ratchet.RatchetMaterial → Std.U64 → Context → core.option.Option Output)
    (h : ratchet.refined.ValidRefined entry.refined) :
    ∃ next output, sealNext execute entry context sealReply = ok (next, output) ∧
      ratchet.refined.ValidRefined next.refined := by
  by_cases hmax : entry.refined.control.send_sequence = core.num.U64.MAX
  · exact ⟨entry, .None, by simp [sealNext, begin_send_exhausted_restores_entry entry context hmax], h⟩
  · obtain ⟨pending, hbegin, hentry, hsequence, hcache⟩ := begin_send_receive_structure entry context hmax
    obtain ⟨stepped, hstep⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok (execute pending.request)
    have hresume := pending.resume_exact (execute pending.request) stepped hstep
    let ready : SendSeal Context := {
      advanced := { refined := { entry.refined with control := pending.committed_control, send_chain := stepped.chain } },
      context := pending.context, logical := pending.logical, sequence := pending.sequence, material := stepped.material
    }
    have hresume' : pending.resume (execute pending.request) = ok ready := by simpa only [hentry] using hresume
    exact ⟨ready.advanced, sealReply ready.material ready.sequence ready.context,
      by simp only [sealNext, hbegin, bind_tc_ok, hresume', SendSeal.finish_returns_interpreter_result],
      h.send_update entry.refined pending.committed_control stepped.chain hsequence hcache⟩

end beaconcrypt_core.ratchet.concrete

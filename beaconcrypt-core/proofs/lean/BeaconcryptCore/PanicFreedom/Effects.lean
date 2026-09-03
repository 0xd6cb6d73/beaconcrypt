import BeaconcryptCore.Refinement.RatchetEffect
import BeaconcryptCore.PanicFreedom.Bytes
import BeaconcryptCore.PanicFreedom.Control

/-! Totality of the production ratchet effect API. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM

set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

theorem begin_send_total {Context : Type}
    (kernel : ConcreteRatchetKernel) (context : Context) :
    ∃ result, begin_send kernel context = ok result := by
  by_cases hmax : kernel.refined.control.send_sequence = core.num.U64.MAX
  · exact ⟨_, begin_send_exhausted_restores_entry kernel context hmax⟩
  · obtain ⟨pending, hbegin, _⟩ := begin_send_nonexhausted_exact kernel context hmax
    exact ⟨_, hbegin⟩

theorem ReceiveOpen.sequence_total {Context : Type} (pending : ReceiveOpen Context) :
    ∃ result, pending.sequence = ok result := by
  cases hprepared : pending.prepared <;> simp [ReceiveOpen.sequence, hprepared]

theorem ReceiveOpen.material_total {Context : Type} (pending : ReceiveOpen Context) :
    ∃ result, pending.material = ok result := by
  cases hprepared : pending.prepared <;>
    simp only [ReceiveOpen.material, hprepared, lift, control.capacity_eq_ok, bind_tc_ok]
  case PreparedReceiveCachedCase prepared =>
    split
    · exact ⟨_, rfl⟩
    · rw [control.array_index_eq_ok _ _ (by scalar_tac)]
      simp only [bind_tc_ok, core.option.Option.as_ref]
      split <;> simp_all only [bind_tc_ok]
      all_goals first | exact ⟨_, rfl⟩ | split <;> exact ⟨_, rfl⟩
  case PreparedReceiveFutureCase future =>
    exact ⟨_, rfl⟩

theorem SendKdf.resume_total {Context : Type} (pending : SendKdf Context)
    (response : RatchetKdfResponse) : ∃ result, pending.resume response = ok result := by
  obtain ⟨stepped, hstep⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
  exact ⟨_, SendKdf.resume_exact pending response stepped hstep⟩

end beaconcrypt_core.ratchet.concrete

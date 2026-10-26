-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RawCtxOwnerOracle
import BeaconcryptCore.Refinement.RecordEffectsComposition
import BeaconcryptCore.PanicFreedom.Record

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RecordEffectsReceiveRank

/-- Only KDF phases recurse; the extracted continuation counter supplies the rank. -/
def rank : record_effects.RecordReceiveEffect → Nat
  | .KdfRequested pending => effectDepth (.ReceiveKdfRequested pending.pending)
  | _ => 0

theorem normalize_rank (effect : ReceiveEffect record.OpenFrameContext)
    (next : record_effects.RecordReceiveEffect)
    (h : record_effects.normalize_receive effect = ok next) : rank next = effectDepth effect := by
  cases effect with
  | ReceiveOpenRequested opening =>
      obtain ⟨start, run⟩ := BeaconcryptCore.PanicFreedom.Record.begin_total opening
      simp only [record_effects.normalize_receive, run, bind_tc_ok] at h
      cases start <;> cases h <;> rfl
  | ReceiveRejected => cases h; rfl
  | ReceiveKdfRequested => cases h; rfl

theorem resume_decreasing (pending : record_effects.RecordReceiveKdf)
    (response : RatchetKdfResponse) (next : record_effects.RecordReceiveEffect)
    (h : pending.resume response = ok next) : rank next < rank (.KdfRequested pending) := by
  have normalized : record_effects.normalize_receive
      (RawCtxOwnerOracle.resume pending.pending response) = ok next := by
    simpa only [record_effects.RecordReceiveKdf.resume,
      RawCtxOwnerOracle.resume_exact, bind_tc_ok] using h
  rw [normalize_rank _ _ normalized]
  exact RawCtxOwnerOracle.resume_rank pending.pending response


end BeaconcryptCore.Computational.RecordEffectsReceiveRank

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveRank.normalize_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveRank.normalize_rank

/-- info: 'BeaconcryptCore.Computational.RecordEffectsReceiveRank.resume_decreasing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RecordEffectsReceiveRank.resume_decreasing

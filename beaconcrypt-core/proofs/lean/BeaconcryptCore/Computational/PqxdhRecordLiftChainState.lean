-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftSeed
import BeaconcryptCore.Computational.PqxdhFirstRecordReplay

/-! Ghost coordinates follow the actual extracted send and receive callbacks. This module adds no cryptographic premise and does not yet connect a dynamic world or a hidden-key interpreter. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainState

structure Coordinate (Slot : Type) where
  slot : Slot
  direction : Bool
  position : Nat
  deriving DecidableEq

def advance {Slot : Type} (coordinate : Coordinate Slot) (count : Nat) : Coordinate Slot :=
  { coordinate with position := coordinate.position + count }

variable {Slot Material Context : Type}
abbrev Kernel (Slot Material : Type) := RefinedRatchet (Coordinate Slot) (Coordinate Slot) Material

/-- The original rollback entry and context survive every callback; the next request counts exactly the source's staged skipped keys. -/
def Tracked (entry : Kernel Slot Material) (context : Context) :
    RawCtxChainReceive.Effect (Coordinate Slot) (Coordinate Slot) Material Context → Prop
  | .rejected original prior => original = entry ∧ prior = context
  | .kdfRequested pending => pending.entry = entry ∧ pending.context = context ∧
      pending.request = advance entry.receive_chain pending.skipped.val
  | .openRequested opening => opening.entry = entry ∧ opening.context = context ∧
      match opening.prepared with
      | .PreparedReceiveCachedCase _ => True
      | .PreparedReceiveFutureCase pending =>
          pending.final_receive_chain = advance entry.receive_chain (pending.skipped.val + 1)

/-- The callback returns the successor coordinate; source control decides whether to stage it, open, or discard it. -/
theorem resume_tracked (entry : Kernel Slot Material) (context : Context)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) Material Context)
    (material : Material) (tracked : Tracked entry context (.kdfRequested pending)) :
    Tracked entry context (RawCtxChainReceive.normalResume pending
      (advance pending.request 1, material)) := by
  obtain ⟨original, prior, request⟩ := tracked
  have run := RawCtxChainReceive.normalResume_exact pending (advance pending.request 1, material)
  generalize RawCtxChainReceive.normalResume pending (advance pending.request 1, material) = effect at run ⊢
  unfold RawCtxChainReceive.resume at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals simp only [RawCtxChainReceive.rejected, RustM.ok.injEq] at run
  all_goals subst effect
  all_goals simp only [Tracked, original, prior, true_and]
  all_goals cases RustM.ok.inj (show ok (advance pending.request 1, material) = ok _ from by assumption)
  all_goals simp only [request, advance, Nat.add_assoc]
  have bump := UScalar.add_equiv pending.skipped 1#u8
  rw [show pending.skipped + 1#u8 = ok _ from by assumption] at bump
  rw [bump.2.1]
  simp only [show (1#u8).val = 1 from by scalar_tac]

/-- Every actual admission starts at the entry's coordinate, including cached and rejected paths. -/
theorem begin_tracked (entry : Kernel Slot Material) (context : Context) (target : Std.U64) :
    Tracked entry context (RawCtxChainReceive.normalBegin entry target context) := by
  have run := RawCtxChainReceive.normalBegin_exact entry target context
  generalize RawCtxChainReceive.normalBegin entry target context = effect at run ⊢
  unfold RawCtxChainReceive.beginReceive at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals simp only [RawCtxChainReceive.rejected, RustM.ok.injEq] at run
  all_goals subst effect
  all_goals simp [Tracked, advance, show (0#u8).val = 0 from by scalar_tac]

/-- Chain positions name the source's already-derived sequences, not an independent cursor. -/
def Aligned (kernel : Kernel Slot Material) : Prop :=
  kernel.send_chain.position = kernel.control.send_sequence.val ∧
    kernel.receive_chain.position = kernel.control.receive_sequence.val

/-- At every admitted skip callback the coordinate agrees with the source's actual working receive counter. -/
theorem request_sequence (entry : Kernel Slot Material) (context : Context) (target : Std.U64)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) Material Context)
    (aligned : Aligned entry) (tracked : Tracked entry context (.kdfRequested pending))
    (admitted : PqxdhFirstRecordReplay.Admitted entry target (.kdfRequested pending)) :
    pending.request.position = pending.working_control.receive_sequence.val := by
  simpa only [tracked.2.2, advance, aligned.2] using admitted.2.2.2.2.sequence.symm

/-- The final future-chain coordinate matches the committed source counter, not the number of receive attempts. -/
theorem future_sequence (entry : Kernel Slot Material) (context : Context) (target : Std.U64)
    (pending : PendingReceive (Coordinate Slot) Material) (aligned : Aligned entry)
    (tracked : Tracked entry context (.openRequested ⟨entry, context, .PreparedReceiveFutureCase pending⟩))
    (prepared : PqxdhFirstRecordReplay.Prepared entry target (.PreparedReceiveFutureCase pending)) :
    pending.final_receive_chain.position = pending.committed_control.receive_sequence.val := by
  have chain : pending.final_receive_chain = advance entry.receive_chain (pending.skipped.val + 1) := tracked.2.2
  simpa only [chain, advance, aligned.2, prepared.2.2.1, Nat.add_assoc] using prepared.2.2.2.1.symm

/-- A failed commitment/opening restores the entire original labeled kernel, including every cached material. -/
theorem failed_open {Plaintext : Type} (entry : Kernel Slot Material) (context : Context)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) Material Context)
    (tracked : Tracked entry context (.openRequested opening)) :
    RawCtxChainReceive.normalFinish opening (.None : core.option.Option Plaintext) = (entry, .None) := by
  rw [PqxdhFirstRecordReplay.finish_none, tracked.1]

/-- Retrying after a failed opening starts the identical source admission and coordinate, without rolling back an external table. -/
theorem failed_open_retry {Plaintext : Type} (entry : Kernel Slot Material) (context : Context)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) Material Context)
    (tracked : Tracked entry context (.openRequested opening)) (target : Std.U64) :
    RawCtxChainReceive.normalBegin
      (RawCtxChainReceive.normalFinish opening (.None : core.option.Option Plaintext)).1 target context =
      RawCtxChainReceive.normalBegin entry target context := by
  rw [failed_open entry context opening tracked]

def SendTracked (entry : Kernel Slot Material) (context : Context) :
    RawCtxChainSend.Start (Coordinate Slot) (Coordinate Slot) Material Context → Prop
  | .exhausted original prior => original = entry ∧ prior = context
  | .requested pending => pending.entry = entry ∧ pending.context = context ∧
      pending.request = entry.send_chain ∧
      pending.committed_control.send_sequence.val = entry.control.send_sequence.val + 1 ∧
      pending.committed_control.receive_sequence = entry.control.receive_sequence ∧
      pending.committed_control.receive_cache = entry.control.receive_cache

/-- Actual send admission preserves both receive coordinates and starts the next send coordinate. -/
theorem send_begin_tracked (entry : Kernel Slot Material) (context : Context) :
    SendTracked entry context (RawCtxChainSend.normalBegin entry context) := by
  have run := RawCtxChainSend.normalBegin_exact entry context
  generalize RawCtxChainSend.normalBegin entry context = start at run ⊢
  unfold RawCtxChainSend.beginSend at run
  by_cases top : entry.control.send_sequence = core.num.U64.MAX
  case pos =>
    simp only [control.advance_send_max entry.control top, bind_tc_ok, RustM.ok.injEq] at run
    simpa only [← run, SendTracked] using (And.intro rfl rfl : entry = entry ∧ context = context)
  case neg =>
    obtain ⟨advanced, advancedEq, sendEq, receiveEq, cacheEq, yielded, _⟩ := control.advance_send_ok entry.control top
    simp only [advancedEq, bind_tc_ok, yielded] at run
    repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
    all_goals simp only [RustM.ok.injEq] at run
    all_goals subst start
    all_goals simp only [SendTracked, sendEq, receiveEq, cacheEq, and_self]

/-- A send callback updates only its source control and successor send coordinate; the full receive cache is retained. -/
theorem send_ready_kernel (entry : Kernel Slot Material) (context : Context)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) Material Context)
    (material : Material) (tracked : SendTracked entry context (.requested pending)) :
    (RawCtxChainSend.ready pending (advance pending.request 1, material)).advanced =
      { entry with control := pending.committed_control, send_chain := advance entry.send_chain 1 } := by
  simp only [RawCtxChainSend.ready, tracked.1, tracked.2.2.1]

/-- Send advancement agrees with both source counters even before a possibly failing seal callback. -/
theorem send_ready_aligned (entry : Kernel Slot Material) (context : Context)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) Material Context)
    (material : Material) (aligned : Aligned entry) (tracked : SendTracked entry context (.requested pending)) :
    Aligned (RawCtxChainSend.ready pending (advance pending.request 1, material)).advanced := by
  rw [send_ready_kernel entry context pending material tracked]
  simp only [Aligned, advance, aligned.1, aligned.2, tracked.2.2.2.1, tracked.2.2.2.2.1, and_self]

/-- Erasure uses arbitrary byte-valued chains; coordinate collisions do not require an injective map. -/
def erase (chains : Coordinate Slot → RatchetChain) (kernel : Kernel Slot RatchetMaterial) :
    ConcreteRatchetKernel := ⟨RawCtxChainInterpretation.mapChains chains chains kernel⟩

/-- Ghost coordinates erase through every actual source skip/target continuation, retaining the whole pending effect. This equality does not assert that a particular KDF backend supplies the stated reply. -/
theorem resume_erasure (chains : Coordinate Slot → RatchetChain)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (material : RatchetMaterial) :
    RawCtxInterpretedReceive.normalResume (RawCtxChainReceive.nativeKdf chains chains pending)
      (chains (advance pending.request 1), material) =
      RawCtxChainReceive.nativeEffect chains chains
        (RawCtxChainReceive.normalResume pending (advance pending.request 1, material)) := by
  exact RawCtxChainReceive.normalResume_native chains chains pending (advance pending.request 1, material)

/-- False names Server-to-Beacon; its sequence-one response is already consumed at this boundary. -/
abbrev serverLabels (slot : Slot) : RustM (Kernel Slot RatchetMaterial) :=
  RefinedRatchet.from_counters RatchetMaterial 1#u64 0#u64 ⟨slot, false, 1⟩ ⟨slot, true, 0⟩

/-- The counterpart uses exactly the same two coordinates in opposite kernel fields. -/
abbrev beaconLabels (slot : Slot) : RustM (Kernel Slot RatchetMaterial) :=
  RefinedRatchet.from_counters RatchetMaterial 0#u64 1#u64 ⟨slot, true, 0⟩ ⟨slot, false, 1⟩

/-- Erasing the two named seed coordinates gives the complete production Server seed kernel. -/
theorem server_seed_erasure (slot : Slot) (seed : PqxdhRecordLiftSeed.Seed)
    (chains : Coordinate Slot → RatchetChain)
    (left : chains ⟨slot, false, 1⟩ = RawCtxFreshChainCut.concreteChain seed.1)
    (right : chains ⟨slot, true, 0⟩ = RawCtxFreshChainCut.concreteChain seed.2) :
    erase chains <$> serverLabels slot = PqxdhRecordLiftSeed.serverKernel seed := by
  simp only [serverLabels, RefinedRatchet.from_counters, erase, RawCtxChainInterpretation.mapChains,
    PqxdhRecordLiftSeed.serverKernel, ConcreteRatchetKernel.from_counters, left, right,
    control.RatchetState.from_counters, control.SequenceCache.empty, empty_material_slots,
    bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok]

/-- Erasing those same coordinates in the counterpart orientation gives the complete production Beacon seed kernel. -/
theorem beacon_seed_erasure (slot : Slot) (seed : PqxdhRecordLiftSeed.Seed)
    (chains : Coordinate Slot → RatchetChain)
    (left : chains ⟨slot, false, 1⟩ = RawCtxFreshChainCut.concreteChain seed.1)
    (right : chains ⟨slot, true, 0⟩ = RawCtxFreshChainCut.concreteChain seed.2) :
    erase chains <$> beaconLabels slot = PqxdhRecordLiftSeed.beaconKernel seed := by
  simp only [beaconLabels, RefinedRatchet.from_counters, erase, RawCtxChainInterpretation.mapChains,
    PqxdhRecordLiftSeed.beaconKernel, ConcreteRatchetKernel.from_counters, left, right,
    control.RatchetState.from_counters, control.SequenceCache.empty, empty_material_slots,
    bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok]

/-- Both initial ghost kernels are total and already agree with the production role counters. -/
theorem seeds_aligned (slot : Slot) :
    (∃ kernel, serverLabels slot = ok kernel ∧ Aligned kernel) ∧
      (∃ kernel, beaconLabels slot = ok kernel ∧ Aligned kernel) := by
  refine ⟨⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩⟩
  all_goals exact ⟨by scalar_tac, by scalar_tac⟩

/-- Erasing coordinates reproduces the actual extracted admission, including every cache/replay/rejection decision. -/
theorem admission_erasure (chains : Coordinate Slot → RatchetChain)
    (entry : Kernel Slot RatchetMaterial) (context : Context) (target : Std.U64) :
    begin_receive (erase chains entry) target context =
      ok (RawCtxInterpretedReceive.nativeEffect (RawCtxChainReceive.nativeEffect chains chains
        (RawCtxChainReceive.normalBegin entry target context))) := by
  simp only [erase, RawCtxInterpretedReceive.native_begin, RawCtxChainReceive.native_begin,
    RawCtxChainReceive.normalBegin_exact, RawCtxMaterialInterpretation.rust_map_ok]

end BeaconcryptCore.Computational.PqxdhRecordLiftChainState

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.resume_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.resume_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.begin_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.begin_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.request_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.request_sequence
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.future_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.future_sequence
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.failed_open' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.failed_open
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.failed_open_retry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.failed_open_retry
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.send_begin_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.send_begin_tracked
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.send_ready_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.send_ready_kernel
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.send_ready_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.send_ready_aligned
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.resume_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.resume_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.server_seed_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.server_seed_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.beacon_seed_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.beacon_seed_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.seeds_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.seeds_aligned
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainState.admission_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainState.admission_erasure

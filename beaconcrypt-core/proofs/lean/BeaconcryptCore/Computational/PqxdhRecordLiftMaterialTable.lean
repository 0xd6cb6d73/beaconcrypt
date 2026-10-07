-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainTable

/-! Private material coordinates retain the same complete full76 reply as the chain coordinate. Interpretation may identify byte values; source control and tagged optional slots are unchanged. This module does not replace real HKDF or claim a global security bound. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
open PqxdhFullSecretInputKdf RawCtxMaterialInterpretation

variable {Slot Context : Type}
abbrev Label (Slot : Type) := Coordinate Slot
abbrev LabeledKernel (Slot : Type) := Kernel Slot (Label Slot)
abbrev Slots (Slot : Type) := Std.Array (core.option.Option (CachedReceiveKey (Label Slot))) 50#usize

def Present (table : Table Slot) (label : Label Slot) : Prop := ∃ output, table label = some output

def SlotsPresent (table : Table Slot) (slots : Slots Slot) : Prop :=
  ∀ cached, core.option.Option.Some cached ∈ slots.val → Present table cached.material

/-- The fallback only totalizes interpretation; present material references never use it. -/
def material (table : Table Slot) (label : Label Slot) : RatchetMaterial :=
  RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material
    ((table label).getD ⟨List.replicate 76 0, by simp⟩))

def eraseKernel (seeds : Seeds Slot) (table : Table Slot) (kernel : LabeledKernel Slot) :
    RefinedRatchet RatchetChain RatchetChain RatchetMaterial :=
  mapRefined (material table) (RawCtxChainInterpretation.mapChains (chain seeds table) (chain seeds table) kernel)

def erasePending (seeds : Seeds Slot) (table : Table Slot)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context) :
    RawCtxInterpretedReceive.Kdf RatchetMaterial Context :=
  RawCtxInterpretedReceive.mapKdf (material table)
    (RawCtxChainReceive.nativeKdf (chain seeds table) (chain seeds table) pending)

def eraseEffect (seeds : Seeds Slot) (table : Table Slot)
    (effect : RawCtxChainReceive.Effect (Label Slot) (Label Slot) (Label Slot) Context) :
    RawCtxInterpretedReceive.Effect RatchetMaterial Context :=
  RawCtxInterpretedReceive.mapEffect (material table)
    (RawCtxChainReceive.nativeEffect (chain seeds table) (chain seeds table) effect)

def PendingPresent (table : Table Slot)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context) : Prop :=
  PendingAvailable table pending ∧ SlotsPresent table pending.entry.receive_slots ∧
    SlotsPresent table pending.staged_slots

/-- Growing the persistent table preserves every already sampled key/nonce pair, including aliases. -/
theorem material_mono (before after : Table Slot) (mono : before ≤ after)
    (label : Label Slot) (present : Present before label) :
    material after label = material before label := by
  obtain ⟨output, found⟩ := present
  simp only [material, found, mono found]

/-- The entire tagged optional source array has unchanged bytes after table growth. -/
theorem slots_mono (before after : Table Slot) (mono : before ≤ after)
    (slots : Slots Slot) (present : SlotsPresent before slots) :
    mapArray (mapOption (mapCached (material after))) slots =
      mapArray (mapOption (mapCached (material before))) slots := by
  apply Subtype.ext
  apply List.map_congr_left
  rintro (_ | cached) found
  · rfl
  · simp only [mapOption, mapCached, material_mono before after mono cached.material (present cached found)]

/-- Table growth preserves the entire pending source request, entry cache, staged cache and rollback context. -/
theorem pending_mono (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (present : PendingPresent before pending) :
    erasePending seeds after pending = erasePending seeds before pending := by
  simp only [erasePending, RawCtxChainReceive.nativeKdf, RawCtxInterpretedReceive.mapKdf,
    mapRefined, RawCtxChainInterpretation.mapChains,
    chain_mono seeds before after mono pending.entry.send_chain present.1.1.1,
    chain_mono seeds before after mono pending.entry.receive_chain present.1.1.2,
    chain_mono seeds before after mono pending.request present.1.2,
    slots_mono before after mono pending.entry.receive_slots present.2.1,
    slots_mono before after mono pending.staged_slots present.2.2]

/-- One actual persistent lookup realizes the complete source callback with both chain and material labels erased. -/
theorem receive_lookup [DecidableEq Slot] (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (present : PendingPresent state.1 pending) (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    RawCtxInterpretedReceive.normalResume (erasePending seeds state.1 pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1)) =
      eraseEffect seeds result.2.1 (RawCtxChainReceive.normalResume pending
        (advance pending.request 1, pending.request)) := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  rw [← pending_mono seeds state.1 result.2.1 facts.2.1 pending present,
    RawCtxFreshChainCut.decoded_parts,
    ← successor_chain seeds result.2.1 pending.request
      (available_mono state.1 result.2.1 facts.2.1 pending.request present.1.2) result.1 facts.1]
  have stored : material result.2.1 pending.request =
      RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material result.1) := by
    simp only [material, facts.1]
    rfl
  rw [← stored, erasePending, eraseEffect, RawCtxInterpretedReceive.normalResume_map (material result.2.1) _
      (chain seeds result.2.1 (advance pending.request 1), pending.request),
    RawCtxChainReceive.normalResume_native (chain seeds result.2.1) (chain seeds result.2.1)
      pending (advance pending.request 1, pending.request)]

/-- A whole cached entry retains any supplied source property when the array is updated. -/
theorem slots_set (property : CachedReceiveKey (Label Slot) → Prop) (slots : Slots Slot)
    (good : ∀ cached, core.option.Option.Some cached ∈ slots.val → property cached)
    (index : Std.Usize) (cached : CachedReceiveKey (Label Slot)) (value : property cached) :
    ∀ found, core.option.Option.Some found ∈ (slots.set index (.Some cached)).val → property found := by
  intro found member
  rcases List.mem_or_eq_of_mem_set member with old | same
  · exact good found old
  · cases same
    exact value

/-- Successful actual source array update retains all old entry properties and the new entry's property. -/
theorem slots_update (property : CachedReceiveKey (Label Slot) → Prop) (slots : Slots Slot)
    (good : ∀ cached, core.option.Option.Some cached ∈ slots.val → property cached)
    (index : Std.Usize) (cached : CachedReceiveKey (Label Slot)) (value : property cached)
    (next : Slots Slot) (executed : Array.update slots index (.Some cached) = ok next) :
    ∀ found, core.option.Option.Some found ∈ next.val → property found := by
  simp only [Std.Array.update] at executed
  split at executed <;> cases executed
  exact slots_set property slots good index cached value

def EffectPresent (table : Table Slot) :
    RawCtxChainReceive.Effect (Label Slot) (Label Slot) (Label Slot) Context → Prop
  | .rejected entry _ => SlotsPresent table entry.receive_slots
  | .kdfRequested pending => SlotsPresent table pending.entry.receive_slots ∧ SlotsPresent table pending.staged_slots
  | .openRequested opening => SlotsPresent table opening.entry.receive_slots ∧
      match opening.prepared with
      | .PreparedReceiveCachedCase _ => True
      | .PreparedReceiveFutureCase pending =>
          SlotsPresent table pending.staged_slots ∧ Present table pending.target_material

/-- Every actual skip/target/rejection branch retains only present old or newly sampled material labels. -/
theorem resume_present (table : Table Slot)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (entry : SlotsPresent table pending.entry.receive_slots)
    (staged : SlotsPresent table pending.staged_slots) (new : Present table pending.request) :
    EffectPresent table (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) := by
  have run := RawCtxChainReceive.normalResume_exact pending (advance pending.request 1, pending.request)
  generalize RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request) = effect at run ⊢
  unfold RawCtxChainReceive.resume at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals simp only [EffectPresent, entry, true_and]
  all_goals cases RustM.ok.inj (show ok (advance pending.request 1, pending.request) = ok _ from by assumption)
  all_goals first
    | exact ⟨staged, new⟩
    | exact slots_update (fun cached => Present table cached.material) pending.staged_slots staged _ _ new _ (by assumption)

/-- Presence persists under table extension without any key-distinctness premise. -/
theorem present_mono (before after : Table Slot) (mono : before ≤ after)
    (label : Label Slot) (present : Present before label) : Present after label :=
  present.elim fun output found => ⟨output, mono found⟩

/-- Every already stored optional cache entry stays interpretable when the table grows. -/
theorem slots_present_mono (before after : Table Slot) (mono : before ≤ after)
    (slots : Slots Slot) (present : SlotsPresent before slots) : SlotsPresent after slots :=
  fun cached found => present_mono before after mono cached.material (present cached found)

/-- Actual source admission retains the original cache and starts with no invented staged labels. -/
theorem begin_present (table : Table Slot) (entry : LabeledKernel Slot)
    (present : SlotsPresent table entry.receive_slots) (target : Std.U64) (context : Context) :
    EffectPresent table (RawCtxChainReceive.normalBegin entry target context) := by
  have run := RawCtxChainReceive.normalBegin_exact entry target context
  generalize RawCtxChainReceive.normalBegin entry target context = effect at run ⊢
  unfold RawCtxChainReceive.beginReceive at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals simp only [EffectPresent, present, true_and]
  cases RustM.ok.inj (show empty_material_slots (Label Slot) = ok _ from by assumption)
  simp [SlotsPresent, Std.Array.make]

/-- Every present source slot read inherits the property's whole-array certificate. -/
theorem slots_property_get (property : CachedReceiveKey (Label Slot) → Prop) (slots : Slots Slot)
    (good : ∀ cached, core.option.Option.Some cached ∈ slots.val → property cached)
    (index : Nat) (bound : index < 50) (cached : CachedReceiveKey (Label Slot))
    (found : slots.val[index]! = core.option.Option.Some cached) : property cached := by
  have inside : index < slots.val.length := by rw [slots.property]; scalar_tac
  apply good cached
  rw [← found, getElem!_pos slots.val index inside]
  exact List.getElem_mem inside

/-- Successful future publication copies only previously certified cache or staged entries. -/
theorem future_publication (property : CachedReceiveKey (Label Slot) → Prop)
    (entry : LabeledKernel Slot) (pending : PendingReceive (Label Slot) (Label Slot))
    (prior : ∀ cached, core.option.Option.Some cached ∈ entry.receive_slots.val → property cached)
    (staged : ∀ cached, core.option.Option.Some cached ∈ pending.staged_slots.val → property cached)
    (bounded : pending.first_slot.val + pending.skipped.val ≤ 50) :
    ∃ out, publish_future_receive entry pending = ok out ∧
      ∀ cached, core.option.Option.Some cached ∈ out.receive_slots.val → property cached := by
  obtain ⟨out, executed, _, _, _, slots⟩ := publish_future_receive_exact entry pending bounded
  refine ⟨out, executed, ?_⟩
  intro cached member
  obtain ⟨index, inside, found⟩ := List.getElem_of_mem member
  have bound : index < 50 := by rw [out.receive_slots.property] at inside; scalar_tac
  have located : out.receive_slots.val[index]! = core.option.Option.Some cached := by
    simpa only [getElem!_pos out.receive_slots.val index inside] using found
  rw [slots index bound] at located
  split at located
  · exact slots_property_get property pending.staged_slots staged index bound cached located
  · exact slots_property_get property entry.receive_slots prior index bound cached located

/-- Cached publication consumes or moves complete certified entries without inventing labels. -/
theorem cached_publication (property : CachedReceiveKey (Label Slot) → Prop)
    (entry : LabeledKernel Slot) (prepared : PreparedCachedReceive)
    (prior : ∀ cached, core.option.Option.Some cached ∈ entry.receive_slots.val → property cached)
    (targetBound : prepared.target_slot.val < 50) (lastBound : prepared.last_slot.val < 50) :
    ∃ out, publish_cached_receive entry prepared = ok out ∧
      ∀ cached, core.option.Option.Some cached ∈ out.receive_slots.val → property cached := by
  obtain ⟨out, executed, _, _, _, slots⟩ := publish_cached_receive_exact entry prepared targetBound lastBound
  refine ⟨out, executed, ?_⟩
  intro cached member
  obtain ⟨index, inside, found⟩ := List.getElem_of_mem member
  have bound : index < 50 := by rw [out.receive_slots.property] at inside; scalar_tac
  have located : out.receive_slots.val[index]! = core.option.Option.Some cached := by
    simpa only [getElem!_pos out.receive_slots.val index inside] using found
  rw [slots index bound] at located
  split at located
  · cases located
  · split at located
    · exact slots_property_get property entry.receive_slots prior prepared.last_slot.val lastBound cached located
    · exact slots_property_get property entry.receive_slots prior index bound cached located

/-- A yielded source target sequence is exactly one past the old counter; exhaustion yields no sequence. -/
theorem target_sequence (working : control.RatchetState) (advanced : control.ReceiveTargetAdvance)
    (executed : control.advance_receive_target working = ok advanced) (sequence : Std.U64)
    (yielded : advanced.sequence = .Some sequence) : sequence.val = working.receive_sequence.val + 1 := by
  by_cases top : working.receive_sequence = core.num.U64.MAX
  · rw [control.advance_receive_target_max working top] at executed
    cases RustM.ok.inj executed
    cases yielded
  · obtain ⟨next, nextEq, nextSequence, _, _, nextYield⟩ := control.advance_receive_target_ok working top
    cases RustM.ok.inj (nextEq.symm.trans executed)
    rw [nextYield] at yielded
    cases yielded
    exact nextSequence

/-- A yielded skipped sequence likewise advances once, including cache-full and counter-exhausted rejection. -/
theorem skipped_sequence (working : control.RatchetState) (advanced : control.ReceiveAdvance)
    (executed : control.advance_receive working = ok advanced) (sequence : Std.U64)
    (yielded : advanced.sequence = .Some sequence) : sequence.val = working.receive_sequence.val + 1 := by
  by_cases top : working.receive_sequence = core.num.U64.MAX
  · rw [control.advance_receive_max working top] at executed
    cases RustM.ok.inj executed
    cases yielded
  by_cases full : 50 ≤ working.receive_cache.len.val
  · rw [control.advance_receive_full working full] at executed
    cases RustM.ok.inj executed
    cases yielded
  obtain ⟨next, nextEq, nextSequence, _, _, nextYield, _⟩ :=
    control.advance_receive_step working top (by omega)
  cases RustM.ok.inj (nextEq.symm.trans executed)
  rw [nextYield] at yielded
  cases yielded
  exact nextSequence

/-- Attribution reads the private source label, never an inverse of key bytes. -/
def Attributed (anchor : Label Slot) (cached : CachedReceiveKey (Label Slot)) : Prop :=
  cached.material.slot = anchor.slot ∧ cached.material.direction = anchor.direction ∧
    cached.sequence.val = cached.material.position + 1

def SlotsAttributed (anchor : Label Slot) (slots : Slots Slot) : Prop :=
  ∀ cached, core.option.Option.Some cached ∈ slots.val → Attributed anchor cached

def EffectAttributed (anchor : Label Slot) :
    RawCtxChainReceive.Effect (Label Slot) (Label Slot) (Label Slot) Context → Prop
  | .rejected entry _ => SlotsAttributed anchor entry.receive_slots
  | .kdfRequested pending => SlotsAttributed anchor pending.entry.receive_slots ∧ SlotsAttributed anchor pending.staged_slots
  | .openRequested opening => SlotsAttributed anchor opening.entry.receive_slots ∧
      match opening.prepared with
      | .PreparedReceiveCachedCase _ => True
      | .PreparedReceiveFutureCase pending => SlotsAttributed anchor pending.staged_slots ∧
          Attributed anchor ⟨pending.target_sequence, pending.target_material⟩

/-- Source skip/target writes give the actual sequence to this exact request label. -/
theorem resume_attributed (anchor : Label Slot)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (entry : SlotsAttributed anchor pending.entry.receive_slots)
    (staged : SlotsAttributed anchor pending.staged_slots)
    (slot : pending.request.slot = anchor.slot) (direction : pending.request.direction = anchor.direction)
    (counter : pending.request.position = pending.working_control.receive_sequence.val) :
    EffectAttributed anchor (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) := by
  have run := RawCtxChainReceive.normalResume_exact pending (advance pending.request 1, pending.request)
  generalize RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request) = effect at run ⊢
  unfold RawCtxChainReceive.resume at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals simp only [EffectAttributed, entry, true_and]
  all_goals cases RustM.ok.inj (show ok (advance pending.request 1, pending.request) = ok _ from by assumption)
  · refine ⟨staged, slot, direction, ?_⟩
    rw [counter]
    exact target_sequence pending.working_control _ (by assumption) _ (by assumption)
  · apply slots_update (Attributed anchor) pending.staged_slots staged _ _ ?_ _ (by assumption)
    refine ⟨slot, direction, ?_⟩
    rw [counter]
    exact skipped_sequence pending.working_control _ (by assumption) _ (by assumption)

/-- The already proved source tracking/admission facts discharge the request's slot, direction and sequence coordinates. -/
theorem resume_source_attributed (entry : LabeledKernel Slot) (context : Context) (target : Std.U64)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (aligned : Aligned entry) (tracked : Tracked entry context (.kdfRequested pending))
    (admitted : PqxdhFirstRecordReplay.Admitted entry target (.kdfRequested pending))
    (prior : SlotsAttributed entry.receive_chain pending.entry.receive_slots)
    (staged : SlotsAttributed entry.receive_chain pending.staged_slots) :
    EffectAttributed entry.receive_chain
      (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) := by
  exact resume_attributed entry.receive_chain pending prior staged
    (by simp only [tracked.2.2, advance]) (by simp only [tracked.2.2, advance])
    (request_sequence entry context target pending aligned tracked admitted)

/-- Actual admission starts only from existing attributed cache entries or an empty staged array. -/
theorem begin_attributed (anchor : Label Slot) (entry : LabeledKernel Slot)
    (prior : SlotsAttributed anchor entry.receive_slots) (target : Std.U64) (context : Context) :
    EffectAttributed anchor (RawCtxChainReceive.normalBegin entry target context) := by
  have run := RawCtxChainReceive.normalBegin_exact entry target context
  generalize RawCtxChainReceive.normalBegin entry target context = effect at run ⊢
  unfold RawCtxChainReceive.beginReceive at run
  repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals simp only [EffectAttributed, prior, true_and]
  cases RustM.ok.inj (show empty_material_slots (Label Slot) = ok _ from by assumption)
  simp [SlotsAttributed, Std.Array.make]

/-- Actual successful source array reads return an existing complete slot entry. -/
theorem index_member (slots : Slots Slot) (index : Std.Usize)
    (value : core.option.Option (CachedReceiveKey (Label Slot)))
    (executed : Array.index_usize slots index = ok value) : value ∈ slots.val := by
  simp only [Array.index_usize] at executed
  split at executed <;> cases executed
  exact List.mem_iff_getElem?.mpr ⟨index.val, by assumption⟩

/-- The actual opening getter returns the attributed cached or target label with the exact source sequence. -/
theorem opening_attributed (anchor : Label Slot)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (attributed : EffectAttributed anchor (.openRequested opening)) (label : Label Slot)
    (executed : RawCtxInterpretedOpening.material opening = ok (.Some label)) :
    ∃ sequence, RawCtxInterpretedOpening.sequence opening = ok sequence ∧ Attributed anchor ⟨sequence, label⟩ := by
  cases prepared : opening.prepared with
  | PreparedReceiveFutureCase pending =>
      simp only [RawCtxInterpretedOpening.material, prepared, RustM.ok.injEq] at executed
      cases executed
      simp only [EffectAttributed, prepared] at attributed
      exact ⟨pending.target_sequence, by simp only [RawCtxInterpretedOpening.sequence, prepared], attributed.2.2⟩
  | PreparedReceiveCachedCase cached =>
      refine ⟨cached.sequence, by simp only [RawCtxInterpretedOpening.sequence, prepared], ?_⟩
      simp only [RawCtxInterpretedOpening.material, prepared, option_as_ref, bind_tc_ok] at executed
      repeat' first | (obtain ⟨_, _, executed⟩ := PqxdhFirstRecordReplay.rust_bind_ok executed) | split at executed
      all_goals cases RustM.ok.inj executed
      have certificate := attributed.1 _ (index_member opening.entry.receive_slots _ _ (by assumption))
      simpa only [Attributed, show _ = cached.sequence from by assumption] using certificate

def eraseSendPending (seeds : Seeds Slot) (table : Table Slot)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context) :
    RawCtxInterpretedSend.Kdf RatchetMaterial Context :=
  RawCtxInterpretedSend.mapKdf (material table)
    (RawCtxChainSend.nativeKdf (chain seeds table) (chain seeds table) pending)

def eraseSeal (seeds : Seeds Slot) (table : Table Slot)
    (pending : RawCtxChainSend.Seal (Label Slot) (Label Slot) (Label Slot) Context) :
    RawCtxInterpretedSend.Seal RatchetMaterial Context :=
  RawCtxInterpretedSend.mapSeal (material table)
    (RawCtxChainSend.nativeSeal (chain seeds table) (chain seeds table) pending)

/-- Send-side table growth also preserves the complete old source request and receive cache. -/
theorem send_pending_mono (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (available : SendAvailable before pending) (present : SlotsPresent before pending.entry.receive_slots) :
    eraseSendPending seeds after pending = eraseSendPending seeds before pending := by
  simp only [eraseSendPending, RawCtxChainSend.nativeKdf, RawCtxInterpretedSend.mapKdf,
    mapRefined, RawCtxChainInterpretation.mapChains,
    chain_mono seeds before after mono pending.entry.send_chain available.1.1,
    chain_mono seeds before after mono pending.entry.receive_chain available.1.2,
    chain_mono seeds before after mono pending.request available.2,
    slots_mono before after mono pending.entry.receive_slots present]

/-- The source send callback keeps the entire advanced kernel and obtains material from the very same full76 reply. -/
theorem send_lookup [DecidableEq Slot] (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (available : SendAvailable state.1 pending) (present : SlotsPresent state.1 pending.entry.receive_slots)
    (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    RawCtxInterpretedSend.resume (eraseSendPending seeds state.1 pending)
      (ok (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1))) =
      ok (eraseSeal seeds result.2.1 (RawCtxChainSend.ready pending (advance pending.request 1, pending.request))) := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  rw [← send_pending_mono seeds state.1 result.2.1 facts.2.1 pending available present,
    RawCtxFreshChainCut.decoded_parts,
    ← successor_chain seeds result.2.1 pending.request
      (available_mono state.1 result.2.1 facts.2.1 pending.request available.2) result.1 facts.1]
  have stored : material result.2.1 pending.request =
      RawCtxFreshChainCut.concreteMaterial (PqxdhOrderedChainHybrids.material result.1) := by
    simp only [material, facts.1]
    rfl
  rw [← stored]
  rfl

def eraseOpening (seeds : Seeds Slot) (table : Table Slot)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context) :
    RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial Context :=
  RawCtxInterpretedOpening.mapOpening (material table)
    (RawCtxChainInterpretation.mapOpeningChains (chain seeds table) (chain seeds table) opening)

/-- Both actual opening getters retain the exact source sequence and optional interpreted material. -/
theorem opening_getters (seeds : Seeds Slot) (table : Table Slot)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context) :
    RawCtxInterpretedOpening.sequence (eraseOpening seeds table opening) = RawCtxInterpretedOpening.sequence opening ∧
    RawCtxInterpretedOpening.material (eraseOpening seeds table opening) =
      mapOption (material table) <$> RawCtxInterpretedOpening.material opening := by
  simp only [eraseOpening, RawCtxInterpretedOpening.sequence_map, RawCtxInterpretedOpening.material_map,
    RawCtxChainInterpretation.opening_sequence_chains, RawCtxChainInterpretation.opening_material_chains, and_self]

/-- Successful publication and failed-opening rollback retain the complete kernel and the supplied optional plaintext. -/
theorem finish_erasure {Plaintext : Type} (seeds : Seeds Slot) (table : Table Slot)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (reply : core.option.Option Plaintext) :
    RawCtxInterpretedReceive.normalFinish (eraseOpening seeds table opening) reply =
      (eraseKernel seeds table (RawCtxChainReceive.normalFinish opening reply).1,
        (RawCtxChainReceive.normalFinish opening reply).2) := by
  simp only [eraseOpening, RawCtxInterpretedReceive.normalFinish_map,
    RawCtxChainReceive.normalFinish_native, eraseKernel]

/-- Any property of complete existing/staged entries survives actual admitted publication or rollback. -/
theorem finish_property {Plaintext : Type} (property : CachedReceiveKey (Label Slot) → Prop)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (target : Std.U64) (prepared : PqxdhFirstRecordReplay.Prepared opening.entry target opening.prepared)
    (prior : ∀ cached, core.option.Option.Some cached ∈ opening.entry.receive_slots.val → property cached)
    (staged : match opening.prepared with
      | .PreparedReceiveCachedCase _ => True
      | .PreparedReceiveFutureCase pending =>
          ∀ cached, core.option.Option.Some cached ∈ pending.staged_slots.val → property cached)
    (reply : core.option.Option Plaintext) :
    ∀ cached, core.option.Option.Some cached ∈ (RawCtxChainReceive.normalFinish opening reply).1.receive_slots.val →
      property cached := by
  cases reply with
  | none => simpa only [PqxdhFirstRecordReplay.finish_none] using prior
  | some plaintext =>
      have run := RawCtxChainReceive.normalFinish_exact opening (.Some plaintext)
      generalize RawCtxChainReceive.normalFinish opening (.Some plaintext) = result at run ⊢
      unfold PqxdhFirstRecordReplay.Prepared at prepared
      cases shape : opening.prepared with
      | PreparedReceiveCachedCase cached =>
          rw [shape] at prepared
          obtain ⟨out, executed, certified⟩ := cached_publication property opening.entry cached prior
            prepared.target_bound prepared.last_bound
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          exact run ▸ certified
      | PreparedReceiveFutureCase pending =>
          rw [shape] at prepared staged
          obtain ⟨_, first, _, _, capacity, cached⟩ := prepared
          have length := congrArg List.length cached
          simp only [control.cacheSeqs_length, List.length_append, List.length_map, List.length_range] at length
          have bounded : pending.first_slot.val + pending.skipped.val ≤ 50 := by
            simp only [control.RatchetState.Wf, control.SequenceCache.Wf] at capacity
            rw [first]
            omega
          obtain ⟨out, executed, certified⟩ := future_publication property opening.entry pending prior staged bounded
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          exact run ▸ certified

abbrev serverLabels (slot : Slot) : RustM (LabeledKernel Slot) :=
  RefinedRatchet.from_counters (Label Slot) 1#u64 0#u64 ⟨slot, false, 1⟩ ⟨slot, true, 0⟩

abbrev beaconLabels (slot : Slot) : RustM (LabeledKernel Slot) :=
  RefinedRatchet.from_counters (Label Slot) 0#u64 1#u64 ⟨slot, true, 0⟩ ⟨slot, false, 1⟩

/-- Complete doubly labeled seed kernels erase to the exact production seed kernels. -/
theorem seeds_erasure (seeds : Seeds Slot) (table : Table Slot) (slot : Slot) :
    ((fun kernel => ConcreteRatchetKernel.mk (eraseKernel seeds table kernel)) <$> serverLabels slot =
      PqxdhRecordLiftSeed.serverKernel (seeds slot)) ∧
    ((fun kernel => ConcreteRatchetKernel.mk (eraseKernel seeds table kernel)) <$> beaconLabels slot =
      PqxdhRecordLiftSeed.beaconKernel (seeds slot)) := by
  constructor <;> rfl

/-- Both directional seed kernels start aligned, with available chains and no invented cache material. -/
theorem seeds_certified (table : Table Slot) (slot : Slot) :
    (∃ kernel, serverLabels slot = ok kernel ∧ Aligned kernel ∧ KernelAvailable table kernel ∧
      SlotsPresent table kernel.receive_slots ∧ SlotsAttributed kernel.receive_chain kernel.receive_slots) ∧
    (∃ kernel, beaconLabels slot = ok kernel ∧ Aligned kernel ∧ KernelAvailable table kernel ∧
      SlotsPresent table kernel.receive_slots ∧ SlotsAttributed kernel.receive_chain kernel.receive_slots) := by
  refine ⟨⟨_, rfl, ?_, ?_, ?_, ?_⟩, ⟨_, rfl, ?_, ?_, ?_, ?_⟩⟩
  all_goals first
    | exact ⟨by scalar_tac, by scalar_tac⟩
    | exact ⟨Or.inl rfl, Or.inl rfl⟩
    | simp [SlotsPresent, SlotsAttributed, Std.Array.make]

/-- A supported callback preserves the closed table and every chain/material reference in the complete source effect. -/
theorem receive_lookup_present [DecidableEq Slot] (state : State Slot) (closed : Closed state.1)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (present : PendingPresent state.1 pending) (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    Closed result.2.1 ∧
      EffectAvailable result.2.1 (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) ∧
      EffectPresent result.2.1 (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  have after : PendingAvailable result.2.1 pending :=
    ⟨⟨available_mono state.1 result.2.1 facts.2.1 _ present.1.1.1,
      available_mono state.1 result.2.1 facts.2.1 _ present.1.1.2⟩,
      available_mono state.1 result.2.1 facts.2.1 _ present.1.2⟩
  exact ⟨closed_lookup state closed pending.request present.1.2 result sampled,
    resume_available result.2.1 pending after (successor_available result.2.1 pending.request after.2 result.1 facts.1) _,
    resume_present result.2.1 pending
      (slots_present_mono state.1 result.2.1 facts.2.1 _ present.2.1)
      (slots_present_mono state.1 result.2.1 facts.2.1 _ present.2.2) ⟨result.1, facts.1⟩⟩

/-- Receive realization retains the full table reply, entire source effect, table and counters under every continuation. -/
theorem receive_continuation [DecidableEq Slot] {Result : Type}
    (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (present : PendingPresent state.1 pending)
    (continuation : FullOutput → RawCtxInterpretedReceive.Effect RatchetMaterial Context → State Slot → ProbComp Result) :
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1 (RawCtxInterpretedReceive.normalResume (erasePending seeds state.1 pending)
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1))) result.2) =
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1 (eraseEffect seeds result.2.1
        (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request))) result.2) := by
  exact bind_congr_of_forall_mem_support _ fun result sampled =>
    congrArg (fun effect => continuation result.1 effect result.2) (receive_lookup seeds state pending present result sampled)

/-- The send equality likewise retains the whole native result and persistent state for any continuation. -/
theorem send_continuation [DecidableEq Slot] {Result : Type}
    (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (available : SendAvailable state.1 pending) (present : SlotsPresent state.1 pending.entry.receive_slots)
    (continuation : FullOutput → RustM (RawCtxInterpretedSend.Seal RatchetMaterial Context) → State Slot → ProbComp Result) :
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1 (RawCtxInterpretedSend.resume (eraseSendPending seeds state.1 pending)
        (ok (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1)))) result.2) =
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1 (ok (eraseSeal seeds result.2.1
        (RawCtxChainSend.ready pending (advance pending.request 1, pending.request)))) result.2) := by
  exact bind_congr_of_forall_mem_support _ fun result sampled =>
    congrArg (fun effect => continuation result.1 effect result.2) (send_lookup seeds state pending available present result sampled)

/-- Actual active send admission names the same material coordinate as its source record sequence. -/
theorem send_begin_attributed (entry : LabeledKernel Slot) (context : Context) (aligned : Aligned entry) :
    match RawCtxChainSend.normalBegin entry context with
    | .exhausted _ _ => True
    | .requested pending => Attributed entry.send_chain ⟨pending.sequence, pending.request⟩ := by
  have run := RawCtxChainSend.normalBegin_exact entry context
  generalize RawCtxChainSend.normalBegin entry context = start at run ⊢
  unfold RawCtxChainSend.beginSend at run
  by_cases top : entry.control.send_sequence = core.num.U64.MAX
  · simp only [control.advance_send_max entry.control top, bind_tc_ok, RustM.ok.injEq] at run
    cases run
    trivial
  · obtain ⟨advanced, executed, sequence, _, _, yielded, _⟩ := control.advance_send_ok entry.control top
    simp only [executed, bind_tc_ok, yielded] at run
    repeat' first | (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
    all_goals cases RustM.ok.inj run
    all_goals simp only [Attributed, aligned.1, sequence, and_self]

/-- Failed opening restores the entire labeled source kernel while retaining the table's first reply after adaptive table work. -/
theorem rollback_lookup [DecidableEq Slot] {Plaintext Result : Type}
    (entry : LabeledKernel Slot) (context : Context)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (tracked : Tracked entry context (.openRequested opening))
    (coordinate : Label Slot) (state : State Slot) (first : FullOutput × State Slot)
    (sampled : first ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) coordinate).run state))
    (program : OracleComp (TableSpec Slot) Result) (last : Result × State Slot)
    (continued : last ∈ support ((simulateQ PqxdhRecordLiftLazyTable.impl program).run first.2)) :
    (PqxdhRecordLiftLazyTable.withCaller coordinate).run
      ((RawCtxChainReceive.normalFinish opening (.None : core.option.Option Plaintext)).1, last.2) =
      pure (first.1, (entry, (last.2.1, ⟨last.2.2.lookups + 1, last.2.2.draws⟩))) := by
  rw [PqxdhRecordLiftChainState.failed_open entry context opening tracked]
  exact PqxdhRecordLiftLazyTable.rollback_after_adaptive entry entry coordinate state first sampled program last continued

/-- Doubly labeled admission erases to the complete source admission, including malformed, cached and rejected paths. -/
theorem admission_erasure (seeds : Seeds Slot) (table : Table Slot) (entry : LabeledKernel Slot)
    (target : Std.U64) (context : Context) :
    RawCtxInterpretedReceive.normalBegin (eraseKernel seeds table entry) target context =
      eraseEffect seeds table (RawCtxChainReceive.normalBegin entry target context) := by
  simp only [eraseKernel, eraseEffect, RawCtxInterpretedReceive.normalBegin_map,
    RawCtxChainReceive.normalBegin_native]

def eraseStart (seeds : Seeds Slot) (table : Table Slot)
    (start : RawCtxChainSend.Start (Label Slot) (Label Slot) (Label Slot) Context) :
    RawCtxInterpretedSend.Start RatchetMaterial Context :=
  RawCtxInterpretedSend.mapStart (material table)
    (RawCtxChainSend.nativeStart (chain seeds table) (chain seeds table) start)

/-- Both send admission branches preserve the full source state under erasure. -/
theorem send_admission_erasure (seeds : Seeds Slot) (table : Table Slot) (entry : LabeledKernel Slot)
    (context : Context) :
    RawCtxInterpretedSend.normalBegin (eraseKernel seeds table entry) context =
      eraseStart seeds table (RawCtxChainSend.normalBegin entry context) := by
  simp only [eraseKernel, eraseStart, RawCtxInterpretedSend.normalBegin_map,
    RawCtxChainSend.normalBegin_native]

/-- Actual source send completion retains its advanced kernel for successful or failed sealing. -/
theorem send_finish_erasure {Output : Type} (seeds : Seeds Slot) (table : Table Slot)
    (pending : RawCtxChainSend.Seal (Label Slot) (Label Slot) (Label Slot) Context)
    (reply : core.option.Option Output) :
    RawCtxInterpretedSend.finish (eraseSeal seeds table pending) reply =
      ok (eraseKernel seeds table pending.advanced, reply) := by
  simp only [RawCtxInterpretedSend.finish, control.finish_send]
  split <;> rfl

/-- Every material actually returned by the source getter refers to a stored full76 reply. -/
theorem opening_present (table : Table Slot)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (present : EffectPresent table (.openRequested opening)) (label : Label Slot)
    (executed : RawCtxInterpretedOpening.material opening = ok (.Some label)) : Present table label := by
  cases prepared : opening.prepared with
  | PreparedReceiveFutureCase pending =>
      simp only [RawCtxInterpretedOpening.material, prepared, RustM.ok.injEq] at executed
      cases executed
      simp only [EffectPresent, prepared] at present
      exact present.2.2
  | PreparedReceiveCachedCase cached =>
      simp only [RawCtxInterpretedOpening.material, prepared, option_as_ref, bind_tc_ok] at executed
      repeat' first | (obtain ⟨_, _, executed⟩ := PqxdhFirstRecordReplay.rust_bind_ok executed) | split at executed
      all_goals cases RustM.ok.inj executed
      exact present.1 _ (index_member opening.entry.receive_slots _ _ (by assumption))

/-- Actual admitted finish preserves table presence and source attribution through consumption, movement and rollback. -/
theorem finish_certified {Plaintext : Type} (table : Table Slot) (anchor : Label Slot)
    (opening : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (target : Std.U64) (prepared : PqxdhFirstRecordReplay.Prepared opening.entry target opening.prepared)
    (present : EffectPresent table (.openRequested opening))
    (attributed : EffectAttributed anchor (.openRequested opening)) (reply : core.option.Option Plaintext) :
    SlotsPresent table (RawCtxChainReceive.normalFinish opening reply).1.receive_slots ∧
      SlotsAttributed anchor (RawCtxChainReceive.normalFinish opening reply).1.receive_slots := by
  have staged : match opening.prepared with
      | .PreparedReceiveCachedCase _ => True
      | .PreparedReceiveFutureCase pending =>
          ∀ cached, core.option.Option.Some cached ∈ pending.staged_slots.val →
            Present table cached.material ∧ Attributed anchor cached := by
    cases shape : opening.prepared with
    | PreparedReceiveCachedCase _ => trivial
    | PreparedReceiveFutureCase pending =>
        simp only [EffectPresent, EffectAttributed, shape] at present attributed
        exact fun cached found => ⟨present.2.1 cached found, attributed.2.1 cached found⟩
  have certified := finish_property (fun cached => Present table cached.material ∧ Attributed anchor cached)
    opening target prepared (fun cached found => ⟨present.1 cached found, attributed.1 cached found⟩) staged reply
  exact ⟨fun cached found => (certified cached found).1, fun cached found => (certified cached found).2⟩

/-- The complete advanced send state retains its old cache and all available source references. -/
theorem send_lookup_present [DecidableEq Slot] (state : State Slot) (closed : Closed state.1)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (available : SendAvailable state.1 pending) (present : SlotsPresent state.1 pending.entry.receive_slots)
    (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    Closed result.2.1 ∧
      KernelAvailable result.2.1 (RawCtxChainSend.ready pending (advance pending.request 1, pending.request)).advanced ∧
      SlotsPresent result.2.1 (RawCtxChainSend.ready pending (advance pending.request 1, pending.request)).advanced.receive_slots ∧
      Present result.2.1 (RawCtxChainSend.ready pending (advance pending.request 1, pending.request)).material := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  exact ⟨closed_lookup state closed pending.request available.2 result sampled,
    ⟨successor_available result.2.1 pending.request
      (available_mono state.1 result.2.1 facts.2.1 _ available.2) result.1 facts.1,
      available_mono state.1 result.2.1 facts.2.1 _ available.1.2⟩,
    slots_present_mono state.1 result.2.1 facts.2.1 _ present, ⟨result.1, facts.1⟩⟩

end BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.material_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.material_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.pending_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.pending_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.receive_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.receive_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_set
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_update' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_update
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.resume_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.resume_present
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.present_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.present_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_present_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_present_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.begin_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.begin_present
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_property_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.slots_property_get
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.future_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.future_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.cached_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.cached_publication
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.target_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.target_sequence
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.skipped_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.skipped_sequence
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.resume_attributed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.resume_attributed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.resume_source_attributed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.resume_source_attributed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.begin_attributed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.begin_attributed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.index_member' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.index_member
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.opening_attributed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.opening_attributed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_pending_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_pending_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.opening_getters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.opening_getters
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.finish_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.finish_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.finish_property' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.finish_property
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.seeds_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.seeds_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.seeds_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.seeds_certified
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.receive_lookup_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.receive_lookup_present
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.receive_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.receive_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_begin_attributed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_begin_attributed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.rollback_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.rollback_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.admission_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.admission_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_admission_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_admission_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_finish_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_finish_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.opening_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.opening_present
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.finish_certified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.finish_certified
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_lookup_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable.send_lookup_present

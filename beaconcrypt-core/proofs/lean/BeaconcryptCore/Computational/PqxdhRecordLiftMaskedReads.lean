-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftMaterialTable
import BeaconcryptCore.Computational.PqxdhRecordLiftProjectionCut
import BeaconcryptCore.Computational.PqxdhRecordLiftSeedCut
import BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters

/-! Exact source read equations for one selected seed half or one selected cached full76 field. Reconstructed states retain every other entry and all counters. Whole native opening and sealing callbacks depend only on their actual source getters and context. These deterministic local equations do not establish global reachability, a target-free whole observer, or a cryptographic hybrid bound. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable
open PqxdhRecordLiftProjectionCut PqxdhOrderedChainHybrids PqxdhFullSecretInputKdf PqxdhSecretInputKdf

/-- Replacing key32 preserves the exact next32 and nonce12 source projections. -/
theorem key_parts (other : Retained) (hidden : RootOutput) :
    (nextChain (restore .key other hidden), material (restore .key other hidden)) =
      (other.1, (hidden, other.2)) := by
  have parts := split_restore .key other hidden
  change ((nextChain (restore .key other hidden), (material (restore .key other hidden)).2),
    (material (restore .key other hidden)).1) = (other, hidden) at parts
  exact Prod.ext (congrArg (fun value => value.1.1) parts)
    (Prod.ext (congrArg Prod.snd parts) (congrArg (fun value => value.1.2) parts))

/-- Replacing next32 preserves the entire key32/nonce12 material pair. -/
theorem chain_parts (other : Retained) (hidden : RootOutput) :
    (material (restore .chain other hidden), nextChain (restore .chain other hidden)) =
      (other, hidden) := split_restore .chain other hidden

variable {Slot : Type} [DecidableEq Slot]

/-- A realization retains the same complete counters and changes exactly one structural cache coordinate. -/
theorem realize_reads (part : Part) (masked : Mask Slot) (hidden : RootOutput) :
    (realize part masked hidden).2.2 = masked.counts ∧
      ∀ coordinate, (realize part masked hidden).2.1 coordinate =
        if coordinate = masked.coordinate then some (restore part masked.value hidden)
        else masked.before coordinate := by
  refine ⟨rfl, fun coordinate => ?_⟩
  by_cases same : coordinate = masked.coordinate
  · subst coordinate
    simp [realize]
  · simp [realize, same, QueryCache.cacheQuery_of_ne]

/-- The exact selected-cache read condition of the total source interpretation. -/
def Reads (coordinate selected : Coordinate Slot) : Prop :=
  coordinate.position ≠ start coordinate.direction ∧ previous coordinate = selected

instance (coordinate selected : Coordinate Slot) : Decidable (Reads coordinate selected) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The source KDF input reads either the selected full reply's next32 or the unchanged prior table. -/
theorem chain_read (part : Part) (masked : Mask Slot) (hidden : RootOutput)
    (seeds : Seeds Slot) (coordinate : Coordinate Slot) :
    chain seeds (realize part masked hidden).2.1 coordinate =
      if Reads coordinate masked.coordinate then
        RawCtxFreshChainCut.concreteChain (nextChain (restore part masked.value hidden))
      else chain seeds masked.before coordinate := by
  by_cases initial : coordinate.position = start coordinate.direction
  · simp [chain, Reads, initial]
  · by_cases same : previous coordinate = masked.coordinate
    · simp [chain, Reads, realize, initial, same]
      rw [same, QueryCache.cacheQuery_self]
    · simp [chain, Reads, realize, initial, same, QueryCache.cacheQuery_of_ne]

omit [DecidableEq Slot] in
/-- On the existing source-coordinate domain, the sole selected-table reader is its successor. -/
theorem reads_iff_successor (coordinate selected : Coordinate Slot)
    (coordinateLower : start coordinate.direction ≤ coordinate.position)
    (selectedLower : start selected.direction ≤ selected.position) :
    Reads coordinate selected ↔ coordinate = advance selected 1 := by
  constructor
  · rintro ⟨notInitial, prior⟩
    have arithmetic : coordinate.position = coordinate.position - 1 + 1 := by omega
    rw [← prior]
    cases coordinate
    simp only [previous, advance]
    congr 1
  · intro same
    subst coordinate
    refine ⟨?_, previous_advance selected⟩
    simp only [advance]
    omega

/-- A chain-part mask supplies its hidden32 only at the exact selected predecessor read. -/
theorem chain_next_read (masked : Mask Slot) (hidden : RootOutput)
    (seeds : Seeds Slot) (coordinate : Coordinate Slot) :
    chain seeds (realize .chain masked hidden).2.1 coordinate =
      if Reads coordinate masked.coordinate then RawCtxFreshChainCut.concreteChain hidden
      else chain seeds masked.before coordinate := by
  have next : nextChain (restore .chain masked.value hidden) = hidden :=
    congrArg Prod.snd (chain_parts masked.value hidden)
  rw [chain_read, next]

/-- A key-part mask gives every source chain input a formula without the selected key32. -/
theorem chain_key_read (masked : Mask Slot) (hidden : RootOutput)
    (seeds : Seeds Slot) (coordinate : Coordinate Slot) :
    chain seeds (realize .key masked hidden).2.1 coordinate =
      if Reads coordinate masked.coordinate then RawCtxFreshChainCut.concreteChain masked.value.1
      else chain seeds masked.before coordinate := by
  have next : nextChain (restore .key masked.value hidden) = masked.value.1 :=
    congrArg Prod.fst (key_parts masked.value hidden)
  rw [chain_read, next]

/-- The exact source material getter reads the selected complete reply or the unchanged other entry. -/
theorem material_read (part : Part) (masked : Mask Slot) (hidden : RootOutput) (coordinate : Coordinate Slot) :
    PqxdhRecordLiftMaterialTable.material (realize part masked hidden).2.1 coordinate =
      if coordinate = masked.coordinate then
        RawCtxFreshChainCut.concreteMaterial (material (restore part masked.value hidden))
      else PqxdhRecordLiftMaterialTable.material masked.before coordinate := by
  by_cases same : coordinate = masked.coordinate
  · subst coordinate
    simp [PqxdhRecordLiftMaterialTable.material, realize]
    rfl
  · simp [PqxdhRecordLiftMaterialTable.material, realize, same, QueryCache.cacheQuery_of_ne]

/-- Every source material read is independent of the chain-part mask's hidden32. -/
theorem material_chain_read (masked : Mask Slot) (hidden : RootOutput) (coordinate : Coordinate Slot) :
    PqxdhRecordLiftMaterialTable.material (realize .chain masked hidden).2.1 coordinate =
      if coordinate = masked.coordinate then RawCtxFreshChainCut.concreteMaterial masked.value
      else PqxdhRecordLiftMaterialTable.material masked.before coordinate := by
  have pair : material (restore .chain masked.value hidden) = masked.value :=
    congrArg Prod.fst (chain_parts masked.value hidden)
  rw [material_read, pair]

/-- Only the selected structural material coordinate obtains the supplied key32; its nonce is retained. -/
theorem material_key_read (masked : Mask Slot) (hidden : RootOutput) (coordinate : Coordinate Slot) :
    PqxdhRecordLiftMaterialTable.material (realize .key masked hidden).2.1 coordinate =
      if coordinate = masked.coordinate then RawCtxFreshChainCut.concreteMaterial (hidden, masked.value.2)
      else PqxdhRecordLiftMaterialTable.material masked.before coordinate := by
  have pair : material (restore .key masked.value hidden) = (hidden, masked.value.2) :=
    congrArg Prod.snd (key_parts masked.value hidden)
  rw [material_read, pair]

/-- Neither selected32 replacement changes a source nonce, at any material coordinate. -/
theorem material_nonce (part : Part) (masked : Mask Slot) (left right : RootOutput)
    (coordinate : Coordinate Slot) :
    (PqxdhRecordLiftMaterialTable.material (realize part masked left).2.1 coordinate).nonce =
      (PqxdhRecordLiftMaterialTable.material (realize part masked right).2.1 coordinate).nonce := by
  cases part
  · rw [material_chain_read, material_chain_read]
  · rw [material_key_read, material_key_read]
    split <;> rfl

/-- The actual pending receive request reads precisely its structural chain input. -/
theorem receive_request_read {Context : Type} (part : Part) (masked : Mask Slot) (hidden : RootOutput)
    (seeds : Seeds Slot)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) Context) :
    (PqxdhRecordLiftMaterialTable.erasePending seeds (realize part masked hidden).2.1 pending).request =
      RawCtxChainSend.nativeRequest (if Reads pending.request masked.coordinate then
        RawCtxFreshChainCut.concreteChain (nextChain (restore part masked.value hidden))
      else chain seeds masked.before pending.request) := by
  change RawCtxChainSend.nativeRequest (chain seeds (realize part masked hidden).2.1 pending.request) = _
  rw [chain_read]

/-- The actual pending send request has the same exact predecessor read condition. -/
theorem send_request_read {Context : Type} (part : Part) (masked : Mask Slot) (hidden : RootOutput)
    (seeds : Seeds Slot)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) Context) :
    (PqxdhRecordLiftMaterialTable.eraseSendPending seeds (realize part masked hidden).2.1 pending).request =
      RawCtxChainSend.nativeRequest (if Reads pending.request masked.coordinate then
        RawCtxFreshChainCut.concreteChain (nextChain (restore part masked.value hidden))
      else chain seeds masked.before pending.request) := by
  change RawCtxChainSend.nativeRequest (chain seeds (realize part masked hidden).2.1 pending.request) = _
  rw [chain_read]

/-- The actual cached/target opening getter changes only a selected label's key, preserving failure and None/Some. -/
theorem opening_key_read {Context : Type} (masked : Mask Slot) (hidden : RootOutput) (seeds : Seeds Slot)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) Context) :
    RawCtxInterpretedOpening.material
      (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize .key masked hidden).2.1 opening) =
      RawCtxMaterialInterpretation.mapOption (fun coordinate => if coordinate = masked.coordinate then
        RawCtxFreshChainCut.concreteMaterial (hidden, masked.value.2)
        else PqxdhRecordLiftMaterialTable.material masked.before coordinate) <$>
          RawCtxInterpretedOpening.material opening := by
  rw [(PqxdhRecordLiftMaterialTable.opening_getters seeds _ opening).2,
    funext (material_key_read masked hidden)]

/-- A next32 replacement cannot affect the actual cached/target opening material result. -/
theorem opening_chain_read {Context : Type} (masked : Mask Slot) (hidden : RootOutput) (seeds : Seeds Slot)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) Context) :
    RawCtxInterpretedOpening.material
      (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize .chain masked hidden).2.1 opening) =
      RawCtxMaterialInterpretation.mapOption (fun coordinate => if coordinate = masked.coordinate then
        RawCtxFreshChainCut.concreteMaterial masked.value
        else PqxdhRecordLiftMaterialTable.material masked.before coordinate) <$>
          RawCtxInterpretedOpening.material opening := by
  rw [(PqxdhRecordLiftMaterialTable.opening_getters seeds _ opening).2,
    funext (material_chain_read masked hidden)]

/-- The actual sealing material uses the selected key only when its original source label matches. -/
theorem seal_key_read {Context : Type} (masked : Mask Slot) (hidden : RootOutput) (seeds : Seeds Slot)
    (pending : RawCtxChainSend.Seal (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) Context) :
    (PqxdhRecordLiftMaterialTable.eraseSeal seeds (realize .key masked hidden).2.1 pending).material =
      if pending.material = masked.coordinate then RawCtxFreshChainCut.concreteMaterial (hidden, masked.value.2)
      else PqxdhRecordLiftMaterialTable.material masked.before pending.material := by
  exact material_key_read masked hidden pending.material

/-- The actual sealing material has no dependency on the replaced next32 field. -/
theorem seal_chain_read {Context : Type} (masked : Mask Slot) (hidden : RootOutput) (seeds : Seeds Slot)
    (pending : RawCtxChainSend.Seal (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) Context) :
    (PqxdhRecordLiftMaterialTable.eraseSeal seeds (realize .chain masked hidden).2.1 pending).material =
      if pending.material = masked.coordinate then RawCtxFreshChainCut.concreteMaterial masked.value
      else PqxdhRecordLiftMaterialTable.material masked.before pending.material := by
  exact material_chain_read masked hidden pending.material

/-- The actual optional opening nonce, including its RustM failure, is unchanged by either selected32 replacement. -/
theorem opening_nonce {Context : Type} (part : Part) (masked : Mask Slot) (left right : RootOutput)
    (seeds : Seeds Slot)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) Context) :
    RawCtxMaterialInterpretation.mapOption RatchetMaterial.nonce <$>
      RawCtxInterpretedOpening.material
        (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize part masked left).2.1 opening) =
      RawCtxMaterialInterpretation.mapOption RatchetMaterial.nonce <$>
        RawCtxInterpretedOpening.material
          (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize part masked right).2.1 opening) := by
  rw [(PqxdhRecordLiftMaterialTable.opening_getters seeds _ opening).2,
    (PqxdhRecordLiftMaterialTable.opening_getters seeds _ opening).2]
  simp only [Functor.map_map]
  congr 1
  funext result
  cases result with
  | none => rfl
  | some coordinate => exact congrArg core.option.Option.Some (material_nonce part masked left right coordinate)

/-- Replacing a seed half keeps its opposite directional32 exactly, independently of byte coincidences. -/
theorem seed_parts (direction : Bool) (other hidden : RootOutput) :
    (if direction then (PqxdhRecordLiftSeedCut.restore direction other hidden).2
      else (PqxdhRecordLiftSeedCut.restore direction other hidden).1) = hidden ∧
    (if direction then (PqxdhRecordLiftSeedCut.restore direction other hidden).1
      else (PqxdhRecordLiftSeedCut.restore direction other hidden).2) = other := by
  cases direction <;> exact ⟨rfl, rfl⟩

/-- Changing the selected seed32 changes only that cache entry in the complete realized World; all counters and other state agree. -/
theorem seed_realize_replace {n : Nat} (direction : Bool) (masked : PqxdhRecordLiftSeedCut.Mask n)
    (left right : RootOutput) :
    (PqxdhRecordLiftSeedCut.realize direction masked right).2 =
      { (PqxdhRecordLiftSeedCut.realize direction masked left).2 with
        seeds := ((PqxdhRecordLiftSeedCut.realize direction masked left).2.seeds.1.cacheQuery masked.slot
          (PqxdhRecordLiftSeedCut.restore direction masked.other right),
          (PqxdhRecordLiftSeedCut.realize direction masked left).2.seeds.2) } := by
  have overwrite : (masked.before.seeds.1.cacheQuery masked.slot
      (PqxdhRecordLiftSeedCut.restore direction masked.other left)).cacheQuery masked.slot
        (PqxdhRecordLiftSeedCut.restore direction masked.other right) =
      masked.before.seeds.1.cacheQuery masked.slot (PqxdhRecordLiftSeedCut.restore direction masked.other right) := by
    funext slot
    by_cases same : slot = masked.slot
    · subst slot
      simp
    · simp [QueryCache.cacheQuery_of_ne, same]
  simp only [PqxdhRecordLiftSeedCut.realize, overwrite]

/-- The actual World seed reader changes exactly the selected slot and retains every other lookup, including its fallback. -/
theorem seed_read {n : Nat} (direction : Bool) (masked : PqxdhRecordLiftSeedCut.Mask n)
    (hidden : RootOutput) (slot : Fin n) :
    PqxdhRecordLiftSeedCut.seedAt (PqxdhRecordLiftSeedCut.realize direction masked hidden).2 slot =
      if slot = masked.slot then PqxdhRecordLiftSeedCut.restore direction masked.other hidden
      else PqxdhRecordLiftSeedCut.seedAt masked.before slot := by
  by_cases same : slot = masked.slot
  · subst slot
    simp [PqxdhRecordLiftSeedCut.seedAt, PqxdhRecordLiftSeedCut.realize]
  · simp [PqxdhRecordLiftSeedCut.seedAt, PqxdhRecordLiftSeedCut.realize, same,
      QueryCache.cacheQuery_of_ne]

/-- Only the selected slot's initial directional chain can read the replaced seed32; later inputs read the unchanged table. -/
theorem seed_chain_read {n : Nat} (direction : Bool) (masked : PqxdhRecordLiftSeedCut.Mask n)
    (hidden : RootOutput) (table : Table (Fin n)) (coordinate : Coordinate (Fin n)) :
    chain (PqxdhRecordLiftSeedCut.seedAt (PqxdhRecordLiftSeedCut.realize direction masked hidden).2)
        table coordinate =
      if coordinate.slot = masked.slot ∧ coordinate.position = start coordinate.direction then
        RawCtxFreshChainCut.concreteChain (if coordinate.direction = direction then hidden else masked.other)
      else chain (PqxdhRecordLiftSeedCut.seedAt masked.before) table coordinate := by
  by_cases initial : coordinate.position = start coordinate.direction
  · simp only [chain, initial, ite_true, seed_read]
    by_cases same : coordinate.slot = masked.slot
    · simp only [same, ite_true, and_self]
      cases direction <;> cases d : coordinate.direction <;> rfl
    · simp [same]
  · simp [chain, initial]

/-- The complete native opening callback reads only source material, sequence and context, retaining every primitive effect and optional reply. -/
theorem receive_open_reads {PrimitiveState : Type}
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative PrimitiveState)
    (left right : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (sequence : RawCtxInterpretedOpening.sequence left = RawCtxInterpretedOpening.sequence right)
    (material : RawCtxInterpretedOpening.material left = RawCtxInterpretedOpening.material right)
    (context : left.context = right.context) :
    PqxdhRecordLiftNativeAdapters.receiveOpen native left =
      PqxdhRecordLiftNativeAdapters.receiveOpen native right := by
  have values : (RawCtxInterpretedOpening.toNative left).material_total.choose =
      (RawCtxInterpretedOpening.toNative right).material_total.choose := by
    apply RustM.ok.inj
    exact (RawCtxInterpretedOpening.toNative left).material_total.choose_spec.symm.trans
      ((RawCtxInterpretedOpening.native_material left).trans
        (material.trans ((RawCtxInterpretedOpening.native_material right).symm.trans
          (RawCtxInterpretedOpening.toNative right).material_total.choose_spec)))
  have sequences : (RawCtxInterpretedOpening.toNative left).sequence_total.choose =
      (RawCtxInterpretedOpening.toNative right).sequence_total.choose := by
    apply RustM.ok.inj
    exact (RawCtxInterpretedOpening.toNative left).sequence_total.choose_spec.symm.trans
      ((RawCtxInterpretedOpening.native_sequence left).trans
        (sequence.trans ((RawCtxInterpretedOpening.native_sequence right).symm.trans
          (RawCtxInterpretedOpening.toNative right).sequence_total.choose_spec)))
  have arguments : RawCtxWholeOwner.arguments (RawCtxInterpretedOpening.toNative left) =
      RawCtxWholeOwner.arguments (RawCtxInterpretedOpening.toNative right) := by
    simp only [RawCtxWholeOwner.arguments, values, sequences]
    cases (RawCtxInterpretedOpening.toNative right).material_total.choose <;> simp [context, RawCtxInterpretedOpening.toNative]
  simp only [PqxdhRecordLiftNativeAdapters.receiveOpen, RawCtxWholeOwner.adapter, arguments]
  rfl

/-- Changing a cached next32 preserves the whole native opening computation, even if private rollback chains differ. -/
theorem receive_open_chain_invariant {PrimitiveState : Type}
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative PrimitiveState)
    (masked : Mask Slot) (left right : RootOutput) (seeds : Seeds Slot)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) RawCtxWholeOwner.OpenContext) :
    PqxdhRecordLiftNativeAdapters.receiveOpen native
        (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize .chain masked left).2.1 opening) =
      PqxdhRecordLiftNativeAdapters.receiveOpen native
        (PqxdhRecordLiftMaterialTable.eraseOpening seeds (realize .chain masked right).2.1 opening) := by
  apply receive_open_reads
  · rw [(PqxdhRecordLiftMaterialTable.opening_getters seeds _ opening).1,
      (PqxdhRecordLiftMaterialTable.opening_getters seeds _ opening).1]
  · rw [opening_chain_read, opening_chain_read]
  · rfl

omit [DecidableEq Slot] in
/-- The whole native opening callback is independent of both seed chains when its labeled material table is fixed. -/
theorem receive_open_seeds {PrimitiveState : Type}
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative PrimitiveState)
    (left right : Seeds Slot) (table : Table Slot)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) RawCtxWholeOwner.OpenContext) :
    PqxdhRecordLiftNativeAdapters.receiveOpen native (PqxdhRecordLiftMaterialTable.eraseOpening left table opening) =
      PqxdhRecordLiftNativeAdapters.receiveOpen native (PqxdhRecordLiftMaterialTable.eraseOpening right table opening) := by
  apply receive_open_reads
  · rw [(PqxdhRecordLiftMaterialTable.opening_getters left table opening).1,
      (PqxdhRecordLiftMaterialTable.opening_getters right table opening).1]
  · rw [(PqxdhRecordLiftMaterialTable.opening_getters left table opening).2,
      (PqxdhRecordLiftMaterialTable.opening_getters right table opening).2]
  · rfl

/-- The complete sealing callback reads only material, sequence and context, preserving attempted primitive work even when the writer returns None. -/
theorem send_seal_reads {PrimitiveState : Type}
    (native : PqxdhRecordLiftNativeAdapters.SendNative PrimitiveState)
    (left right : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext)
    (material : left.material = right.material) (sequence : left.sequence = right.sequence)
    (context : left.context = right.context) :
    PqxdhRecordLiftNativeAdapters.sendSeal native left =
      PqxdhRecordLiftNativeAdapters.sendSeal native right := by
  have arguments : RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal left) =
      RawCtxSourceSend.arguments (RawCtxInterpretedSend.nativeSeal right) := by
    simp only [RawCtxSourceSend.arguments, RawCtxInterpretedSend.nativeSeal, material, sequence, context]
  rw [PqxdhRecordLiftNativeAdapters.send_seal_reply, PqxdhRecordLiftNativeAdapters.send_seal_reply,
    arguments]

/-- Changing a cached next32 preserves the complete sealing callback and all attempted native frame work. -/
theorem send_seal_chain_invariant {PrimitiveState : Type}
    (native : PqxdhRecordLiftNativeAdapters.SendNative PrimitiveState)
    (masked : Mask Slot) (left right : RootOutput) (seeds : Seeds Slot)
    (pending : RawCtxChainSend.Seal (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) RawCtxSourceSend.SealContext) :
    PqxdhRecordLiftNativeAdapters.sendSeal native
        (PqxdhRecordLiftMaterialTable.eraseSeal seeds (realize .chain masked left).2.1 pending) =
      PqxdhRecordLiftNativeAdapters.sendSeal native
        (PqxdhRecordLiftMaterialTable.eraseSeal seeds (realize .chain masked right).2.1 pending) := by
  apply send_seal_reads
  · rw [seal_chain_read, seal_chain_read]
  · rfl
  · rfl

omit [DecidableEq Slot] in
/-- The complete native sealing callback is independent of the seed family at a fixed material table. -/
theorem send_seal_seeds {PrimitiveState : Type}
    (native : PqxdhRecordLiftNativeAdapters.SendNative PrimitiveState)
    (left right : Seeds Slot) (table : Table Slot)
    (pending : RawCtxChainSend.Seal (Coordinate Slot) (Coordinate Slot) (Coordinate Slot) RawCtxSourceSend.SealContext) :
    PqxdhRecordLiftNativeAdapters.sendSeal native (PqxdhRecordLiftMaterialTable.eraseSeal left table pending) =
      PqxdhRecordLiftNativeAdapters.sendSeal native (PqxdhRecordLiftMaterialTable.eraseSeal right table pending) := by
  exact send_seal_reads native _ _ rfl rfl rfl

/-- Every source chain input is unchanged when only one cached key32 is replaced. -/
theorem chain_key_invariant (masked : Mask Slot) (left right : RootOutput)
    (seeds : Seeds Slot) (coordinate : Coordinate Slot) :
    chain seeds (realize .key masked left).2.1 coordinate =
      chain seeds (realize .key masked right).2.1 coordinate := by
  rw [chain_key_read, chain_key_read]

/-- On source-admissible positions, a replaced next32 affects only the selected coordinate's exact successor. -/
theorem chain_successor_read (masked : Mask Slot) (hidden : RootOutput)
    (seeds : Seeds Slot) (coordinate : Coordinate Slot)
    (coordinateLower : start coordinate.direction ≤ coordinate.position)
    (selectedLower : start masked.coordinate.direction ≤ masked.coordinate.position) :
    chain seeds (realize .chain masked hidden).2.1 coordinate =
      if coordinate = advance masked.coordinate 1 then RawCtxFreshChainCut.concreteChain hidden
      else chain seeds masked.before coordinate := by
  simp only [chain_next_read, reads_iff_successor coordinate masked.coordinate coordinateLower selectedLower]

/-- The actual receive KDF request reads the selected seed only at the selected slot's initial position. -/
theorem seed_receive_request {n : Nat} {Context : Type} (direction : Bool)
    (masked : PqxdhRecordLiftSeedCut.Mask n) (hidden : RootOutput) (table : Table (Fin n))
    (pending : RawCtxChainReceive.Kdf (Coordinate (Fin n)) (Coordinate (Fin n)) (Coordinate (Fin n)) Context) :
    (PqxdhRecordLiftMaterialTable.erasePending
      (PqxdhRecordLiftSeedCut.seedAt (PqxdhRecordLiftSeedCut.realize direction masked hidden).2) table pending).request =
      RawCtxChainSend.nativeRequest
        (if pending.request.slot = masked.slot ∧ pending.request.position = start pending.request.direction then
          RawCtxFreshChainCut.concreteChain (if pending.request.direction = direction then hidden else masked.other)
        else chain (PqxdhRecordLiftSeedCut.seedAt masked.before) table pending.request) := by
  change RawCtxChainSend.nativeRequest (chain
    (PqxdhRecordLiftSeedCut.seedAt (PqxdhRecordLiftSeedCut.realize direction masked hidden).2) table pending.request) = _
  rw [seed_chain_read]

/-- The actual send KDF request uses the same slot, direction and initial-position selector for the replaced seed32. -/
theorem seed_send_request {n : Nat} {Context : Type} (direction : Bool)
    (masked : PqxdhRecordLiftSeedCut.Mask n) (hidden : RootOutput) (table : Table (Fin n))
    (pending : RawCtxChainSend.Kdf (Coordinate (Fin n)) (Coordinate (Fin n)) (Coordinate (Fin n)) Context) :
    (PqxdhRecordLiftMaterialTable.eraseSendPending
      (PqxdhRecordLiftSeedCut.seedAt (PqxdhRecordLiftSeedCut.realize direction masked hidden).2) table pending).request =
      RawCtxChainSend.nativeRequest
        (if pending.request.slot = masked.slot ∧ pending.request.position = start pending.request.direction then
          RawCtxFreshChainCut.concreteChain (if pending.request.direction = direction then hidden else masked.other)
        else chain (PqxdhRecordLiftSeedCut.seedAt masked.before) table pending.request) := by
  change RawCtxChainSend.nativeRequest (chain
    (PqxdhRecordLiftSeedCut.seedAt (PqxdhRecordLiftSeedCut.realize direction masked hidden).2) table pending.request) = _
  rw [seed_chain_read]

end BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.key_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.key_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.realize_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.realize_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.reads_iff_successor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.reads_iff_successor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_next_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_next_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_key_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_key_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_chain_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_chain_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_key_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_key_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_nonce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.material_nonce

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_request_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_request_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_request_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_request_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.opening_key_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.opening_key_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.opening_chain_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.opening_chain_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seal_key_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seal_key_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seal_chain_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seal_chain_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.opening_nonce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.opening_nonce

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_parts' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_realize_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_realize_replace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_chain_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_chain_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_open_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_open_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_open_chain_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_open_chain_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_open_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.receive_open_seeds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_seal_reads' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_seal_reads

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_seal_chain_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_seal_chain_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_seal_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.send_seal_seeds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_key_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_key_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_successor_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.chain_successor_read

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_receive_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_receive_request

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_send_request' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMaskedReads.seed_send_request

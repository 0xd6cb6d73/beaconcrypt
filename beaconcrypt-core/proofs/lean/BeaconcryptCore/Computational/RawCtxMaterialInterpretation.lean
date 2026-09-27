import BeaconcryptCore.Computational.RawCtxMaterialPositions

/-!
# Noninjective source material interpretation

Private payload labels are interpreted by an arbitrary function that may map different labels to the same value. These laws retain the actual extracted slot presence, sequence tags, validation, initialization and cached/future publication, including malformed-input rejection. The source chains and controls remain unchanged. No inverse key lookup, fresh-key distribution, generic KDF continuation or complete owner/schedule erasure is assumed or proved here.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.control
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxMaterialInterpretation

/-- Interpret private material payloads without changing slot presence or source sequence tags. -/
def mapCached {Material Value : Type} (interpret : Material → Value) (cached : CachedReceiveKey Material) :
    CachedReceiveKey Value := ⟨cached.sequence, interpret cached.material⟩

def mapOption {Material Value : Type} (interpret : Material → Value) :
    core.option.Option Material → core.option.Option Value
  | .None => .None
  | .Some material => .Some (interpret material)

def mapArray {Material Value : Type} {size : Std.Usize} (interpret : Material → Value)
    (array : Std.Array Material size) : Std.Array Value size :=
  ⟨array.val.map interpret, by simpa only [List.length_map] using array.property⟩

def mapRefined {SendChain ReceiveChain Material Value : Type} (interpret : Material → Value)
    (state : RefinedRatchet SendChain ReceiveChain Material) : RefinedRatchet SendChain ReceiveChain Value :=
  ⟨state.control, state.send_chain, state.receive_chain, mapArray (mapOption (mapCached interpret)) state.receive_slots⟩

/-- Interpretation commutes with the actual potentially failing array access. -/
theorem mapArray_index {Material Value : Type} {size : Std.Usize} (interpret : Material → Value)
    (array : Std.Array Material size) (index : Std.Usize) :
    Array.index_usize (mapArray interpret array) index = interpret <$> Array.index_usize array index := by
  have indexed : (mapArray interpret array)[index]? = interpret <$> array[index]? := by
    change (array.val.map interpret)[index.val]? = interpret <$> array.val[index.val]?
    exact List.getElem?_map
  simp only [Array.index_usize, indexed]
  cases found : array[index]? <;> rfl

/-- The actual tagged lookup commutes with arbitrary material interpretation, including rejection. -/
theorem receive_key_map {SendChain ReceiveChain Material Value : Type} (interpret : Material → Value)
    (state : RefinedRatchet SendChain ReceiveChain Material) (sequence : Std.U64) :
    refined_receive_key (mapRefined interpret state) sequence =
      mapOption interpret <$> refined_receive_key state sequence := by
  simp only [refined_receive_key, mapRefined, mapArray_index, map_bind]
  congr 1
  funext logical
  cases logical with
  | none => rfl
  | some slot =>
    simp only [map_bind]
    congr 1
    funext index
    congr 1
    funext capacity
    by_cases outside : index ≥ capacity
    · simp only [outside, if_true]
      rfl
    · simp only [outside, if_false, map_bind, bind_map_left]
      congr 1
      funext entry
      cases entry <;> simp [mapOption, mapCached, core.option.Option.as_ref]
      all_goals first | rfl | (split <;> rfl)

/-- Branching on slot presence commutes with an arbitrary payload interpretation. -/
theorem mapOption_elim {Material Value Result : Type} (interpret : Material → Value)
    (entry : core.option.Option Material) (absent : Result) (present : Value → Result) :
    (match mapOption interpret entry with | .None => absent | .Some value => present value) =
      (match entry with | .None => absent | .Some material => present (interpret material)) := by
  cases entry <;> rfl

/-- The extracted immutable option borrow retains the complete optional payload. -/
theorem option_as_ref {Material : Type} (entry : core.option.Option Material) :
    core.option.Option.as_ref entry = RustM.ok entry := by
  cases entry <;> rfl

/-- Actual cached preparation inspects source control and sequence tags, not interpreted material bytes. -/
theorem prepare_cached_map {SendChain ReceiveChain Material Value : Type} (interpret : Material → Value)
    (state : RefinedRatchet SendChain ReceiveChain Material) (sequence : Std.U64) :
    prepare_cached_receive (mapRefined interpret state) sequence = prepare_cached_receive state sequence := by
  simp only [prepare_cached_receive, mapRefined, mapArray_index, bind_map_left,
    option_as_ref, bind_tc_ok]
  congr 1
  funext logical
  cases logical with
  | none => rfl
  | some slot =>
    dsimp only
    congr 1
    funext index
    congr 1
    funext capacity
    by_cases outside : index ≥ capacity
    · simp only [outside, if_true]
    · simp only [outside, if_false]
      congr 1
      funext selected
      congr 1
      funext matchesTag
      cases matchesTag with
      | false => rfl
      | true =>
        simp only [↓reduceIte]
        congr 1
        funext entry
        cases entry with
        | none => rfl
        | some target =>
          simp only [mapOption, mapCached]
          congr 1
          congr 1
          funext len
          congr 1
          congr 1
          funext lastSlot
          congr 1
          funext lastIndex
          congr 1
          congr 1
          funext lastLogical
          cases lastLogical with
          | none => rfl
          | some lastSequence =>
            dsimp only
            congr 1
            funext lastEntry
            cases lastEntry <;> rfl

/-- Updating a source array preserves the exact interpreted payload and index. -/
theorem mapArray_set {Material Value : Type} {size : Std.Usize} (interpret : Material → Value)
    (array : Std.Array Material size) (index : Std.Usize) (value : Material) :
    mapArray interpret (Std.Array.set array index value) =
      Std.Array.set (mapArray interpret array) index (interpret value) := by
  apply Subtype.ext
  simp only [mapArray, Std.Array.set, List.map_set]

/-- The potentially failing source update commutes with the same payload interpretation. -/
theorem mapArray_update {Material Value : Type} {size : Std.Usize} (interpret : Material → Value)
    (array : Std.Array Material size) (index : Std.Usize) (value : Material) :
    Std.Array.update (mapArray interpret array) index (interpret value) =
      mapArray interpret <$> Std.Array.update array index value := by
  have indexed : (mapArray interpret array)[index]? = interpret <$> array[index]? := by
    change (array.val.map interpret)[index.val]? = interpret <$> array.val[index.val]?
    exact List.getElem?_map
  simp only [Std.Array.update, indexed]
  cases found : array[index]? with
  | none => rfl
  | some original =>
    change RustM.ok _ = RustM.ok _
    congr 1
    apply Subtype.ext
    simp only [mapArray, List.map_set]

/-- Taking an optional slot returns its payload and clears precisely that slot. -/
theorem option_take {Material : Type} (entry : core.option.Option Material) :
    core.option.Option.take entry = RustM.ok (entry, core.option.Option.None) := by
  rfl

/-- Mapping a successful complete source result retains success and its interpreted value. -/
theorem rust_map_ok {Input Output : Type} (interpret : Input → Output) (value : Input) :
    interpret <$> RustM.ok value = RustM.ok (interpret value) := by
  rfl

/-- Actual cached publication clears or moves whole interpreted entries with unchanged control. -/
theorem publish_cached_map {SendChain ReceiveChain Material Value : Type} (interpret : Material → Value)
    (state : RefinedRatchet SendChain ReceiveChain Material) (prepared : PreparedCachedReceive) :
    publish_cached_receive (mapRefined interpret state) prepared =
      mapRefined interpret <$> publish_cached_receive state prepared := by
  simp only [publish_cached_receive, mapRefined, Array.index_mut_usize, mapArray_index,
    bind_map_left, option_take, bind_tc_ok, map_bind, bind_assoc]
  congr 1
  funext targetIndex
  congr 1
  funext lastIndex
  congr 1
  funext capacity
  by_cases targetOutside : targetIndex ≥ capacity
  · simp only [targetOutside, if_true, rust_map_ok, mapRefined]
  · simp only [targetOutside, if_false]
    by_cases lastOutside : lastIndex ≥ capacity
    · simp only [lastOutside, if_true, rust_map_ok, mapRefined]
    · simp only [lastOutside, if_false]
      by_cases same : targetIndex = lastIndex
      · simp only [same, if_true, map_bind]
        congr 1
        funext entry
        exact congrArg (fun slots => RustM.ok
          { mapRefined interpret state with control := prepared.committed_control, receive_slots := slots })
          (mapArray_set (mapOption (mapCached interpret)) state.receive_slots lastIndex
            core.option.Option.None).symm
      · simp only [same, if_false, map_bind]
        congr 1
        funext moved
        change (massert (targetIndex < 50#usize) >>= _) =
          mapRefined interpret <$> (massert (targetIndex < 50#usize) >>= _)
        rw [map_bind]
        congr 1
        funext checked
        have cleared := mapArray_set (mapOption (mapCached interpret)) state.receive_slots lastIndex
          core.option.Option.None
        simp only [mapOption] at cleared
        rw [← cleared]
        simp only [mapArray_index, bind_map_left]
        rw [map_bind]
        congr 1
        funext targetEntry
        change (Std.Array.update _ targetIndex _ >>= _) =
          mapRefined interpret <$> (Std.Array.update _ targetIndex moved >>= _)
        rw [← mapArray_set, mapArray_update, bind_map_left, map_bind]
        congr 1

/-- Every in-bounds slot value is interpreted exactly, independently of arbitrary defaults. -/
theorem mapArray_get {Material Value : Type} [Inhabited Material] [Inhabited Value]
    {size : Std.Usize} (interpret : Material → Value) (array : Std.Array Material size)
    (index : Nat) (bound : index < size.val) :
    (mapArray interpret array).val[index]! = interpret array.val[index]! := by
  have inside : index < array.val.length := by simpa only [array.property] using bound
  change (array.val.map interpret)[index]! = interpret array.val[index]!
  rw [getElem!_pos (array.val.map interpret) index (by simpa only [List.length_map] using inside),
    getElem!_pos array.val index inside]
  simp only [List.getElem_map]

/-- All in-bounds slot observations determine the entire fixed-size source array. -/
theorem array_ext {Material : Type} [Inhabited Material] {size : Std.Usize}
    (left right : Std.Array Material size)
    (same : ∀ index, index < size.val → left.val[index]! = right.val[index]!) : left = right := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact left.property.trans right.property.symm
  · intro index leftBound rightBound
    simpa only [getElem!_pos left.val index leftBound, getElem!_pos right.val index rightBound] using
      same index (by simpa only [left.property] using leftBound)

/-- Bounded future publication copies and clears the same complete interpreted window. -/
theorem publish_future_slots_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (staged : Std.Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
    (slot left : Std.U8) (bounded : slot.val + left.val ≤ 50) :
    publish_future_receive_slots (mapRefined interpret state)
        (mapArray (mapOption (mapCached interpret)) staged) slot left =
      (fun result => (mapRefined interpret result.1,
        mapArray (mapOption (mapCached interpret)) result.2)) <$>
        publish_future_receive_slots state staged slot left := by
  obtain ⟨out, remaining, executed, control, send, receive, slots, cleared⟩ :=
    publish_future_receive_slots_exact state staged slot left bounded
  obtain ⟨mappedOut, mappedRemaining, mappedExecuted, mappedControl, mappedSend,
    mappedReceive, mappedSlots, mappedCleared⟩ :=
    publish_future_receive_slots_exact (mapRefined interpret state)
      (mapArray (mapOption (mapCached interpret)) staged) slot left bounded
  rw [executed, mappedExecuted, rust_map_ok]
  have slotEquality : mappedOut.receive_slots = mapArray (mapOption (mapCached interpret)) out.receive_slots := by
    apply array_ext
    intro index bound
    rw [mappedSlots index bound]
    simp only [mapRefined,
      mapArray_get (mapOption (mapCached interpret)) staged index bound,
      mapArray_get (mapOption (mapCached interpret)) state.receive_slots index bound,
      mapArray_get (mapOption (mapCached interpret)) out.receive_slots index bound,
      slots index bound]
    split <;> rfl
  have remainingEquality : mappedRemaining = mapArray (mapOption (mapCached interpret)) remaining := by
    apply array_ext
    intro index bound
    rw [mappedCleared index bound]
    simp only [mapArray_get (mapOption (mapCached interpret)) staged index bound,
      mapArray_get (mapOption (mapCached interpret)) remaining index bound, cleared index bound]
    split <;> rfl
  have stateEquality : mappedOut = mapRefined interpret out := by
    cases mappedOut
    cases out
    simp_all only [mapRefined]
  rw [stateEquality, remainingEquality]

/-- Pending interpretation retains all source control, chains, tags, and window coordinates. -/
def mapPending {ReceiveChain Material Value : Type} (interpret : Material → Value)
    (pending : PendingReceive ReceiveChain Material) : PendingReceive ReceiveChain Value :=
  ⟨pending.committed_control, pending.final_receive_chain,
    mapArray (mapOption (mapCached interpret)) pending.staged_slots,
    pending.target_sequence, interpret pending.target_material, pending.first_slot, pending.skipped⟩

/-- Full future publication commutes whenever the actual source window is admitted. -/
theorem publish_future_map_bounded {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material)
    (bounded : pending.first_slot.val + pending.skipped.val ≤ 50) :
    publish_future_receive (mapRefined interpret state) (mapPending interpret pending) =
      mapRefined interpret <$> publish_future_receive state pending := by
  obtain ⟨available, subtraction, availableValue⟩ :=
    uscalar_sub_eq_ok (UScalar.cast UScalarTy.Usize 50#u64)
      (UScalar.cast UScalarTy.Usize pending.first_slot) (by scalar_tac)
  simp only [publish_future_receive, mapPending, mapRefined, lift, capacity_eq_ok, bind_tc_ok,
    if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize pending.first_slot >
      UScalar.cast UScalarTy.Usize 50#u64), subtraction,
    if_neg (by scalar_tac : ¬UScalar.cast UScalarTy.Usize pending.skipped > available)]
  change (publish_future_receive_slots (mapRefined interpret state)
      (mapArray (mapOption (mapCached interpret)) pending.staged_slots)
      pending.first_slot pending.skipped >>= _) = _
  rw [publish_future_slots_map interpret state pending.staged_slots pending.first_slot pending.skipped bounded,
    bind_map_left, map_bind]
  congr 1


/-- A malformed publication window returns the original state before copying any material. -/
theorem publish_future_rejected {SendChain ReceiveChain Material : Type}
    (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material)
    (outside : ¬pending.first_slot.val + pending.skipped.val ≤ 50) :
    publish_future_receive state pending = RustM.ok state := by
  simp only [publish_future_receive, lift, capacity_eq_ok, bind_tc_ok]
  by_cases firstOutside : 50 < pending.first_slot.val
  · rw [if_pos (by scalar_tac)]
  · rw [if_neg (by scalar_tac)]
    obtain ⟨available, subtraction, availableValue⟩ :=
      uscalar_sub_eq_ok (UScalar.cast UScalarTy.Usize 50#u64)
        (UScalar.cast UScalarTy.Usize pending.first_slot) (by scalar_tac)
    simp only [subtraction, bind_tc_ok, if_pos (by scalar_tac :
      UScalar.cast UScalarTy.Usize pending.skipped > available)]

/-- Full actual future publication commutes for every typed pending transaction, including malformed windows. -/
theorem publish_future_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) :
    publish_future_receive (mapRefined interpret state) (mapPending interpret pending) =
      mapRefined interpret <$> publish_future_receive state pending := by
  by_cases bounded : pending.first_slot.val + pending.skipped.val ≤ 50
  · exact publish_future_map_bounded interpret state pending bounded
  · rw [publish_future_rejected state pending bounded,
      publish_future_rejected (mapRefined interpret state) (mapPending interpret pending) bounded,
      rust_map_ok]

/-- Source presence tests never inspect an interpreted payload. -/
theorem option_is_some_map {Material Value : Type} (interpret : Material → Value)
    (entry : core.option.Option Material) :
    core.option.Option.is_some (mapOption interpret entry) = core.option.Option.is_some entry := by
  cases entry <;> rfl

/-- The actual empty-slot loop body is unchanged under material interpretation. -/
theorem empty_slots_body_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (slot left : Std.U8) :
    refined_receive_slots_are_empty_loop.body (mapRefined interpret state) slot left =
      refined_receive_slots_are_empty_loop.body state slot left := by
  simp only [refined_receive_slots_are_empty_loop.body, mapRefined, mapArray_index,
    bind_map_left, option_is_some_map]

/-- The full actual empty-window test is identical, including all loop outcomes. -/
theorem empty_slots_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (slot left : Std.U8) :
    refined_receive_slots_are_empty (mapRefined interpret state) slot left =
      refined_receive_slots_are_empty state slot left := by
  simp only [refined_receive_slots_are_empty, refined_receive_slots_are_empty_loop,
    empty_slots_body_map]

/-- The pending-slot validation body sees the same presence and sequence tags. -/
theorem pending_slots_body_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) (slot left : Std.U8) (expected : Std.U64) :
    pending_receive_slots_are_valid_loop.body (mapRefined interpret state) (mapPending interpret pending)
        slot expected left =
      pending_receive_slots_are_valid_loop.body state pending slot expected left := by
  simp only [pending_receive_slots_are_valid_loop.body, mapRefined, mapPending, mapArray_index,
    bind_map_left, option_is_some_map, option_as_ref, bind_tc_ok]
  congr 1
  congr 1
  funext index
  congr 1
  funext capacity
  congr 1
  congr 1
  funext entry
  congr 1
  funext occupied
  cases occupied with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    congr 1
    funext staged
    cases staged <;> rfl

/-- The complete pending-slot loop is the same source Boolean computation for all indices. -/
theorem pending_slots_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) (slot left : Std.U8) (expected : Std.U64) :
    pending_receive_slots_are_valid (mapRefined interpret state) (mapPending interpret pending)
        slot expected left = pending_receive_slots_are_valid state pending slot expected left := by
  simp only [pending_receive_slots_are_valid, pending_receive_slots_are_valid_loop, pending_slots_body_map]

/-- Every actual pending-transaction validation result is preserved; no well-formedness premise is added. -/
theorem pending_valid_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (state : RefinedRatchet SendChain ReceiveChain Material)
    (pending : PendingReceive ReceiveChain Material) (requested : Std.U64) :
    pending_receive_is_valid (mapRefined interpret state) (mapPending interpret pending) requested =
      pending_receive_is_valid state pending requested := by
  simp only [pending_receive_is_valid, ↓pending_slots_map, mapRefined, mapPending,
    mapArray_index, bind_map_left, option_is_some_map]

/-- Source initialization creates the same fifty empty slots under every interpretation. -/
theorem empty_material_map {Material Value : Type} (interpret : Material → Value) :
    empty_material_slots Value =
      mapArray (mapOption (mapCached interpret)) <$> empty_material_slots Material := by
  rfl

/-- Initial source chains and explicit counters are unchanged when material payloads are interpreted. -/
theorem from_counters_map {SendChain ReceiveChain Material Value : Type}
    (interpret : Material → Value) (send : SendChain) (receive : ReceiveChain)
    (sendSequence receiveSequence : Std.U64) :
    RefinedRatchet.from_counters Value sendSequence receiveSequence send receive =
      mapRefined interpret <$>
        RefinedRatchet.from_counters Material sendSequence receiveSequence send receive := by
  simp only [RefinedRatchet.from_counters, map_bind]
  congr 1

end BeaconcryptCore.Computational.RawCtxMaterialInterpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_index' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_index

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.receive_key_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.receive_key_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapOption_elim' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapOption_elim

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.option_as_ref' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.option_as_ref

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.prepare_cached_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.prepare_cached_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_set' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_set

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_update' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_update

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.option_take' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.option_take

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.rust_map_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.rust_map_ok

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_cached_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_cached_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_get' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.mapArray_get

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.array_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.array_ext

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_slots_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_slots_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_map_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_map_bounded

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_rejected

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.publish_future_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.option_is_some_map' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.option_is_some_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.empty_slots_body_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.empty_slots_body_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.empty_slots_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.empty_slots_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.pending_slots_body_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.pending_slots_body_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.pending_slots_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.pending_slots_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.pending_valid_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.pending_valid_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.empty_material_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.empty_material_map

/-- info: 'BeaconcryptCore.Computational.RawCtxMaterialInterpretation.from_counters_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxMaterialInterpretation.from_counters_map

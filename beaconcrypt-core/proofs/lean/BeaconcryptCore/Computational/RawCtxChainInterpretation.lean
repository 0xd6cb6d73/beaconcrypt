import BeaconcryptCore.Computational.RawCtxInterpretedOpening

/-!
These source laws interpret the send and receive chain coordinates by arbitrary functions, including noninjective functions, while retaining every original material slot, sequence tag, control field and opening context. Cached and future publication preserve the complete RustM result, including malformed-window rejection. The opening interpreter retains arbitrary lawful callback effects and every optional reply without assuming decryption correctness.

The laws do not construct a KDF request interpreter, invert source bytes, sample fresh keys or assert independence, authentication, reveal freshness or a global hybrid. Their purpose is the operational chain representation seam needed by the separate source begin/resume/KDF compiler. Material interpretation remains separate and unchanged.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.control
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxChainInterpretation
open RawCtxMaterialInterpretation RawCtxInterpretedOpening

variable {Send Receive SendValue ReceiveValue Material : Type}

/-- Interpret the two chain coordinates while retaining the complete original control and material slots. -/
def mapChains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) : RefinedRatchet SendValue ReceiveValue Material :=
  ⟨state.control, send state.send_chain, receive state.receive_chain, state.receive_slots⟩

/-- A pending transaction changes only its final receive-chain coordinate. -/
def mapPendingChain (receive : Receive → ReceiveValue)
    (pending : PendingReceive Receive Material) : PendingReceive ReceiveValue Material :=
  ⟨pending.committed_control, receive pending.final_receive_chain, pending.staged_slots,
    pending.target_sequence, pending.target_material, pending.first_slot, pending.skipped⟩

def mapPreparedChain (receive : Receive → ReceiveValue) :
    PreparedReceive Receive Material → PreparedReceive ReceiveValue Material
  | .PreparedReceiveCachedCase prepared => .PreparedReceiveCachedCase prepared
  | .PreparedReceiveFutureCase pending => .PreparedReceiveFutureCase (mapPendingChain receive pending)

def mapOpeningChains {Context : Type} (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (opening : Opening Send Receive Material Context) : Opening SendValue ReceiveValue Material Context :=
  ⟨mapChains send receive opening.entry, opening.context, mapPreparedChain receive opening.prepared⟩

private theorem rust_map_if {Input Output : Type} (f : Input → Output) (p : Prop) [Decidable p]
    (left right : RustM Input) :
    f <$> (if p then left else right) = if p then f <$> left else f <$> right := by
  by_cases h : p <;> simp only [h, ite_true, ite_false]

/-- Cached publication keeps all diagnostic branches and the actual slot movement under arbitrary chain maps. -/
theorem publish_cached_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (prepared : PreparedCachedReceive) :
    publish_cached_receive (mapChains send receive state) prepared =
      mapChains send receive <$> publish_cached_receive state prepared := by
  simp only [publish_cached_receive, mapChains, Array.index_mut_usize, option_take,
    bind_tc_ok, map_bind, bind_assoc, rust_map_if, rust_map_ok]
  congr 1
  funext targetIndex
  congr 1
  funext lastIndex
  congr 1
  funext capacity
  split_ifs
  all_goals try rfl
  congr 1
  funext moved
  change (massert (targetIndex < 50#usize) >>= _) =
    mapChains send receive <$> (massert (targetIndex < 50#usize) >>= _)
  rw [map_bind]
  congr 1
  funext checked
  rw [map_bind]
  congr 1
  funext targetEntry
  change (Std.Array.update _ targetIndex moved >>= _) =
    mapChains send receive <$> (Std.Array.update _ targetIndex moved >>= _)
  rw [map_bind]
  congr 1

/-- The actual cached material accessor does not inspect either chain coordinate. -/
theorem receive_key_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (requested : Std.U64) :
    refined_receive_key (mapChains send receive state) requested = refined_receive_key state requested := rfl

/-- Cached preparation retains the original complete control and slot checks. -/
theorem prepare_cached_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (requested : Std.U64) :
    prepare_cached_receive (mapChains send receive state) requested = prepare_cached_receive state requested := rfl

/-- The slot-validation loop body reads only unchanged slots, sequence tags and control. -/
theorem pending_slots_body_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (pending : PendingReceive Receive Material)
    (slot left : Std.U8) (expected : Std.U64) :
    pending_receive_slots_are_valid_loop.body (mapChains send receive state) (mapPendingChain receive pending)
        slot expected left = pending_receive_slots_are_valid_loop.body state pending slot expected left := rfl

/-- The full source validation loop preserves success, rejection and diagnostics at all indices. -/
theorem pending_slots_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (pending : PendingReceive Receive Material)
    (slot left : Std.U8) (expected : Std.U64) :
    pending_receive_slots_are_valid (mapChains send receive state) (mapPendingChain receive pending)
        slot expected left = pending_receive_slots_are_valid state pending slot expected left := by
  simp only [pending_receive_slots_are_valid, pending_receive_slots_are_valid_loop, pending_slots_body_chains]

/-- Every pending validation branch is unchanged, including malformed pending transactions. -/
theorem pending_valid_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (pending : PendingReceive Receive Material)
    (requested : Std.U64) :
    pending_receive_is_valid (mapChains send receive state) (mapPendingChain receive pending) requested =
      pending_receive_is_valid state pending requested := by
  simp only [pending_receive_is_valid, ↓pending_slots_chains, mapChains, mapPendingChain]

/-- The admitted source copy-and-clear loop preserves every slot while interpreting both chain coordinates. -/
theorem publish_future_slots_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material)
    (staged : Std.Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
    (slot left : Std.U8) (bounded : slot.val + left.val ≤ 50) :
    publish_future_receive_slots (mapChains send receive state) staged slot left =
      (fun result => (mapChains send receive result.1, result.2)) <$>
        publish_future_receive_slots state staged slot left := by
  obtain ⟨out, remaining, executed, control, sent, received, slots, cleared⟩ :=
    publish_future_receive_slots_exact state staged slot left bounded
  obtain ⟨mappedOut, mappedRemaining, mappedExecuted, mappedControl, mappedSend,
    mappedReceive, mappedSlots, mappedCleared⟩ :=
    publish_future_receive_slots_exact (mapChains send receive state) staged slot left bounded
  rw [executed, mappedExecuted, rust_map_ok]
  have slotEquality : mappedOut.receive_slots = out.receive_slots := by
    apply array_ext
    intro index bound
    exact (mappedSlots index bound).trans (slots index bound).symm
  have remainingEquality : mappedRemaining = remaining := by
    apply array_ext
    intro index bound
    exact (mappedCleared index bound).trans (cleared index bound).symm
  have stateEquality : mappedOut = mapChains send receive out := by
    cases mappedOut
    cases out
    simp_all only [mapChains]
  rw [stateEquality, remainingEquality]

/-- Admitted future publication installs the interpreted final chain and the same complete material window. -/
theorem publish_future_chains_bounded (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (pending : PendingReceive Receive Material)
    (bounded : pending.first_slot.val + pending.skipped.val ≤ 50) :
    publish_future_receive (mapChains send receive state) (mapPendingChain receive pending) =
      mapChains send receive <$> publish_future_receive state pending := by
  obtain ⟨available, subtraction, availableValue⟩ :=
    uscalar_sub_eq_ok (UScalar.cast UScalarTy.Usize 50#u64)
      (UScalar.cast UScalarTy.Usize pending.first_slot) (by scalar_tac)
  simp only [publish_future_receive, mapPendingChain, mapChains, lift, capacity_eq_ok, bind_tc_ok,
    ite_eq_right (by scalar_tac : ¬UScalar.cast UScalarTy.Usize pending.first_slot >
      UScalar.cast UScalarTy.Usize 50#u64), subtraction,
    ite_eq_right (by scalar_tac : ¬UScalar.cast UScalarTy.Usize pending.skipped > available)]
  change (publish_future_receive_slots (mapChains send receive state) pending.staged_slots
      pending.first_slot pending.skipped >>= _) = _
  rw [publish_future_slots_chains send receive state pending.staged_slots pending.first_slot
    pending.skipped bounded, bind_map_left, map_bind]
  congr 1

/-- Future publication commutes for every typed transaction; malformed windows retain the original state. -/
theorem publish_future_chains (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (state : RefinedRatchet Send Receive Material) (pending : PendingReceive Receive Material) :
    publish_future_receive (mapChains send receive state) (mapPendingChain receive pending) =
      mapChains send receive <$> publish_future_receive state pending := by
  by_cases bounded : pending.first_slot.val + pending.skipped.val ≤ 50
  · exact publish_future_chains_bounded send receive state pending bounded
  · rw [publish_future_rejected state pending bounded,
      publish_future_rejected (mapChains send receive state) (mapPendingChain receive pending) bounded,
      rust_map_ok]

/-- Opening sequence selection retains the actual cached or future source sequence. -/
theorem opening_sequence_chains {Context : Type} (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (opening : Opening Send Receive Material Context) :
    sequence (mapOpeningChains send receive opening) = sequence opening := by
  cases prepared : opening.prepared <;>
    simp only [RawCtxInterpretedOpening.sequence, mapOpeningChains, prepared, mapPreparedChain, mapPendingChain]

/-- The complete opening material getter retains missing and mistagged slots, without inspecting chains. -/
theorem opening_material_chains {Context : Type} (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (opening : Opening Send Receive Material Context) :
    material (mapOpeningChains send receive opening) = material opening := by
  cases prepared : opening.prepared <;>
    simp only [material, mapOpeningChains, prepared, mapPreparedChain, mapPendingChain, mapChains]

/-- Every optional opening reply returns the correspondingly interpreted full kernel and unchanged reply. -/
theorem opening_finish_chains {Context Plaintext : Type}
    (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (opening : Opening Send Receive Material Context) (reply : core.option.Option Plaintext) :
    finish (mapOpeningChains send receive opening) reply =
      (fun result => (mapChains send receive result.1, result.2)) <$> finish opening reply := by
  cases reply with
  | none => rfl
  | some plaintext =>
      cases prepared : opening.prepared <;>
        simp only [finish, mapOpeningChains, mapPreparedChain, prepared,
          publish_cached_chains, publish_future_chains, bind_map_left, map_bind]
      all_goals congr 1

/-- Arbitrary lawful callback effects and every optional publication survive chain interpretation without a callback compatibility premise. -/
theorem opening_run_chains {m : Type → Type} [Monad m] [LawfulMonad m]
    {Context Plaintext : Type} (send : Send → SendValue) (receive : Receive → ReceiveValue)
    (opening : Opening Send Receive Material Context)
    (callback : Material → Std.U64 → Context → m (core.option.Option Plaintext)) :
    RawCtxInterpretedOpening.run callback (mapOpeningChains send receive opening) =
      (fun result => (fun published => (mapChains send receive published.1, published.2)) <$> result) <$>
        RawCtxInterpretedOpening.run callback opening := by
  simp only [RawCtxInterpretedOpening.run, opening_material_chains]
  cases actual : material opening with
  | fail error => simp only [bindResult, map_pure]; rfl
  | div => simp only [bindResult, map_pure]; rfl
  | ok selected =>
    cases selected with
    | none => simp only [bindResult, opening_finish_chains, map_pure]
    | some selected =>
      simp only [bindResult, opening_sequence_chains]
      cases prepared : RawCtxInterpretedOpening.sequence opening with
      | fail error => simp only [map_pure]; rfl
      | div => simp only [map_pure]; rfl
      | ok preparedSequence =>
        simp only [↓opening_finish_chains, mapOpeningChains, map_bind, map_pure]

end BeaconcryptCore.Computational.RawCtxChainInterpretation

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_cached_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_cached_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.receive_key_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.receive_key_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.prepare_cached_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.prepare_cached_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.pending_slots_body_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.pending_slots_body_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.pending_slots_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.pending_slots_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.pending_valid_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.pending_valid_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_future_slots_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_future_slots_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_future_chains_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_future_chains_bounded

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_future_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.publish_future_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_sequence_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_sequence_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_material_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_material_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_finish_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_finish_chains

/-- info: 'BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_run_chains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainInterpretation.opening_run_chains

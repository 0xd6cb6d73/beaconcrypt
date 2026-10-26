import BeaconcryptCore.Computational.RawCtxSelectedSendAddress

/-!
The private nonce-stop trace records actual selected send callbacks, including an unsuccessful writer and the final refused attempt. Owner labels come from original outer dispatch; they are never recovered from key bytes, addresses, sender IDs or associated data. Recording has no selected-key argument and leaves the complete component program intact. The later global source consumer must supply original admission and routing witnesses for these same records.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSendTrace
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey
open AdaptiveCtxReceive AdaptiveCtxDynamicKnownKeys RawCtxSelectedMessageSealing

abbrev Pending := RawCtxInterpretedSend.Seal Slot RawCtxSourceSend.SealContext

/-- These are actual key-free private caller values. The outer dispatcher supplies owner and old kernel; the original driver supplies the pending seal. -/
structure Occurrence (Owner : Type) where
  owner : Owner
  entry : RawCtxSelectedMessageReveals.Kernel
  pending : Pending

def nonce (pending : Pending) : Option NonceOutput :=
  match pending.material with
  | .known _ => none
  | .hidden value => if pending.context.associatedData.length = 281 then some value else none

def note {Owner : Type} (occurrence : Occurrence Owner) (before : List (Occurrence Owner)) : List (Occurrence Owner) :=
  if (nonce occurrence.pending).isSome then before ++ [occurrence] else before

/-- The unchanged scalar optional reply is returned together with the same original pending occurrence, even when the reply is the explicit nonce stop. -/
noncomputable def sealing {Owner : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (occurrence : Occurrence Owner) : StateT (List (Occurrence Owner)) (OracleComp Spec)
      (Option (Option RawCtxSourceSend.Encrypted)) := fun before =>
  (fun reply => (reply, note occurrence before)) <$> RawCtxSelectedSealConsumer.sealing c writer occurrence.pending

/-- Private occurrence instrumentation erases to the literal original scalar component program, with both option layers untouched. -/
theorem erase {Owner : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (occurrence : Occurrence Owner) (before : List (Occurrence Owner)) :
    Prod.fst <$> (sealing c writer occurrence).run before =
      RawCtxSelectedSealConsumer.sealing c writer occurrence.pending := by
  simp only [sealing, StateT.run, Functor.map_map]
  exact id_map _

/-- An actual component refusal is precisely an already-used selected nonce; neither a known-key alias nor writer failure can produce it. -/
theorem repeated_source (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext)
    (before after : SourceState)
    (supported : (SealResult.repeatedNonce, after) ∈ support ((simulateQ (sourceImpl true decode c key)
      (RawCtxSelectedSealConsumer.call c writer input)).run before)) :
    ∃ value, input.material = .hidden value ∧ input.context.associatedData.length = 281 ∧
      value ∈ before.selected.1.usedNonces ∧ after = before := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | known material =>
      rw [RawCtxSelectedSealConsumer.known_call] at supported
      simp only [support_map] at supported
      obtain ⟨reply, _, impossible⟩ := supported
      cases impossible
  | hidden value =>
      by_cases width : context.associatedData.length = 281
      · by_cases used : value ∈ before.selected.1.usedNonces
        · rw [RawCtxSelectedSealConsumer.selected_repeat_call decode c key writer value sequence context width before used] at supported
          simp only [mem_support_pure_iff, Prod.mk.injEq, true_and] at supported
          exact ⟨value, rfl, width, used, supported⟩
        · rw [RawCtxSelectedSealConsumer.selected_fresh_call decode c key writer value sequence context width before used] at supported
          simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
          obtain ⟨reply, _, impossible⟩ := supported
          cases impossible
      · simp only [RawCtxSelectedSealConsumer.call, RawCtxSelectedMessageSealing.selected, dite_eq_right width,
          simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported

/-- The native scalar callback's outer stop retains its complete prior component state and has an actual selected-nonce witness. -/
theorem stopped_source (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (pending : Pending) (before after : SourceState)
    (supported : (none, after) ∈ support ((simulateQ (sourceImpl true decode c key)
      (RawCtxSelectedSealConsumer.sealing c writer pending)).run before)) :
    ∃ value, nonce pending = some value ∧ value ∈ before.selected.1.usedNonces ∧ after = before := by
  simp only [RawCtxSelectedSealConsumer.sealing, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨reply, reached, equal⟩ := supported
  cases found : reply.1 with
  | repeatedNonce =>
      have actual := repeated_source decode c key writer (RawCtxInterpretedArguments.sealArguments pending) before reply.2
        (by rw [← found]; exact reached)
      obtain ⟨value, material, width, used, state⟩ := actual
      have same : after = reply.2 := (congrArg Prod.snd equal).symm
      refine ⟨value, ?_, used, same.trans state⟩
      change pending.material = .hidden value at material
      change pending.context.associatedData.length = 281 at width
      simp only [nonce, material, ite_eq_left width]
  | completed ciphertext =>
      have impossible := congrArg Prod.fst equal
      simp only [found, RawCtxSelectedSealConsumer.reply] at impossible
      cases impossible

/-- A callback can add only the nonce carried by its original selected pending send. -/
theorem call_used (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer)
    (input : RawCtxInterpretedArguments.Input Slot RawCtxSourceSend.SealContext)
    (before after : SourceState) (reply : SealResult)
    (supported : (reply, after) ∈ support ((simulateQ (sourceImpl true decode c key)
      (RawCtxSelectedSealConsumer.call c writer input)).run before)) :
    ∀ value ∈ after.selected.1.usedNonces,
      value ∈ before.selected.1.usedNonces ∨
        (input.material = .hidden value ∧ input.context.associatedData.length = 281) := by
  rcases input with ⟨material, sequence, context⟩
  cases material with
  | known material =>
      rw [RawCtxSelectedSealConsumer.known_call] at supported
      simp only [support_map] at supported
      obtain ⟨result, _, equal⟩ := supported
      have state := congrArg Prod.snd equal
      dsimp only at state
      subst after
      intro value used
      exact Or.inl used
  | hidden value =>
      by_cases width : context.associatedData.length = 281
      · by_cases used : value ∈ before.selected.1.usedNonces
        · rw [RawCtxSelectedSealConsumer.selected_repeat_call decode c key writer value sequence context width before used] at supported
          simp only [mem_support_pure_iff, Prod.mk.injEq] at supported
          rcases supported with ⟨_, rfl⟩
          exact fun _ found => Or.inl found
        · rw [RawCtxSelectedSealConsumer.selected_fresh_call decode c key writer value sequence context width before used] at supported
          simp only [mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at supported
          obtain ⟨result, _, _, state⟩ := supported
          subst after
          intro candidate found
          change candidate ∈ value :: before.selected.1.usedNonces at found
          rcases List.mem_cons.mp found with equal | old
          · subst candidate
            exact Or.inr ⟨rfl, width⟩
          · exact Or.inl old
      · simp only [RawCtxSelectedSealConsumer.call, RawCtxSelectedMessageSealing.selected, dite_eq_right width,
          simulateQ_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
        rcases supported with ⟨_, rfl⟩
        exact fun _ found => Or.inl found

/-- Every nonce in the ordinary component ledger has an earlier privately recorded original send callback. -/
def Tracked {Owner : Type} (state : SourceState) (history : List (Occurrence Owner)) : Prop :=
  ∀ value ∈ state.selected.1.usedNonces,
    ∃ occurrence ∈ history, nonce occurrence.pending = some value

/-- Empty ordinary sealing history starts with an empty occurrence ledger; no caller-supplied nonce invariant is needed. -/
theorem tracked_empty {Owner : Type} (state : SourceState)
    (empty : state.selected.1.usedNonces = []) : Tracked state ([] : List (Occurrence Owner)) := by
  simp only [Tracked, empty, List.not_mem_nil, false_implies, forall_const]

/-- Recording retains every earlier occurrence in its original order and adds at most this one actual attempt. -/
theorem note_old {Owner : Type} (current earlier : Occurrence Owner) (history : List (Occurrence Owner))
    (found : earlier ∈ history) : earlier ∈ note current history := by
  simp only [note]
  split
  · exact List.mem_append_left _ found
  · exact found

/-- A selected call is recorded even if serialization failed or the nonce was refused. -/
theorem note_selected {Owner : Type} (current : Occurrence Owner) (history : List (Occurrence Owner))
    (value : NonceOutput) (selected : nonce current.pending = some value) :
    note current history = history ++ [current] := by
  simp only [note, selected, Option.isSome_some, ↓reduceIte]

/-- The scalar optional API does not change which nonce can enter the selected ledger. -/
theorem scalar_used (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (pending : Pending) (before after : SourceState)
    (reply : Option (Option RawCtxSourceSend.Encrypted))
    (supported : (reply, after) ∈ support ((simulateQ (sourceImpl true decode c key)
      (RawCtxSelectedSealConsumer.sealing c writer pending)).run before)) :
    ∀ value ∈ after.selected.1.usedNonces,
      value ∈ before.selected.1.usedNonces ∨ nonce pending = some value := by
  simp only [RawCtxSelectedSealConsumer.sealing, simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  have state := congrArg Prod.snd equal
  dsimp only at state
  subst after
  intro value used
  rcases call_used decode c key writer (RawCtxInterpretedArguments.sealArguments pending)
      before result.2 result.1 reached value used with old | selected
  · exact Or.inl old
  · obtain ⟨material, width⟩ := selected
    change pending.material = .hidden value at material
    change pending.context.associatedData.length = 281 at width
    exact Or.inr (by simp only [nonce, material, ite_eq_left width])

/-- Every actual scalar sealing outcome preserves the occurrence invariant, including writer rejection and nonce stopping. -/
theorem tracked_step {Owner : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (current : Occurrence Owner) (history : List (Occurrence Owner))
    (before after : SourceState) (reply : Option (Option RawCtxSourceSend.Encrypted))
    (tracked : Tracked before history)
    (supported : (reply, after) ∈ support ((simulateQ (sourceImpl true decode c key)
      (RawCtxSelectedSealConsumer.sealing c writer current.pending)).run before)) :
    Tracked after (note current history) := by
  intro value used
  rcases scalar_used decode c key writer current.pending before after reply supported value used with old | selected
  · obtain ⟨earlier, found, same⟩ := tracked value old
    exact ⟨earlier, note_old current earlier history found, same⟩
  · rw [note_selected current history value selected]
    exact ⟨current, List.mem_append_right _ (List.mem_singleton_self _), selected⟩

/-- An actual stopped send has an earlier recorded occurrence with exactly the same nonce, and records the current attempt last. The full component state is unchanged at refusal. -/
theorem stopped_evidence {Owner : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (current : Occurrence Owner)
    (history afterHistory : List (Occurrence Owner)) (before after : SourceState)
    (tracked : Tracked before history)
    (supported : ((none, afterHistory), after) ∈ support ((simulateQ (sourceImpl true decode c key)
      ((sealing c writer current).run history)).run before)) :
    ∃ value earlier, earlier ∈ history ∧ nonce earlier.pending = some value ∧
      nonce current.pending = some value ∧ afterHistory = history ++ [current] ∧ after = before := by
  change ((none, afterHistory), after) ∈ support ((simulateQ (sourceImpl true decode c key)
    ((fun reply => (reply, note current history)) <$> RawCtxSelectedSealConsumer.sealing c writer current.pending)).run before) at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  have reply := congrArg (fun value => value.1.1) equal
  have state := congrArg Prod.snd equal
  have historyEq := congrArg (fun value => value.1.2) equal
  dsimp only at reply state historyEq
  obtain ⟨value, selected, used, unchanged⟩ := stopped_source decode c key writer current.pending before result.2
    (by rw [← reply]; exact reached)
  obtain ⟨earlier, found, same⟩ := tracked value used
  exact ⟨value, earlier, found, same, selected,
    historyEq.symm.trans (note_selected current history value selected), state.symm.trans unchanged⟩

/-- Source provenance is the actual normal send admission and the original driver's literal ready callback. It is checked before any challenger reply. -/
def Routed {Owner : Type} (route : SymmetricRatchetKdfRequest → RatchetChain × Slot)
    (occurrence : Occurrence Owner) : Prop :=
  ∃ request : RawCtxInterpretedSend.Kdf Slot RawCtxSourceSend.SealContext,
    RawCtxInterpretedSend.normalBegin occurrence.entry occurrence.pending.context = .requested request ∧
      occurrence.pending = RawCtxInterpretedSend.ready request (route request.request)

/-- The first-record source route attributes a recorded selected nonce to the actual selected sending-chain input. -/
theorem routed_chain {Owner : Type} (prior : RawCtxSelectedParentTable.Prior)
    (target next : RootOutput) (selectedNonce value : NonceOutput) (occurrence : Occurrence Owner)
    (routed : Routed (RawCtxSelectedMessageKdf.step prior target selectedNonce next) occurrence)
    (selected : nonce occurrence.pending = some value) :
    occurrence.entry.send_chain = RawCtxFreshChainCut.concreteChain target := by
  obtain ⟨request, admitted, ready⟩ := routed
  have material : occurrence.pending.material = .hidden value := by
    unfold nonce at selected
    split at selected
    · cases selected
    · split at selected
      · cases selected
        assumption
      · cases selected
  rw [ready] at material
  exact RawCtxSelectedSendAddress.selected_chain prior target selectedNonce value next
    occurrence.entry occurrence.pending.context request admitted material

/-- The later source route additionally retains predecessor priority; nonce evidence still attributes the original sending chain exactly. -/
theorem later_routed_chain {Owner : Type} (prior : RawCtxSelectedParentTable.Prior)
    (parent : RawCtxSelectedParentEntry.Entry) (target next : RootOutput)
    (selectedNonce value : NonceOutput) (occurrence : Occurrence Owner)
    (routed : Routed (RawCtxSelectedMessageKdf.later prior parent target selectedNonce next) occurrence)
    (selected : nonce occurrence.pending = some value) :
    RawCtxSelectedPendingCut.requestAddress occurrence.entry.send_chain ≠ parent.address ∧
      occurrence.entry.send_chain = RawCtxFreshChainCut.concreteChain target := by
  obtain ⟨request, admitted, ready⟩ := routed
  have material : occurrence.pending.material = .hidden value := by
    unfold nonce at selected
    split at selected
    · cases selected
    · split at selected
      · cases selected
        assumption
      · cases selected
  rw [ready] at material
  have source := (RawCtxSelectedSendAddress.selected_later_send prior parent target selectedNonce value next
    occurrence.entry occurrence.pending.context request admitted).mp material
  exact ⟨source.1, RawCtxSelectedSendAddress.address_injective source.2.1⟩

/-- Instrumentation counts at most one actual selected attempt per original scalar callback. -/
theorem note_length {Owner : Type} (current : Occurrence Owner) (history : List (Occurrence Owner)) :
    (note current history).length ≤ history.length + 1 := by
  simp only [note]
  split <;> simp

/-- Every component query allowance is exactly that of the original scalar callback; private tracing adds no primitive work. -/
theorem sealing_bound {Owner : Type} (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (current : Occurrence Owner) (history : List (Occurrence Owner))
    (predicate : Spec.Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    ((sealing c writer current).run history).IsQueryBoundP predicate bound ↔
      (RawCtxSelectedSealConsumer.sealing c writer current.pending).IsQueryBoundP predicate bound := by
  change ((fun reply => (reply, note current history)) <$>
    RawCtxSelectedSealConsumer.sealing c writer current.pending).IsQueryBoundP predicate bound ↔ _
  exact isQueryBoundP_map_iff _ _ _

/-- The ordinary empty initial game supplies the trace invariant directly. -/
theorem initial_tracked {Owner : Type} : Tracked initialSource ([] : List (Occurrence Owner)) := by
  exact tracked_empty initialSource rfl

/-- The actual instrumented callback preserves the nonce/occurrence relation and charges at most one recorded attempt, for every optional outcome. -/
theorem recorded_step {Owner : Type} (decode : RawDecoder) (c : Pqxdh.Crypto) (key : RootOutput)
    (writer : RawCtxMixedShared.Writer) (current : Occurrence Owner)
    (history afterHistory : List (Occurrence Owner)) (before after : SourceState)
    (reply : Option (Option RawCtxSourceSend.Encrypted)) (tracked : Tracked before history)
    (supported : ((reply, afterHistory), after) ∈ support ((simulateQ (sourceImpl true decode c key)
      ((sealing c writer current).run history)).run before)) :
    Tracked after afterHistory ∧ afterHistory.length ≤ history.length + 1 := by
  change ((reply, afterHistory), after) ∈ support ((simulateQ (sourceImpl true decode c key)
    ((fun answer => (answer, note current history)) <$> RawCtxSelectedSealConsumer.sealing c writer current.pending)).run before) at supported
  simp only [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨result, reached, equal⟩ := supported
  have state := congrArg Prod.snd equal
  have historyEq := congrArg (fun value => value.1.2) equal
  dsimp only at state historyEq
  subst after afterHistory
  exact ⟨tracked_step decode c key writer current history before result.2 result.1 tracked reached,
    note_length current history⟩

end BeaconcryptCore.Computational.RawCtxSelectedSendTrace

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.repeated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.repeated_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.stopped_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.stopped_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.call_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.call_used

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.tracked_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.tracked_empty

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.note_old' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.note_old

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.note_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.note_selected

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.scalar_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.scalar_used

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.tracked_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.tracked_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.stopped_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.stopped_evidence

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.routed_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.routed_chain

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.later_routed_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.later_routed_chain

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.note_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.note_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.sealing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.sealing_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.initial_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.initial_tracked

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendTrace.recorded_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendTrace.recorded_step

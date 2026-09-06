import BeaconcryptCore.Computational.RawCtxMaterialInterpretation

/-!
This thin polymorphic opening adapter uses the extracted cached/future publication functions and preserves the native opening object's exact getter and finish behavior. Material interpretation may identify distinct labels. It does not infer a unique label from bytes, replace the receive control machine, or assert a whole-owner/evolving-key security reduction.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInterpretedOpening
open RawCtxMaterialInterpretation

structure Opening (SendChain ReceiveChain Material Context : Type) where
  entry : RefinedRatchet SendChain ReceiveChain Material
  context : Context
  prepared : PreparedReceive ReceiveChain Material

def mapPrepared {ReceiveChain Material Value : Type} (interpret : Material → Value) :
    PreparedReceive ReceiveChain Material → PreparedReceive ReceiveChain Value
  | .PreparedReceiveCachedCase prepared => .PreparedReceiveCachedCase prepared
  | .PreparedReceiveFutureCase pending => .PreparedReceiveFutureCase (mapPending interpret pending)

def mapOpening {SendChain ReceiveChain Material Value Context : Type} (interpret : Material → Value)
    (opening : Opening SendChain ReceiveChain Material Context) : Opening SendChain ReceiveChain Value Context :=
  ⟨mapRefined interpret opening.entry, opening.context, mapPrepared interpret opening.prepared⟩

def sequence {SendChain ReceiveChain Material Context : Type}
    (opening : Opening SendChain ReceiveChain Material Context) : RustM Std.U64 :=
  match opening.prepared with
  | .PreparedReceiveCachedCase prepared => ok prepared.sequence
  | .PreparedReceiveFutureCase pending => ok pending.target_sequence

def material {SendChain ReceiveChain Material Context : Type}
    (opening : Opening SendChain ReceiveChain Material Context) : RustM (core.option.Option Material) :=
  match opening.prepared with
  | .PreparedReceiveCachedCase prepared => do
    let index ← lift (UScalar.cast .Usize prepared.target_slot)
    let capacity ← ratchet.control.RECEIVE_CACHE_CAPACITY
    if index ≥ capacity then ok core.option.Option.None else do
      let entry ← Array.index_usize opening.entry.receive_slots index
      let borrowed ← core.option.Option.as_ref entry
      match borrowed with
      | .None => ok core.option.Option.None
      | .Some cached =>
        if cached.sequence = prepared.sequence then ok (.Some cached.material) else ok core.option.Option.None
  | .PreparedReceiveFutureCase pending => ok (.Some pending.target_material)

def finish {SendChain ReceiveChain Material Context Plaintext : Type}
    (opening : Opening SendChain ReceiveChain Material Context) (reply : core.option.Option Plaintext) :
    RustM (RefinedRatchet SendChain ReceiveChain Material × core.option.Option Plaintext) :=
  match reply with
  | .None => ok (opening.entry, core.option.Option.None)
  | .Some _ => match opening.prepared with
    | .PreparedReceiveCachedCase prepared => do
      let published ← publish_cached_receive opening.entry prepared
      ok (published, reply)
    | .PreparedReceiveFutureCase pending => do
      let published ← publish_future_receive opening.entry pending
      ok (published, reply)

def toNative {Context : Type} (opening : Opening RatchetChain RatchetChain RatchetMaterial Context) :
    ReceiveOpen Context := ⟨⟨opening.entry⟩, opening.context, opening.prepared⟩

/-- Specialization preserves the complete actual native finish result, including rejection and publication. -/
theorem native_finish {Context Plaintext : Type}
    (opening : Opening RatchetChain RatchetChain RatchetMaterial Context) (reply : core.option.Option Plaintext) :
    ReceiveOpen.finish (toNative opening) reply =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> finish opening reply := by
  cases reply with
  | none => rfl
  | some plaintext =>
    cases prepared : opening.prepared <;> simp only [toNative, ReceiveOpen.finish, finish, prepared, map_bind]
    all_goals congr 1

/-- The specialized sequence getter is exactly the extracted native getter. -/
theorem native_sequence {Context : Type}
    (opening : Opening RatchetChain RatchetChain RatchetMaterial Context) :
    ReceiveOpen.sequence (toNative opening) = sequence opening := by
  cases prepared : opening.prepared <;>
    simp only [toNative, ReceiveOpen.sequence, sequence, prepared]

/-- The specialized material getter retains the actual prepared slot lookup and every rejection. -/
theorem native_material {Context : Type}
    (opening : Opening RatchetChain RatchetChain RatchetMaterial Context) :
    ReceiveOpen.material (toNative opening) = material opening := by
  cases prepared : opening.prepared <;>
    simp only [toNative, ReceiveOpen.material, material, prepared]
  all_goals
    congr 1
    funext index
    congr 1
    funext capacity
    congr 1
    congr 1
    funext entry
    congr 1
    funext borrowed
    cases borrowed <;> rfl

/-- Material interpretation commutes with final publication for every actual optional reply. -/
theorem finish_map {SendChain ReceiveChain Material Value Context Plaintext : Type}
    (interpret : Material → Value) (opening : Opening SendChain ReceiveChain Material Context)
    (reply : core.option.Option Plaintext) :
    finish (mapOpening interpret opening) reply =
      (fun result => (mapRefined interpret result.1, result.2)) <$> finish opening reply := by
  cases reply with
  | none => rfl
  | some plaintext =>
    cases prepared : opening.prepared <;>
      simp only [finish, mapOpening, mapPrepared, prepared, publish_cached_map, publish_future_map,
        bind_map_left, map_bind]
    all_goals congr 1

/-- Interpretation retains the actual prepared sequence without a provenance premise. -/
theorem sequence_map {SendChain ReceiveChain Material Value Context : Type}
    (interpret : Material → Value) (opening : Opening SendChain ReceiveChain Material Context) :
    sequence (mapOpening interpret opening) = sequence opening := by
  cases prepared : opening.prepared <;>
    simp only [sequence, mapOpening, mapPrepared, mapPending, prepared]

/-- The exact prepared-slot getter commutes with arbitrary interpretation, including missing or mistagged slots. -/
theorem material_map {SendChain ReceiveChain Material Value Context : Type}
    (interpret : Material → Value) (opening : Opening SendChain ReceiveChain Material Context) :
    material (mapOpening interpret opening) = mapOption interpret <$> material opening := by
  cases prepared : opening.prepared with
  | PreparedReceiveFutureCase pending =>
    simp only [material, mapOpening, mapPrepared, mapPending, prepared]
    rfl
  | PreparedReceiveCachedCase cached =>
    simp only [material, mapOpening, mapPrepared, prepared, mapRefined, mapArray_index,
      bind_map_left, option_as_ref, bind_tc_ok, map_bind]
    congr 1
    funext index
    congr 1
    funext capacity
    by_cases outside : index ≥ capacity
    · simp only [outside, if_true]
      rfl
    · simp only [outside, if_false, map_bind]
      congr 1
      funext entry
      cases entry with
      | none => rfl
      | some found =>
        simp only [mapOption, mapCached]
        split <;> rfl

/-- Lift source failure/divergence without inventing an optional API rejection. -/
def bindResult {m : Type → Type} [Pure m] {Input Output : Type}
    (result : RustM Input) (next : Input → m (RustM Output)) : m (RustM Output) :=
  match result with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- The thin opening interpreter queries only the actual optional material and retains complete source results. -/
def run {m : Type → Type} [Monad m] {SendChain ReceiveChain Material Context Plaintext : Type}
    (callback : Material → Std.U64 → Context → m (core.option.Option Plaintext))
    (opening : Opening SendChain ReceiveChain Material Context) :
    m (RustM (RefinedRatchet SendChain ReceiveChain Material × core.option.Option Plaintext)) :=
  bindResult (material opening) fun selected => match selected with
  | .None => pure (finish opening core.option.Option.None)
  | .Some selected => bindResult (sequence opening) fun preparedSequence => do
    let reply ← callback selected preparedSequence opening.context
    pure (finish opening reply)

/-- Arbitrary lawful effect interpretation retains all callback state before the same optional publication. -/
theorem run_map {m : Type → Type} [Monad m] [LawfulMonad m]
    {SendChain ReceiveChain Material Value Context Plaintext : Type}
    (interpret : Material → Value) (opening : Opening SendChain ReceiveChain Material Context)
    (native : Value → Std.U64 → Context → m (core.option.Option Plaintext))
    (labelled : Material → Std.U64 → Context → m (core.option.Option Plaintext))
    (compatible : ∀ label preparedSequence context,
      native (interpret label) preparedSequence context = labelled label preparedSequence context) :
    run native (mapOpening interpret opening) =
      (fun result => (fun published => (mapRefined interpret published.1, published.2)) <$> result) <$>
        run labelled opening := by
  simp only [run, material_map]
  cases actual : material opening with
  | fail error => simp only [bindResult, map_pure]; rfl
  | div => simp only [bindResult, map_pure]; rfl
  | ok selected =>
    cases selected with
    | none => simp only [rust_map_ok, bindResult, mapOption, finish_map, map_pure]
    | some selected =>
      simp only [rust_map_ok, mapOption, bindResult, sequence_map]
      cases prepared : sequence opening with
      | fail error => simp only [map_pure]; rfl
      | div => simp only [map_pure]; rfl
      | ok preparedSequence =>
        simp only [↓finish_map, mapOpening, compatible, map_bind, map_pure]

/-- Interpret the extracted native getters and finish while retaining their complete source result. -/
def nativeRun {m : Type → Type} [Monad m] {Context Plaintext : Type}
    (callback : RatchetMaterial → Std.U64 → Context → m (core.option.Option Plaintext))
    (opening : ReceiveOpen Context) : m (RustM (ConcreteRatchetKernel × core.option.Option Plaintext)) :=
  bindResult (ReceiveOpen.material opening) fun selected => match selected with
  | .None => pure (ReceiveOpen.finish opening core.option.Option.None)
  | .Some selected => bindResult (ReceiveOpen.sequence opening) fun preparedSequence =>
      bindResult (ReceiveOpen.impl.context opening) fun context => do
        let reply ← callback selected preparedSequence context
        pure (ReceiveOpen.finish opening reply)

/-- The thin interpreter specializes to the extracted native material/sequence/context/finish choreography. -/
theorem native_run {m : Type → Type} [Monad m] [LawfulMonad m] {Context Plaintext : Type}
    (callback : RatchetMaterial → Std.U64 → Context → m (core.option.Option Plaintext))
    (opening : Opening RatchetChain RatchetChain RatchetMaterial Context) :
    nativeRun callback (toNative opening) =
      (fun result => (fun published => (ConcreteRatchetKernel.mk published.1, published.2)) <$> result) <$>
        run callback opening := by
  simp only [nativeRun, native_material, native_sequence, run]
  cases actual : material opening with
  | fail error => simp only [bindResult, map_pure]; rfl
  | div => simp only [bindResult, map_pure]; rfl
  | ok selected =>
    cases selected <;> simp only [bindResult, ↓native_finish, map_pure]
    all_goals
      cases prepared : sequence opening <;>
        simp only [ReceiveOpen.impl.context, toNative, map_bind, map_pure]
    all_goals rfl

/-- A label-only opening callback reconstructs the exact native source result and all effects under its local handler equation. -/
theorem native_run_map {m : Type → Type} [Monad m] [LawfulMonad m]
    {Material Context Plaintext : Type} (interpret : Material → RatchetMaterial)
    (opening : Opening RatchetChain RatchetChain Material Context)
    (native : RatchetMaterial → Std.U64 → Context → m (core.option.Option Plaintext))
    (labelled : Material → Std.U64 → Context → m (core.option.Option Plaintext))
    (compatible : ∀ label preparedSequence context,
      native (interpret label) preparedSequence context = labelled label preparedSequence context) :
    nativeRun native (toNative (mapOpening interpret opening)) =
      (fun result => (fun published =>
        (ConcreteRatchetKernel.mk (mapRefined interpret published.1), published.2)) <$> result) <$>
          run labelled opening := by
  rw [native_run, run_map interpret opening native labelled compatible, Functor.map_map]
  simp only [Functor.map_map]

end BeaconcryptCore.Computational.RawCtxInterpretedOpening

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_finish

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_sequence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_sequence

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_material

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.finish_map

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.sequence_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.sequence_map

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.material_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.material_map

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.run_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.run_map

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_run

/-- info: 'BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_run_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedOpening.native_run_map

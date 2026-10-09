-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhBoundaryRecordExecution
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Publication

/-! Exact real registration receive on the finish's local candidate kernel, before the sequence-one gate. -/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive
open PqxdhRefinement PqxdhBeaconPhase2Publication
open PqxdhBeaconPhase2Preparation (Prepared Word32)
variable {Message Root Response : Type}

/-- Forward the literal receive natives. Seal/writer branches are unused by the source receive embedding, as proved below. -/
def receiveTail : QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp (NativeTailSpec Response))
  | .inl request => (NativeTailSpec Response).query (.inl (.inl request))
  | .inr (.inl _) => pure none
  | .inr (.inr (.inl input)) => (NativeTailSpec Response).query (.inl (.inr (.inr input)))
  | .inr (.inr (.inr (.inl bytes))) => (NativeTailSpec Response).query (.inl (.inr (.inl bytes)))
  | .inr (.inr (.inr (.inr _))) => pure none

/-- Every actual receive request forwards unchanged to the real native tail interface; no unused mixed branch is reachable. -/
theorem receive_lift : receiveTail (Response := Response) ∘ₛ RawCtxMixedOwner.receiveLift = nativeRawLift := by
  funext query
  rcases query with request | bytes | input
  all_goals simp only [QueryImpl.compose, RawCtxMixedOwner.receiveLift, simulateQ_spec_query, receiveTail, nativeRawLift]


/-- The complete CTX opening expansion is the original real tail adapter, preserving hash and optional AEAD replies. -/
theorem receive_adapter : receiveTail (Response := Response) ∘ₛ RawCtxMixedOwner.receiveAdapter =
    nativeTailAdapter ∘ₛ rawLift := by
  funext query
  change simulateQ receiveTail (simulateQ RawCtxMixedOwner.receiveLift (RawCtxSourceOpen.nativeAdapter query)) = _
  rw [← QueryImpl.simulateQ_compose, receive_lift]
  simp only [QueryImpl.compose, rawLift, simulateQ_spec_query, nativeTailAdapter]

/-- Execute the real candidate-local receive boundary; this does not use any installed persistent owner. -/
noncomputable def localReceive (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (raw : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel) :
    OracleComp (NativeTailSpec Response)
      (RustM (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit)) :=
  simulateQ receiveTail (PqxdhBoundaryRecordExecution.executeOwner reader candidate.associated_data erased raw
    (localOwner candidate kernel))

/-- Uniform in every raw input and decoded sequence, the local source executor is exactly the original native tail receive, retaining its complete optional result and candidate kernel. -/
theorem local_receive_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (raw : Pqxdh.Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel) :
    localReceive (Response := Response) reader erased raw candidate kernel =
      (fun result => ok result) <$> simulateQ nativeTailAdapter
        (simulateQ rawLift ((RawCtxWholeOwner.rawReceive (RawCtxFrameDecoding.decode reader.model) raw).run
          (localOwner candidate kernel))) := by
  unfold localReceive
  rw [PqxdhBoundaryRecordExecution.executeOwner_exact reader candidate.associated_data erased raw
    (localOwner candidate kernel) rfl,
    PqxdhBoundaryRecordPrelude.owner_exact reader candidate.associated_data raw (localOwner candidate kernel) (0#u64) rfl]
  simp only [StateT.run, RawCtxMixedOwner.ownerImpl, simulateQ_map, ← QueryImpl.simulateQ_compose, receive_adapter]


/-- Real registration order: initial KDF, application getter, complete local receive, then afterOpening's sequence-one and binding gates. -/
noncomputable def executeAfterRoot (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (prepared : Prepared Response) (root : Word32) :
    OracleComp (NativeTailSpec Response) (RustM (Option Staged)) := do
  let candidate := clearedCandidate prepared.candidate
  let initial ← (NativeTailSpec Response).query (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request))
  let kernel := normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) initial
  let raw ← (NativeTailSpec Response).query (.inr (.application prepared.response))
  match raw with
  | none => pure (ok none)
  | some raw => do
      let received ← localReceive reader erased raw candidate kernel
      pure ((fun result => afterOpening candidate result.2.owner.kernel result.1) <$> received)

/-- Exact full real Publication.afterRoot program under nativeTailAdapter, uniform over all decoded sequences and failures. The receive uses only the finish's local candidate kernel; the sequence-one gate is applied after its full reply. -/
theorem after_root_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (prepared : Prepared Response) (root : Word32) :
    executeAfterRoot reader erased prepared root =
      (fun result => ok result) <$> simulateQ nativeTailAdapter
        (afterRoot (RawCtxFrameDecoding.decode reader.model) prepared root) := by
  simp only [executeAfterRoot, afterRoot, initialRun, simulateQ_bind, simulateQ_spec_query, nativeTailAdapter,
    bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro initial
  apply bind_congr
  intro application
  cases application with
  | none => simp only [simulateQ_pure, map_pure]
  | some raw =>
    simp only [local_receive_exact, bind_pure_comp, simulateQ_map, Functor.map_map,
      PqxdhOpenContextBridge.map_ok]


/-- Exact real root request and optional reply, followed by the same local candidate receive executor. -/
noncomputable def executeTail (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (prepared : Prepared Response) :
    OracleComp (NativeTailSpec Response) (RustM (Option Staged)) := do
  let root ← (NativeTailSpec Response).query (.inr (.root prepared.candidate.root_key_input))
  match root with
  | none => pure (ok none)
  | some root => executeAfterRoot reader erased prepared root

/-- Root processing retains the identical request and interpreter point, including rejection effects, without assuming any functional root answer. -/
theorem tail_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (prepared : Prepared Response) :
    executeTail reader erased prepared =
      (fun result => ok result) <$> simulateQ nativeTailAdapter
        (tail (RawCtxFrameDecoding.decode reader.model) prepared) := by
  simp only [executeTail, tail, simulateQ_bind, simulateQ_spec_query, nativeTailAdapter, map_bind]
  apply bind_congr
  intro root
  cases root with
  | none => simp only [simulateQ_pure, map_pure]
  | some root => exact after_root_exact reader erased prepared root

/-- Arbitrary native/base interpretation and complete continuation retain the actual value, full poststate, and literal request transcript of real Publication.afterRoot. -/
theorem after_root_complete {ι PrimitiveState Result : Type} {base : OracleSpec ι}
    (handler : QueryImpl (NativeTailSpec Response) (StateT PrimitiveState (OracleComp base)))
    (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (prepared : Prepared Response) (root : Word32)
    (state : PrimitiveState) (next : RustM (Option Staged) × PrimitiveState → OracleComp base Result) :
    (simulateQ handler (executeAfterRoot reader erased prepared root)).run state >>= next =
      (simulateQ handler (simulateQ nativeTailAdapter
        (afterRoot (RawCtxFrameDecoding.decode reader.model) prepared root))).run state >>=
          fun result => next (ok result.1, result.2) := by
  rw [after_root_exact, simulateQ_map, StateT.run_map, bind_map_left]

/-- The full tail equality retains its original root interpreter and arbitrary complete continuation, so the real finish's existing callback accounting transfers unchanged. -/
theorem tail_complete {ι PrimitiveState Result : Type} {base : OracleSpec ι}
    (handler : QueryImpl (NativeTailSpec Response) (StateT PrimitiveState (OracleComp base)))
    (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (prepared : Prepared Response)
    (state : PrimitiveState) (next : RustM (Option Staged) × PrimitiveState → OracleComp base Result) :
    (simulateQ handler (executeTail reader erased prepared)).run state >>= next =
      (simulateQ handler (simulateQ nativeTailAdapter
        (tail (RawCtxFrameDecoding.decode reader.model) prepared))).run state >>=
          fun result => next (ok result.1, result.2) := by
  rw [tail_exact, simulateQ_map, StateT.run_map, bind_map_left]


variable {I D K X : Type}

/-- The real tail embedding keeps every native request at the original Phase2 interpreter point. -/
theorem tail_lift : nativeAdapter (I := I) (D := D) (K := K) (X := X) (Response := Response) ∘ₛ tailLift =
    nativeTailLift ∘ₛ nativeTailAdapter := by
  funext query
  simp only [QueryImpl.compose, tailLift, simulateQ_spec_query, nativeAdapter]

/-- Run actual preparation, real root and local receive on InitSent; the unchanged finish retains active abort and inactive no-op. -/
noncomputable def executeRegistration (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (raw : Pqxdh.Bytes) (state : PqxdhBeaconPhase2Preparation.State I D K) :
    OracleComp (NativeSpec I D K X Response) (RustM (Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State I D K)) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ nativeAdapter (simulateQ preLift
        (PqxdhBeaconPhase2Preparation.prepare control state.beacon.identity prekey oneTime kem raw))
      match prepared with
      | none => pure (ok (finish control state none))
      | some prepared => do
          let staged ← simulateQ nativeTailLift (executeTail reader erased prepared)
          pure (finish control state <$> staged)
  | _ => pure (ok (none, state))

/-- The real full native registration program has the identical returned bytes/state and every primitive request, with only the explicit normal-return wrapper. -/
theorem registration_exact (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (raw : Pqxdh.Bytes) (state : PqxdhBeaconPhase2Preparation.State I D K) :
    executeRegistration (X := X) (Response := Response) reader erased raw state =
      (fun result => ok result) <$> nativeOwner (RawCtxFrameDecoding.decode reader.model) raw state := by
  unfold executeRegistration nativeOwner owner
  cases state.beacon.phase <;> try simp only [simulateQ_pure, map_pure]
  rename_i control prekey oneTime kem
  simp only [simulateQ_bind, map_bind]
  apply bind_congr
  intro prepared
  cases prepared with
  | none => simp only [simulateQ_pure, map_pure]
  | some prepared =>
    simp only [tail_exact, simulateQ_map, bind_pure_comp, Functor.map_map,
      PqxdhOpenContextBridge.map_ok, ← QueryImpl.simulateQ_compose, tail_lift]

/-- Any stateful native interpreter, including its request transcript, receives the same exact full registration value/poststate at every complete continuation. -/
theorem registration_complete {ι PrimitiveState Result : Type} {base : OracleSpec ι}
    (handler : QueryImpl (NativeSpec I D K X Response) (StateT PrimitiveState (OracleComp base)))
    (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) (primitive : PrimitiveState)
    (next : RustM (Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State I D K) × PrimitiveState → OracleComp base Result) :
    (simulateQ handler (executeRegistration reader erased raw state)).run primitive >>= next =
      (simulateQ handler (nativeOwner (RawCtxFrameDecoding.decode reader.model) raw state)).run primitive >>=
        fun result => next (ok result.1, result.2) := by
  rw [registration_exact, simulateQ_map, StateT.run_map, bind_map_left]

/-- Every supported normal failed active finish aborts InitSent; inactive calls preserve both owner and complete primitive state. -/
theorem registration_failure {PrimitiveState : Type}
    (handler : QueryImpl (NativeSpec I D K X Response) (StateT PrimitiveState ProbComp))
    (reader : RawCtxNativeFramePrelude.Reader Message Root)
    (erased : Std.Array Std.U8 229#usize) (raw : Pqxdh.Bytes)
    (state after : PqxdhBeaconPhase2Preparation.State I D K) (primitive final : PrimitiveState)
    (supported : (ok (none, after), final) ∈ support
      ((simulateQ handler (executeRegistration reader erased raw state)).run primitive)) :
    match state.beacon.phase with
    | .initSent control _ _ _ => after = PqxdhBeaconPhase2Preparation.abort control state
    | _ => after = state ∧ final = primitive := by
  rw [registration_exact, simulateQ_map, StateT.run_map] at supported
  simp only [support_map, Set.mem_image, Prod.mk.injEq, RustM.ok.injEq] at supported
  obtain ⟨⟨actual, result⟩, reached, rfl, rfl⟩ := supported
  exact PqxdhBeaconPhase2Publication.native_failure handler _ raw state after primitive _ reached

end BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.receive_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.receive_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.receive_adapter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.receive_adapter

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.local_receive_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.local_receive_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.after_root_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.after_root_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.tail_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.tail_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.after_root_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.after_root_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.tail_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.tail_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.tail_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.tail_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.registration_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.registration_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.registration_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.registration_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.registration_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBoundaryRegistrationReceive.registration_failure

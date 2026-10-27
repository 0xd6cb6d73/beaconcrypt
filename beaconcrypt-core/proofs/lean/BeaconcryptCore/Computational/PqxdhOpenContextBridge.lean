import BeaconcryptCore.Computational.PqxdhOpenBridges
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared

/-!
# Context completion of the record-opening bridge B12

B12 (`PqxdhOpenBridges.open_bridge`) equates the experiments' opening step on a source capability `pending : ReceiveOpen RawCtxWholeOwner.OpenContext` with `PqxdhOpenBridges.executeOpen` on `withContext pending context`, the capability with the same ratchet entry and prepared receive and production's admitted `record.OpenFrameContext`. Both capabilities come from the extracted receive driver `ratchet.concrete.begin_receive` and `ratchet.concrete.ReceiveKdf.resume`, which is generic in the context type: the experiments instantiate it with `RawCtxWholeOwner.OpenContext`, production (`decrypt_message_with_ratchet` in `beaconcrypt/src/ratchet.rs`) with `record.OpenFrameContext`. This module proves that the two instantiations yield capabilities with the same entry and prepared receive, and it relates a hand-written transcription of production's receive loop, composed with B12, to the experiments' complete receive driver. It adds new statements and changes no existing theorem.

`mapEffect f` replaces the context of an extracted receive effect by its image under `f` and keeps every other field: the entry kernel, the target, the working control, the staged slots, the counters, the KDF request and the prepared receive. `begin_receive_map` and `resume_map` prove, by unfolding the extracted bodies, that for every `f : C → D` the extracted `begin_receive` with context `f c` returns `mapEffect f` of its result with context `c`, and that the extracted `ReceiveKdf.resume` on the mapped KDF state returns `mapEffect f` of its result on the original state, for every KDF reply. Both are equalities of complete `RustM` results, so they cover failure and divergence as well as every rejection branch; the extracted driver never inspects the context.

`receiveReplies` iterates the extracted phases over a finite list of KDF replies: it runs `begin_receive` and resumes each KDF request with the next reply through `ReceiveKdf.resume`, stopping at the first effect that is not a KDF request (later replies are ignored). It is a hand-written Lean model of the iteration that production's loop performs with the replies of `ratchet_hkdf`. That correspondence is adapter-level trust checked only by review, the fold assumes nothing about how the replies are produced, and no theorem relates it to the transcription `executeReceive` below. `receiveReplies_context` states that the outcome for one context is the outcome for any other context with the context replaced. `open_transfer`, and its instance `open_frame_context_transfer` for `first : RawCtxWholeOwner.OpenContext` and `second : record.OpenFrameContext`, state the corollary needed by B12: if a list of replies drives the receive with `first` to `ReceiveOpenRequested pending`, then `pending.context = first` and the same replies drive the receive with `second` to `ReceiveOpenRequested (withContext pending second)`. `opened_record_bridge` adds B12: when `second` is the frame context that the extracted `record.OpenFrameContext.from_frame` admits for a slice and a 281-byte array representing the payload and associated data of `first`, the experiments' opening step on `pending` equals `executeOpen` on `withContext pending second`, the capability that the extracted phases produce with production's context type, wrapped in `ok`.

The experiments do not iterate over a list; their driver `RawCtxOwnerOracle.program` issues each KDF request and the opening capability as queries. `program_map` shows that this driver on a mapped effect equals the driver on the original effect with its opening query renamed by `relabel` and its KDF queries unchanged, and `oracle_receive_map` states the same for `RawCtxOwnerOracle.receive`, which begins with the extracted `begin_receive`.

`executeReceive` is a hand-written Lean transcription of the loop of `decrypt_message_with_ratchet`: a rejection returns its kernel without plaintext; a KDF request is read with the extracted `ReceiveKdf.impl.request`, answered by a query of the KDF interface of `RawCtxSourceOpen.NativeSpec` in place of `ratchet_hkdf`, and resumed with the extracted `ReceiveKdf.resume`; an opening capability is passed to `executeOpen`, the transcription of `execute_open` from B12. `executeReceiveFrom` starts the loop with the extracted `begin_receive`. `executeDecoded` transcribes the checks that `decrypt_message_with_ratchet` performs on an already decoded frame: the sender key identifier comparison and the extracted `from_frame` admission, each returning the unchanged kernel without plaintext on rejection. The recursion is well founded on the extracted continuation counter. These three functions are adapter-level trust, checked only by review of `beaconcrypt/src/ratchet.rs`; no Lean statement relates them to the Rust function, including its order of checks, the correspondence of `ratchet_hkdf` with the KDF query and the kernel `take` and `put` around the loop, which the transcription models by taking the kernel as an argument and returning the kernel to reinstall.

`receive_loop_bridge` proves that, when `from_frame` admits `second` for a slice and array representing the payload and associated data of `first`, `executeReceiveFrom` with `second` at the experiments' primitive interface equals, wrapped in `ok`, the experiments' receive driver `RawCtxOwnerOracle.receive` with `first`, interpreted by `RawCtxWholeOwner.adapter` and `RawCtxMixedOwner.receiveAdapter`. `decoded_receive_bridge` extends this to the decoded-frame checks: for every decoded frame whose payload and associated data are represented, `executeDecoded` equals, wrapped in `ok`, the branch of `RawCtxWholeOwner.rawReceive` after decoding and before publication (the `RawCtxReceive.ValidFrame` check followed by the receive driver, or the unchanged kernel without plaintext). The sender comparisons coincide, the extracted admission rejects exactly the payloads of at most 80 bytes, which is the length condition of `ValidFrame`, and the 281-byte representation of the associated data meets its remaining condition. Both equalities hold as programs over the experiments' KDF, hash and AEAD queries, so they cover every reply and every outcome: rejection before any KDF query, rejection after KDF replies, a capability without material, hash failure, commitment mismatch, AEAD failure and success. `ContextBridge` bundles `opened_record_bridge`, `receive_loop_bridge` and `decoded_receive_bridge`, and `context_bridge` proves it; its only premises are the representation conditions of B12, the admission of the frame context by `from_frame` for the first two parts, and, for the first part, that the replies drive the receive with the experiments' context to an opening capability. `receive_loop_native`, `decoded_receive_native` and `decoded_after_root` state the loop and decoded-frame equalities before the embedding into the receive adapter, the last at the interface of the HB-111 target raw-opening site `PqxdhBeaconPhase2Shared.afterRoot`.

Not covered: frame decoding and the check that decoding consumed the whole input, as performed by `decrypt_message_with_ratchet`, are outside the proof, because messages are arbitrary byte strings that each side knows how to decode; the statements quantify over the decoded frame and a payload slice representing it, so the agreement of production's decoder with the experiments' free decoder, including the target sequence, is not proved. The empty-input rejection that precedes decoding in both `decrypt_message_with_ratchet` and `RawCtxWholeOwner.rawReceive` is not transcribed; the bridges start after decoding. The realisation of the KDF query by `ratchet_hkdf` (HKDF and `RatchetKdfResponse::from_bytes`) is not addressed; both sides use the same KDF interface. The transcriptions are not the Rust code: the loop, the checks and the kernel ownership remain adapter trust as described above, and so does the serialization of operations on one owner, which `RawCtxWholeOwner.rawReceive` assumes. HB-112's experiments run `RawCtxWholeOwner.rawReceive` in `PqxdhBeaconPhase2Publication.afterRoot`, but they also receive through the symbolic chain owner `RawCtxChainOwner.rawReceive` with the pending-query driver `RawCtxPendingOwnerQueries.calls`. `RawCtxPendingOwnerQueries.receive_call` relates that driver to `RawCtxChainReceive.execute` after erasing its pending-query payload, and `RawCtxChainRealization.receive_native` relates `RawCtxChainReceive.execute` to `RawCtxOwnerOracle.receive` under its realization premises. This module does not compose those theorems with `receive_loop_bridge`. The headline theorems are not restated here, and the experiments still execute the hand-written programs.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhOpenContextBridge
open PqxdhRefinement BeaconcryptCore.Refinement.RepresentationBridge
open RawCtxInterpretedOpening (bindResult)
open PqxdhOpenBridges (withContext)

/-! ## A context map on the extracted receive effects -/

/-- The opening capability with its context replaced by its image under `f`; the ratchet entry and the prepared receive are unchanged. -/
def mapOpen {C D : Type} (f : C → D) (pending : ReceiveOpen C) : ReceiveOpen D :=
  withContext pending (f pending.context)

/-- The KDF capability with its context replaced by its image under `f`; the entry kernel, target, working control, staged slots, counters and KDF request are unchanged. -/
def mapKdf {C D : Type} (f : C → D) (pending : ReceiveKdf C) : ReceiveKdf D :=
  ⟨pending.entry, f pending.context, pending.target, pending.working_control, pending.staged_slots,
    pending.first_slot, pending.skipped, pending.remaining, pending.request⟩

/-- The receive effect with its context replaced by its image under `f`, constructor by constructor. -/
def mapEffect {C D : Type} (f : C → D) : ReceiveEffect C → ReceiveEffect D
  | .ReceiveRejected kernel context => .ReceiveRejected kernel (f context)
  | .ReceiveKdfRequested pending => .ReceiveKdfRequested (mapKdf f pending)
  | .ReceiveOpenRequested pending => .ReceiveOpenRequested (mapOpen f pending)

/-- The context carried by a receive effect. -/
def effectContext {C : Type} : ReceiveEffect C → C
  | .ReceiveRejected _ context => context
  | .ReceiveKdfRequested pending => pending.context
  | .ReceiveOpenRequested pending => pending.context

/-- Mapping an effect maps its context. -/
theorem effectContext_map {C D : Type} (f : C → D) (effect : ReceiveEffect C) :
    effectContext (mapEffect f effect) = f (effectContext effect) := by
  cases effect <;> rfl

/-! ## Naturality of the extracted receive phases -/

/-- Mapping a `RustM` result distributes over a branch. -/
theorem map_branch {Input Output : Type} (f : Input → Output) (condition : Prop)
    [Decidable condition] (left right : RustM Input) :
    f <$> (if condition then left else right) =
      if condition then f <$> left else f <$> right := by
  by_cases h : condition <;> simp only [h, ite_true, ite_false]

/-- Mapping a normal `RustM` result maps its value. -/
theorem map_ok {Input Output : Type} (f : Input → Output) (value : Input) :
    f <$> RustM.ok value = RustM.ok (f value) := rfl

/-- Naturality of the extracted `begin_receive`: for every context map `f`, admission with context `f context` returns the complete `RustM` result of admission with `context`, mapped by `mapEffect f`. -/
theorem begin_receive_map {C D : Type} (f : C → D) (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (context : C) :
    begin_receive kernel target (f context) = mapEffect f <$> begin_receive kernel target context := by
  simp only [begin_receive, receive_rejected, map_bind]
  congr 1
  funext plan
  cases plan.sequence with
  | none => rfl
  | some sequence =>
    by_cases zero : plan.derivations = 0#u64 <;> simp only [zero, ite_true, ite_false, map_bind]
    · congr 1
      funext o
      cases o <;> rfl
    · congr 1
      funext skipped
      by_cases gap : skipped > control.RATCHET_MAX_GAP <;> simp only [gap, ite_true, ite_false, map_bind]
      · rfl
      · congr 1; funext remaining; congr 1; funext first; congr 1; funext i; congr 1; funext b
        cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false, map_bind]
        · rfl
        · rfl

/-- Naturality of the extracted `ReceiveKdf.resume`: for every context map `f` and every KDF reply, resuming the mapped KDF capability returns the complete `RustM` result of resuming the original capability, mapped by `mapEffect f`. -/
theorem resume_map {C D : Type} (f : C → D) (pending : ReceiveKdf C)
    (response : RatchetKdfResponse) :
    (mapKdf f pending).resume response = mapEffect f <$> pending.resume response := by
  by_cases zero : pending.remaining = 0#u8
  · simp only [ReceiveKdf.resume, mapKdf, zero, ite_true, receive_rejected, map_ok, mapEffect]
  · simp only [ReceiveKdf.resume, mapKdf, zero, ite_false]
    by_cases last : pending.remaining = 1#u8 <;> simp only [last, ite_true, ite_false, map_bind]
    all_goals
      congr 1
      funext advanced
      cases present : advanced.sequence
    all_goals simp only [receive_rejected, map_ok, mapEffect, map_bind, map_branch]
    all_goals first
      | cases slot : advanced.slot
      | skip
    all_goals simp only [map_bind, map_branch, map_ok, mapEffect, mapKdf, mapOpen, withContext]
    all_goals rfl

/-- The mapped KDF capability issues the same request through the extracted request getter. -/
theorem request_mapKdf {C D : Type} (f : C → D) (pending : ReceiveKdf C) :
    ReceiveKdf.impl.request (mapKdf f pending) = ReceiveKdf.impl.request pending := rfl

/-- The extracted `ReceiveOpen.finish` does not read the context: the mapped capability publishes the same result for every reply. -/
theorem finish_mapOpen {C D P : Type} (f : C → D) (pending : ReceiveOpen C)
    (reply : core.option.Option P) :
    ReceiveOpen.finish (mapOpen f pending) reply = ReceiveOpen.finish pending reply := rfl

/-! ## Iteration of the extracted phases over KDF replies -/

/-- One iteration with one KDF reply: a KDF request is resumed with the reply by the extracted `ReceiveKdf.resume`; any other effect is returned unchanged. -/
def replyStep {C : Type} (effect : ReceiveEffect C) (response : RatchetKdfResponse) :
    RustM (ReceiveEffect C) :=
  match effect with
  | .ReceiveKdfRequested pending => pending.resume response
  | other => ok other

/-- Hand-written fold of `replyStep` over a finite list of KDF replies, threading `RustM` results. -/
def driveReplies {C : Type} (effect : ReceiveEffect C) (responses : List RatchetKdfResponse) :
    RustM (ReceiveEffect C) :=
  responses.foldlM replyStep effect

/-- The extracted admission `begin_receive` followed by `driveReplies` on a finite list of KDF replies. -/
def receiveReplies {C : Type} (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : C)
    (responses : List RatchetKdfResponse) : RustM (ReceiveEffect C) := do
  let start ← begin_receive kernel target context
  driveReplies start responses

/-- One reply step commutes with the context map. -/
theorem replyStep_map {C D : Type} (f : C → D) (effect : ReceiveEffect C) (response : RatchetKdfResponse) :
    replyStep (mapEffect f effect) response = mapEffect f <$> replyStep effect response := by
  cases effect with
  | ReceiveRejected kernel context => rfl
  | ReceiveKdfRequested pending => exact resume_map f pending response
  | ReceiveOpenRequested pending => rfl

/-- The fold over any list of KDF replies commutes with the context map. -/
theorem driveReplies_map {C D : Type} (f : C → D) (effect : ReceiveEffect C)
    (responses : List RatchetKdfResponse) :
    driveReplies (mapEffect f effect) responses = mapEffect f <$> driveReplies effect responses := by
  induction responses generalizing effect with
  | nil => rfl
  | cons response rest ih =>
    simp only [driveReplies, List.foldlM_cons] at ih ⊢
    rw [replyStep_map, bind_map_left, map_bind]
    congr 1
    funext next
    exact ih next

/-- Admission followed by any list of KDF replies commutes with the context map, as complete `RustM` results. -/
theorem receiveReplies_map {C D : Type} (f : C → D) (kernel : ConcreteRatchetKernel) (target : Std.U64)
    (context : C) (responses : List RatchetKdfResponse) :
    receiveReplies kernel target (f context) responses =
      mapEffect f <$> receiveReplies kernel target context responses := by
  simp only [receiveReplies, begin_receive_map, bind_map_left, map_bind, driveReplies_map]

/-- The outcome of admission and KDF replies for one context is the outcome for any other context, with that context installed. -/
theorem receiveReplies_context {C D : Type} (kernel : ConcreteRatchetKernel) (target : Std.U64)
    (first : C) (second : D) (responses : List RatchetKdfResponse) :
    receiveReplies kernel target second responses =
      mapEffect (fun _ => second) <$> receiveReplies kernel target first responses :=
  receiveReplies_map (fun _ => second) kernel target first responses

/-- If KDF replies drive the receive with context `first` to an opening capability `pending`, then `pending` carries `first`, and the same replies drive the receive with any context `second` to `withContext pending second`, the capability with the same entry and prepared receive. -/
theorem open_transfer {C D : Type} (kernel : ConcreteRatchetKernel) (target : Std.U64)
    (first : C) (second : D) (responses : List RatchetKdfResponse) (pending : ReceiveOpen C)
    (h : receiveReplies kernel target first responses = ok (.ReceiveOpenRequested pending)) :
    receiveReplies kernel target second responses = ok (.ReceiveOpenRequested (withContext pending second)) ∧
      pending.context = first := by
  refine ⟨by rw [receiveReplies_context kernel target first second, h]; rfl, ?_⟩
  have same := receiveReplies_map (fun _ => first) kernel target first responses
  rw [h] at same
  exact congrArg (fun effect => match effect with
    | RustM.ok (.ReceiveOpenRequested other) => other.context
    | _ => first) same

/-- `open_transfer` for the experiments' context type `RawCtxWholeOwner.OpenContext` and production's context type `record.OpenFrameContext`. -/
theorem open_frame_context_transfer (kernel : ConcreteRatchetKernel) (target : Std.U64)
    (first : RawCtxWholeOwner.OpenContext) (second : record.OpenFrameContext)
    (responses : List RatchetKdfResponse) (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (hopen : receiveReplies kernel target first responses = ok (.ReceiveOpenRequested pending)) :
    receiveReplies kernel target second responses = ok (.ReceiveOpenRequested (withContext pending second)) ∧
      pending.context = first :=
  open_transfer kernel target first second responses pending hopen

/-! ## The experiments' receive driver -/

/-- Naturality of the experiments' normalized admission `RawCtxOwnerOracle.begin`. -/
theorem oracle_begin_map {C D : Type} (f : C → D) (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (context : C) :
    RawCtxOwnerOracle.begin kernel target (f context) =
      mapEffect f (RawCtxOwnerOracle.begin kernel target context) := by
  have h := begin_receive_map f kernel target context
  rw [RawCtxOwnerOracle.begin_exact, RawCtxOwnerOracle.begin_exact] at h
  exact RustM.ok.inj h

/-- Naturality of the experiments' normalized resumption `RawCtxOwnerOracle.resume`, for every KDF reply. -/
theorem oracle_resume_map {C D : Type} (f : C → D) (pending : ReceiveKdf C)
    (response : RatchetKdfResponse) :
    RawCtxOwnerOracle.resume (mapKdf f pending) response =
      mapEffect f (RawCtxOwnerOracle.resume pending response) := by
  have h := resume_map f pending response
  rw [RawCtxOwnerOracle.resume_exact, RawCtxOwnerOracle.resume_exact] at h
  exact RustM.ok.inj h

/-- The experiments' normalized publication `RawCtxOwnerOracle.finish` does not depend on the context. -/
theorem oracle_finish_map {C D P : Type} (f : C → D) (pending : ReceiveOpen C)
    (reply : core.option.Option P) :
    RawCtxOwnerOracle.finish (mapOpen f pending) reply = RawCtxOwnerOracle.finish pending reply := by
  have h := RawCtxOwnerOracle.finish_exact (mapOpen f pending) reply
  rw [finish_mapOpen, RawCtxOwnerOracle.finish_exact] at h
  exact (RustM.ok.inj h).symm

/-- Renaming of the receive driver's queries: KDF requests are forwarded unchanged and the opening capability is forwarded with its context mapped by `f`. -/
def relabel {C D P : Type} (f : C → D) :
    QueryImpl (RawCtxOwnerOracle.ReceiveSpec C P) (OracleComp (RawCtxOwnerOracle.ReceiveSpec D P))
  | .inl request => liftM ((RawCtxOwnerOracle.ReceiveSpec D P).query (.inl request))
  | .inr pending => liftM ((RawCtxOwnerOracle.ReceiveSpec D P).query (.inr (mapOpen f pending)))

/-- The experiments' receive driver on a mapped effect is the driver on the original effect with its opening query renamed by `relabel`: the same KDF queries in the same order, and an opening query on the mapped capability. -/
theorem program_map {C D P : Type} (f : C → D) (effect : ReceiveEffect C) :
    simulateQ (relabel (P := P) f) (RawCtxOwnerOracle.program effect) =
      RawCtxOwnerOracle.program (mapEffect f effect) := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | ReceiveRejected kernel context =>
      rw [RawCtxOwnerOracle.program.eq_1]
      simp only [mapEffect, simulateQ_pure]
      rw [RawCtxOwnerOracle.program.eq_1]
    | ReceiveOpenRequested pending =>
      rw [RawCtxOwnerOracle.program.eq_2]
      simp only [mapEffect, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rw [RawCtxOwnerOracle.program.eq_2]
      simp only [relabel, oracle_finish_map]
      rfl
    | ReceiveKdfRequested pending =>
      rw [RawCtxOwnerOracle.program.eq_3]
      simp only [mapEffect, simulateQ_bind, simulateQ_spec_query]
      rw [RawCtxOwnerOracle.program.eq_3]
      simp only [relabel]
      refine bind_congr fun response => ?_
      rw [oracle_resume_map, ih _ (hdepth ▸ RawCtxOwnerOracle.resume_rank pending response) _ rfl]

/-- The experiments' complete receive `RawCtxOwnerOracle.receive` with context `f context` is the receive with `context`, with its opening query renamed by `relabel`. -/
theorem oracle_receive_map {C D P : Type} (f : C → D) (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (context : C) :
    simulateQ (relabel (P := P) f) (RawCtxOwnerOracle.receive kernel target context) =
      RawCtxOwnerOracle.receive kernel target (f context) := by
  rw [RawCtxOwnerOracle.receive, RawCtxOwnerOracle.receive, program_map, oracle_begin_map]

/-- The normalized admission carries the admitted context. -/
theorem begin_context {C : Type} (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : C) :
    effectContext (RawCtxOwnerOracle.begin kernel target context) = context := by
  have h := oracle_begin_map (fun _ : Unit => context) kernel target ()
  rw [h, effectContext_map]

/-- The normalized resumption keeps the capability's context, for every KDF reply. -/
theorem resume_context {C : Type} (pending : ReceiveKdf C) (response : RatchetKdfResponse) :
    effectContext (RawCtxOwnerOracle.resume pending response) = pending.context := by
  have h := oracle_resume_map (fun _ : C => pending.context) pending response
  have hself : mapKdf (fun _ : C => pending.context) pending = pending := rfl
  rw [hself] at h
  rw [h, effectContext_map]

/-! ## Connection with B12 -/

/-- B12 at an admitted frame context: if the extracted `from_frame` admits `context` for a slice and array representing the capability's payload and associated data, the experiments' opening step equals `executeOpen` on the capability with that context, wrapped in `ok`. -/
theorem open_step (erased : Std.Array Std.U8 357#usize)
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize) (context : record.OpenFrameContext)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = pending.context.frame.payload)
    (had : absBytes ad = pending.context.associatedData)
    (hframe : record.OpenFrameContext.from_frame payload ad pending.context.frame.sender =
      ok (.Some context)) :
    simulateQ PqxdhOpenBridges.mixedOpen (PqxdhOpenBridges.executeOpen erased (withContext pending context)) =
      (fun result => ok result) <$> simulateQ (RawCtxMixedOwner.receiveAdapter ∘ₛ RawCtxWholeOwner.adapter)
        (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending)) := by
  rcases PqxdhOpenBridges.open_bridge.1 erased pending payload ad hpayload had with
    ⟨hnone, _, _⟩ | ⟨admitted, hadmitted, hstep, _⟩
  · rw [hframe] at hnone
    cases hnone
  · rw [hframe] at hadmitted
    cases hadmitted
    exact hstep

/-- The context gap of B12 for the extracted receive phases, for any finite list of KDF replies (the fold `receiveReplies` is a hand-written model of production's loop): if the replies drive the receive with the experiments' context `first` to `pending`, they drive the receive with production's admitted context `second` to `withContext pending second`, and the experiments' opening step on `pending` equals `executeOpen` on that capability, wrapped in `ok`. -/
theorem opened_record_bridge (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (first : RawCtxWholeOwner.OpenContext) (second : record.OpenFrameContext)
    (responses : List RatchetKdfResponse) (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = first.frame.payload)
    (had : absBytes ad = first.associatedData)
    (hframe : record.OpenFrameContext.from_frame payload ad first.frame.sender = ok (.Some second))
    (hopen : receiveReplies kernel target first responses = ok (.ReceiveOpenRequested pending)) :
    receiveReplies kernel target second responses = ok (.ReceiveOpenRequested (withContext pending second)) ∧
      simulateQ PqxdhOpenBridges.mixedOpen (PqxdhOpenBridges.executeOpen erased (withContext pending second)) =
        (fun result => ok result) <$> simulateQ (RawCtxMixedOwner.receiveAdapter ∘ₛ RawCtxWholeOwner.adapter)
          (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending)) := by
  obtain ⟨transfer, hcontext⟩ := open_transfer kernel target first second responses pending hopen
  subst hcontext
  exact ⟨transfer, open_step erased pending payload ad second hpayload had hframe⟩

/-! ## Hand-written transcription of production's receive loop -/

/-- A normal result of the extracted `ReceiveKdf.resume` strictly decreases the continuation rank. -/
theorem resume_decreasing {C : Type} (pending : ReceiveKdf C) (response : RatchetKdfResponse)
    (next : ReceiveEffect C) (h : pending.resume response = ok next) :
    effectDepth next < effectDepth (.ReceiveKdfRequested pending) := by
  have hnext : next = RawCtxOwnerOracle.resume pending response :=
    RustM.ok.inj (h.symm.trans (RawCtxOwnerOracle.resume_exact pending response))
  rw [hnext]
  exact RawCtxOwnerOracle.resume_rank pending response

/-- Hand-written Lean transcription of the receive loop of production's `decrypt_message_with_ratchet` (`beaconcrypt/src/ratchet.rs`), adapter-level trust: a rejection returns its kernel without plaintext; a KDF request is read by the extracted `ReceiveKdf.impl.request`, answered by a query of the KDF interface (production calls `ratchet_hkdf`) and resumed by the extracted `ReceiveKdf.resume`; an opening capability is passed to `executeOpen`. The returned kernel is the one production reinstalls with `put`; a `RustM` failure or divergence of an extracted phase is returned unchanged (production has no corresponding return; the bridges show that under their conditions every result is `ok`). -/
def executeReceive (erased : Std.Array Std.U8 357#usize)
    (effect : ReceiveEffect record.OpenFrameContext) :
    OracleComp RawCtxSourceOpen.NativeSpec
      (RustM (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted)) :=
  match effect with
  | .ReceiveRejected kernel _ => pure (ok (kernel, .None))
  | .ReceiveKdfRequested pending =>
      bindResult (ReceiveKdf.impl.request pending) fun request => do
        let response ← RawCtxSourceOpen.NativeSpec.query (.inl request)
        match _resumed : pending.resume response with
        | .ok next => executeReceive erased next
        | .fail error => pure (.fail error)
        | .div => pure .div
  | .ReceiveOpenRequested opening =>
      simulateQ RawCtxSourceOpen.openLift (PqxdhOpenBridges.executeOpen erased opening)
termination_by effectDepth effect
decreasing_by exact resume_decreasing pending response next _resumed

/-- Hand-written transcription, adapter-level trust: production's loop started by the extracted `begin_receive` on the taken kernel, the decoded target sequence and the admitted frame context. -/
def executeReceiveFrom (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (context : record.OpenFrameContext) :
    OracleComp RawCtxSourceOpen.NativeSpec
      (RustM (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted)) :=
  bindResult (begin_receive kernel target context) (executeReceive erased)

/-- Hand-written transcription, adapter-level trust: the checks of `decrypt_message_with_ratchet` on an already decoded frame. A sender key identifier different from the expected one, or a payload that the extracted `from_frame` rejects, returns the unchanged kernel without plaintext; otherwise the loop runs on the admitted frame context and the frame's sequence. -/
def executeDecoded (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (expected : Std.U64) (frame : RawCtxReceive.DecodedFrame) (payload : Slice Std.U8)
    (ad : Std.Array Std.U8 281#usize) :
    OracleComp RawCtxSourceOpen.NativeSpec
      (RustM (ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted)) :=
  if frame.sender = expected then
    bindResult (record.OpenFrameContext.from_frame payload ad frame.sender) fun admitted =>
      match admitted with
      | .None => pure (ok (kernel, .None))
      | .Some context => executeReceiveFrom erased kernel frame.sequence context
  else pure (ok (kernel, .None))

/-- Unfolding of the loop at a KDF request. -/
theorem executeReceive_kdf (erased : Std.Array Std.U8 357#usize)
    (pending : ReceiveKdf record.OpenFrameContext) :
    executeReceive erased (.ReceiveKdfRequested pending) = (do
      let response ← RawCtxSourceOpen.NativeSpec.query (.inl pending.request)
      bindResult (pending.resume response) (executeReceive erased)) := by
  rw [executeReceive]
  simp only [ReceiveKdf.impl.request, PqxdhOpenBridges.bindResult_ok]
  refine bind_congr fun response => ?_
  split <;> rename_i h <;> rw [h] <;> rfl

/-! ## Bridges for the whole receive -/

/-- Loop invariant: on every effect carrying the experiments' context `first`, the transcribed loop on the effect with production's admitted context `second` equals, wrapped in `ok`, the experiments' receive driver interpreted at their primitive interface. -/
theorem executeReceive_loop (erased : Std.Array Std.U8 357#usize)
    (first : RawCtxWholeOwner.OpenContext) (second : record.OpenFrameContext)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = first.frame.payload)
    (had : absBytes ad = first.associatedData)
    (hframe : record.OpenFrameContext.from_frame payload ad first.frame.sender = ok (.Some second))
    (effect : ReceiveEffect RawCtxWholeOwner.OpenContext) (hcontext : effectContext effect = first) :
    simulateQ RawCtxMixedOwner.receiveLift (executeReceive erased (mapEffect (fun _ => second) effect)) =
      (fun result => ok result) <$> simulateQ RawCtxMixedOwner.receiveAdapter
        (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) effect)) := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | ReceiveRejected kernel context =>
      rw [RawCtxOwnerOracle.program.eq_1]
      simp only [mapEffect, executeReceive, simulateQ_pure, map_pure]
    | ReceiveOpenRequested pending =>
      change pending.context = first at hcontext
      subst hcontext
      have step := open_step erased pending payload ad second hpayload had hframe
      simp only [mapEffect, mapOpen, executeReceive]
      rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
      exact step
    | ReceiveKdfRequested pending =>
      change pending.context = first at hcontext
      simp only [mapEffect, executeReceive_kdf]
      rw [RawCtxOwnerOracle.program.eq_3]
      simp only [simulateQ_bind, map_bind, simulateQ_spec_query, RawCtxWholeOwner.adapter,
        RawCtxMixedOwner.receiveAdapter, QueryImpl.apply_compose, RawCtxSourceOpen.nativeAdapter]
      refine bind_congr fun response => ?_
      rw [resume_map, RawCtxOwnerOracle.resume_exact, map_ok, PqxdhOpenBridges.bindResult_ok]
      exact ih _ (hdepth ▸ RawCtxOwnerOracle.resume_rank pending response) _
        ((resume_context pending response).trans hcontext) rfl

/-- Receive-loop bridge: if the extracted `from_frame` admits `second` for a slice and array representing the payload and associated data of the experiments' context `first`, the transcribed loop started by the extracted `begin_receive` with `second`, at the experiments' primitive interface, equals the experiments' receive driver `RawCtxOwnerOracle.receive` with `first`, interpreted by `RawCtxWholeOwner.adapter` and `RawCtxMixedOwner.receiveAdapter`, wrapped in `ok`. -/
theorem receive_loop_bridge (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (first : RawCtxWholeOwner.OpenContext) (second : record.OpenFrameContext)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = first.frame.payload)
    (had : absBytes ad = first.associatedData)
    (hframe : record.OpenFrameContext.from_frame payload ad first.frame.sender = ok (.Some second)) :
    simulateQ RawCtxMixedOwner.receiveLift (executeReceiveFrom erased kernel target second) =
      (fun result => ok result) <$> simulateQ RawCtxMixedOwner.receiveAdapter
        (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel target first)) := by
  have hbegin : begin_receive kernel target second =
      ok (mapEffect (fun _ => second) (RawCtxOwnerOracle.begin kernel target first)) := by
    have h : begin_receive kernel target second = _ := begin_receive_map (fun _ => second) kernel target first
    rw [h, RawCtxOwnerOracle.begin_exact]
    rfl
  rw [executeReceiveFrom, hbegin, PqxdhOpenBridges.bindResult_ok, RawCtxOwnerOracle.receive]
  exact executeReceive_loop erased first second payload ad hpayload had hframe _ (begin_context kernel target first)

/-- Decoded-frame bridge: for every decoded frame whose payload and associated data are represented by a slice and a 281-byte array, the transcribed checks and loop equal, wrapped in `ok`, the branch of `RawCtxWholeOwner.rawReceive` after decoding and before publication (the `RawCtxReceive.ValidFrame` check, then the experiments' receive driver with the decoded frame, or the unchanged kernel without plaintext), at the experiments' primitive interface. -/
theorem decoded_receive_bridge (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (expected : Std.U64) (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame)
    (associatedData : Pqxdh.Bytes) (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = frame.payload)
    (had : absBytes ad = associatedData) :
    simulateQ RawCtxMixedOwner.receiveLift (executeDecoded erased kernel expected frame payload ad) =
      (fun result => ok result) <$> simulateQ RawCtxMixedOwner.receiveAdapter
        (if RawCtxReceive.ValidFrame expected associatedData frame then
          simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
              ⟨raw, frame, associatedData⟩)
        else pure (kernel, .None)) := by
  have hlength : frame.payload.length = payload.val.length := by
    rw [← hpayload, RawCtxNativeFramePrelude.sliceBytes, List.length_map]
  have hadLength : associatedData.length = 281 := by
    rw [← had]; simp [absBytes_length]
  by_cases hsender : frame.sender = expected
  · obtain ⟨result, execution, fields⟩ :=
      BeaconcryptCore.Refinement.NativeRecordWrapper.payload_views payload ad frame.sender
    cases result with
    | none =>
      have hinvalid : ¬ RawCtxReceive.ValidFrame expected associatedData frame := by
        intro hvalid
        have := hvalid.2.1
        change payload.val.length ≤ 80 at fields
        omega
      rw [executeDecoded, ite_eq_left hsender, execution, PqxdhOpenBridges.bindResult_ok,
        ite_eq_right hinvalid]
      simp only [simulateQ_pure, map_pure]
    | some second =>
      have hvalid : RawCtxReceive.ValidFrame expected associatedData frame :=
        ⟨hsender, by rw [hlength]; exact fields.1, hadLength⟩
      rw [executeDecoded, ite_eq_left hsender, execution, PqxdhOpenBridges.bindResult_ok, ite_eq_left hvalid]
      exact receive_loop_bridge erased kernel frame.sequence ⟨raw, frame, associatedData⟩ second payload ad
        hpayload had execution
  · have hinvalid : ¬ RawCtxReceive.ValidFrame expected associatedData frame := fun hvalid => hsender hvalid.1
    rw [executeDecoded, ite_eq_right hsender, ite_eq_right hinvalid]
    simp only [simulateQ_pure, map_pure]

/-- Context completion of B12: (1) for every finite list of KDF replies that drives the receive with the experiments' context to an opening capability, the same replies drive the receive with production's admitted frame context to the capability with the same entry and prepared receive, on which `executeOpen` equals the experiments' opening step; (2) the transcribed receive loop started by the extracted `begin_receive` equals the experiments' receive driver; (3) the transcribed decoded-frame checks and loop equal the branch of `RawCtxWholeOwner.rawReceive` after decoding and before publication. All equalities are wrapped in `ok` and hold at the experiments' primitive interface, under the representation conditions of B12, the admission of the frame context by `from_frame` (parts 1 and 2) and, for part 1, the hypothesis that the replies reach an opening capability. -/
def ContextBridge : Prop :=
  (∀ (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel) (target : Std.U64)
      (first : RawCtxWholeOwner.OpenContext) (second : record.OpenFrameContext)
      (responses : List RatchetKdfResponse) (pending : ReceiveOpen RawCtxWholeOwner.OpenContext)
      (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize),
    RawCtxNativeFramePrelude.sliceBytes payload = first.frame.payload →
    absBytes ad = first.associatedData →
    record.OpenFrameContext.from_frame payload ad first.frame.sender = ok (.Some second) →
    receiveReplies kernel target first responses = ok (.ReceiveOpenRequested pending) →
    receiveReplies kernel target second responses = ok (.ReceiveOpenRequested (withContext pending second)) ∧
      simulateQ PqxdhOpenBridges.mixedOpen (PqxdhOpenBridges.executeOpen erased (withContext pending second)) =
        (fun result => ok result) <$> simulateQ (RawCtxMixedOwner.receiveAdapter ∘ₛ RawCtxWholeOwner.adapter)
          (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) (.ReceiveOpenRequested pending))) ∧
  (∀ (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel) (target : Std.U64)
      (first : RawCtxWholeOwner.OpenContext) (second : record.OpenFrameContext)
      (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize),
    RawCtxNativeFramePrelude.sliceBytes payload = first.frame.payload →
    absBytes ad = first.associatedData →
    record.OpenFrameContext.from_frame payload ad first.frame.sender = ok (.Some second) →
    simulateQ RawCtxMixedOwner.receiveLift (executeReceiveFrom erased kernel target second) =
      (fun result => ok result) <$> simulateQ RawCtxMixedOwner.receiveAdapter
        (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel target first))) ∧
  (∀ (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel) (expected : Std.U64)
      (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame) (associatedData : Pqxdh.Bytes)
      (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize),
    RawCtxNativeFramePrelude.sliceBytes payload = frame.payload →
    absBytes ad = associatedData →
    simulateQ RawCtxMixedOwner.receiveLift (executeDecoded erased kernel expected frame payload ad) =
      (fun result => ok result) <$> simulateQ RawCtxMixedOwner.receiveAdapter
        (if RawCtxReceive.ValidFrame expected associatedData frame then
          simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
              ⟨raw, frame, associatedData⟩)
        else pure (kernel, .None)))

/-- The context completion of B12 holds. -/
theorem context_bridge : ContextBridge :=
  ⟨fun erased kernel target first second responses pending payload ad hpayload had hframe hopen =>
    opened_record_bridge erased kernel target first second responses pending payload ad hpayload had hframe hopen,
   fun erased kernel target first second payload ad hpayload had hframe =>
    receive_loop_bridge erased kernel target first second payload ad hpayload had hframe,
   fun erased kernel expected raw frame associatedData payload ad hpayload had =>
    decoded_receive_bridge erased kernel expected raw frame associatedData payload ad hpayload had⟩


/-! ## Bridges at the native opening interface -/

/-- The loop transcription equals the experiments' driver before any embedding of the primitive interface: for an effect of the experiments' driver carrying the context `first`, `executeReceive` on the same effect with production's admitted context `second` equals, wrapped in `ok`, the experiments' driver `RawCtxOwnerOracle.program` interpreted by the whole-owner adapter and `RawCtxSourceOpen.nativeAdapter`, as programs over `RawCtxSourceOpen.NativeSpec`. -/
theorem receive_loop_native (erased : Std.Array Std.U8 357#usize)
    (first : RawCtxWholeOwner.OpenContext) (second : record.OpenFrameContext)
    (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = first.frame.payload)
    (had : absBytes ad = first.associatedData)
    (hframe : record.OpenFrameContext.from_frame payload ad first.frame.sender = ok (.Some second))
    (effect : ReceiveEffect RawCtxWholeOwner.OpenContext) (hcontext : effectContext effect = first) :
    executeReceive erased (mapEffect (fun _ => second) effect) =
      (fun result => ok result) <$> simulateQ RawCtxSourceOpen.nativeAdapter
        (simulateQ RawCtxWholeOwner.adapter
          (RawCtxOwnerOracle.program (Plaintext := RawCtxWholeOwner.Decrypted) effect)) := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | ReceiveRejected kernel context =>
      rw [RawCtxOwnerOracle.program.eq_1]
      simp only [mapEffect, executeReceive, simulateQ_pure, map_pure]
    | ReceiveOpenRequested pending =>
      change pending.context = first at hcontext
      subst hcontext
      simp only [mapEffect, mapOpen, executeReceive]
      rw [PqxdhOpenBridges.executeOpen_source erased pending payload ad second hpayload had hframe,
        simulateQ_map, ← PqxdhOpenBridges.standInOpen_source, PqxdhOpenBridges.standInOpen,
        QueryImpl.simulateQ_compose]
    | ReceiveKdfRequested pending =>
      change pending.context = first at hcontext
      simp only [mapEffect, executeReceive_kdf]
      rw [RawCtxOwnerOracle.program.eq_3]
      simp only [simulateQ_bind, map_bind, simulateQ_spec_query, RawCtxWholeOwner.adapter,
        RawCtxSourceOpen.nativeAdapter]
      refine bind_congr fun response => ?_
      rw [resume_map, RawCtxOwnerOracle.resume_exact, map_ok, PqxdhOpenBridges.bindResult_ok]
      exact ih _ (hdepth ▸ RawCtxOwnerOracle.resume_rank pending response) _
        ((resume_context pending response).trans hcontext) rfl

/-- The decoded-frame checks and loop equal the experiments' post-decoding raw receive before any embedding of the primitive interface: under B12's representation conditions, `executeDecoded` equals, wrapped in `ok`, the branch of `RawCtxWholeOwner.rawReceive` after decoding and before publication, interpreted by `RawCtxSourceOpen.nativeAdapter`. The receive-adapter form `decoded_receive_bridge` follows by composing with `RawCtxMixedOwner.receiveAdapter`. -/
theorem decoded_receive_native (erased : Std.Array Std.U8 357#usize) (kernel : ConcreteRatchetKernel)
    (expected : Std.U64) (raw : Pqxdh.Bytes) (frame : RawCtxReceive.DecodedFrame)
    (associatedData : Pqxdh.Bytes) (payload : Slice Std.U8) (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = frame.payload)
    (had : absBytes ad = associatedData) :
    executeDecoded erased kernel expected frame payload ad =
      (fun result => ok result) <$> simulateQ RawCtxSourceOpen.nativeAdapter
        (if RawCtxReceive.ValidFrame expected associatedData frame then
          simulateQ RawCtxWholeOwner.adapter
            (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
              ⟨raw, frame, associatedData⟩)
        else pure (kernel, .None)) := by
  have hlength : frame.payload.length = payload.val.length := by
    rw [← hpayload, RawCtxNativeFramePrelude.sliceBytes, List.length_map]
  have hadLength : associatedData.length = 281 := by
    rw [← had]; simp [absBytes_length]
  by_cases hsender : frame.sender = expected
  · obtain ⟨result, execution, fields⟩ :=
      BeaconcryptCore.Refinement.NativeRecordWrapper.payload_views payload ad frame.sender
    cases result with
    | none =>
      have hinvalid : ¬ RawCtxReceive.ValidFrame expected associatedData frame := by
        intro hvalid
        have := hvalid.2.1
        change payload.val.length ≤ 80 at fields
        omega
      rw [executeDecoded, ite_eq_left hsender, execution, PqxdhOpenBridges.bindResult_ok,
        ite_eq_right hinvalid]
      simp only [simulateQ_pure, map_pure]
    | some second =>
      have hvalid : RawCtxReceive.ValidFrame expected associatedData frame :=
        ⟨hsender, by rw [hlength]; exact fields.1, hadLength⟩
      rw [executeDecoded, ite_eq_left hsender, execution, PqxdhOpenBridges.bindResult_ok, ite_eq_left hvalid]
      have hbegin : begin_receive kernel frame.sequence second =
          ok (mapEffect (fun _ => second) (RawCtxOwnerOracle.begin kernel frame.sequence
            (⟨raw, frame, associatedData⟩ : RawCtxWholeOwner.OpenContext))) := by
        have h : begin_receive kernel frame.sequence second = _ :=
          begin_receive_map (fun _ => second) kernel frame.sequence
            (⟨raw, frame, associatedData⟩ : RawCtxWholeOwner.OpenContext)
        rw [h, RawCtxOwnerOracle.begin_exact]
        rfl
      dsimp only
      rw [executeReceiveFrom, hbegin, PqxdhOpenBridges.bindResult_ok, RawCtxOwnerOracle.receive]
      exact receive_loop_native erased ⟨raw, frame, associatedData⟩ second payload ad hpayload had execution _
        (begin_context kernel frame.sequence _)
  · have hinvalid : ¬ RawCtxReceive.ValidFrame expected associatedData frame := fun hvalid => hsender hvalid.1
    rw [executeDecoded, ite_eq_right hsender, ite_eq_right hinvalid]
    simp only [simulateQ_pure, map_pure]

/-- The same equality at the interface of the HB-111 target raw-opening site `PqxdhBeaconPhase2Shared.afterRoot`, which interprets the raw receive with `PqxdhBeaconPhase2Shared.rawLift` over `RawCtxSourceOpen.nativeAdapter` rather than with `RawCtxMixedOwner.receiveAdapter`. -/
theorem decoded_after_root {Response Shared : Type} (erased : Std.Array Std.U8 357#usize)
    (kernel : ConcreteRatchetKernel) (expected : Std.U64) (raw : Pqxdh.Bytes)
    (frame : RawCtxReceive.DecodedFrame) (associatedData : Pqxdh.Bytes) (payload : Slice Std.U8)
    (ad : Std.Array Std.U8 281#usize)
    (hpayload : RawCtxNativeFramePrelude.sliceBytes payload = frame.payload)
    (had : absBytes ad = associatedData) :
    simulateQ (PqxdhBeaconPhase2Shared.rawLift (Response := Response) (Shared := Shared))
        (executeDecoded erased kernel expected frame payload ad) =
      (fun result => ok result) <$> simulateQ PqxdhBeaconPhase2Shared.rawLift
        (simulateQ RawCtxSourceOpen.nativeAdapter
          (if RawCtxReceive.ValidFrame expected associatedData frame then
            simulateQ RawCtxWholeOwner.adapter
              (RawCtxOwnerOracle.receive (Plaintext := RawCtxWholeOwner.Decrypted) kernel frame.sequence
                ⟨raw, frame, associatedData⟩)
          else pure (kernel, .None))) := by
  rw [decoded_receive_native erased kernel expected raw frame associatedData payload ad hpayload had, simulateQ_map]

end BeaconcryptCore.Computational.PqxdhOpenContextBridge

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.effectContext_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.effectContext_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.map_branch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.map_branch

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.map_ok' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.map_ok

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.begin_receive_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.begin_receive_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.resume_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.resume_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.request_mapKdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.request_mapKdf

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.finish_mapOpen' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.finish_mapOpen

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.replyStep_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.replyStep_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.driveReplies_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.driveReplies_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.receiveReplies_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.receiveReplies_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.receiveReplies_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.receiveReplies_context

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.open_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.open_transfer

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.open_frame_context_transfer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.open_frame_context_transfer

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_begin_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_begin_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_resume_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_resume_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_finish_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.program_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_receive_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.oracle_receive_map

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.begin_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.begin_context

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.resume_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.resume_context

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.open_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.open_step

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.opened_record_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.opened_record_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.resume_decreasing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.resume_decreasing

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.executeReceive_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.executeReceive_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.executeReceive_loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.executeReceive_loop

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.receive_loop_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.receive_loop_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.decoded_receive_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.decoded_receive_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.context_bridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.context_bridge

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.receive_loop_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.receive_loop_native

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.decoded_receive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.decoded_receive_native

/-- info: 'BeaconcryptCore.Computational.PqxdhOpenContextBridge.decoded_after_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOpenContextBridge.decoded_after_root

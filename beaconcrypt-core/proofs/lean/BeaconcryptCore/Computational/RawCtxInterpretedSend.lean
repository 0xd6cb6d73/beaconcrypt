import BeaconcryptCore.Computational.RawCtxInterpretedReceive
import BeaconcryptCore.Computational.RawCtxSourceSend

/-!
The complete private source send-effect driver is parameterized only in material payloads. An arbitrary material interpretation may identify different labels while retaining the actual chains, source control, saved entry, logical capability, sequence, request, context and receive slots. The extracted admission, resume and finish specialize exactly to their native functions. RustM step failure/divergence is preserved; every typed chain/material reply directly supplies the exact advanced sealing capability.

Total source admission justifies its unique normalizer. The finite program forwards one actual KDF request and at most one selected seal, then returns the advanced kernel with the real optional reply. An active failed seal therefore retains source send advancement. Every represented exhausted admission makes no callback. Application empty-input rejection is an outer sendOwner gate and is not attributed to this opaque-context effect interface.

The complete arbitrary lawful-monad mapping requires explicit compatible KDF and sealing callback equations. The native compiler forwards the original request and full typed response before applying the existing source response decoder; no fixed KDF value law or inverse key lookup is used. Full primitive poststate and every selective underlying query cap are preserved. This does not construct a hidden-key label table or discharge its callback realization, source getter/primitive dispatch, whole-owner/raw/mixed schedules, reveals/restores, evolving-key independence or global security. Native control, logical finish, array/state copying, interpretation and callback execution remain real local work; oracle budgets do not imply native timing, memory, compiler or library-trace equality. Private labels and source state are not added to public or reveal interfaces.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInterpretedSend
open RawCtxMaterialInterpretation

structure Kdf (Material Context : Type) where
  entry : RefinedRatchet RatchetChain RatchetChain Material
  context : Context
  committed_control : ratchet.control.RatchetState
  logical : ratchet.control.SendKey
  sequence : Std.U64
  request : SymmetricRatchetKdfRequest

structure Seal (Material Context : Type) where
  advanced : RefinedRatchet RatchetChain RatchetChain Material
  context : Context
  logical : ratchet.control.SendKey
  sequence : Std.U64
  material : Material

inductive Start (Material Context : Type) where
  | exhausted : RefinedRatchet RatchetChain RatchetChain Material → Context → Start Material Context
  | requested : Kdf Material Context → Start Material Context

def mapKdf {Material Value Context : Type} (interpret : Material → Value) (pending : Kdf Material Context) :
    Kdf Value Context :=
  ⟨mapRefined interpret pending.entry, pending.context, pending.committed_control,
    pending.logical, pending.sequence, pending.request⟩

def mapSeal {Material Value Context : Type} (interpret : Material → Value) (pending : Seal Material Context) :
    Seal Value Context :=
  ⟨mapRefined interpret pending.advanced, pending.context, pending.logical,
    pending.sequence, interpret pending.material⟩

def mapStart {Material Value Context : Type} (interpret : Material → Value) : Start Material Context → Start Value Context
  | .exhausted entry context => .exhausted (mapRefined interpret entry) context
  | .requested pending => .requested (mapKdf interpret pending)

def nativeKdf {Context : Type} (pending : Kdf RatchetMaterial Context) : SendKdf Context :=
  ⟨⟨pending.entry⟩, pending.context, pending.committed_control, pending.logical, pending.sequence, pending.request⟩

def nativeSeal {Context : Type} (pending : Seal RatchetMaterial Context) : SendSeal Context :=
  ⟨⟨pending.advanced⟩, pending.context, pending.logical, pending.sequence, pending.material⟩

def nativeStart {Context : Type} : Start RatchetMaterial Context → SendStart Context
  | .exhausted entry context => .SendExhausted ⟨entry⟩ context
  | .requested pending => .SendKdfRequested (nativeKdf pending)

def resume {Material Context : Type} (pending : Kdf Material Context)
    (step : RustM (RatchetChain × Material)) : RustM (Seal Material Context) := do
  let stepped ← step
  ok {
    advanced := { pending.entry with control := pending.committed_control, send_chain := stepped.1 }
    context := pending.context
    logical := pending.logical
    sequence := pending.sequence
    material := stepped.2 }

def finish {Material Context Output : Type} (pending : Seal Material Context) (sealed : core.option.Option Output) :
    RustM (RefinedRatchet RatchetChain RatchetChain Material × core.option.Option Output) := do
  let _ ← ratchet.control.finish_send pending.logical
  ok (pending.advanced, sealed)

/-- The generic source continuation retains the entire actual native typed response conversion. -/
theorem native_resume {Context : Type} (pending : Kdf RatchetMaterial Context) (response : RatchetKdfResponse) :
    SendKdf.resume (nativeKdf pending) response =
      nativeSeal <$> resume pending (RawCtxInterpretedReceive.nativeStep response) := by
  simp only [SendKdf.resume, nativeKdf, RawCtxInterpretedReceive.nativeStep, resume,
    bind_map_left, map_bind, rust_map_ok, nativeSeal]

/-- Arbitrary noninjective material interpretation preserves the complete source continuation, including diagnostics. -/
theorem resume_map {Material Value Context : Type} (interpret : Material → Value) (pending : Kdf Material Context)
    (step : RustM (RatchetChain × Material)) :
    resume (mapKdf interpret pending) ((fun reply => (reply.1, interpret reply.2)) <$> step) =
      mapSeal interpret <$> resume pending step := by
  simp only [resume, mapKdf, bind_map_left, map_bind, rust_map_ok, mapSeal, mapRefined]

/-- Source finish retains the logical finish step and returns the advanced kernel even when sealing fails. -/
theorem native_finish {Context Output : Type} (pending : Seal RatchetMaterial Context)
    (reply : core.option.Option Output) :
    SendSeal.finish (nativeSeal pending) reply =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> finish pending reply := by
  simp only [SendSeal.finish, nativeSeal, finish, map_bind, rust_map_ok]

/-- Material interpretation preserves source publication and the exact optional sealing reply. -/
theorem finish_map {Material Value Context Output : Type} (interpret : Material → Value)
    (pending : Seal Material Context) (reply : core.option.Option Output) :
    finish (mapSeal interpret pending) reply =
      (fun result => (mapRefined interpret result.1, result.2)) <$> finish pending reply := by
  simp only [finish, mapSeal, map_bind, rust_map_ok]

def beginSend {Material Context : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) : RustM (Start Material Context) := do
  let advanced ← ratchet.control.advance_send kernel.control
  match advanced.sequence with
  | core.option.Option.None => ok (.exhausted kernel context)
  | core.option.Option.Some sequence =>
    let original ← ratchet.control.SendKey.impl.sequence advanced.key
    let equal ← core.option.Option.Insts.CoreCmpPartialEqOption.eq
      core.U64.Insts.CoreCmpPartialEqU64 original advanced.sequence
    if equal then
      let sequenceNow ← ratchet.control.RatchetState.impl.send_sequence advanced.state
      if sequenceNow = sequence then
        let bytes ← RatchetChain.as_bytes kernel.send_chain
        let request ← SymmetricRatchetKdfRequest.new bytes
        ok (.requested {
          entry := kernel, context, committed_control := advanced.state,
          logical := advanced.key, sequence, request })
      else ok (.exhausted kernel context)
    else ok (.exhausted kernel context)

private theorem map_branch {Input Output : Type} (f : Input → Output) (condition : Prop)
    [Decidable condition] (left right : RustM Input) :
    f <$> (if condition then left else right) = if condition then f <$> left else f <$> right := by
  by_cases h : condition <;> simp only [h, ite_true, ite_false]

/-- Generic admission specializes to every branch of the original source send admission. -/
theorem native_begin {Context : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain RatchetMaterial) (context : Context) :
    begin_send ⟨kernel⟩ context = nativeStart <$> beginSend kernel context := by
  simp only [begin_send, beginSend, map_bind]
  congr 1
  funext advanced
  cases sequence : advanced.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, nativeStart, nativeKdf]

/-- Every admission branch preserves the original payload interpretation and complete retained receive slots. -/
theorem begin_map {Material Value Context : Type} (interpret : Material → Value)
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) :
    beginSend (mapRefined interpret kernel) context = mapStart interpret <$> beginSend kernel context := by
  simp only [beginSend, mapRefined, map_bind]
  congr 1
  funext advanced
  cases sequence : advanced.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, mapStart, mapKdf, mapRefined]

/-- Generic source send admission is total for every represented kernel. -/
theorem begin_total {Material Context : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) :
    ∃ result, beginSend kernel context = ok result := by
  obtain ⟨advanced, hadvanced⟩ := ratchet.control.advance_send_total kernel.control
  cases hseq : advanced.sequence <;>
    simp only [beginSend, hadvanced, hseq, bind_tc_ok]
  · exact ⟨_, rfl⟩
  · cases hkey : advanced.key.available <;>
      simp only [ratchet.control.SendKey.impl.sequence, hkey, Bool.false_eq_true, ite_false, ite_true,
        core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
        ratchet.control.RatchetState.impl.send_sequence, RatchetChain.as_bytes,
        SymmetricRatchetKdfRequest.new, bind_tc_ok]
    all_goals repeat' first | exact ⟨_, rfl⟩ | split

def ready {Material Context : Type} (pending : Kdf Material Context) (reply : RatchetChain × Material) : Seal Material Context :=
  { advanced := { pending.entry with control := pending.committed_control, send_chain := reply.1 }
    context := pending.context
    logical := pending.logical
    sequence := pending.sequence
    material := reply.2 }

/-- Every typed reply directly produces the exact source sealing capability. -/
theorem ready_exact {Material Context : Type} (pending : Kdf Material Context) (reply : RatchetChain × Material) :
    resume pending (ok reply) = ok (ready pending reply) := rfl

/-- Finishing retains the actual advanced kernel and option for either logical capability state. -/
theorem finish_exact {Material Context Output : Type} (pending : Seal Material Context)
    (reply : core.option.Option Output) : finish pending reply = ok (pending.advanced, reply) := by
  cases available : pending.logical.available <;> simp [finish, ratchet.control.finish_send, available]

noncomputable def normalBegin {Material Context : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) : Start Material Context :=
  (begin_total kernel context).choose

theorem normalBegin_exact {Material Context : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) :
    beginSend kernel context = ok (normalBegin kernel context) := (begin_total kernel context).choose_spec

theorem normalBegin_map {Material Value Context : Type} (interpret : Material → Value)
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) :
    normalBegin (mapRefined interpret kernel) context = mapStart interpret (normalBegin kernel context) := by
  apply RustM.ok.inj
  rw [← normalBegin_exact]
  simpa only [normalBegin_exact, rust_map_ok] using begin_map interpret kernel context

theorem ready_map {Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Material Context) (reply : RatchetChain × Material) :
    ready (mapKdf interpret pending) (reply.1, interpret reply.2) = mapSeal interpret (ready pending reply) := rfl

theorem normalBegin_native {Context : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain RatchetMaterial) (context : Context) :
    RawCtxSourceSend.beginSend ⟨kernel⟩ context = nativeStart (normalBegin kernel context) := by
  apply RustM.ok.inj
  rw [← RawCtxSourceSend.beginSend_exact, native_begin, normalBegin_exact, rust_map_ok]

theorem ready_native {Context : Type} (pending : Kdf RatchetMaterial Context) (response : RatchetKdfResponse) :
    RawCtxSourceSend.resumeSend (nativeKdf pending) response =
      nativeSeal (ready pending (RawCtxInterpretedReceive.decodeResponse response)) := by
  apply RustM.ok.inj
  rw [← RawCtxSourceSend.resumeSend_exact, native_resume, RawCtxInterpretedReceive.decodeResponse_exact,
    ready_exact, rust_map_ok]

abbrev SendSpec (Material Context Output : Type) :=
  (SymmetricRatchetKdfRequest →ₒ (RatchetChain × Material)) + (Seal Material Context →ₒ Option Output)

noncomputable def program {Material Context Output : Type} (start : Start Material Context) :
    OracleComp (SendSpec Material Context Output)
      (RefinedRatchet RatchetChain RatchetChain Material × Option Output) :=
  match start with
  | .exhausted entry _ => pure (entry, none)
  | .requested pending => do
    let reply ← (SendSpec Material Context Output).query (.inl pending.request)
    let pendingSeal := ready pending reply
    let sealed ← (SendSpec Material Context Output).query (.inr pendingSeal)
    pure (pendingSeal.advanced, sealed)

noncomputable def send {Material Context Output : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) :
    OracleComp (SendSpec Material Context Output)
      (RefinedRatchet RatchetChain RatchetChain Material × Option Output) := program (normalBegin kernel context)

/-- Compatible callbacks preserve the complete source send computation in any lawful stateful monad. -/
theorem program_map {Material Value Context Output : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → Value)
    (labels : QueryImpl (SendSpec Material Context Output) m)
    (values : QueryImpl (SendSpec Value Context Output) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, values (.inr (mapSeal interpret pending)) = labels (.inr pending))
    (start : Start Material Context) :
    simulateQ values (program (mapStart interpret start)) =
      (fun result => (mapRefined interpret result.1, result.2)) <$> simulateQ labels (program start) := by
  cases start with
  | exhausted entry context => simp only [mapStart, program, simulateQ_pure, map_pure]
  | requested pending =>
    simp only [mapStart, program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      mapKdf, kdf, map_bind, map_pure]
    dsimp only [OracleSpec.Range, SendSpec, OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
    rw [bind_map_left]
    apply bind_congr
    intro reply
    change (do let sealed ← values (.inr (ready (mapKdf interpret pending) (reply.1, interpret reply.2)))
               pure ((ready (mapKdf interpret pending) (reply.1, interpret reply.2)).advanced, sealed)) = _
    rw [ready_map, sealing]
    rfl

/-- Native compilation forwards the actual source request/response and selected seal. -/
noncomputable def nativeAdapter {Context Output : Type} :
    QueryImpl (SendSpec RatchetMaterial Context Output) (OracleComp (RawCtxSourceSend.SendSpec Context Output))
  | .inl request => RawCtxInterpretedReceive.decodeResponse <$>
      (RawCtxSourceSend.SendSpec Context Output).query (.inl request)
  | .inr pending => (RawCtxSourceSend.SendSpec Context Output).query (.inr (nativeSeal pending))

/-- The complete generic program at native material equals the original source send driver. -/
theorem program_native {Context Output : Type} (start : Start RatchetMaterial Context) :
    RawCtxSourceSend.program (Output := Output) (nativeStart start) =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> simulateQ nativeAdapter (program start) := by
  cases start with
  | exhausted entry context => simp only [nativeStart, program, RawCtxSourceSend.program, simulateQ_pure, map_pure]
  | requested pending =>
    simp only [nativeStart, program, RawCtxSourceSend.program, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, nativeAdapter, nativeKdf, map_bind, map_pure]
    rw [bind_map_left]
    apply bind_congr
    intro response
    change (do let reply ← (RawCtxSourceSend.SendSpec Context Output).query
                 (.inr (RawCtxSourceSend.resumeSend (nativeKdf pending) response))
               pure ((RawCtxSourceSend.resumeSend (nativeKdf pending) response).advanced, reply) :
      OracleComp (RawCtxSourceSend.SendSpec Context Output) (ConcreteRatchetKernel × Option Output)) = _
    rw [ready_native]
    rfl

theorem send_map {Material Value Context Output : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → Value)
    (labels : QueryImpl (SendSpec Material Context Output) m)
    (values : QueryImpl (SendSpec Value Context Output) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, values (.inr (mapSeal interpret pending)) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) :
    simulateQ values (send (mapRefined interpret entry) context) =
      (fun result => (mapRefined interpret result.1, result.2)) <$> simulateQ labels (send entry context) := by
  simpa only [send, normalBegin_map] using program_map interpret labels values kdf sealing (normalBegin entry context)

theorem send_native {Context Output : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain RatchetMaterial) (context : Context) :
    RawCtxSourceSend.send (Output := Output) ⟨entry⟩ context =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> simulateQ nativeAdapter (send entry context) := by
  simpa only [RawCtxSourceSend.send, send, normalBegin_native] using program_native (Output := Output) (normalBegin entry context)

/-- Compatible native and label callbacks retain complete source send state, including failed sealing advancement. -/
theorem send_interpreted {Material Context Output : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (labels : QueryImpl (SendSpec Material Context Output) m)
    (native : QueryImpl (RawCtxSourceSend.SendSpec Context Output) m)
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (nativeSeal (mapSeal interpret pending))) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) :
    simulateQ native (RawCtxSourceSend.send ⟨mapRefined interpret entry⟩ context) =
      (fun result => (ConcreteRatchetKernel.mk (mapRefined interpret result.1), result.2)) <$>
        simulateQ labels (send entry context) := by
  rw [send_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := send_map interpret labels (native ∘ₛ nativeAdapter) ?_ ?_ entry context
  · rw [mapped, Functor.map_map]
  · intro request
    change simulateQ native (RawCtxInterpretedReceive.decodeResponse <$>
      (RawCtxSourceSend.SendSpec Context Output).query (.inl request)) = _
    rw [simulateQ_map]
    exact (congrArg (fun computation => RawCtxInterpretedReceive.decodeResponse <$> computation)
      (simulateQ_spec_query native (.inl request))).trans (kdf request)
  · intro pending
    change simulateQ native ((RawCtxSourceSend.SendSpec Context Output).query
      (.inr (nativeSeal (mapSeal interpret pending)))) = _
    rw [simulateQ_spec_query]
    exact sealing pending

/-- Every possible typed reply retains the one-KDF source budget. -/
theorem program_kdf_bound {Material Context Output : Type} (start : Start Material Context) :
    (program (Output := Output) start).IsQueryBoundP (fun request => request.isLeft = true) 1 := by
  cases start with
  | exhausted => simp [program]
  | requested pending =>
    rw [program, isQueryBoundP_query_bind_iff]
    refine ⟨by simp, fun response => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    simp

/-- The actual optional sealing result cannot add a second source sealing callback. -/
theorem program_seal_bound {Material Context Output : Type} (start : Start Material Context) :
    (program (Output := Output) start).IsQueryBoundP (fun request => request.isRight = true) 1 := by
  cases start with
  | exhausted => simp [program]
  | requested pending =>
    rw [program, isQueryBoundP_query_bind_iff]
    refine ⟨by simp, fun response => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    simp

/-- Complete native send interpretation retains every primitive effect through optional failure or success. -/
theorem send_state {Material Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (labels : QueryImpl (SendSpec Material Context Output) (StateT PrimitiveState (OracleComp base)))
    (native : QueryImpl (RawCtxSourceSend.SendSpec Context Output) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (nativeSeal (mapSeal interpret pending))) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) (state : PrimitiveState) :
    (simulateQ native (RawCtxSourceSend.send ⟨mapRefined interpret entry⟩ context)).run state =
      (fun result => ((ConcreteRatchetKernel.mk (mapRefined interpret result.1.1), result.1.2), result.2)) <$>
        (simulateQ labels (send entry context)).run state := by
  simpa only [StateT.run_map] using congrArg (fun work : StateT PrimitiveState (OracleComp base)
      (ConcreteRatchetKernel × Option Output) => work.run state)
    (send_interpreted interpret labels native kdf sealing entry context)

/-- All selective underlying query budgets are unchanged by the compatible complete source interpretation. -/
theorem send_query_bounds {Material Context Output PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (labels : QueryImpl (SendSpec Material Context Output) (StateT PrimitiveState (OracleComp base)))
    (native : QueryImpl (RawCtxSourceSend.SendSpec Context Output) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, RawCtxInterpretedReceive.decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (nativeSeal (mapSeal interpret pending))) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (context : Context) (state : PrimitiveState)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ native (RawCtxSourceSend.send ⟨mapRefined interpret entry⟩ context)).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ labels (send entry context)).run state).IsQueryBoundP predicate budget := by
  rw [send_state interpret labels native kdf sealing entry context state, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxInterpretedSend

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.native_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.native_resume

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.resume_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.resume_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.native_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.native_finish

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.finish_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.native_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.native_begin

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.begin_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.begin_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.begin_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.begin_total

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.ready_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.ready_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.finish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.finish_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.normalBegin_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.normalBegin_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.normalBegin_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.normalBegin_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.ready_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.ready_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.normalBegin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.normalBegin_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.ready_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.ready_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.program_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.program_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.send_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.send_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.send_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.send_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.send_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.send_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.program_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.program_kdf_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.program_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.program_seal_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.send_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.send_state

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedSend.send_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedSend.send_query_bounds

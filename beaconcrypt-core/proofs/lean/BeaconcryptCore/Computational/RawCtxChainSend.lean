import BeaconcryptCore.Computational.RawCtxChainInterpretation
import BeaconcryptCore.Computational.RawCtxInterpretedSend

/-!
The complete extracted send-effect driver carries arbitrary private send/receive chain payloads and an opaque pending chain request. The source control and original material slots are retained. Arbitrary noninjective chain interpretation reconstructs the exact source request, admission, continuation and complete stateful program. An active failed seal retains actual send advancement. Every typed continuation has at most one KDF and one seal call.

The source normalizer is total; constant native chains appear only as proof witnesses for totality reflection, never as protocol values or a runtime replacement. Callback realization equations remain explicit operational obligations. They are not a new security assumption, a hidden-input sampler, an independent-key table or a source ownership/reveal/persistence theorem. Opaque handles and entire source state remain private protocol context; local conversion/control/copying/primitive work is not erased by query bounds.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxChainSend
open RawCtxChainInterpretation RawCtxMaterialInterpretation

structure Kdf (Send Receive Material Context : Type) where
  entry : RefinedRatchet Send Receive Material
  context : Context
  committed_control : ratchet.control.RatchetState
  logical : ratchet.control.SendKey
  sequence : Std.U64
  request : Send

structure Seal (Send Receive Material Context : Type) where
  advanced : RefinedRatchet Send Receive Material
  context : Context
  logical : ratchet.control.SendKey
  sequence : Std.U64
  material : Material

inductive Start (Send Receive Material Context : Type) where
  | exhausted : RefinedRatchet Send Receive Material → Context → Start Send Receive Material Context
  | requested : Kdf Send Receive Material Context → Start Send Receive Material Context

def nativeRequest (chain : RatchetChain) : SymmetricRatchetKdfRequest := ⟨chain.bytes, ratchet.SYM_RATCHET_INFO⟩

def nativeKdf {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Kdf Send Receive Material Context) : RawCtxInterpretedSend.Kdf Material Context :=
  ⟨mapChains send receive pending.entry, pending.context, pending.committed_control,
    pending.logical, pending.sequence, nativeRequest (send pending.request)⟩

def nativeSeal {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Seal Send Receive Material Context) : RawCtxInterpretedSend.Seal Material Context :=
  ⟨mapChains send receive pending.advanced, pending.context, pending.logical, pending.sequence, pending.material⟩

def nativeStart {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) :
    Start Send Receive Material Context → RawCtxInterpretedSend.Start Material Context
  | .exhausted entry context => .exhausted (mapChains send receive entry) context
  | .requested pending => .requested (nativeKdf send receive pending)

def resume {Send Receive Material Context : Type} (pending : Kdf Send Receive Material Context)
    (step : RustM (Send × Material)) : RustM (Seal Send Receive Material Context) := do
  let stepped ← step
  ok {
    advanced := { pending.entry with control := pending.committed_control, send_chain := stepped.1 }
    context := pending.context
    logical := pending.logical
    sequence := pending.sequence
    material := stepped.2 }

/-- Source resume advances the same complete kernel under arbitrary chain interpretation. -/
theorem native_resume {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Kdf Send Receive Material Context) (step : RustM (Send × Material)) :
    RawCtxInterpretedSend.resume (nativeKdf send receive pending)
      ((fun result => (send result.1, result.2)) <$> step) =
      nativeSeal send receive <$> resume pending step := by
  simp only [RawCtxInterpretedSend.resume, nativeKdf, bind_map_left, map_bind, rust_map_ok,
    resume, nativeSeal, mapChains]

def beginSend {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (context : Context) : RustM (Start Send Receive Material Context) := do
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
        ok (.requested {
          entry := kernel, context, committed_control := advanced.state,
          logical := advanced.key, sequence, request := kernel.send_chain })
      else ok (.exhausted kernel context)
    else ok (.exhausted kernel context)

/-- Interpreting only the two private chain fields gives the unchanged source admission program. -/
theorem native_begin {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    RawCtxInterpretedSend.beginSend (mapChains send receive kernel) context =
      nativeStart send receive <$> beginSend kernel context := by
  simp only [RawCtxInterpretedSend.beginSend, beginSend, mapChains, map_bind]
  congr 1
  funext advanced
  cases present : advanced.sequence
  all_goals simp only [map_bind, apply_ite, rust_map_ok, nativeStart, nativeKdf, mapChains,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, bind_tc_ok, nativeRequest]

/-- Source admission remains total without inspecting either chain payload. -/
theorem begin_total {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    ∃ result, beginSend kernel context = ok result := by
  let zero : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩
  have equal := native_begin (fun _ : Send => zero) (fun _ : Receive => zero) kernel context
  obtain ⟨result, executed⟩ := RawCtxInterpretedSend.begin_total
    (mapChains (fun _ : Send => zero) (fun _ : Receive => zero) kernel) context
  rw [executed] at equal
  cases observed : beginSend kernel context <;> simp_all [rust_map_ok]
  all_goals cases equal

noncomputable def normalBegin {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (context : Context) : Start Send Receive Material Context :=
  (begin_total kernel context).choose

theorem normalBegin_exact {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    beginSend kernel context = ok (normalBegin kernel context) := (begin_total kernel context).choose_spec

/-- The unique source normalizer preserves the complete interpreted admission value. -/
theorem normalBegin_native {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    RawCtxInterpretedSend.normalBegin (mapChains send receive kernel) context =
      nativeStart send receive (normalBegin kernel context) :=
  RustM.ok.inj ((RawCtxInterpretedSend.normalBegin_exact _ _).symm.trans
    ((native_begin send receive kernel context).trans
      (congrArg (fun result => nativeStart send receive <$> result) (normalBegin_exact kernel context))))

def ready {Send Receive Material Context : Type} (pending : Kdf Send Receive Material Context)
    (reply : Send × Material) : Seal Send Receive Material Context :=
  { advanced := { pending.entry with control := pending.committed_control, send_chain := reply.1 }
    context := pending.context, logical := pending.logical, sequence := pending.sequence, material := reply.2 }

abbrev SendSpec (Send Receive Material Context Output : Type) :=
  (Send →ₒ (Send × Material)) + (Seal Send Receive Material Context →ₒ Option Output)

noncomputable def program {Send Receive Material Context Output : Type}
    (start : Start Send Receive Material Context) :
    OracleComp (SendSpec Send Receive Material Context Output) (RefinedRatchet Send Receive Material × Option Output) :=
  match start with
  | .exhausted entry _ => pure (entry, none)
  | .requested pending => do
      let reply ← (SendSpec Send Receive Material Context Output).query (.inl pending.request)
      let pendingSeal := ready pending reply
      let sealed ← (SendSpec Send Receive Material Context Output).query (.inr pendingSeal)
      pure (pendingSeal.advanced, sealed)

/-- Actual full send effects factor through private chain handles and the same stateful callbacks. -/
theorem program_native {Send Receive Material Context Output : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (labels : QueryImpl (SendSpec Send Receive Material Context Output) m)
    (native : QueryImpl (RawCtxInterpretedSend.SendSpec Material Context Output) m)
    (kdf : ∀ request, native (.inl (nativeRequest (send request))) =
      (fun reply => (send reply.1, reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (nativeSeal send receive pending)) = labels (.inr pending))
    (start : Start Send Receive Material Context) :
    simulateQ native (RawCtxInterpretedSend.program (nativeStart send receive start)) =
      (fun result => (mapChains send receive result.1, result.2)) <$> simulateQ labels (program start) := by
  cases start with
  | exhausted entry context => simp only [nativeStart, program, RawCtxInterpretedSend.program, simulateQ_pure, map_pure]
  | requested pending =>
      simp only [nativeStart, program, RawCtxInterpretedSend.program, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, nativeKdf, kdf, map_bind, map_pure]
      dsimp only [OracleSpec.Range, SendSpec, RawCtxInterpretedSend.SendSpec,
        OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
      rw [bind_map_left]
      refine bind_congr (fun reply => ?_)
      change (do let sealed ← native (.inr (nativeSeal send receive (ready pending reply)))
                 pure (mapChains send receive (ready pending reply).advanced, sealed)) = _
      rw [sealing]
      rfl

noncomputable def execute {Send Receive Material Context Output : Type}
    (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    OracleComp (SendSpec Send Receive Material Context Output) (RefinedRatchet Send Receive Material × Option Output) :=
  program (normalBegin kernel context)

/-- The complete original send driver preserves all callback effects and failed-seal advancement. -/
theorem execute_native {Send Receive Material Context Output : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (labels : QueryImpl (SendSpec Send Receive Material Context Output) m)
    (native : QueryImpl (RawCtxInterpretedSend.SendSpec Material Context Output) m)
    (kdf : ∀ request, native (.inl (nativeRequest (send request))) =
      (fun reply => (send reply.1, reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, native (.inr (nativeSeal send receive pending)) = labels (.inr pending))
    (kernel : RefinedRatchet Send Receive Material) (context : Context) :
    simulateQ native (RawCtxInterpretedSend.send (mapChains send receive kernel) context) =
      (fun result => (mapChains send receive result.1, result.2)) <$> simulateQ labels (execute kernel context) := by
  simpa only [execute, RawCtxInterpretedSend.send, normalBegin_native] using
    program_native send receive labels native kdf sealing (normalBegin kernel context)

/-- Every typed continuation retains the source's one-KDF call cap. -/
theorem program_kdf_bound {Send Receive Material Context Output : Type}
    (start : Start Send Receive Material Context) :
    (program (Output := Output) start).IsQueryBoundP (fun query => query.isLeft = true) 1 := by
  cases start with
  | exhausted => simp [program]
  | requested pending =>
    rw [program, isQueryBoundP_query_bind_iff]
    refine ⟨by simp, fun response => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    simp

/-- Actual optional sealing replies retain the source's one-seal call cap. -/
theorem program_seal_bound {Send Receive Material Context Output : Type}
    (start : Start Send Receive Material Context) :
    (program (Output := Output) start).IsQueryBoundP (fun query => query.isRight = true) 1 := by
  cases start with
  | exhausted => simp [program]
  | requested pending =>
    rw [program, isQueryBoundP_query_bind_iff]
    refine ⟨by simp, fun response => ?_⟩
    rw [isQueryBoundP_query_bind_iff]
    simp

end BeaconcryptCore.Computational.RawCtxChainSend

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.native_resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.native_resume

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.native_begin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.native_begin

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.begin_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.begin_total

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.normalBegin_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.normalBegin_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.normalBegin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.normalBegin_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.program_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.execute_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.execute_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.program_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.program_kdf_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxChainSend.program_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainSend.program_seal_bound

import BeaconcryptCore.Computational.RawCtxChainSend

/-!
The actual receive-effect driver retains both private chain coordinates and its original pending request as arbitrary payloads. Source control, staged slots, requested sequence, context, cached/future opening capability and rollback entry remain complete. Exact admission/resume laws and total normalizers commute with arbitrary noninjective chain maps. Every possible typed reply decreases the original source measure, so the complete recursive program uses no fuel fallback. Arbitrary lawful callback effects and actual optional publication replies are preserved.

Constant native chains are proof witnesses for reflecting source totality and the unchanged measure; they are not runtime protocol values or a distribution replacement. Callback realization equations remain explicit and must be discharged by the actual source/table interpreter. This does not hide all input aliases from a cryptographic observer, assume freshness, instantiate independent evolving keys, add a reveal/restore policy or prove global security. The termination rank remaining+1 is distinct from the tight callback allowance proved separately.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxChainReceive
open RawCtxChainInterpretation RawCtxMaterialInterpretation
open RawCtxInterpretedOpening hiding sequence

structure Kdf (Send Receive Material Context : Type) where
  entry : RefinedRatchet Send Receive Material
  context : Context
  target : Std.U64
  working_control : ratchet.control.RatchetState
  staged_slots : Std.Array (core.option.Option (CachedReceiveKey Material)) 50#usize
  first_slot : Std.U8
  skipped : Std.U8
  remaining : Std.U8
  request : Receive

inductive Effect (Send Receive Material Context : Type) where
  | rejected : RefinedRatchet Send Receive Material → Context → Effect Send Receive Material Context
  | kdfRequested : Kdf Send Receive Material Context → Effect Send Receive Material Context
  | openRequested : Opening Send Receive Material Context → Effect Send Receive Material Context

def rejected {Send Receive Material Context : Type} (entry : RefinedRatchet Send Receive Material)
    (context : Context) : RustM (Effect Send Receive Material Context) := ok (.rejected entry context)

def nativeKdf {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Kdf Send Receive Material Context) : RawCtxInterpretedReceive.Kdf Material Context :=
  ⟨mapChains send receive pending.entry, pending.context, pending.target, pending.working_control,
    pending.staged_slots, pending.first_slot, pending.skipped, pending.remaining,
    RawCtxChainSend.nativeRequest (receive pending.request)⟩

def nativeEffect {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain) :
    Effect Send Receive Material Context → RawCtxInterpretedReceive.Effect Material Context
  | .rejected entry context => .rejected (mapChains send receive entry) context
  | .kdfRequested pending => .kdfRequested (nativeKdf send receive pending)
  | .openRequested opening => .openRequested (mapOpeningChains send receive opening)

/-- Actual extracted receive-resume control, with private chain payloads and an opaque next request. -/
def resume {Send Receive Material Context : Type} (self : Kdf Send Receive Material Context)
    (step : RustM (Receive × Material)) : RustM (Effect Send Receive Material Context) := do
  if self.remaining = 0#u8
  then rejected self.entry self.context
  else
    if self.remaining = 1#u8
    then
      let advanced ←
        ratchet.control.advance_receive_target self.working_control
      match advanced.sequence with
      | core.option.Option.None =>
        rejected self.entry self.context
      | core.option.Option.Some sequence =>
        if sequence = self.target
        then
          let stepped ← step
          let b ←
            ratchet.refined.pending_receive_is_valid self.entry
              {
                committed_control := advanced.state,
                final_receive_chain := stepped.1,
                staged_slots := self.staged_slots,
                target_sequence := sequence,
                target_material := stepped.2,
                first_slot := self.first_slot,
                skipped := self.skipped
              } self.target
          if b
          then
            ok (Effect.openRequested
              {
                entry := self.entry,
                context := self.context,
                prepared :=
                  (ratchet.refined.PreparedReceive.PreparedReceiveFutureCase
                    {
                      committed_control := advanced.state,
                      final_receive_chain := stepped.1,
                      staged_slots := self.staged_slots,
                      target_sequence := sequence,
                      target_material := stepped.2,
                      first_slot := self.first_slot,
                      skipped := self.skipped
                    })
              })
          else rejected self.entry self.context
        else rejected self.entry self.context
    else
      let advanced ← ratchet.control.advance_receive self.working_control
      match advanced.sequence with
      | core.option.Option.None =>
        rejected self.entry self.context
      | core.option.Option.Some sequence =>
        match advanced.slot with
        | core.option.Option.None =>
          rejected self.entry self.context
        | core.option.Option.Some slot =>
          let slot_index ← lift (UScalar.cast .Usize slot)
          let o ←
            ratchet.control.RatchetState.receive_key_at advanced.state slot
          let b ←
            core.option.Option.Insts.CoreCmpPartialEqOption.eq
              core.U64.Insts.CoreCmpPartialEqU64 o advanced.sequence
          if b
          then
            let i ← ratchet.control.RECEIVE_CACHE_CAPACITY
            if slot_index >= i
            then rejected self.entry self.context
            else
              let i1 ← lift (UScalar.cast .Usize self.first_slot)
              let i2 ← lift (UScalar.cast .Usize self.skipped)
              let i3 ← i1 + i2
              if slot_index = i3
              then
                let o1 ← Array.index_usize self.staged_slots slot_index
                let b1 ← core.option.Option.is_some o1
                if b1
                then rejected self.entry self.context
                else
                  if sequence >= self.target
                  then
                    rejected self.entry self.context
                  else
                    let stepped ←
                      step
                    let a ←
                      Array.update self.staged_slots slot_index
                        (core.option.Option.Some
                        ({ sequence, material := stepped.2 } :
                        ratchet.refined.CachedReceiveKey
                        Material))
                    let i4 ← self.skipped + 1#u8
                    let i5 ← self.remaining - 1#u8
                    ok (Effect.kdfRequested
                      {
                        self
                          with
                          working_control := advanced.state,
                          staged_slots := a,
                          skipped := i4,
                          remaining := i5,
                          request := stepped.1
                      })
              else rejected self.entry self.context
          else rejected self.entry self.context


/-- The extracted admission branches retain original counters, cache window, chain request and context. -/
def beginReceive {Send Receive Material Context : Type} (kernel : RefinedRatchet Send Receive Material)
    (target : Std.U64) (context : Context) : RustM (Effect Send Receive Material Context) := do
  let plan ← ratchet.control.plan_receive_until kernel.control target
  match plan.sequence with
  | core.option.Option.None => rejected kernel context
  | core.option.Option.Some sequence =>
    if plan.derivations = 0#u64
    then
      let o ← ratchet.refined.prepare_cached_receive kernel sequence
      match o with
      | core.option.Option.None =>
        rejected kernel context
      | core.option.Option.Some prepared =>
        ok (Effect.openRequested
          {
            entry := kernel,
            context,
            prepared :=
              (ratchet.refined.PreparedReceive.PreparedReceiveCachedCase
                prepared)
          })
    else
      let skipped ← plan.derivations - 1#u64
      if skipped > ratchet.control.RATCHET_MAX_GAP
      then rejected kernel context
      else
        let remaining ← lift (UScalar.cast .U8 plan.derivations)
        let first_slot ←
          ratchet.control.RatchetState.receive_cache_len kernel.control
        let i ← lift (UScalar.cast .U8 skipped)
        let b ←
          ratchet.refined.refined_receive_slots_are_empty kernel
            first_slot i
        if b
        then
          let a1 ←
            ratchet.refined.empty_material_slots Material
          ok (Effect.kdfRequested
            {
              entry := kernel,
              context,
              target := sequence,
              working_control := kernel.control,
              staged_slots := a1,
              first_slot,
              skipped := 0#u8,
              remaining,
              request := kernel.receive_chain
            })
        else rejected kernel context



private theorem pending_step_valid {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Kdf Send Receive Material Context) (committed : ratchet.control.RatchetState)
    (chain : Receive) (material : Material) (target : Std.U64) :
    pending_receive_is_valid (mapChains send receive pending.entry)
      ⟨committed, receive chain, pending.staged_slots, target, material, pending.first_slot, pending.skipped⟩
      pending.target =
    pending_receive_is_valid pending.entry
      ⟨committed, chain, pending.staged_slots, target, material, pending.first_slot, pending.skipped⟩
      pending.target :=
  pending_valid_chains send receive pending.entry
    ⟨committed, chain, pending.staged_slots, target, material, pending.first_slot, pending.skipped⟩ pending.target

private theorem map_branch {Input Output : Type} (f : Input → Output) (condition : Prop)
    [Decidable condition] (left right : RustM Input) :
    f <$> (if condition then left else right) = if condition then f <$> left else f <$> right := by
  by_cases h : condition <;> simp only [h, if_true, if_false]

/-- The complete source skip/target resume preserves rollback state and the opaque next-chain request. -/
theorem native_resume {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Kdf Send Receive Material Context) (step : RustM (Receive × Material)) :
    RawCtxInterpretedReceive.resume (nativeKdf send receive pending)
      ((fun result => (receive result.1, result.2)) <$> step) =
      nativeEffect send receive <$> resume pending step := by
  simp only [RawCtxInterpretedReceive.resume, resume, nativeKdf, map_branch, map_bind,
    bind_map_left, rejected, RawCtxInterpretedReceive.rejected, rust_map_ok, nativeEffect,
    pending_step_valid]
  congr 1
  congr 1
  all_goals congr 1
  all_goals funext advanced
  all_goals cases present : advanced.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, nativeEffect, mapOpeningChains,
    mapPreparedChain, mapPendingChain]
  all_goals cases slot : advanced.slot
  all_goals simp only [map_branch, map_bind, rust_map_ok, nativeEffect, nativeKdf,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, bind_tc_ok, RawCtxChainSend.nativeRequest]

private theorem empty_slots_chains {Send Receive Material : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (kernel : RefinedRatchet Send Receive Material) (slot left : Std.U8) :
    refined_receive_slots_are_empty (mapChains send receive kernel) slot left =
      refined_receive_slots_are_empty kernel slot left := rfl

/-- Exact source admission retains every control/window/cache branch and creates its real request from the interpreted receive chain. -/
theorem native_begin {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    RawCtxInterpretedReceive.beginReceive (mapChains send receive kernel) target context =
      nativeEffect send receive <$> beginReceive kernel target context := by
  simp only [RawCtxInterpretedReceive.beginReceive, beginReceive, ↓prepare_cached_chains,
    ↓empty_slots_chains, map_bind, mapChains]
  congr 1
  funext plan
  cases sequence : plan.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, nativeEffect,
    RawCtxInterpretedReceive.rejected, rejected, nativeKdf,
    RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, bind_tc_ok, RawCtxChainSend.nativeRequest]
  all_goals congr 1
  congr 1
  funext prepared
  cases prepared <;> rfl

/-- Every typed callback still has a normal source continuation, without a chain-value premise. -/
theorem resume_total {Send Receive Material Context : Type}
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material) :
    ∃ effect, resume pending (ok reply) = ok effect := by
  let zero : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩
  have equal := native_resume (fun _ : Send => zero) (fun _ : Receive => zero) pending (ok reply)
  simp only [rust_map_ok, RawCtxInterpretedReceive.normalResume_exact] at equal
  cases observed : resume pending (ok reply) <;> simp_all [rust_map_ok]
  all_goals cases equal

/-- Total actual admission transports to arbitrary private chain payloads. -/
theorem begin_total {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    ∃ effect, beginReceive kernel target context = ok effect := by
  let zero : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩
  have equal := native_begin (fun _ : Send => zero) (fun _ : Receive => zero) kernel target context
  rw [RawCtxInterpretedReceive.normalBegin_exact] at equal
  cases observed : beginReceive kernel target context <;> simp_all [rust_map_ok]
  all_goals cases equal

noncomputable def normalResume {Send Receive Material Context : Type}
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material) : Effect Send Receive Material Context :=
  (resume_total pending reply).choose

noncomputable def normalBegin {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    Effect Send Receive Material Context := (begin_total kernel target context).choose

theorem normalResume_exact {Send Receive Material Context : Type}
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material) :
    resume pending (ok reply) = ok (normalResume pending reply) := (resume_total pending reply).choose_spec

theorem normalBegin_exact {Send Receive Material Context : Type}
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    beginReceive kernel target context = ok (normalBegin kernel target context) :=
  (begin_total kernel target context).choose_spec

/-- Exact normal resume maps to the whole existing source continuation. -/
theorem normalResume_native {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material) :
    RawCtxInterpretedReceive.normalResume (nativeKdf send receive pending) (receive reply.1, reply.2) =
      nativeEffect send receive (normalResume pending reply) := by
  apply RustM.ok.inj
  rw [← RawCtxInterpretedReceive.normalResume_exact]
  simpa only [rust_map_ok, normalResume_exact] using native_resume send receive pending (ok reply)

/-- Exact normal admission retains the entire source entry and pending request relation. -/
theorem normalBegin_native {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    RawCtxInterpretedReceive.normalBegin (mapChains send receive kernel) target context =
      nativeEffect send receive (normalBegin kernel target context) :=
  RustM.ok.inj ((RawCtxInterpretedReceive.normalBegin_exact _ _ _).symm.trans
    ((native_begin send receive kernel target context).trans
      (congrArg (fun result => nativeEffect send receive <$> result) (normalBegin_exact kernel target context))))

def effectRank {Send Receive Material Context : Type} : Effect Send Receive Material Context → Nat
  | .kdfRequested pending => pending.remaining.val + 1
  | _ => 0

/-- The source measure inspects only the unchanged receive counter. -/
theorem native_rank {Send Receive Material Context : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (effect : Effect Send Receive Material Context) :
    RawCtxInterpretedReceive.effectRank (nativeEffect send receive effect) = effectRank effect := by
  cases effect <;> rfl

/-- Every possible typed reply decreases the unchanged source continuation measure. -/
theorem normalResume_rank {Send Receive Material Context : Type}
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material) :
    effectRank (normalResume pending reply) < effectRank (.kdfRequested pending) := by
  let zero : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩
  have decreasing := RawCtxInterpretedReceive.normalResume_rank
    (nativeKdf (fun _ : Send => zero) (fun _ : Receive => zero) pending) (zero, reply.2)
  rw [normalResume_native (fun _ : Send => zero) (fun _ : Receive => zero) pending reply] at decreasing
  rw [native_rank] at decreasing
  exact decreasing

/-- Full cached/future publication is total for every optional reply and typed pending state. -/
theorem finish_total {Send Receive Material Context Plaintext : Type}
    (pending : Opening Send Receive Material Context) (reply : core.option.Option Plaintext) :
    ∃ result, RawCtxInterpretedOpening.finish pending reply = ok result := by
  let zero : RatchetChain := ⟨⟨List.replicate 32 0#u8, by simp⟩⟩
  have equal := opening_finish_chains (fun _ : Send => zero) (fun _ : Receive => zero) pending reply
  rw [RawCtxInterpretedReceive.normalFinish_exact] at equal
  cases observed : RawCtxInterpretedOpening.finish pending reply <;> simp_all [rust_map_ok]
  all_goals cases equal

noncomputable def normalFinish {Send Receive Material Context Plaintext : Type}
    (pending : Opening Send Receive Material Context) (reply : core.option.Option Plaintext) :
    RefinedRatchet Send Receive Material × core.option.Option Plaintext := (finish_total pending reply).choose

theorem normalFinish_exact {Send Receive Material Context Plaintext : Type}
    (pending : Opening Send Receive Material Context) (reply : core.option.Option Plaintext) :
    RawCtxInterpretedOpening.finish pending reply = ok (normalFinish pending reply) :=
  (finish_total pending reply).choose_spec

/-- The full original normal publication retains the mapped kernel and exactly the same option. -/
theorem normalFinish_native {Send Receive Material Context Plaintext : Type}
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (pending : Opening Send Receive Material Context) (reply : core.option.Option Plaintext) :
    RawCtxInterpretedReceive.normalFinish (mapOpeningChains send receive pending) reply =
      (mapChains send receive (normalFinish pending reply).1, (normalFinish pending reply).2) :=
  RustM.ok.inj ((RawCtxInterpretedReceive.normalFinish_exact _ _).symm.trans
    ((opening_finish_chains send receive pending reply).trans
      (congrArg (fun result => (fun value => (mapChains send receive value.1, value.2)) <$> result)
        (normalFinish_exact pending reply))))

abbrev ReceiveSpec (Send Receive Material Context Plaintext : Type) :=
  (Receive →ₒ (Receive × Material)) +
    (Opening Send Receive Material Context →ₒ core.option.Option Plaintext)

/-- The source skip driver is finite on every reply; its private request contains only a chain handle. -/
noncomputable def program {Send Receive Material Context Plaintext : Type}
    (effect : Effect Send Receive Material Context) :
    OracleComp (ReceiveSpec Send Receive Material Context Plaintext)
      (RefinedRatchet Send Receive Material × core.option.Option Plaintext) :=
  match effect with
  | .rejected entry _ => pure (entry, .None)
  | .openRequested pending => do
      let reply ← (ReceiveSpec Send Receive Material Context Plaintext).query (.inr pending)
      pure (normalFinish pending reply)
  | .kdfRequested pending => do
      let reply ← (ReceiveSpec Send Receive Material Context Plaintext).query (.inl pending.request)
      program (normalResume pending reply)
termination_by effectRank effect
decreasing_by exact normalResume_rank _ _

noncomputable def execute {Send Receive Material Context Plaintext : Type}
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    OracleComp (ReceiveSpec Send Receive Material Context Plaintext)
      (RefinedRatchet Send Receive Material × core.option.Option Plaintext) :=
  program (normalBegin kernel target context)

/-- Every adaptive source skip/open continuation retains complete state under compatible chain callbacks. -/
theorem program_native {Send Receive Material Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (labels : QueryImpl (ReceiveSpec Send Receive Material Context Plaintext) m)
    (native : QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Material Context Plaintext) m)
    (kdf : ∀ request, native (.inl (RawCtxChainSend.nativeRequest (receive request))) =
      (fun reply => (receive reply.1, reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (mapOpeningChains send receive pending)) = labels (.inr pending))
    (effect : Effect Send Receive Material Context) :
    simulateQ native (RawCtxInterpretedReceive.program (nativeEffect send receive effect)) =
      (fun result => (mapChains send receive result.1, result.2)) <$> simulateQ labels (program effect) := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      simp only [nativeEffect, program, RawCtxInterpretedReceive.program, simulateQ_pure, map_pure]
    | openRequested pending =>
      simp only [nativeEffect, program, RawCtxInterpretedReceive.program, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, opening, map_bind, map_pure, normalFinish_native]
      rfl
    | kdfRequested pending =>
      simp only [nativeEffect, program, RawCtxInterpretedReceive.program, simulateQ_bind,
        simulateQ_spec_query, nativeKdf, kdf, map_bind]
      dsimp only [OracleSpec.Range, ReceiveSpec, RawCtxInterpretedReceive.ReceiveSpec,
        OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
      rw [_root_.bind_map_left]
      refine bind_congr (fun reply => ?_)
      change simulateQ native (RawCtxInterpretedReceive.program
        (RawCtxInterpretedReceive.normalResume (nativeKdf send receive pending) (receive reply.1, reply.2))) = _
      rw [normalResume_native]
      exact ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl

/-- Actual admission and every later stateful skip/open callback have the same complete source interpretation. -/
theorem execute_native {Send Receive Material Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (send : Send → RatchetChain) (receive : Receive → RatchetChain)
    (labels : QueryImpl (ReceiveSpec Send Receive Material Context Plaintext) m)
    (native : QueryImpl (RawCtxInterpretedReceive.ReceiveSpec Material Context Plaintext) m)
    (kdf : ∀ request, native (.inl (RawCtxChainSend.nativeRequest (receive request))) =
      (fun reply => (receive reply.1, reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (mapOpeningChains send receive pending)) = labels (.inr pending))
    (kernel : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    simulateQ native (RawCtxInterpretedReceive.receive (mapChains send receive kernel) target context) =
      (fun result => (mapChains send receive result.1, result.2)) <$> simulateQ labels (execute kernel target context) := by
  simpa only [execute, RawCtxInterpretedReceive.receive, normalBegin_native] using
    program_native send receive labels native kdf opening (normalBegin kernel target context)

end BeaconcryptCore.Computational.RawCtxChainReceive

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.native_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.native_resume

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.native_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.native_begin

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.resume_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.resume_total

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.begin_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.begin_total

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.normalResume_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.normalResume_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.normalBegin_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.normalBegin_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.normalResume_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.normalResume_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.normalBegin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.normalBegin_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.native_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.native_rank

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.normalResume_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.normalResume_rank

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.finish_total

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.normalFinish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.normalFinish_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.normalFinish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.normalFinish_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.program_native

/-- info: 'BeaconcryptCore.Computational.RawCtxChainReceive.execute_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainReceive.execute_native

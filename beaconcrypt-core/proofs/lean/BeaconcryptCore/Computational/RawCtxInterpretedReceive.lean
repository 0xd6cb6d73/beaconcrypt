import BeaconcryptCore.Computational.RawCtxInterpretedOpening

/-!
This is the complete private receive-effect driver with material payloads interpreted by an arbitrary function, which may identify different labels. The source chains, controls, pending counters, array presence and sequence tags, KDF request, target and opening context stay unchanged. The extracted begin and resume bodies are parameterized only where material is carried or returned; exact native specialization and noninjective mapping laws retain every RustM rejection, failure and divergence. Publication uses the existing generic cached/future source functions.

Totality is proved for every represented generic entry and every typed chain/material callback reply. Exact normalizers select only those unique source results. The finite oracle driver uses the actual strictly decreasing remaining counter and has no fuel fallback. Its material-mapping theorem holds in an arbitrary lawful monad under explicit compatible KDF and opening callback equations; these are operational realization obligations, not cryptographic assumptions. The native compiler forwards the actual source request and complete typed response before applying the existing 76-byte response conversion. Complete native receive equality retains the original optional result, source publication and entire primitive poststate.

The generic program has at most its source rank in KDF calls and one opening call; that rank allowance is conservative and is not advertised as the sharper existing 51-call admission bound. Every selective underlying query budget is exactly preserved by the compatible full-state interpretation. Deterministic control, array copying, response conversion, material interpretation and callback work remain local computation. Equal oracle-query budgets do not imply zero local work or native timing, allocation, panic/unwind or library trace equality.

This establishes a complete receive-effect interface, before a concrete hidden-key label table or whole-owner/raw/mixed schedule compiler is supplied. The opening callback still receives the private selected capability; compatibility with a particular getter/primitive interpreter must be discharged using the actual opening laws. There is no inverse key lookup, material injectivity, fixed functional KDF reply law, independent key sampling, freshness, ideal opening correctness, public exposure of private state, source send erasure or global security conclusion. Actual typed native replies and all represented malformed source states remain covered.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxInterpretedReceive
open RawCtxMaterialInterpretation
open RawCtxInterpretedOpening hiding sequence

structure Kdf (Material Context : Type) where
  entry : RefinedRatchet RatchetChain RatchetChain Material
  context : Context
  target : Std.U64
  working_control : ratchet.control.RatchetState
  staged_slots : Std.Array (core.option.Option (CachedReceiveKey Material)) 50#usize
  first_slot : Std.U8
  skipped : Std.U8
  remaining : Std.U8
  request : SymmetricRatchetKdfRequest

inductive Effect (Material Context : Type) where
  | rejected : RefinedRatchet RatchetChain RatchetChain Material → Context → Effect Material Context
  | kdfRequested : Kdf Material Context → Effect Material Context
  | openRequested : Opening RatchetChain RatchetChain Material Context → Effect Material Context

def rejected {Material Context : Type} (entry : RefinedRatchet RatchetChain RatchetChain Material)
    (context : Context) : RustM (Effect Material Context) := ok (.rejected entry context)

def nativeKdf {Context : Type} (pending : Kdf RatchetMaterial Context) : ReceiveKdf Context :=
  ⟨⟨pending.entry⟩, pending.context, pending.target, pending.working_control, pending.staged_slots,
    pending.first_slot, pending.skipped, pending.remaining, pending.request⟩

def nativeEffect {Context : Type} : Effect RatchetMaterial Context → ReceiveEffect Context
  | .rejected entry context => .ReceiveRejected ⟨entry⟩ context
  | .kdfRequested pending => .ReceiveKdfRequested (nativeKdf pending)
  | .openRequested opening => .ReceiveOpenRequested (toNative opening)

def nativeStep (response : RatchetKdfResponse) : RustM (RatchetChain × RatchetMaterial) :=
  (fun step => (step.chain, step.material)) <$> ratchet_step_from_response response

/-- Actual extracted receive-resume control, parameterized only by its chain/material step payload. -/
def resume {Material Context : Type} (self : Kdf Material Context)
    (step : RustM (RatchetChain × Material)) : RustM (Effect Material Context) := do
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
                    let a1 ← ratchet.RatchetChain.as_bytes stepped.1
                    let srkr ← ratchet.SymmetricRatchetKdfRequest.new a1
                    ok (Effect.kdfRequested
                      {
                        self
                          with
                          working_control := advanced.state,
                          staged_slots := a,
                          skipped := i4,
                          remaining := i5,
                          request := srkr
                      })
              else rejected self.entry self.context
          else rejected self.entry self.context


private theorem map_branch {Input Output : Type} (f : Input → Output) (condition : Prop)
    [Decidable condition] (left right : RustM Input) :
    f <$> (if condition then left else right) =
      if condition then f <$> left else f <$> right := by
  by_cases h : condition <;> simp only [h, if_true, if_false]

/-- Concrete specialization retains the complete extracted native receive-resume result. -/
theorem native_resume {Context : Type} (pending : Kdf RatchetMaterial Context)
    (response : RatchetKdfResponse) :
    ReceiveKdf.resume (nativeKdf pending) response =
      nativeEffect <$> resume pending (nativeStep response) := by
  simp only [nativeKdf]
  by_cases zero : pending.remaining = 0#u8
  · simp only [ReceiveKdf.resume, resume, zero, if_true, receive_rejected,
      rejected, rust_map_ok, nativeEffect]
  · simp only [ReceiveKdf.resume, resume, zero, if_false, nativeStep,
      bind_map_left]
    by_cases last : pending.remaining = 1#u8 <;>
      simp only [last, if_true, if_false, map_bind]
    all_goals
      congr 1
      funext advanced
      cases present : advanced.sequence
    all_goals simp only [receive_rejected, rejected, rust_map_ok, nativeEffect, map_bind, map_branch, toNative]
    all_goals first
      | cases slot : advanced.slot
      | skip
    all_goals simp only [map_bind, map_branch, rust_map_ok, nativeEffect, nativeKdf]

def mapKdf {Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Material Context) : Kdf Value Context :=
  ⟨mapRefined interpret pending.entry, pending.context, pending.target, pending.working_control,
    mapArray (mapOption (mapCached interpret)) pending.staged_slots, pending.first_slot,
    pending.skipped, pending.remaining, pending.request⟩

def mapEffect {Material Value Context : Type} (interpret : Material → Value) :
    Effect Material Context → Effect Value Context
  | .rejected entry context => .rejected (mapRefined interpret entry) context
  | .kdfRequested pending => .kdfRequested (mapKdf interpret pending)
  | .openRequested opening => .openRequested (mapOpening interpret opening)

private theorem pending_step_valid_map {Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Material Context) (committed : ratchet.control.RatchetState)
    (chain : RatchetChain) (material : Material) (target : Std.U64) :
    pending_receive_is_valid (mapRefined interpret pending.entry)
      ⟨committed, chain, mapArray (mapOption (mapCached interpret)) pending.staged_slots,
        target, interpret material, pending.first_slot, pending.skipped⟩ pending.target =
    pending_receive_is_valid pending.entry
      ⟨committed, chain, pending.staged_slots, target, material, pending.first_slot, pending.skipped⟩
        pending.target :=
  pending_valid_map interpret pending.entry
    ⟨committed, chain, pending.staged_slots, target, material, pending.first_slot, pending.skipped⟩ pending.target

private theorem update_cached_map {Material Value : Type} (interpret : Material → Value)
    (slots : Std.Array (core.option.Option (CachedReceiveKey Material)) 50#usize)
    (index : Std.Usize) (sequence : Std.U64) (material : Material) :
    Array.update (mapArray (mapOption (mapCached interpret)) slots) index
        (.Some ⟨sequence, interpret material⟩) =
      mapArray (mapOption (mapCached interpret)) <$>
        Array.update slots index (.Some ⟨sequence, material⟩) :=
  mapArray_update (mapOption (mapCached interpret)) slots index (.Some ⟨sequence, material⟩)

/-- Interpretation retains every source resume branch and its complete step result, without injective material values. -/
theorem resume_map {Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Material Context) (step : RustM (RatchetChain × Material)) :
    resume (mapKdf interpret pending) ((fun result => (result.1, interpret result.2)) <$> step) =
      mapEffect interpret <$> resume pending step := by
  simp only [resume, mapKdf, map_branch, map_bind, bind_map_left, rejected, rust_map_ok, mapEffect,
    pending_step_valid_map, mapArray_index, option_is_some_map, update_cached_map]
  congr 1
  congr 1
  all_goals
    congr 1
    funext advanced
    cases present : advanced.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, mapEffect, mapOpening, mapPrepared, mapPending]
  all_goals cases slot : advanced.slot
  all_goals simp only [map_branch, map_bind, rust_map_ok, mapEffect, mapKdf]

/-- The extracted admission branches retain original counters, cache window, chain request and context. -/
def beginReceive {Material Context : Type} (kernel : RefinedRatchet RatchetChain RatchetChain Material)
    (target : Std.U64) (context : Context) : RustM (Effect Material Context) := do
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
          let a ← ratchet.RatchetChain.as_bytes kernel.receive_chain
          let request ← ratchet.SymmetricRatchetKdfRequest.new a
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
              request
            })
        else rejected kernel context


/-- Concrete admission is the exact extracted source begin operation. -/
theorem native_begin {Context : Type} (kernel : RefinedRatchet RatchetChain RatchetChain RatchetMaterial)
    (target : Std.U64) (context : Context) :
    begin_receive (ConcreteRatchetKernel.mk kernel) target context =
      nativeEffect <$> beginReceive kernel target context := by
  simp only [begin_receive, beginReceive, map_bind]
  congr 1
  funext plan
  cases sequence : plan.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, nativeEffect, rejected, receive_rejected, nativeKdf]
  all_goals
    congr 1
    congr 1
    funext prepared
    cases prepared <;> simp only [rust_map_ok, nativeEffect, toNative]

/-- Source admission, rejection and initial request commute with arbitrary material interpretation. -/
theorem begin_map {Material Value Context : Type} (interpret : Material → Value)
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    beginReceive (mapRefined interpret kernel) target context =
      mapEffect interpret <$> beginReceive kernel target context := by
  simp only [beginReceive, ↓prepare_cached_map, ↓empty_slots_map, map_bind, bind_map_left,
    rejected, empty_material_map interpret, mapRefined]
  congr 1
  funext plan
  cases sequence : plan.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, mapEffect, mapKdf, mapRefined]
  all_goals
    congr 1
    congr 1
    funext prepared
    cases prepared <;> simp only [rust_map_ok, mapEffect, mapOpening, mapPrepared, mapRefined]

def effectEntry {Material Context : Type} : Effect Material Context → RefinedRatchet RatchetChain RatchetChain Material
  | .rejected entry _ => entry
  | .kdfRequested pending => pending.entry
  | .openRequested opening => opening.entry

def Progress {Material Context : Type} (pending : Kdf Material Context) (effect : Effect Material Context) : Prop :=
  effectEntry effect = pending.entry ∧ match effect with
    | .kdfRequested next => next.remaining.val < pending.remaining.val
    | _ => True

/-- Every typed chain/material reply yields a total source continuation with retained entry and strictly decreasing KDF count. -/
theorem resume_progress {Material Context : Type} (pending : Kdf Material Context)
    (stepped : RatchetChain × Material) :
    ∃ result, resume pending (ok stepped) = ok result ∧ Progress pending result := by
  by_cases hzero : pending.remaining = 0#u8
  · simp [resume, hzero, rejected, Progress, effectEntry]
  · simp only [resume, hzero, if_false]
    split
    case isFalse hlast =>
      obtain ⟨advanced, hadvanced⟩ := ratchet.control.advance_receive_ok pending.working_control
      cases hseq : advanced.sequence <;> cases hslot : advanced.slot <;>
        simp only [hadvanced, hseq, hslot, lift, bind_tc_ok, rejected]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      rename_i sequence slot
      obtain ⟨logical, hlogical⟩ := ratchet.control.RatchetState.receive_key_at_total advanced.state slot
      obtain ⟨nextSlot, hnextSlot, hnextSlotVal⟩ := ratchet.control.uscalar_add_eq_ok
        (UScalar.cast UScalarTy.Usize pending.first_slot) (UScalar.cast UScalarTy.Usize pending.skipped)
        (by scalar_tac)
      cases logical <;> simp only [hlogical, core.option.Option.Insts.CoreCmpPartialEqOption.eq,
        core.U64.Insts.CoreCmpPartialEqU64, ratchet.control.capacity_eq_ok, hnextSlot, bind_tc_ok,
        Bool.false_eq_true, if_false]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      repeat' first | exact ⟨_, rfl, rfl, True.intro⟩ | split
      all_goals simp only [ratchet.control.array_index_eq_ok pending.staged_slots
        (UScalar.cast UScalarTy.Usize slot) (by scalar_tac), BeaconcryptCore.core_option_is_some_eq_ok,
        bind_tc_ok, ite_self, RustM.ok.injEq, Progress, effectEntry]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      obtain ⟨skipped, hskipped, _⟩ := ratchet.control.uscalar_add_eq_ok pending.skipped 1#u8 (by scalar_tac)
      obtain ⟨remaining, hremaining, hremainingval⟩ := ratchet.control.uscalar_sub_eq_ok pending.remaining 1#u8 (by scalar_tac)
      simp only [hskipped, hremaining, RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new,
        ratchet.control.array_update_eq_ok pending.staged_slots (UScalar.cast UScalarTy.Usize slot)
          (.Some ⟨sequence, stepped.2⟩) (by scalar_tac), bind_tc_ok]
      split <;> refine ⟨_, rfl, rfl, ?_⟩
      all_goals first | exact True.intro | (dsimp; scalar_tac)
    case isTrue hlast =>
      obtain ⟨advanced, hadvanced⟩ := ratchet.control.advance_receive_target_total pending.working_control
      cases hseq : advanced.sequence <;> simp only [hadvanced, hseq, bind_tc_ok, rejected]
      all_goals first | exact ⟨_, rfl, rfl, True.intro⟩ | skip
      rename_i sequence
      obtain ⟨valid, hvalid⟩ := refined.pending_receive_is_valid_ok pending.entry
        { committed_control := advanced.state, final_receive_chain := stepped.1,
          staged_slots := pending.staged_slots, target_sequence := sequence,
          target_material := stepped.2, first_slot := pending.first_slot, skipped := pending.skipped }
        pending.target
      simp only [hvalid, bind_tc_ok]
      repeat' first | exact ⟨_, rfl, rfl, True.intro⟩ | split

/-- Source admission is total for every represented generic-material kernel and retains that entry. -/
theorem begin_total {Material Context : Type}
    (kernel : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    ∃ result, beginReceive kernel target context = ok result ∧ effectEntry result = kernel := by
  obtain ⟨plan, hplan⟩ := ratchet.control.plan_receive_until_total kernel.control target
  cases hseq : plan.sequence <;> simp only [beginReceive, hplan, bind_tc_ok, hseq, rejected]
  all_goals first | exact ⟨_, rfl, rfl⟩ | skip
  rename_i sequence
  split
  · obtain ⟨prepared, hprepared⟩ := refined.prepare_cached_receive_total kernel sequence
    cases prepared <;> simp [hprepared, effectEntry]
  · obtain ⟨skipped, hskipped, _⟩ := ratchet.control.uscalar_sub_eq_ok plan.derivations 1#u64 (by scalar_tac)
    obtain ⟨empty, hempty⟩ := refined.refined_receive_slots_are_empty_ok kernel
      kernel.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped)
    cases empty <;> by_cases hgap : skipped > ratchet.control.RATCHET_MAX_GAP <;>
      simp only [hskipped, lift, ratchet.control.RatchetState.receive_cache_len, hempty, hgap,
        RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, refined.empty_material_slots,
        bind_tc_ok, Bool.false_eq_true, if_false, if_true, RustM.ok.injEq, effectEntry]
    all_goals exact ⟨_, rfl, rfl⟩

/-- Generic publication is total and returns the exact callback option, including malformed represented pending states. -/
theorem finish_total {Material Context Plaintext : Type}
    (pending : Opening RatchetChain RatchetChain Material Context) (reply : core.option.Option Plaintext) :
    ∃ kernel, RawCtxInterpretedOpening.finish pending reply = ok (kernel, reply) := by
  cases reply with
  | none => exact ⟨pending.entry, rfl⟩
  | some plaintext =>
    cases hprepared : pending.prepared with
    | PreparedReceiveCachedCase prepared =>
      obtain ⟨published, hpublish⟩ := refined.publish_cached_receive_ok pending.entry prepared
      exact ⟨published, by simp only [RawCtxInterpretedOpening.finish, hprepared, hpublish, bind_tc_ok]⟩
    | PreparedReceiveFutureCase prepared =>
      obtain ⟨published, hpublish⟩ := refined.publish_future_receive_ok pending.entry prepared
      exact ⟨published, by simp only [RawCtxInterpretedOpening.finish, hprepared, hpublish, bind_tc_ok]⟩

/-- Exact total source normalizers, with no fallback on malformed states. -/
noncomputable def normalResume {Material Context : Type} (pending : Kdf Material Context)
    (reply : RatchetChain × Material) : Effect Material Context := (resume_progress pending reply).choose

noncomputable def normalBegin {Material Context : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    Effect Material Context := (begin_total entry target context).choose

noncomputable def normalFinish {Material Context Plaintext : Type}
    (pending : Opening RatchetChain RatchetChain Material Context) (reply : core.option.Option Plaintext) :
    RefinedRatchet RatchetChain RatchetChain Material × core.option.Option Plaintext :=
  ((finish_total pending reply).choose, reply)

theorem normalResume_exact {Material Context : Type} (pending : Kdf Material Context)
    (reply : RatchetChain × Material) : resume pending (ok reply) = ok (normalResume pending reply) :=
  (resume_progress pending reply).choose_spec.1

theorem normalBegin_exact {Material Context : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    beginReceive entry target context = ok (normalBegin entry target context) :=
  (begin_total entry target context).choose_spec.1

theorem normalFinish_exact {Material Context Plaintext : Type}
    (pending : Opening RatchetChain RatchetChain Material Context) (reply : core.option.Option Plaintext) :
    RawCtxInterpretedOpening.finish pending reply = ok (normalFinish pending reply) :=
  (finish_total pending reply).choose_spec

def effectRank {Material Context : Type} : Effect Material Context → Nat
  | .kdfRequested pending => pending.remaining.val + 1
  | _ => 0

/-- Every possible typed reply decreases the actual continuation measure. -/
theorem normalResume_rank {Material Context : Type} (pending : Kdf Material Context)
    (reply : RatchetChain × Material) :
    effectRank (normalResume pending reply) < effectRank (.kdfRequested pending) := by
  have progress := (resume_progress pending reply).choose_spec.2
  change Progress pending (normalResume pending reply) at progress
  cases hnext : normalResume pending reply with
  | rejected => simp [effectRank]
  | openRequested => simp [effectRank]
  | kdfRequested later =>
    have remaining := progress.2
    simp only [hnext] at remaining
    simpa only [effectRank, Nat.add_lt_add_iff_right] using remaining

open OracleComp OracleSpec

/-- The only private callbacks are the unchanged source KDF request and selected opening capability. -/
abbrev ReceiveSpec (Material Context Plaintext : Type) :=
  (SymmetricRatchetKdfRequest →ₒ (RatchetChain × Material)) +
    (Opening RatchetChain RatchetChain Material Context →ₒ core.option.Option Plaintext)

/-- The generic source driver is finite for every typed reply and has no fuel fallback. -/
noncomputable def program {Material Context Plaintext : Type} (effect : Effect Material Context) :
    OracleComp (ReceiveSpec Material Context Plaintext)
      (RefinedRatchet RatchetChain RatchetChain Material × core.option.Option Plaintext) :=
  match effect with
  | .rejected entry _ => pure (entry, .None)
  | .openRequested pending => do
    let reply ← (ReceiveSpec Material Context Plaintext).query (.inr pending)
    pure (normalFinish pending reply)
  | .kdfRequested pending => do
    let reply ← (ReceiveSpec Material Context Plaintext).query (.inl pending.request)
    program (normalResume pending reply)
termination_by effectRank effect
decreasing_by exact normalResume_rank _ _

noncomputable def receive {Material Context Plaintext : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    OracleComp (ReceiveSpec Material Context Plaintext)
      (RefinedRatchet RatchetChain RatchetChain Material × core.option.Option Plaintext) :=
  program (normalBegin entry target context)

/-- Exact source normalization commutes with any material interpretation. -/
theorem normalResume_map {Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Material Context) (reply : RatchetChain × Material) :
    normalResume (mapKdf interpret pending) (reply.1, interpret reply.2) =
      mapEffect interpret (normalResume pending reply) := by
  apply RustM.ok.inj
  rw [← normalResume_exact]
  have mapped := resume_map interpret pending (ok reply)
  simpa only [rust_map_ok, normalResume_exact] using mapped

theorem normalBegin_map {Material Value Context : Type} (interpret : Material → Value)
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    normalBegin (mapRefined interpret entry) target context =
      mapEffect interpret (normalBegin entry target context) := by
  apply RustM.ok.inj
  rw [← normalBegin_exact]
  simpa only [normalBegin_exact, rust_map_ok] using begin_map interpret entry target context

theorem normalFinish_map {Material Value Context Plaintext : Type} (interpret : Material → Value)
    (pending : Opening RatchetChain RatchetChain Material Context) (reply : core.option.Option Plaintext) :
    normalFinish (mapOpening interpret pending) reply =
      (mapRefined interpret (normalFinish pending reply).1, (normalFinish pending reply).2) := by
  apply RustM.ok.inj
  rw [← normalFinish_exact]
  simpa only [normalFinish_exact, rust_map_ok] using finish_map interpret pending reply

/-- Compatible private callbacks preserve the complete finite source program in any lawful stateful monad. -/
theorem program_map {Material Value Context Plaintext : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → Value)
    (labels : QueryImpl (ReceiveSpec Material Context Plaintext) m)
    (values : QueryImpl (ReceiveSpec Value Context Plaintext) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, values (.inr (mapOpening interpret pending)) = labels (.inr pending))
    (effect : Effect Material Context) :
    simulateQ values (program (mapEffect interpret effect)) =
      (fun result => (mapRefined interpret result.1, result.2)) <$> simulateQ labels (program effect) := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp only [mapEffect, program, simulateQ_pure, map_pure]
    | openRequested pending =>
      simp only [mapEffect, program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        opening, map_bind, map_pure, normalFinish_map]
      rfl
    | kdfRequested pending =>
      simp only [mapEffect, program, simulateQ_bind, simulateQ_spec_query, mapKdf, kdf,
        map_bind]
      dsimp only [OracleSpec.Range, ReceiveSpec, OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
      rw [_root_.bind_map_left]
      apply bind_congr
      intro reply
      change simulateQ values (program (normalResume (mapKdf interpret pending) (reply.1, interpret reply.2))) = _
      rw [normalResume_map]
      exact ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl

/-- Initial admission followed by every adaptive callback retains the full interpreted result and state. -/
theorem receive_map {Material Value Context Plaintext : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → Value)
    (labels : QueryImpl (ReceiveSpec Material Context Plaintext) m)
    (values : QueryImpl (ReceiveSpec Value Context Plaintext) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, values (.inr (mapOpening interpret pending)) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    simulateQ values (receive (mapRefined interpret entry) target context) =
      (fun result => (mapRefined interpret result.1, result.2)) <$>
        simulateQ labels (receive entry target context) := by
  simpa only [receive, normalBegin_map] using program_map interpret labels values kdf opening
    (normalBegin entry target context)

/-- Decode the complete actual source response using its already proved total conversion. -/
noncomputable def decodeResponse (response : RatchetKdfResponse) : RatchetChain × RatchetMaterial :=
  let stepped := (BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response).choose
  (stepped.chain, stepped.material)

theorem decodeResponse_exact (response : RatchetKdfResponse) :
    nativeStep response = ok (decodeResponse response) := by
  unfold nativeStep
  rw [(BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response).choose_spec]
  rfl

/-- Decoding a native typed reply yields exactly the existing normalized source continuation. -/
theorem normalResume_native {Context : Type} (pending : Kdf RatchetMaterial Context)
    (response : RatchetKdfResponse) :
    RawCtxOwnerOracle.resume (nativeKdf pending) response =
      nativeEffect (normalResume pending (decodeResponse response)) := by
  apply RustM.ok.inj
  rw [← RawCtxOwnerOracle.resume_exact, native_resume, decodeResponse_exact,
    normalResume_exact, rust_map_ok]

theorem normalBegin_native {Context : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain RatchetMaterial) (target : Std.U64) (context : Context) :
    RawCtxOwnerOracle.begin ⟨entry⟩ target context = nativeEffect (normalBegin entry target context) := by
  apply RustM.ok.inj
  rw [← RawCtxOwnerOracle.begin_exact, native_begin, normalBegin_exact, rust_map_ok]

theorem normalFinish_native {Context Plaintext : Type}
    (pending : Opening RatchetChain RatchetChain RatchetMaterial Context) (reply : core.option.Option Plaintext) :
    RawCtxOwnerOracle.finish (toNative pending) reply =
      (ConcreteRatchetKernel.mk (normalFinish pending reply).1, (normalFinish pending reply).2) := by
  apply RustM.ok.inj
  rw [← RawCtxOwnerOracle.finish_exact, native_finish, normalFinish_exact, rust_map_ok]

/-- The native compiler forwards every original query and only decodes its actual complete KDF response. -/
noncomputable def nativeAdapter {Context Plaintext : Type} :
    QueryImpl (ReceiveSpec RatchetMaterial Context Plaintext)
      (OracleComp (RawCtxOwnerOracle.ReceiveSpec Context Plaintext))
  | .inl request => decodeResponse <$> (RawCtxOwnerOracle.ReceiveSpec Context Plaintext).query (.inl request)
  | .inr pending => (RawCtxOwnerOracle.ReceiveSpec Context Plaintext).query (.inr (toNative pending))

/-- The complete generic driver at native material is the actual source oracle program. -/
theorem program_native {Context Plaintext : Type} (effect : Effect RatchetMaterial Context) :
    RawCtxOwnerOracle.program (Plaintext := Plaintext) (nativeEffect effect) =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$>
        simulateQ nativeAdapter (program effect) := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      simp only [nativeEffect, RawCtxOwnerOracle.program, program, simulateQ_pure, map_pure]
    | openRequested pending =>
      simp only [nativeEffect, RawCtxOwnerOracle.program, program, simulateQ_bind,
        simulateQ_spec_query, nativeAdapter, simulateQ_pure, map_bind, map_pure, normalFinish_native]
      rfl
    | kdfRequested pending =>
      simp only [nativeEffect, RawCtxOwnerOracle.program, program, simulateQ_bind,
        simulateQ_spec_query, nativeAdapter, nativeKdf, map_bind]
      rw [bind_map_left]
      apply bind_congr
      intro response
      change RawCtxOwnerOracle.program (RawCtxOwnerOracle.resume (nativeKdf pending) response) = _
      rw [normalResume_native]
      exact ih _ (hdepth ▸ normalResume_rank pending (decodeResponse response)) _ rfl

/-- Exact admission and the native compiler connect the complete operation to the original source receive. -/
theorem receive_native {Context Plaintext : Type}
    (entry : RefinedRatchet RatchetChain RatchetChain RatchetMaterial) (target : Std.U64) (context : Context) :
    RawCtxOwnerOracle.receive (Plaintext := Plaintext) ⟨entry⟩ target context =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$>
        simulateQ nativeAdapter (receive entry target context) := by
  simpa only [RawCtxOwnerOracle.receive, receive, normalBegin_native] using
    program_native (Plaintext := Plaintext) (normalBegin entry target context)

/-- Native typed callbacks and compatible material-label callbacks give the same complete source operation. -/
theorem receive_interpreted {Material Context Plaintext : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (interpret : Material → RatchetMaterial)
    (labels : QueryImpl (ReceiveSpec Material Context Plaintext) m)
    (native : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) m)
    (kdf : ∀ request, decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (toNative (mapOpening interpret pending))) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context) :
    simulateQ native (RawCtxOwnerOracle.receive ⟨mapRefined interpret entry⟩ target context) =
      (fun result => (ConcreteRatchetKernel.mk (mapRefined interpret result.1), result.2)) <$>
        simulateQ labels (receive entry target context) := by
  rw [receive_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  have mapped := receive_map interpret labels (native ∘ₛ nativeAdapter) ?_ ?_ entry target context
  · rw [mapped, Functor.map_map]
  · intro request
    change simulateQ native (decodeResponse <$>
      (RawCtxOwnerOracle.ReceiveSpec Context Plaintext).query (.inl request)) = _
    rw [simulateQ_map]
    exact (congrArg (fun computation => decodeResponse <$> computation)
      (simulateQ_spec_query native (.inl request))).trans (kdf request)
  · intro pending
    change simulateQ native ((RawCtxOwnerOracle.ReceiveSpec Context Plaintext).query
      (.inr (toNative (mapOpening interpret pending)))) = _
    rw [simulateQ_spec_query]
    exact opening pending

/-- Generic source KDF calls are bounded for all possible material labels and chain replies. -/
theorem program_kdf_bound {Material Context Plaintext : Type} (effect : Effect Material Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP
      (fun request => request.isLeft = true) (effectRank effect) := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [program]
    | openRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp
    | kdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp only [Sum.isLeft, not_true_eq_false, false_or, if_true]
      refine ⟨by simp only [effectRank] at hdepth; omega, fun reply => ?_⟩
      exact (ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl).mono
        (Nat.le_pred_of_lt (hdepth ▸ normalResume_rank pending reply))

/-- Generic receive performs at most one actual opening callback, independently of its optional result. -/
theorem program_open_bound {Material Context Plaintext : Type} (effect : Effect Material Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP (fun request => request.isRight = true) 1 := by
  generalize hdepth : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context => simp [program]
    | openRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp
    | kdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      simp only [Sum.isRight, Bool.false_eq_true, not_false_eq_true, true_or, if_false, true_and]
      exact fun reply => ih _ (hdepth ▸ normalResume_rank pending reply) _ rfl

/-- The actual native receive retains the same entire primitive poststate under material interpretation. -/
theorem receive_state {Material Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (labels : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT PrimitiveState (OracleComp base)))
    (native : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (toNative (mapOpening interpret pending))) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context)
    (state : PrimitiveState) :
    (simulateQ native (RawCtxOwnerOracle.receive ⟨mapRefined interpret entry⟩ target context)).run state =
      (fun result => ((ConcreteRatchetKernel.mk (mapRefined interpret result.1.1), result.1.2), result.2)) <$>
        (simulateQ labels (receive entry target context)).run state := by
  simpa only [StateT.run_map] using congrArg (fun work : StateT PrimitiveState (OracleComp base)
      (ConcreteRatchetKernel × core.option.Option Plaintext) => work.run state)
    (receive_interpreted interpret labels native kdf opening entry target context)

/-- Every selective underlying query budget is identical after retaining the full interpreted primitive state. -/
theorem receive_query_bounds {Material Context Plaintext PrimitiveState ι : Type} {base : OracleSpec ι}
    (interpret : Material → RatchetMaterial)
    (labels : QueryImpl (ReceiveSpec Material Context Plaintext) (StateT PrimitiveState (OracleComp base)))
    (native : QueryImpl (RawCtxOwnerOracle.ReceiveSpec Context Plaintext) (StateT PrimitiveState (OracleComp base)))
    (kdf : ∀ request, decodeResponse <$> native (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, native (.inr (toNative (mapOpening interpret pending))) = labels (.inr pending))
    (entry : RefinedRatchet RatchetChain RatchetChain Material) (target : Std.U64) (context : Context)
    (state : PrimitiveState) (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((simulateQ native (RawCtxOwnerOracle.receive ⟨mapRefined interpret entry⟩ target context)).run state).IsQueryBoundP predicate budget ↔
      ((simulateQ labels (receive entry target context)).run state).IsQueryBoundP predicate budget := by
  rw [receive_state interpret labels native kdf opening entry target context state, isQueryBoundP_map_iff]

end BeaconcryptCore.Computational.RawCtxInterpretedReceive

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.native_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.native_resume

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.resume_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.resume_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.native_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.native_begin

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.begin_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.begin_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.resume_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.resume_progress

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.begin_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.begin_total

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.finish_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.finish_total

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalBegin_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalBegin_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalFinish_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalFinish_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_rank

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalBegin_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalBegin_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalFinish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalFinish_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_map

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.decodeResponse_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.decodeResponse_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalResume_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalBegin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalBegin_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalFinish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.normalFinish_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_native

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_interpreted

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_kdf_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_open_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.program_open_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_state

/--
info: 'BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxInterpretedReceive.receive_query_bounds

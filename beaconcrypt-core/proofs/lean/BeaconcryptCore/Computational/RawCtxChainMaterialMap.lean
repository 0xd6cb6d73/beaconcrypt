import BeaconcryptCore.Computational.RawCtxChainRealization

/-!
Material interpretation for the existing private-chain driver retains the same opaque chain requests. The map need not be injective. These operational equations preserve every original cached/future branch and complete continuation; they add no distribution or security premise.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxChainMaterialMap
open RawCtxMaterialInterpretation RawCtxInterpretedOpening
open RawCtxChainReceive

def receiveKdf {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Send Receive Material Context) : Kdf Send Receive Value Context :=
  ⟨mapRefined interpret pending.entry, pending.context, pending.target, pending.working_control,
    mapArray (mapOption (mapCached interpret)) pending.staged_slots, pending.first_slot,
    pending.skipped, pending.remaining, pending.request⟩

def receiveEffect {Send Receive Material Value Context : Type} (interpret : Material → Value) :
    Effect Send Receive Material Context → Effect Send Receive Value Context
  | .rejected entry context => .rejected (mapRefined interpret entry) context
  | .kdfRequested pending => .kdfRequested (receiveKdf interpret pending)
  | .openRequested pending => .openRequested (mapOpening interpret pending)

private theorem map_branch {Input Output : Type} (f : Input → Output) (condition : Prop)
    [Decidable condition] (left right : RustM Input) :
    f <$> (if condition then left else right) =
      if condition then f <$> left else f <$> right := by
  by_cases h : condition <;> simp only [h, ite_true, ite_false]

private theorem pending_step_valid_map {Send Receive Material Value Context : Type}
    (interpret : Material → Value) (pending : Kdf Send Receive Material Context)
    (committed : ratchet.control.RatchetState) (chain : Receive) (material : Material)
    (target : Std.U64) :
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

/-- A material map preserves the full extracted resume with the identical opaque next-chain request. -/
theorem receive_resume {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Send Receive Material Context) (step : RustM (Receive × Material)) :
    resume (receiveKdf interpret pending) ((fun result => (result.1, interpret result.2)) <$> step) =
      receiveEffect interpret <$> resume pending step := by
  simp only [resume, receiveKdf, map_branch, map_bind, bind_map_left, rejected, rust_map_ok, receiveEffect,
    pending_step_valid_map, mapArray_index, option_is_some_map, update_cached_map]
  congr 1
  congr 1
  all_goals congr 1
  all_goals funext advanced
  all_goals cases present : advanced.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, receiveEffect, mapOpening, mapPrepared, mapPending]
  all_goals cases slot : advanced.slot
  all_goals simp only [map_branch, map_bind, rust_map_ok, receiveEffect, receiveKdf]

/-- The same source cache/sequence checks select the same branch before any material is used. -/
theorem receive_begin {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (entry : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    beginReceive (mapRefined interpret entry) target context =
      receiveEffect interpret <$> beginReceive entry target context := by
  simp only [beginReceive, ↓prepare_cached_map, ↓empty_slots_map, map_bind, bind_map_left,
    rejected, empty_material_map interpret, mapRefined]
  congr 1
  funext plan
  cases sequence : plan.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, receiveEffect, receiveKdf, mapRefined]
  all_goals
    congr 1
    congr 1
    funext prepared
    cases prepared <;> simp only [rust_map_ok, receiveEffect, mapOpening, mapPrepared, mapRefined]

/-- Normalizing the same typed source response preserves its entire mapped effect. -/
theorem receive_normalResume {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (pending : Kdf Send Receive Material Context) (reply : Receive × Material) :
    normalResume (receiveKdf interpret pending) (reply.1, interpret reply.2) =
      receiveEffect interpret (normalResume pending reply) := by
  apply RustM.ok.inj
  rw [← normalResume_exact]
  simpa only [rust_map_ok, normalResume_exact] using receive_resume interpret pending (ok reply)

/-- The original total admission normalizer keeps the same complete entry and target. -/
theorem receive_normalBegin {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (entry : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    normalBegin (mapRefined interpret entry) target context =
      receiveEffect interpret (normalBegin entry target context) := by
  apply RustM.ok.inj
  rw [← normalBegin_exact]
  simpa only [rust_map_ok, normalBegin_exact] using receive_begin interpret entry target context

/-- Every actual optional plaintext, including failure, finishes with the same mapped source state. -/
theorem receive_normalFinish {Send Receive Material Value Context Plaintext : Type}
    (interpret : Material → Value) (pending : Opening Send Receive Material Context)
    (reply : core.option.Option Plaintext) :
    normalFinish (mapOpening interpret pending) reply =
      (mapRefined interpret (normalFinish pending reply).1, (normalFinish pending reply).2) := by
  apply RustM.ok.inj
  rw [← normalFinish_exact]
  simpa only [rust_map_ok, normalFinish_exact] using finish_map interpret pending reply

/-- Material mapping adds no source derivation or termination step. -/
theorem receive_rank {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (effect : Effect Send Receive Material Context) :
    effectRank (receiveEffect interpret effect) = effectRank effect := by
  cases effect <;> rfl

/-- The entire skip/open computation retains every callback effect and the actual optional plaintext under a material map. The supplied callback equalities are operational interfaces to be discharged by a concrete compiler. -/
theorem receive_program {Send Receive Material Value Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m] (interpret : Material → Value)
    (labels : QueryImpl (ReceiveSpec Send Receive Material Context Plaintext) m)
    (values : QueryImpl (ReceiveSpec Send Receive Value Context Plaintext) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, values (.inr (mapOpening interpret pending)) = labels (.inr pending))
    (effect : Effect Send Receive Material Context) :
    simulateQ values (program (receiveEffect interpret effect)) =
      (fun result => (mapRefined interpret result.1, result.2)) <$> simulateQ labels (program effect) := by
  generalize ranked : effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | rejected entry context =>
          simp only [receiveEffect, program, simulateQ_pure, map_pure]
      | openRequested pending =>
          simp only [receiveEffect, program, simulateQ_bind, simulateQ_spec_query,
            simulateQ_pure, opening, map_bind, map_pure, receive_normalFinish]
          rfl
      | kdfRequested pending =>
          simp only [receiveEffect, program, simulateQ_bind, simulateQ_spec_query,
            receiveKdf, kdf, map_bind]
          dsimp only [OracleSpec.Range, ReceiveSpec, OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
          rw [_root_.bind_map_left]
          refine bind_congr fun reply => ?_
          change simulateQ values (program
            (normalResume (receiveKdf interpret pending) (reply.1, interpret reply.2))) = _
          rw [receive_normalResume]
          exact ih _ (ranked ▸ normalResume_rank pending reply) _ rfl

/-- Material interpretation commutes with original receive admission followed by its complete stateful continuation. -/
theorem receive_execute {Send Receive Material Value Context Plaintext : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m] (interpret : Material → Value)
    (labels : QueryImpl (ReceiveSpec Send Receive Material Context Plaintext) m)
    (values : QueryImpl (ReceiveSpec Send Receive Value Context Plaintext) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (opening : ∀ pending, values (.inr (mapOpening interpret pending)) = labels (.inr pending))
    (entry : RefinedRatchet Send Receive Material) (target : Std.U64) (context : Context) :
    simulateQ values (execute (mapRefined interpret entry) target context) =
      (fun result => (mapRefined interpret result.1, result.2)) <$>
        simulateQ labels (execute entry target context) := by
  simpa only [execute, receive_normalBegin] using
    receive_program interpret labels values kdf opening (normalBegin entry target context)

def sendKdf {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (pending : RawCtxChainSend.Kdf Send Receive Material Context) :
    RawCtxChainSend.Kdf Send Receive Value Context :=
  ⟨mapRefined interpret pending.entry, pending.context, pending.committed_control,
    pending.logical, pending.sequence, pending.request⟩

def sendSeal {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (pending : RawCtxChainSend.Seal Send Receive Material Context) :
    RawCtxChainSend.Seal Send Receive Value Context :=
  ⟨mapRefined interpret pending.advanced, pending.context, pending.logical,
    pending.sequence, interpret pending.material⟩

def sendStart {Send Receive Material Value Context : Type} (interpret : Material → Value) :
    RawCtxChainSend.Start Send Receive Material Context → RawCtxChainSend.Start Send Receive Value Context
  | .exhausted entry context => .exhausted (mapRefined interpret entry) context
  | .requested pending => .requested (sendKdf interpret pending)

/-- Original sending admission and sequence exhaustion inspect no mapped material value. -/
theorem send_begin {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (entry : RefinedRatchet Send Receive Material) (context : Context) :
    RawCtxChainSend.beginSend (mapRefined interpret entry) context =
      sendStart interpret <$> RawCtxChainSend.beginSend entry context := by
  simp only [RawCtxChainSend.beginSend, mapRefined, map_bind]
  congr 1
  funext advanced
  cases sequence : advanced.sequence
  all_goals simp only [map_branch, map_bind, rust_map_ok, sendStart, sendKdf, mapRefined]

/-- The same total source sending normalizer carries all old cached material through the map. -/
theorem send_normalBegin {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (entry : RefinedRatchet Send Receive Material) (context : Context) :
    RawCtxChainSend.normalBegin (mapRefined interpret entry) context =
      sendStart interpret (RawCtxChainSend.normalBegin entry context) := by
  apply RustM.ok.inj
  rw [← RawCtxChainSend.normalBegin_exact]
  simpa only [rust_map_ok, RawCtxChainSend.normalBegin_exact] using send_begin interpret entry context

/-- Sending advances the complete state before sealing, retaining the interpreted response and unchanged old cache. -/
theorem send_ready {Send Receive Material Value Context : Type} (interpret : Material → Value)
    (pending : RawCtxChainSend.Kdf Send Receive Material Context) (reply : Send × Material) :
    RawCtxChainSend.ready (sendKdf interpret pending) (reply.1, interpret reply.2) =
      sendSeal interpret (RawCtxChainSend.ready pending reply) := rfl

/-- A mapped send makes the same KDF and optional sealing calls and retains the advanced kernel even when sealing fails. -/
theorem send_program {Send Receive Material Value Context Output : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m] (interpret : Material → Value)
    (labels : QueryImpl (RawCtxChainSend.SendSpec Send Receive Material Context Output) m)
    (values : QueryImpl (RawCtxChainSend.SendSpec Send Receive Value Context Output) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, values (.inr (sendSeal interpret pending)) = labels (.inr pending))
    (start : RawCtxChainSend.Start Send Receive Material Context) :
    simulateQ values (RawCtxChainSend.program (sendStart interpret start)) =
      (fun result => (mapRefined interpret result.1, result.2)) <$>
        simulateQ labels (RawCtxChainSend.program start) := by
  cases start with
  | exhausted entry context =>
      simp only [sendStart, RawCtxChainSend.program, simulateQ_pure, map_pure]
  | requested pending =>
      simp only [sendStart, RawCtxChainSend.program, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, sendKdf, kdf, map_bind, map_pure]
      dsimp only [OracleSpec.Range, RawCtxChainSend.SendSpec,
        OracleSpec.add_def, Sum.elim_inl, OracleSpec.ofFn]
      rw [_root_.bind_map_left]
      refine bind_congr fun reply => ?_
      change (do
        let sealed ← values (.inr (RawCtxChainSend.ready (sendKdf interpret pending)
          (reply.1, interpret reply.2)))
        pure ((RawCtxChainSend.ready (sendKdf interpret pending) (reply.1, interpret reply.2)).advanced,
          sealed)) = _
      rw [send_ready, sealing]
      rfl

/-- Actual sending admission and its complete continuation commute with material interpretation in any lawful stateful monad. -/
theorem send_execute {Send Receive Material Value Context Output : Type}
    {m : Type → Type*} [Monad m] [LawfulMonad m] (interpret : Material → Value)
    (labels : QueryImpl (RawCtxChainSend.SendSpec Send Receive Material Context Output) m)
    (values : QueryImpl (RawCtxChainSend.SendSpec Send Receive Value Context Output) m)
    (kdf : ∀ request, values (.inl request) =
      (fun reply => (reply.1, interpret reply.2)) <$> labels (.inl request))
    (sealing : ∀ pending, values (.inr (sendSeal interpret pending)) = labels (.inr pending))
    (entry : RefinedRatchet Send Receive Material) (context : Context) :
    simulateQ values (RawCtxChainSend.execute (mapRefined interpret entry) context) =
      (fun result => (mapRefined interpret result.1, result.2)) <$>
        simulateQ labels (RawCtxChainSend.execute entry context) := by
  simpa only [RawCtxChainSend.execute, send_normalBegin] using
    send_program interpret labels values kdf sealing (RawCtxChainSend.normalBegin entry context)

end BeaconcryptCore.Computational.RawCtxChainMaterialMap

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_resume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_resume

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_begin

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_normalResume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_normalResume

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_normalBegin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_normalBegin

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_normalFinish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_normalFinish

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_rank

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_program

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.receive_execute

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_begin

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_normalBegin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_normalBegin

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_ready

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_program

/-- info: 'BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_execute' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxChainMaterialMap.send_execute

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftRealTable

/-! The recursive source driver threads a growing private table and the complete native primitive state. Coordinate erasure is evaluated at each actual callback and final poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable
open PqxdhFullSecretInputKdf
variable {Slot Context Plaintext PrimitiveState : Type}

abbrev Execution (Slot PrimitiveState : Type) := Table Slot × PrimitiveState
abbrev Effect (Slot Context : Type) := RawCtxChainReceive.Effect (Label Slot) (Label Slot) (Label Slot) Context
abbrev NativeOpening (Context : Type) :=
  RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial Context
abbrev Lookup (Slot PrimitiveState : Type) :=
  Label Slot → StateT (Execution Slot PrimitiveState) ProbComp FullOutput
abbrev Open (Context Plaintext PrimitiveState : Type) :=
  NativeOpening Context → StateT PrimitiveState ProbComp (core.option.Option Plaintext)

def References (table : Table Slot) (effect : Effect Slot Context) : Prop :=
  EffectAvailable table effect ∧ EffectPresent table effect

/-- Logical KDF replies advance only source coordinates; the native opening receives the complete currently erased pending state. -/
noncomputable def receive (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (effect : Effect Slot Context) :
    StateT (Execution Slot PrimitiveState) ProbComp (LabeledKernel Slot × core.option.Option Plaintext) :=
  fun state => match effect with
  | .rejected entry _ => pure ((entry, .None), state)
  | .openRequested pending => do
      let reply ← (opening (eraseOpening seeds state.1 pending)).run state.2
      pure (RawCtxChainReceive.normalFinish pending reply.1, (state.1, reply.2))
  | .kdfRequested pending => do
      let reply ← (lookup pending.request).run state
      (receive seeds lookup opening
        (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request))).run reply.2
termination_by RawCtxChainReceive.effectRank effect
decreasing_by exact RawCtxChainReceive.normalResume_rank _ _

/-- An operational lookup contract exposes complete support facts; it is discharged by actual callback interpreters. -/
def LookupPreserves (valid : Table Slot → Prop) (lookup : Lookup Slot PrimitiveState) : Prop :=
  ∀ coordinate state, valid state.1 → Available state.1 coordinate →
    ∀ result ∈ support ((lookup coordinate).run state),
      state.1 ≤ result.2.1 ∧ result.2.1 coordinate = some result.1 ∧ valid result.2.1

abbrev Kdf (PrimitiveState : Type) :=
  SymmetricRatchetKdfRequest → StateT PrimitiveState ProbComp FullOutput

noncomputable def receiveImpl (kdf : Kdf PrimitiveState) (opening : Open Context Plaintext PrimitiveState) :
    QueryImpl (RawCtxInterpretedReceive.ReceiveSpec RatchetMaterial Context Plaintext)
      (StateT PrimitiveState ProbComp)
  | .inl input => (fun value => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value)) <$> kdf input
  | .inr pending => opening pending

def eraseResult (seeds : Seeds Slot)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState) :=
  ((eraseKernel seeds result.2.1 result.1.1, result.1.2), result.2.2)

/-- Complete native state, reply and its evaluated distribution are preserved after dropping only the private table. -/
def LookupRealized (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (kdf : Kdf PrimitiveState) : Prop :=
  ∀ coordinate state, valid state.1 → Available state.1 coordinate →
    (fun result => (result.1, result.2.2)) <$> ((lookup coordinate).run state) =
      (kdf (PqxdhRecordLiftRealTable.request seeds state.1 coordinate)).run state.2

/-- Every source skip/target/rejection callback retains all live chain and cache references under the actual extended table. -/
theorem resume_references (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainReceive.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (refs : References before (.kdfRequested pending)) (value : FullOutput)
    (found : after pending.request = some value) :
    References after (RawCtxChainReceive.normalResume pending (advance pending.request 1, pending.request)) := by
  have available : PendingAvailable after pending :=
    ⟨⟨available_mono before after mono _ refs.1.1.1, available_mono before after mono _ refs.1.1.2⟩,
      available_mono before after mono _ refs.1.2⟩
  exact ⟨resume_available after pending available (successor_available after pending.request available.2 value found) _,
    resume_present after pending (slots_present_mono before after mono _ refs.2.1)
      (slots_present_mono before after mono _ refs.2.2) ⟨value, found⟩⟩

/-- The growing-table interpreter erases to the complete ordinary source receive execution, including arbitrary native poststate and optional plaintext. -/
theorem receive_erasure (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (kdf : Kdf PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState)
    (preserves : LookupPreserves valid lookup) (realized : LookupRealized seeds valid lookup kdf)
    (effect : Effect Slot Context) (state : Execution Slot PrimitiveState)
    (good : valid state.1) (refs : References state.1 effect) :
    eraseResult seeds <$> ((receive seeds lookup opening effect).run state) =
      (simulateQ (receiveImpl kdf opening)
        (RawCtxInterpretedReceive.program (eraseEffect seeds state.1 effect))).run state.2 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      simp only [StateT.run, receive, eraseEffect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect,
        RawCtxInterpretedReceive.program, simulateQ_pure, map_pure, eraseResult, eraseKernel]
      rfl
    | openRequested pending =>
      simp only [receive, eraseEffect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect,
        RawCtxInterpretedReceive.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, receiveImpl,
        StateT.run, map_bind, map_pure]
      change ((opening (eraseOpening seeds state.1 pending)).run state.2 >>= fun reply =>
        pure (eraseResult seeds (RawCtxChainReceive.normalFinish pending reply.1, state.1, reply.2))) =
        ((opening (eraseOpening seeds state.1 pending)).run state.2 >>= fun reply =>
          pure (RawCtxInterpretedReceive.normalFinish (eraseOpening seeds state.1 pending) reply.1, reply.2))
      apply bind_congr
      intro reply
      rw [finish_erasure]
      rfl
    | kdfRequested pending =>
      simp only [StateT.run, receive, eraseEffect, RawCtxChainReceive.nativeEffect, RawCtxInterpretedReceive.mapEffect,
        RawCtxInterpretedReceive.program, simulateQ_bind, simulateQ_spec_query, receiveImpl, map_bind]
      change _ = ((fun value => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value)) <$>
        kdf (PqxdhRecordLiftRealTable.request seeds state.1 pending.request) >>= fun reply =>
          simulateQ (receiveImpl kdf opening) (RawCtxInterpretedReceive.program
            (RawCtxInterpretedReceive.normalResume (erasePending seeds state.1 pending) reply))).run state.2
      rw [StateT.run_bind, StateT.run_map, bind_map_left,
        ← realized pending.request state good refs.1.2, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro reply supported
      have facts := preserves pending.request state good refs.1.2 reply supported
      rw [PqxdhRecordLiftRealTable.receive_store seeds state.1 reply.2.1 facts.1 pending refs reply.1 facts.2.1]
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ reply.2 facts.2.2 (resume_references state.1 reply.2.1 facts.1 pending refs reply.1 facts.2.1) rfl

/-- The real interpreter always evaluates its native KDF callback before recording the returned full76 bytes. -/
noncomputable def realLookup [DecidableEq Slot] (seeds : Seeds Slot) (kdf : Kdf PrimitiveState) :
    Lookup Slot PrimitiveState := fun coordinate state => do
  let reply ← (kdf (PqxdhRecordLiftRealTable.request seeds state.1 coordinate)).run state.2
  pure (reply.1, (state.1.cacheQuery coordinate reply.1, reply.2))

/-- Dropping the private annotation keeps the exact native response distribution and all caller state, including instrumentation. -/
theorem realLookup_realized [DecidableEq Slot] (seeds : Seeds Slot) (kdf : Kdf PrimitiveState)
    (valid : Table Slot → Prop) : LookupRealized seeds valid (realLookup seeds kdf) kdf := by
  intro coordinate state _ _
  simp [realLookup, StateT.run, bind_pure_comp, Functor.map_map]

/-- This is ordinary functional KDF correctness at the exact input/info; no key distribution or security event occurs in this property. -/
def KdfReal (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (kdf : Kdf PrimitiveState) : Prop :=
  ∀ input state result, result ∈ support ((kdf input).run state) →
    RawCtxKdfRequestTable.fullResponse result.1 = RawCtxSourceHkdf.response source.crypto input

def RealValid (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (table : Table Slot) : Prop :=
  Closed table ∧ PqxdhRecordLiftRealTable.Consistent source seeds table

/-- Literal real KDF execution discharges the callback preservation obligations from previously derived real table consistency. -/
theorem realLookup_preserves [DecidableEq Slot] (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (kdf : Kdf PrimitiveState) (correct : KdfReal source kdf) :
    LookupPreserves (RealValid source seeds) (realLookup seeds kdf) := by
  intro coordinate state good available result supported
  simp only [realLookup, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨reply, member, equal⟩ := supported
  have actual := correct (PqxdhRecordLiftRealTable.request seeds state.1 coordinate) state.2 reply member
  have value : reply.1 = PqxdhRecordLiftRealTable.output source seeds state.1 coordinate := by
    have mapped := congrArg PqxdhRecordLiftRealTable.fromResponse actual
    rw [← PqxdhRecordLiftRealTable.output_source, PqxdhRecordLiftRealTable.from_fullResponse,
      PqxdhRecordLiftRealTable.from_fullResponse] at mapped
    exact mapped
  subst result
  simp only [value]
  exact PqxdhRecordLiftRealTable.record_facts source seeds state.1 good.2 good.1 coordinate available

/-- The real invariant is initialized without a distribution or a related-key premise. -/
theorem realValid_empty (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot) :
    RealValid source seeds (∅ : Table Slot) :=
  ⟨closed_empty, PqxdhRecordLiftRealTable.consistent_empty source seeds⟩

/-- The actual source admission starts the complete growing-table receive simulation, covering rejected, cached and future targets. -/
theorem admitted_receive_erasure (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (kdf : Kdf PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState)
    (preserves : LookupPreserves valid lookup) (realized : LookupRealized seeds valid lookup kdf)
    (entry : LabeledKernel Slot) (target : Std.U64) (context : Context)
    (state : Execution Slot PrimitiveState) (good : valid state.1)
    (available : KernelAvailable state.1 entry) (present : SlotsPresent state.1 entry.receive_slots) :
    eraseResult seeds <$> ((receive seeds lookup opening
      (RawCtxChainReceive.normalBegin entry target context)).run state) =
      (simulateQ (receiveImpl kdf opening)
        (RawCtxInterpretedReceive.receive (eraseKernel seeds state.1 entry) target context)).run state.2 := by
  rw [RawCtxInterpretedReceive.receive, PqxdhRecordLiftMaterialTable.admission_erasure]
  exact receive_erasure seeds valid lookup kdf opening preserves realized _ state good
    ⟨begin_available state.1 entry available target context, begin_present state.1 entry present target context⟩

/-- With ordinary functional native KDF correctness, all lookup obligations are discharged for the full actual receive. -/
theorem real_receive_erasure [DecidableEq Slot] (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : Seeds Slot) (kdf : Kdf PrimitiveState) (correct : KdfReal source kdf)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot)
    (target : Std.U64) (context : Context) (state : Execution Slot PrimitiveState)
    (good : RealValid source seeds state.1) (available : KernelAvailable state.1 entry)
    (present : SlotsPresent state.1 entry.receive_slots) :
    eraseResult seeds <$> ((receive seeds (realLookup seeds kdf) opening
      (RawCtxChainReceive.normalBegin entry target context)).run state) =
      (simulateQ (receiveImpl kdf opening)
        (RawCtxInterpretedReceive.receive (eraseKernel seeds state.1 entry) target context)).run state.2 :=
  admitted_receive_erasure seeds (RealValid source seeds) _ kdf opening
    (realLookup_preserves source seeds kdf correct) (realLookup_realized seeds kdf _) entry target context
      state good available present

def KernelReferences (table : Table Slot) (kernel : LabeledKernel Slot) : Prop :=
  KernelAvailable table kernel ∧ SlotsPresent table kernel.receive_slots

/-- Actual publication or rollback leaves available chains and existing skipped material only. -/
theorem finish_references (table : Table Slot)
    (pending : RawCtxInterpretedOpening.Opening (Label Slot) (Label Slot) (Label Slot) Context)
    (target : Std.U64) (prepared : PqxdhFirstRecordReplay.Prepared pending.entry target pending.prepared)
    (refs : References table (.openRequested pending)) (reply : core.option.Option Plaintext) :
    KernelReferences table (RawCtxChainReceive.normalFinish pending reply).1 := by
  have slots : SlotsPresent table (RawCtxChainReceive.normalFinish pending reply).1.receive_slots :=
    finish_property (fun cached => Present table cached.material) pending target prepared refs.2.1
      (by cases shape : pending.prepared <;> simp_all [References, EffectPresent, SlotsPresent]) reply
  refine ⟨?_, slots⟩
  cases reply with
  | none => simpa only [PqxdhFirstRecordReplay.finish_none] using refs.1.1
  | some plaintext =>
      have run := RawCtxChainReceive.normalFinish_exact pending (.Some plaintext)
      generalize RawCtxChainReceive.normalFinish pending (.Some plaintext) = result at run ⊢
      cases shape : pending.prepared with
      | PreparedReceiveCachedCase cached =>
          rw [shape] at prepared
          obtain ⟨out, executed, _, send, recv, _⟩ := publish_cached_receive_exact pending.entry cached
            prepared.target_bound prepared.last_bound
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          cases run
          simpa only [KernelAvailable, send, recv] using refs.1.1
      | PreparedReceiveFutureCase future =>
          rw [shape] at prepared
          obtain ⟨_, first, _, _, capacity, cached⟩ := prepared
          have length := congrArg List.length cached
          simp only [control.cacheSeqs_length, List.length_append, List.length_map, List.length_range] at length
          have bounded : future.first_slot.val + future.skipped.val ≤ 50 := by
            simp only [control.RatchetState.Wf, control.SequenceCache.Wf] at capacity
            rw [first]
            omega
          obtain ⟨out, executed, _, send, recv, _⟩ := publish_future_receive_exact pending.entry future bounded
          simp only [RawCtxInterpretedOpening.finish, shape, executed, bind_tc_ok, RustM.ok.injEq] at run
          cases run
          exact ⟨send ▸ refs.1.1.1, recv ▸ (by simpa only [References, EffectAvailable, shape] using refs.1.2)⟩

/-- Every recursive lookup preserves its table invariant and all earlier entries; admitted publication leaves a reusable complete kernel. -/
theorem receive_preserves (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (opening : Open Context Plaintext PrimitiveState)
    (preserves : LookupPreserves valid lookup) (entry : LabeledKernel Slot) (target : Std.U64)
    (effect : Effect Slot Context) (admitted : PqxdhFirstRecordReplay.Admitted entry target effect)
    (state : Execution Slot PrimitiveState) (good : valid state.1) (refs : References state.1 effect)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    valid result.2.1 ∧ state.1 ≤ result.2.1 ∧ KernelReferences result.2.1 result.1.1 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
    cases effect with
    | rejected original context =>
      simp only [StateT.run, receive, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨good, le_rfl, refs⟩
    | openRequested pending =>
      simp only [StateT.run, receive, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _, equal⟩ := supported
      subst result
      exact ⟨good, le_rfl, finish_references state.1 pending target
        (by simpa only [admitted.1] using admitted.2) refs reply.1⟩
    | kdfRequested pending =>
      simp only [StateT.run, receive, mem_support_bind_iff] at supported
      obtain ⟨reply, member, continued⟩ := supported
      have facts := preserves pending.request state good refs.1.2 reply member
      have later := ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ (PqxdhFirstRecordReplay.resume_admitted entry target pending (advance pending.request 1, pending.request) admitted)
        reply.2 facts.2.2 (resume_references state.1 reply.2.1 facts.1 pending refs reply.1 facts.2.1)
        result continued rfl
      exact ⟨later.1, le_trans facts.1 later.2.1, later.2.2⟩

/-- The private growing-table interpreter reaches only results of the original source program with its actual typed replies. -/
theorem receive_source_support (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (effect : Effect Slot Context)
    (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    result.1 ∈ support (RawCtxPendingReceiveQueries.program effect) := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
      simp only [StateT.run, receive, support_pure, Set.mem_singleton_iff] at supported
      subst result
      simp [RawCtxPendingReceiveQueries.program]
    | openRequested pending =>
      simp only [StateT.run, receive, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _, equal⟩ := supported
      subst result
      rw [RawCtxPendingReceiveQueries.program]
      simp only [mem_support_bind_iff]
      exact ⟨reply.1, mem_support_query _ _, by simp⟩
    | kdfRequested pending =>
      simp only [StateT.run, receive, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      rw [RawCtxPendingReceiveQueries.program]
      simp only [mem_support_bind_iff]
      exact ⟨(advance pending.request 1, pending.request), mem_support_query _ _,
        ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
          _ reply.2 result continued rfl⟩

/-- The existing source control theorem transfers to the actual growing-table driver, including whole-entry rejection and permanent target consumption on acceptance. -/
theorem receive_control (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open Context Plaintext PrimitiveState) (entry : LabeledKernel Slot) (target : Std.U64)
    (controlValid : control.ValidControl entry.control) (effect : Effect Slot Context)
    (admitted : PqxdhFirstRecordReplay.Admitted entry target effect)
    (state : Execution Slot PrimitiveState)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening effect).run state)) :
    (result.1.2 = .None → result.1.1 = entry) ∧
      ∀ value, result.1.2 = .Some value → control.ValidControl result.1.1.control ∧
        PqxdhFirstRecordReplay.Consumed result.1.1.control target.val ∧
        ∀ position, PqxdhFirstRecordReplay.Consumed entry.control position →
          PqxdhFirstRecordReplay.Consumed result.1.1.control position :=
  PqxdhFirstRecordReplay.program_result entry target controlValid effect admitted result.1
    (receive_source_support seeds lookup opening effect state result supported)

/-- All accepted source receive targets start a preservation proof from the actual kernel, without a selected-trace premise. -/
theorem admitted_receive_preserves (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (opening : Open Context Plaintext PrimitiveState)
    (preserves : LookupPreserves valid lookup) (entry : LabeledKernel Slot) (target : Std.U64) (context : Context)
    (capacity : entry.control.Wf) (state : Execution Slot PrimitiveState) (good : valid state.1)
    (refs : KernelReferences state.1 entry)
    (result : (LabeledKernel Slot × core.option.Option Plaintext) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((receive seeds lookup opening
      (RawCtxChainReceive.normalBegin entry target context)).run state)) :
    valid result.2.1 ∧ state.1 ≤ result.2.1 ∧ KernelReferences result.2.1 result.1.1 :=
  receive_preserves seeds valid lookup opening preserves entry target _
    (PqxdhFirstRecordReplay.begin_admitted entry target context capacity) state good
    ⟨begin_available state.1 entry refs.1 target context, begin_present state.1 entry refs.2 target context⟩
    result supported

abbrev Seal (Context Output PrimitiveState : Type) :=
  RawCtxInterpretedSend.Seal RatchetMaterial Context → StateT PrimitiveState ProbComp (Option Output)
abbrev Start (Slot Context : Type) := RawCtxChainSend.Start (Label Slot) (Label Slot) (Label Slot) Context

def SendReferences (table : Table Slot) : Start Slot Context → Prop
  | .exhausted entry _ => KernelReferences table entry
  | .requested pending => SendAvailable table pending ∧ SlotsPresent table pending.entry.receive_slots

/-- Actual send advancement precedes native sealing, and a failed seal keeps that advanced source kernel. -/
noncomputable def send {Output : Type} (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (sealing : Seal Context Output PrimitiveState) (start : Start Slot Context) :
    StateT (Execution Slot PrimitiveState) ProbComp (LabeledKernel Slot × Option Output) := fun state =>
  match start with
  | .exhausted entry _ => pure ((entry, none), state)
  | .requested pending => do
      let reply ← (lookup pending.request).run state
      let ready := RawCtxChainSend.ready pending (advance pending.request 1, pending.request)
      let sealed ← (sealing (eraseSeal seeds reply.2.1 ready)).run reply.2.2
      pure ((ready.advanced, sealed.1), (reply.2.1, sealed.2))

noncomputable def sendImpl {Output : Type} (kdf : Kdf PrimitiveState) (sealing : Seal Context Output PrimitiveState) :
    QueryImpl (RawCtxInterpretedSend.SendSpec RatchetMaterial Context Output)
      (StateT PrimitiveState ProbComp)
  | .inl input => (fun value => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value)) <$> kdf input
  | .inr pending => sealing pending

def eraseSendResult {Output : Type} (seeds : Seeds Slot)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState) :=
  ((eraseKernel seeds result.2.1 result.1.1, result.1.2), result.2.2)

/-- The actual ready-to-seal payload is interpreted with the full stored reply and the final table. -/
theorem send_ready (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainSend.Kdf (Label Slot) (Label Slot) (Label Slot) Context)
    (refs : SendReferences before (.requested pending)) (value : FullOutput)
    (found : after pending.request = some value) :
    RawCtxInterpretedSend.ready (eraseSendPending seeds before pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value)) =
      eraseSeal seeds after (RawCtxChainSend.ready pending (advance pending.request 1, pending.request)) := by
  apply RustM.ok.inj
  rw [← RawCtxInterpretedSend.ready_exact]
  exact PqxdhRecordLiftRealTable.send_store seeds before after mono pending refs.1 refs.2 value found

/-- Complete send execution erases at the final table, retaining the native seal/writer reply and every primitive state field. -/
theorem send_erasure {Output : Type} (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (kdf : Kdf PrimitiveState)
    (sealing : Seal Context Output PrimitiveState)
    (preserves : LookupPreserves valid lookup) (realized : LookupRealized seeds valid lookup kdf)
    (start : Start Slot Context) (state : Execution Slot PrimitiveState)
    (good : valid state.1) (refs : SendReferences state.1 start) :
    eraseSendResult seeds <$> ((send seeds lookup sealing start).run state) =
      (simulateQ (sendImpl kdf sealing)
        (RawCtxInterpretedSend.program (eraseStart seeds state.1 start))).run state.2 := by
  cases start with
  | exhausted entry context =>
      simp only [StateT.run, send, eraseStart, RawCtxChainSend.nativeStart, RawCtxInterpretedSend.mapStart,
        RawCtxInterpretedSend.program, simulateQ_pure, map_pure, eraseSendResult, eraseKernel]
      rfl
  | requested pending =>
      simp only [StateT.run, send, eraseStart, RawCtxChainSend.nativeStart, RawCtxInterpretedSend.mapStart,
        RawCtxInterpretedSend.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, sendImpl,
        map_bind, map_pure]
      change _ = ((fun value => RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse value)) <$>
        kdf (PqxdhRecordLiftRealTable.request seeds state.1 pending.request) >>= fun reply => do
          let sealed ← sealing (RawCtxInterpretedSend.ready (eraseSendPending seeds state.1 pending) reply)
          pure ((RawCtxInterpretedSend.ready (eraseSendPending seeds state.1 pending) reply).advanced, sealed)).run state.2
      rw [StateT.run_bind, StateT.run_map, bind_map_left,
        ← realized pending.request state good refs.1.2, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro reply supported
      have facts := preserves pending.request state good refs.1.2 reply supported
      rw [send_ready seeds state.1 reply.2.1 facts.1 pending refs reply.1 facts.2.1, StateT.run_bind]
      apply bind_congr
      intro sealed
      rfl

/-- Actual send admission obtains its request and every retained cache entry from the same available entry kernel. -/
theorem send_begin_references (table : Table Slot) (entry : LabeledKernel Slot)
    (refs : KernelReferences table entry) (context : Context) :
    SendReferences table (RawCtxChainSend.normalBegin entry context) := by
  have tracked := send_begin_tracked entry context
  have available := send_begin_available table entry refs.1 context
  cases shape : RawCtxChainSend.normalBegin entry context <;>
    simp_all [SendReferences, KernelReferences, StartAvailable, SendTracked]

/-- A send retains valid private tables and all live source references even when its actual native seal returns failure. -/
theorem send_preserves {Output : Type} (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (sealing : Seal Context Output PrimitiveState)
    (preserves : LookupPreserves valid lookup) (start : Start Slot Context)
    (state : Execution Slot PrimitiveState) (good : valid state.1) (refs : SendReferences state.1 start)
    (result : (LabeledKernel Slot × Option Output) × Execution Slot PrimitiveState)
    (supported : result ∈ support ((send seeds lookup sealing start).run state)) :
    valid result.2.1 ∧ state.1 ≤ result.2.1 ∧ KernelReferences result.2.1 result.1.1 := by
  cases start with
  | exhausted entry context =>
      simp only [StateT.run, send, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨good, le_rfl, refs⟩
  | requested pending =>
      simp only [StateT.run, send, mem_support_bind_iff] at supported
      obtain ⟨reply, member, sealed, _, equal⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at equal
      subst result
      have facts := preserves pending.request state good refs.1.2 reply member
      exact ⟨facts.2.2, facts.1,
        ⟨successor_available reply.2.1 pending.request
          (available_mono state.1 reply.2.1 facts.1 _ refs.1.2) reply.1 facts.2.1,
          available_mono state.1 reply.2.1 facts.1 _ refs.1.1.2⟩,
        slots_present_mono state.1 reply.2.1 facts.1 _ refs.2⟩

/-- Actual send admission and every source seal response preserve the entire native result distribution. -/
theorem admitted_send_erasure {Output : Type} (seeds : Seeds Slot) (valid : Table Slot → Prop)
    (lookup : Lookup Slot PrimitiveState) (kdf : Kdf PrimitiveState)
    (sealing : Seal Context Output PrimitiveState)
    (preserves : LookupPreserves valid lookup) (realized : LookupRealized seeds valid lookup kdf)
    (entry : LabeledKernel Slot) (context : Context) (state : Execution Slot PrimitiveState)
    (good : valid state.1) (refs : KernelReferences state.1 entry) :
    eraseSendResult seeds <$> ((send seeds lookup sealing (RawCtxChainSend.normalBegin entry context)).run state) =
      (simulateQ (sendImpl kdf sealing)
        (RawCtxInterpretedSend.send (eraseKernel seeds state.1 entry) context)).run state.2 := by
  rw [RawCtxInterpretedSend.send, PqxdhRecordLiftMaterialTable.send_admission_erasure]
  exact send_erasure seeds valid lookup kdf sealing preserves realized _ state good
    (send_begin_references state.1 entry refs context)

/-- Literal native source KDF calls discharge every lookup realization premise for the complete actual send. -/
theorem real_send_erasure [DecidableEq Slot] {Output : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (seeds : Seeds Slot)
    (kdf : Kdf PrimitiveState) (correct : KdfReal source kdf) (sealing : Seal Context Output PrimitiveState)
    (entry : LabeledKernel Slot) (context : Context) (state : Execution Slot PrimitiveState)
    (good : RealValid source seeds state.1) (refs : KernelReferences state.1 entry) :
    eraseSendResult seeds <$> ((send seeds (realLookup seeds kdf) sealing (RawCtxChainSend.normalBegin entry context)).run state) =
      (simulateQ (sendImpl kdf sealing)
        (RawCtxInterpretedSend.send (eraseKernel seeds state.1 entry) context)).run state.2 :=
  admitted_send_erasure seeds (RealValid source seeds) _ kdf sealing
    (realLookup_preserves source seeds kdf correct) (realLookup_realized seeds kdf _) entry context state good refs

end BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.resume_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.resume_references
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.realLookup_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.realLookup_realized
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.realLookup_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.realLookup_preserves
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.realValid_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.realValid_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.admitted_receive_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.admitted_receive_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.real_receive_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.real_receive_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.finish_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.finish_references
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_preserves
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_source_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.receive_control
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.admitted_receive_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.admitted_receive_preserves
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_ready
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_begin_references' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_begin_references
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.send_preserves
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.admitted_send_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.admitted_send_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.real_send_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler.real_send_erasure

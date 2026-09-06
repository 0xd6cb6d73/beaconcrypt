import BeaconcryptCore.Computational.RawCtxSourceOpen
import BeaconcryptCore.Refinement.RatchetStructuralSend

/-!
This module interprets the extracted send phases and the thin established-owner send driver. Exact totality results justify analysis-only begin/resume normalizers. Every nonexhausted send requests the actual old chain and fixed KDF label once, resumes the actual 76-byte response, invokes one selected sealing capability, and publishes the advanced source kernel with its actual optional result. In particular, sealing failure consumes the allocated send step; it does not roll back like receive failure. Empty application input and counter exhaustion invoke neither callback. Complete primitive state is retained separately from the whole owner.

The private frame executor receives the exact source material, sequence and immutable context, including the application plaintext. The returned API value uses the target handle; the distinct sender handle remains in the sealing context. This is a private source callback, not an adversarial key/material interface or a new security assumption. Native role lookup must supply the sender, target and 153-byte associated data, and the AEAD/commitment/frame-writer executor still needs its own argument/refinement contracts and internal query ledger. No callback work is declared free.

The adaptive client here chooses plaintext requests and stopping through a send-only interface. It shares one complete owner, retains actual frame bytes and metadata, and charges KDF and frame callbacks separately by qSend. Interleaved receives, raw network/reveal actions, multiple owners, copied or restored states, runtime slot/CAS/physical-erasure behavior and global computational-symbolic reductions remain separate obligations. Arbitrary stateful probabilistic callback support is preserved without fixed-reply, key-independence, honest-target, freshness or losslessness premises. The functional driver equality does not prove native compiler, allocation, timing or primitive implementation behavior.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxSourceSend

noncomputable def beginSend {Context : Type} (kernel : ConcreteRatchetKernel)
    (context : Context) : SendStart Context :=
  (begin_send_total kernel context).choose

theorem beginSend_exact {Context : Type} (kernel : ConcreteRatchetKernel)
    (context : Context) : begin_send kernel context = ok (beginSend kernel context) :=
  (begin_send_total kernel context).choose_spec

noncomputable def resumeSend {Context : Type} (pending : SendKdf Context)
    (response : RatchetKdfResponse) : SendSeal Context :=
  (pending.resume_total response).choose

theorem resumeSend_exact {Context : Type} (pending : SendKdf Context)
    (response : RatchetKdfResponse) : pending.resume response = ok (resumeSend pending response) :=
  (pending.resume_total response).choose_spec

abbrev SendSpec (Context Output : Type) :=
  (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) +
    (SendSeal Context →ₒ Option Output)

noncomputable def program {Context Output : Type} (start : SendStart Context) :
    OracleComp (SendSpec Context Output) (ConcreteRatchetKernel × Option Output) :=
  match start with
  | .SendExhausted entry _ => pure (entry, none)
  | .SendKdfRequested pending => do
      let response ← (SendSpec Context Output).query (.inl pending.request)
      let ready := resumeSend pending response
      let reply ← (SendSpec Context Output).query (.inr ready)
      pure (ready.advanced, reply)

noncomputable def send {Context Output : Type} (kernel : ConcreteRatchetKernel)
    (context : Context) : OracleComp (SendSpec Context Output)
      (ConcreteRatchetKernel × Option Output) := program (beginSend kernel context)

/-- Both source callbacks retain their actual next state, even when sealing fails. -/
theorem requested_support {Context Output PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (SendSpec Context Output) (StateT PrimitiveState (OracleComp base)))
    (pending : SendKdf Context) (primitive : PrimitiveState)
    (result : (ConcreteRatchetKernel × Option Output) × PrimitiveState)
    (hsupport : result ∈ support
      ((simulateQ impl (program (.SendKdfRequested pending))).run primitive)) :
    ∃ response afterKdf reply afterSeal,
      (response, afterKdf) ∈ support ((impl (.inl pending.request)).run primitive) ∧
      (reply, afterSeal) ∈ support ((impl (.inr (resumeSend pending response))).run afterKdf) ∧
      result = (((resumeSend pending response).advanced, reply), afterSeal) := by
  simp only [program, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hsupport
  obtain ⟨⟨response, afterKdf⟩, hkdf, ⟨reply, afterSeal⟩, hopen, hresult⟩ := hsupport
  exact ⟨response, afterKdf, reply, afterSeal, hkdf, hopen, hresult⟩

/-- The actual 76-byte source response determines all continuation fields together. -/
theorem resumeSend_fields {Context : Type} (pending : SendKdf Context)
    (response : RatchetKdfResponse) :
    ∃ stepped, ratchet_step_from_response response = ok stepped ∧
      resumeSend pending response = {
        advanced := { refined := { pending.entry.refined with
          control := pending.committed_control, send_chain := stepped.chain } },
        context := pending.context, logical := pending.logical,
        sequence := pending.sequence, material := stepped.material } := by
  obtain ⟨stepped, hstep⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
  exact ⟨stepped, hstep, RustM.ok.inj
    ((resumeSend_exact pending response).symm.trans (pending.resume_exact response stepped hstep))⟩

/-- Exhaustion returns without invoking either private callback. -/
theorem send_exhausted {Context Output : Type} (kernel : ConcreteRatchetKernel)
    (context : Context) (hmax : kernel.refined.control.send_sequence = core.num.U64.MAX) :
    send (Output := Output) kernel context = pure (kernel, none) := by
  have hbegin := RustM.ok.inj ((beginSend_exact kernel context).symm.trans
    (begin_send_exhausted_restores_entry kernel context hmax))
  simp only [send, hbegin, program]

/-- Source admission pins the exact old chain, next counter and all retained receive state. -/
theorem beginSend_fields {Context : Type} (kernel : ConcreteRatchetKernel)
    (context : Context) (hmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX) :
    ∃ pending, beginSend kernel context = .SendKdfRequested pending ∧
      pending.entry = kernel ∧ pending.context = context ∧
      pending.request.input = kernel.refined.send_chain.bytes ∧
      pending.request.info = SYM_RATCHET_INFO ∧
      pending.sequence = pending.committed_control.send_sequence ∧
      pending.sequence.val = kernel.refined.control.send_sequence.val + 1 ∧
      pending.committed_control.receive_sequence = kernel.refined.control.receive_sequence ∧
      pending.committed_control.receive_cache = kernel.refined.control.receive_cache := by
  obtain ⟨advanced, hadvance, hsend, hreceive, hcache, hsequence, hkey⟩ :=
    control.advance_send_ok kernel.refined.control hmax
  let pending : SendKdf Context := {
    entry := kernel, context, committed_control := advanced.state, logical := advanced.key,
    sequence := advanced.state.send_sequence,
    request := { input := kernel.refined.send_chain.bytes, info := SYM_RATCHET_INFO } }
  refine ⟨pending, ?_, rfl, rfl, rfl, rfl, rfl, hsend, hreceive, hcache⟩
  apply RustM.ok.inj
  rw [← beginSend_exact]
  simp [begin_send, hadvance, hsequence, hkey, control.SendKey.impl.sequence,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq, core.U64.Insts.CoreCmpPartialEqU64,
    control.RatchetState.impl.send_sequence, RatchetChain.as_bytes,
    SymmetricRatchetKdfRequest.new, pending]

/-- Every supported nonexhausted send advances once, preserving receive state even if its option is None. -/
theorem send_nonexhausted_support {Context Output PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (SendSpec Context Output) (StateT PrimitiveState (OracleComp base)))
    (kernel : ConcreteRatchetKernel) (context : Context) (primitive : PrimitiveState)
    (hmax : kernel.refined.control.send_sequence ≠ core.num.U64.MAX)
    (result : (ConcreteRatchetKernel × Option Output) × PrimitiveState)
    (hsupport : result ∈ support ((simulateQ impl (send kernel context)).run primitive)) :
    ∃ pending response afterKdf,
      pending.entry = kernel ∧ pending.context = context ∧
      pending.request.input = kernel.refined.send_chain.bytes ∧
      pending.request.info = SYM_RATCHET_INFO ∧
      (response, afterKdf) ∈ support ((impl (.inl pending.request)).run primitive) ∧
      (result.1.2, result.2) ∈ support ((impl (.inr (resumeSend pending response))).run afterKdf) ∧
      result.1.1 = (resumeSend pending response).advanced ∧
      result.1.1.refined.control.send_sequence.val = kernel.refined.control.send_sequence.val + 1 ∧
      result.1.1.refined.control.receive_sequence = kernel.refined.control.receive_sequence ∧
      result.1.1.refined.control.receive_cache = kernel.refined.control.receive_cache ∧
      result.1.1.refined.receive_chain = kernel.refined.receive_chain ∧
      result.1.1.refined.receive_slots = kernel.refined.receive_slots := by
  obtain ⟨pending, hbegin, hentry, hcontext, hinput, hinfo, hsequence, hnext, hreceive, hcache⟩ :=
    beginSend_fields kernel context hmax
  rw [send, hbegin] at hsupport
  obtain ⟨response, afterKdf, reply, afterSeal, hkdf, hseal, rfl⟩ :=
    requested_support impl pending primitive result hsupport
  refine ⟨pending, response, afterKdf, hentry, hcontext, hinput, hinfo, hkdf, hseal, rfl, ?_⟩
  obtain ⟨stepped, _, hready⟩ := resumeSend_fields pending response
  simp only [hready, hentry, ← hsequence, hnext, hreceive, hcache, and_self]

/-- One send makes at most one actual KDF request, including all reply branches. -/
theorem program_kdf_bound {Context Output : Type} (start : SendStart Context) :
    (program (Output := Output) start).IsQueryBoundP
      (fun request => request.isLeft = true) 1 := by
  cases start with
  | SendExhausted => simp [program]
  | SendKdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      refine ⟨by simp, fun response => ?_⟩
      rw [isQueryBoundP_query_bind_iff]
      simp

/-- One send invokes at most one actual sealing capability. -/
theorem program_seal_bound {Context Output : Type} (start : SendStart Context) :
    (program (Output := Output) start).IsQueryBoundP
      (fun request => request.isRight = true) 1 := by
  cases start with
  | SendExhausted => simp [program]
  | SendKdfRequested pending =>
      rw [program, isQueryBoundP_query_bind_iff]
      refine ⟨by simp, fun response => ?_⟩
      rw [isQueryBoundP_query_bind_iff]
      simp

def deterministicImpl {Context Output PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → SendSeal Context → Option Output × PrimitiveState) :
    QueryImpl (SendSpec Context Output) (StateM PrimitiveState)
  | .inl request => fun state => execute state request
  | .inr pending => fun state => sealReply state pending

/-- The direct source driver retains all callback state and actually invokes the extracted finish. -/
def sourceDriver {Context Output PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → SendSeal Context → Option Output × PrimitiveState)
    (kernel : ConcreteRatchetKernel) (context : Context) (primitive : PrimitiveState) :
    RustM ((ConcreteRatchetKernel × Option Output) × PrimitiveState) := do
  let start ← begin_send kernel context
  match start with
  | .SendExhausted entry _ => ok ((entry, none), primitive)
  | .SendKdfRequested pending =>
      let (response, afterKdf) := execute primitive pending.request
      let ready ← pending.resume response
      let (reply, afterSeal) := sealReply afterKdf ready
      let result ← ready.finish reply
      ok (result, afterSeal)

/-- State-dependent functional interpretation equals the actual extracted source driver, including finish. -/
theorem sourceDriver_exact {Context Output PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → SendSeal Context → Option Output × PrimitiveState)
    (kernel : ConcreteRatchetKernel) (context : Context) (primitive : PrimitiveState) :
    sourceDriver execute sealReply kernel context primitive =
      ok ((simulateQ (deterministicImpl execute sealReply) (send kernel context)).run primitive) := by
  rw [sourceDriver, beginSend_exact]
  cases hstart : beginSend kernel context <;> simp only [bind_tc_ok, send, hstart, program]
  all_goals simp only [resumeSend_exact, SendSeal.finish_returns_interpreter_result,
    bind_tc_ok, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, deterministicImpl]
  all_goals rfl

/-- Borrowed source sealing fields distinguish the returned target handle from the encoded sender. -/
structure SealContext where
  plaintext : Pqxdh.Bytes
  targetId : Std.U64
  senderId : Std.U64
  associatedData : Pqxdh.Bytes

structure SealInput where
  material : RatchetMaterial
  sequence : Std.U64
  context : SealContext

structure Encrypted where
  ciphertext : Pqxdh.Bytes
  keyId : Std.U64
  sequence : Std.U64

/-- The private frame executor receives only the actual material, sequence and immutable source context. -/
abbrev PrimitiveSpec :=
  (SymmetricRatchetKdfRequest →ₒ RatchetKdfResponse) + (SealInput →ₒ Option Pqxdh.Bytes)

def arguments (pending : SendSeal SealContext) : SealInput :=
  ⟨pending.material, pending.sequence, pending.context⟩

def encrypted (input : SealInput) (ciphertext : Pqxdh.Bytes) : Encrypted :=
  ⟨ciphertext, input.context.targetId, input.sequence⟩

/-- Construct the real optional API value before the source finish, without altering frame bytes. -/
def adapter : QueryImpl (SendSpec SealContext Encrypted) (OracleComp PrimitiveSpec)
  | .inl request => liftM (PrimitiveSpec.query (.inl request))
  | .inr pending => do
      let ciphertext ← PrimitiveSpec.query (.inr (arguments pending))
      pure (ciphertext.map (encrypted (arguments pending)))

/-- Every private argument is the exact value of the extracted source getter. -/
theorem arguments_exact (pending : SendSeal SealContext) :
    SendSeal.impl.material pending = ok (arguments pending).material ∧
      SendSeal.impl.sequence pending = ok (arguments pending).sequence ∧
      SendSeal.impl.context pending = ok (arguments pending).context := by
  exact ⟨rfl, rfl, rfl⟩

/-- The API exposes the target route, while the sealing context separately retains the sender route. -/
theorem encrypted_fields (input : SealInput) (ciphertext : Pqxdh.Bytes) :
    (encrypted input ciphertext).ciphertext = ciphertext ∧
      (encrypted input ciphertext).keyId = input.context.targetId ∧
      (encrypted input ciphertext).sequence = input.sequence := by
  exact ⟨rfl, rfl, rfl⟩

/-- One whole established owner serializes sends; the complete receive state stays in the same kernel. -/
noncomputable def sendOwner {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes) :
    StateT (RawCtxWholeOwner.OwnerState Metadata) (OracleComp PrimitiveSpec) (Option Encrypted) :=
  fun state => if plaintext.isEmpty then pure (none, state) else do
    let context : SealContext :=
      ⟨plaintext, state.owner.expectedSender, senderId, state.owner.associatedData⟩
    let result ← simulateQ adapter (send state.owner.kernel context)
    pure (result.2, { state with owner := { state.owner with kernel := result.1 } })

noncomputable def sendGame {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    OracleComp base ((Option Encrypted × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState) :=
  (simulateQ impl ((sendOwner senderId plaintext).run state)).run primitive

/-- Empty application input rejects before state take, KDF or sealing. -/
theorem sendOwner_empty {Metadata : Type} (senderId : Std.U64)
    (state : RawCtxWholeOwner.OwnerState Metadata) :
    (sendOwner senderId []).run state = pure (none, state) := by
  rfl

/-- Every returned send value preserves the raw-attempt count and immutable owner metadata. -/
theorem sendGame_publication {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (result : (Option Encrypted × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext state primitive)) :
    result.1.2.rawAttempts = state.rawAttempts ∧
      result.1.2.owner.expectedSender = state.owner.expectedSender ∧
      result.1.2.owner.associatedData = state.owner.associatedData ∧
      result.1.2.owner.metadata = state.owner.metadata := by
  unfold sendGame sendOwner StateT.run at hsupport
  split at hsupport
  all_goals change result ∈ support ((simulateQ impl _).run primitive) at hsupport
  all_goals simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsupport
  · simp only [hsupport, and_self]
  · obtain ⟨_, _, rfl⟩ := hsupport
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- The adapter preserves either private query category without treating the frame executor's work as free. -/
theorem adapter_bound {α : Type} (p : Bool → Prop) [DecidablePred p]
    (source : OracleComp (SendSpec SealContext Encrypted) α) (bound : Nat)
    (hbound : source.IsQueryBoundP (fun query => p query.isLeft) bound) :
    (simulateQ adapter source).IsQueryBoundP (fun query => p query.isLeft) bound := by
  apply RawCtxSourceOpen.simulate_bound adapter _ _ source bound hbound
  intro query
  cases query
  · rename_i request
    exact (isQueryBoundP_query_iff (spec := PrimitiveSpec)
      (p := fun query => p query.isLeft) (.inl request) _).2 (by split_ifs <;> simp_all)
  · rename_i pending
    rw [adapter, isQueryBoundP_query_bind_iff]
    by_cases hp : p false <;> simp [hp]

/-- Both selected private interfaces inherit the source's one-call cap. -/
theorem selected_bounds (kernel : ConcreteRatchetKernel) (context : SealContext) :
    (simulateQ adapter (send kernel context)).IsQueryBoundP (fun query => query.isLeft = true) 1 ∧
      (simulateQ adapter (send kernel context)).IsQueryBoundP (fun query => query.isLeft = false) 1 := by
  refine ⟨adapter_bound (· = true) _ 1 (program_kdf_bound (beginSend kernel context)), ?_⟩
  apply adapter_bound (· = false)
  have hpred : (fun query : (SendSpec SealContext Encrypted).Domain => query.isLeft = false) =
      (fun query => query.isRight = true) := funext (fun query => by cases query <;> simp)
  simpa only [send, hpred] using program_seal_bound (Output := Encrypted) (beginSend kernel context)

/-- Empty input, exhaustion, and both seal outcomes are all covered by the per-owner private-call caps. -/
theorem sendOwner_bound {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (category : Bool) :
    ((sendOwner senderId plaintext).run state).IsQueryBoundP
      (fun query => query.isLeft = category) 1 := by
  unfold sendOwner StateT.run
  split
  · simp
  · simp only [bind_pure_comp, isQueryBoundP_map_iff]
    cases category with
    | false => exact (selected_bounds _ _).2
    | true => exact (selected_bounds _ _).1

/-- The application chooses plaintext and stopping; owner routing and primitive capabilities stay private. -/
abbrev ApplicationSpec := Pqxdh.Bytes →ₒ Option Encrypted

noncomputable def applicationImpl {Metadata : Type} (senderId : Std.U64) :
    QueryImpl ApplicationSpec (StateT (RawCtxWholeOwner.OwnerState Metadata) (OracleComp PrimitiveSpec)) :=
  fun plaintext => sendOwner senderId plaintext

/-- Adaptive send-only schedules charge each KDF and frame executor invocation to an application request. -/
theorem application_bounds {Metadata Result : Type} (senderId : Std.U64)
    (client : OracleComp ApplicationSpec Result) (qSend : Nat)
    (hbound : client.IsTotalQueryBound qSend) (state : RawCtxWholeOwner.OwnerState Metadata)
    (category : Bool) :
    ((simulateQ (applicationImpl senderId) client).run state).IsQueryBoundP
      (fun query => query.isLeft = category) qSend := by
  have hb : client.IsQueryBoundP (fun _ => True) qSend := hbound.isQueryBoundP
  exact hb.simulateQ_run_StateT_of_step
    (fun plaintext owner => sendOwner_bound senderId plaintext owner category) state

noncomputable def ownerImpl {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) :
    QueryImpl ApplicationSpec (StateT (RawCtxWholeOwner.OwnerState Metadata × PrimitiveState)
      (OracleComp base)) := fun plaintext state => do
  let result ← sendGame impl senderId plaintext state.1 state.2
  pure (result.1.1, result.1.2, result.2)

/-- Flattening private primitive state preserves exact owner publication and every callback effect. -/
theorem application_interpretation {Metadata PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) :
    (impl.mapStateTBase (applicationImpl (Metadata := Metadata) senderId)).flattenStateT =
      ownerImpl impl senderId := by
  funext plaintext state
  simp only [QueryImpl.flattenStateT, QueryImpl.mapStateTBase, applicationImpl, ownerImpl,
    sendGame, StateT.run, StateT.mk, bind_pure_comp]

/-- The counted adaptive program and complete owner/primitive-state game are exactly equal. -/
theorem application_schedule_interpretation {Metadata PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (client : OracleComp ApplicationSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState) :
    (simulateQ impl ((simulateQ (applicationImpl senderId) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (ownerImpl impl senderId) client).run (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, application_interpretation]

/-- An active owner send consumes the next send step on every returned option and retains all receive data. -/
theorem sendGame_active_state {Metadata PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl PrimitiveSpec (StateT PrimitiveState (OracleComp base)))
    (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (state : RawCtxWholeOwner.OwnerState Metadata) (primitive : PrimitiveState)
    (hnonempty : plaintext.isEmpty = false)
    (hmax : state.owner.kernel.refined.control.send_sequence ≠ core.num.U64.MAX)
    (result : (Option Encrypted × RawCtxWholeOwner.OwnerState Metadata) × PrimitiveState)
    (hsupport : result ∈ support (sendGame impl senderId plaintext state primitive)) :
    result.1.2.owner.kernel.refined.control.send_sequence.val =
        state.owner.kernel.refined.control.send_sequence.val + 1 ∧
      result.1.2.owner.kernel.refined.control.receive_sequence =
        state.owner.kernel.refined.control.receive_sequence ∧
      result.1.2.owner.kernel.refined.control.receive_cache =
        state.owner.kernel.refined.control.receive_cache ∧
      result.1.2.owner.kernel.refined.receive_chain = state.owner.kernel.refined.receive_chain ∧
      result.1.2.owner.kernel.refined.receive_slots = state.owner.kernel.refined.receive_slots := by
  unfold sendGame sendOwner at hsupport
  simp only [hnonempty, Bool.false_eq_true, ↓reduceIte] at hsupport
  unfold StateT.run at hsupport
  change result ∈ support ((simulateQ impl _).run primitive) at hsupport
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsupport
  obtain ⟨sent, hsent, rfl⟩ := hsupport
  rw [← QueryImpl.simulateQ_compose] at hsent
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hstate⟩ :=
    send_nonexhausted_support (impl ∘ₛ adapter) state.owner.kernel _ primitive hmax sent hsent
  exact hstate

end BeaconcryptCore.Computational.RawCtxSourceSend

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.beginSend_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.beginSend_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.resumeSend_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.resumeSend_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.requested_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.requested_support

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.resumeSend_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.resumeSend_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.send_exhausted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.send_exhausted

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.beginSend_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.beginSend_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.send_nonexhausted_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.send_nonexhausted_support

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.program_kdf_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.program_kdf_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.program_seal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.program_seal_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.sourceDriver_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.sourceDriver_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.arguments_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.arguments_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.encrypted_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.encrypted_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.sendOwner_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.sendOwner_empty

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.sendGame_publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.sendGame_publication

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.adapter_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.adapter_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.selected_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.selected_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.sendOwner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.sendOwner_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.application_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.application_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.application_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.application_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.application_schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.application_schedule_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxSourceSend.sendGame_active_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSourceSend.sendGame_active_state

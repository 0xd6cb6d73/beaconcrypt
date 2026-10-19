import BeaconcryptCore.Computational.RawCtxCanonicalSchedule

/-!
The actual source receive window supplies an unconditional aggregate KDF-call budget. Its own skipped-count check and fixed-width cast imply at most 51 pending steps before any primitive reply, even for an arbitrary represented entry kernel. This does not assume structural validity, successful authentication, fixed callback values, independent keys or a protocol security conclusion.

The old termination rank is remaining+1 because it handles malformed zero-count phases. The refined call allowance is max(1,remaining): a zero-count phase can still issue its one KDF request before source resume rejects. Actual zero/one branches have no later KDF call, and universal source progress makes the allowance decrease for every typed reply. The actual receive therefore issues at most 51 KDF requests; parsing/missing material/callback rejection do not increase that count.

Exact source embedding and arbitrary raw-only scheduling yield 51*qRaw actual KDF callbacks. The complete shared-state and source-selected canonical games consequently have uniform-oracle cap (51*kdfCoins+64)*qRaw under an explicit per-callback KDF cap. The 64 term counts byte-valued hash draws; KDF calls may use arbitrary finite uniform distributions. All prior complete-state/optional-reply equations remain unchanged, with no discarded failed cache effects or hidden randomness.

This is protocol-owned source control and resource accounting, not a primitive implementation or new computational security assumption. Actual source HKDF/shared-cache consistency, native library/runtime/codec and deployment contracts, local primitive/byte/cache work, correlated evolving-key security, interleaved send/reveal/multiple-owner actions and the global computational-symbolic experiment remain separate obligations.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxKdfBudget
open RawCtxOwnerOracle

/-- Every admitted source KDF phase has at most 51 remaining steps. -/
def RemainingBound {Context : Type} (effect : ReceiveEffect Context) : Prop :=
  match effect with
  | .ReceiveKdfRequested pending => pending.remaining.val ≤ 51
  | _ => True

/-- The actual source skipped-window guard bounds remaining steps without an entry-validity premise. -/
theorem begin_remaining {Context : Type} (kernel : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    ∃ result, begin_receive kernel target context = ok result ∧ RemainingBound result := by
  obtain ⟨plan, hplan⟩ := control.plan_receive_until_total kernel.refined.control target
  cases hseq : plan.sequence <;> simp only [begin_receive, hplan, bind_tc_ok, hseq, receive_rejected]
  all_goals first | exact ⟨_, rfl, True.intro⟩ | skip
  rename_i sequence
  split
  · obtain ⟨prepared, hprepared⟩ := refined.prepare_cached_receive_total kernel.refined sequence
    cases prepared <;> simp [hprepared, RemainingBound]
  · obtain ⟨skipped, hskipped, hskippedval⟩ := control.uscalar_sub_eq_ok plan.derivations 1#u64 (by scalar_tac)
    obtain ⟨empty, hempty⟩ := refined.refined_receive_slots_are_empty_ok kernel.refined
      kernel.refined.control.receive_cache.len (UScalar.cast UScalarTy.U8 skipped)
    cases empty <;> by_cases hgap : skipped > control.RATCHET_MAX_GAP <;>
      simp only [hskipped, lift, control.RatchetState.receive_cache_len, hempty, hgap,
        RatchetChain.as_bytes, SymmetricRatchetKdfRequest.new, refined.empty_material_slots,
        bind_tc_ok, Bool.false_eq_true, ite_false, ite_true, RustM.ok.injEq, RemainingBound]
    all_goals first | exact ⟨_, rfl, True.intro⟩ | skip
    refine ⟨_, rfl, ?_⟩
    scalar_tac

/-- A malformed zero-count phase still makes its original one KDF request before rejecting. -/
def kdfCost {Context : Type} : ReceiveEffect Context → Nat
  | .ReceiveKdfRequested pending => max 1 pending.remaining.val
  | _ => 0

/-- Actual source zero/one-count resume branches make no later KDF request under any typed reply. -/
theorem resume_small {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) (small : pending.remaining.val ≤ 1) :
    ∃ next, pending.resume response = ok next ∧ kdfCost next = 0 := by
  by_cases hzero : pending.remaining = 0#u8
  · simp [ReceiveKdf.resume, hzero, receive_rejected, kdfCost]
  · have hone : pending.remaining = 1#u8 := by scalar_tac
    simp only [ReceiveKdf.resume, hone, ite_true]
    obtain ⟨advanced, hadvanced⟩ := control.advance_receive_target_total pending.working_control
    cases hseq : advanced.sequence <;> simp only [hadvanced, hseq, bind_tc_ok, receive_rejected]
    all_goals first | exact ⟨_, rfl, rfl⟩ | skip
    rename_i sequence
    obtain ⟨stepped, hstepped⟩ := BeaconcryptCore.PanicFreedom.ratchet_step_from_response_ok response
    obtain ⟨valid, hvalid⟩ := refined.pending_receive_is_valid_ok pending.entry.refined
      { committed_control := advanced.state, final_receive_chain := stepped.chain,
        staged_slots := pending.staged_slots, target_sequence := sequence,
        target_material := stepped.material, first_slot := pending.first_slot, skipped := pending.skipped }
      pending.target
    simp only [hstepped, hvalid, bind_tc_ok]
    repeat' first | exact ⟨_, rfl, rfl⟩ | split

/-- The actual callback allowance decreases by one across every typed KDF reply. -/
theorem resume_cost {Context : Type} (pending : ReceiveKdf Context)
    (response : RatchetKdfResponse) :
    kdfCost (RawCtxOwnerOracle.resume pending response) + 1 ≤
      kdfCost (.ReceiveKdfRequested pending) := by
  by_cases small : pending.remaining.val ≤ 1
  · obtain ⟨next, hnext, hcost⟩ := resume_small pending response small
    have same := RustM.ok.inj ((resume_exact pending response).symm.trans hnext)
    rw [same, hcost]
    simp only [kdfCost]
    omega
  · have progress := (pending.resume_progress response).choose_spec.2
    change ResumeProgress pending (RawCtxOwnerOracle.resume pending response) at progress
    cases hnext : RawCtxOwnerOracle.resume pending response with
    | ReceiveRejected => simp [kdfCost]
    | ReceiveOpenRequested => simp [kdfCost]
    | ReceiveKdfRequested next =>
        have remaining := progress.2
        simp only [hnext] at remaining
        simp only [kdfCost]
        omega

/-- The full adaptive source program has the refined KDF allowance, including malformed phases. -/
theorem program_cost {Context Plaintext : Type} (effect : ReceiveEffect Context) :
    (program (Plaintext := Plaintext) effect).IsQueryBoundP
      (fun request => request.isLeft = true) (kdfCost effect) := by
  generalize hdepth : effectDepth effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
      cases effect with
      | ReceiveRejected entry context => simp [program]
      | ReceiveOpenRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          simp [kdfCost]
      | ReceiveKdfRequested pending =>
          rw [program, isQueryBoundP_query_bind_iff]
          simp only [Sum.isLeft, not_true_eq_false, false_or, ite_true]
          refine ⟨by simp [kdfCost], fun response => ?_⟩
          apply (ih _ (hdepth ▸ resume_rank pending response) _ rfl).mono
          have cost := resume_cost pending response
          omega

/-- The source admission guard turns the refined allowance into a constant 51 bound. -/
theorem begin_cost {Context : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    kdfCost (RawCtxOwnerOracle.begin entry target context) ≤ 51 := by
  obtain ⟨effect, hexact, hbound⟩ := begin_remaining entry target context
  have same := RustM.ok.inj ((begin_exact entry target context).symm.trans hexact)
  rw [same]
  cases effect <;> simp_all only [RemainingBound, kdfCost] <;> omega

/-- Every actual receive issues at most 51 KDF calls before any optional outcome is known. -/
theorem receive_bound {Context Plaintext : Type} (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : Context) :
    (receive (Plaintext := Plaintext) entry target context).IsQueryBoundP
      (fun request => request.isLeft = true) 51 :=
  (program_cost _).mono (begin_cost entry target context)

open RawCtxSourceOpen

/-- Actual native opening expansion preserves the derived receive KDF cap. -/
theorem native_receive_bound (entry : ConcreteRatchetKernel)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    (simulateQ ownerAdapter (receive (Plaintext := RawCtxWholeOwner.Decrypted) entry target context)).IsQueryBoundP
      (fun query => query.isLeft = true) 51 := by
  apply simulate_bound ownerAdapter _ _ _ _ (receive_bound entry target context)
  intro query
  cases query
  · rename_i request
    simp [ownerAdapter, QueryImpl.compose, RawCtxWholeOwner.adapter, nativeAdapter, OracleSpec.query]
    exact (isQueryBoundP_query_iff (spec := NativeSpec)
      (p := fun query => query.isLeft = true) (.inl request) 1).2 (by simp)
  · rename_i pending
    simp only [ownerAdapter, QueryImpl.apply_compose, RawCtxWholeOwner.adapter, Sum.isLeft]
    cases RawCtxWholeOwner.arguments pending
    · simp
    · rename_i input
      simp [nativeAdapter, OracleSpec.query]
      change (simulateQ openLift (openInput input)).IsQueryBoundP (fun query => query.isLeft = true) 0
      exact openLift_no_kdf (openInput input)

/-- Every raw request, including earlier parser and material rejection, has at most 51 KDF callbacks. -/
theorem raw_bound {Metadata : Type} (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : RawCtxWholeOwner.OwnerState Metadata) :
    (simulateQ nativeAdapter (RawCtxWholeOwner.rawReceive decode raw state)).IsQueryBoundP
      (fun query => query.isLeft = true) 51 := by
  unfold RawCtxWholeOwner.rawReceive
  split
  · simp
  · split
    · simp
    · split
      · simp only [bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff,
          ← QueryImpl.simulateQ_compose]
        exact native_receive_bound _ _ _
      · simp

/-- Arbitrary adaptive raw scheduling derives its aggregate KDF bound from the outer request count. -/
theorem schedule_bound {Metadata Result : Type} (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxWholeOwner.RawSpec Result) (qRaw : Nat)
    (hbound : client.IsTotalQueryBound qRaw) (state : RawCtxWholeOwner.OwnerState Metadata) :
    ((simulateQ (nativeOwnerImpl decode) client).run state).IsQueryBoundP
      (fun query => query.isLeft = true) (51 * qRaw) := by
  induction client using OracleComp.inductionOn generalizing qRaw state with
  | pure value => trivial
  | query_bind raw next ih =>
      rw [isTotalQueryBound_query_bind_iff] at hbound
      rw [simulateQ_query_bind, StateT.run_bind]
      apply (isQueryBoundP_bind (raw_bound decode raw state)
        (fun result _ => ih result.1 (qRaw - 1) (hbound.2 result.1) result.2)).mono
      omega

/-- The actual complete shared-state source game needs only the per-callback KDF randomness cap. -/
theorem source_uniform {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (owner : RawCtxWholeOwner.OwnerState Metadata)
    (primitive : RawCtxSharedPrimitive.SharedState Auxiliary)
    (qRaw : Nat) (hbound : client.IsTotalQueryBound qRaw) :
    (RawCtxSharedPrimitive.sharedSchedule c kdf decode client owner primitive).IsTotalQueryBound
      ((51 * kdfCoins + 64) * qRaw) := by
  have bound := RawCtxSharedPrimitive.sharedSchedule_uniform c kdf kdfCoins bounded
    decode client owner primitive (51 * qRaw) qRaw hbound (schedule_bound decode client qRaw hbound owner)
  have same : kdfCoins * (51 * qRaw) + 64 * qRaw = (51 * kdfCoins + 64) * qRaw := by ring
  rwa [same] at bound

/-- The exact source-selected canonical schedule inherits the same derived complete uniform ledger. -/
theorem canonical_uniform {Metadata Auxiliary Result : Type} (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp)) (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxWholeOwner.RawSpec Result)
    (state : RawCtxWholeOwner.OwnerState Metadata × RawCtxCanonicalSchedule.AnnotatedState Auxiliary)
    (qRaw : Nat) (hbound : client.IsTotalQueryBound qRaw) :
    (RawCtxWholeOwner.scheduleGame (RawCtxCanonicalSchedule.canonicalImpl c kdf decode)
      decode client state).IsTotalQueryBound ((51 * kdfCoins + 64) * qRaw) := by
  have bound := RawCtxCanonicalSchedule.canonical_uniform c kdf kdfCoins bounded decode client state
    (51 * qRaw) qRaw hbound (schedule_bound decode client qRaw hbound state.1)
  have same : kdfCoins * (51 * qRaw) + 64 * qRaw = (51 * kdfCoins + 64) * qRaw := by ring
  rwa [same] at bound

end BeaconcryptCore.Computational.RawCtxKdfBudget

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.begin_remaining' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.begin_remaining

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.resume_small' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.resume_small

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.resume_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.resume_cost

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.program_cost

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.begin_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.begin_cost

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.receive_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.receive_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.native_receive_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.native_receive_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.raw_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.raw_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.schedule_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.source_uniform

/--
info: 'BeaconcryptCore.Computational.RawCtxKdfBudget.canonical_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxKdfBudget.canonical_uniform

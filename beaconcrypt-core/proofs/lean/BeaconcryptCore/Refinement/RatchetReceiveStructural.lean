import BeaconcryptCore.Refinement.RatchetCachedStructural
import BeaconcryptCore.Refinement.RatchetRelativeFuture
import BeaconcryptCore.Refinement.RatchetReceiveBoundary
import BeaconcryptCore.Refinement.RatchetStructuralSend
import BeaconcryptCore.Refinement.RatchetLifetime

/-! Complete receive execution preserves the structural invariant without assumptions about stored material provenance. -/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core.ratchet.control

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace beaconcrypt_core.ratchet.concrete

/-- Every missing old target is rejected before calling any external interpreter. -/
theorem begin_receive_old_missing {Context : Type}
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (hpast : target.val ≤ entry.refined.control.receive_sequence.val)
    (hmissing : lookup_receive_key entry.refined.control target = ok core.option.Option.None) :
    begin_receive entry target context = ok (ReceiveEffect.ReceiveRejected entry context) := by
  simp only [begin_receive, plan_receive_until_replay entry.refined.control target hpast,
    bind_tc_ok, if_true, ratchet.refined.prepare_cached_receive, hmissing, receive_rejected]

/-- Capacity rejection preserves the entire entry without any validity premise. -/
theorem begin_receive_capacity_rejected {Context : Type}
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (hfuture : entry.refined.control.receive_sequence.val < target.val)
    (hcapacity : 50 < entry.refined.control.receive_cache.len.val +
      (target.val - entry.refined.control.receive_sequence.val - 1)) :
    begin_receive entry target context = ok (ReceiveEffect.ReceiveRejected entry context) := by
  have hplan : plan_receive_until entry.refined.control target =
      ok { sequence := core.option.Option.None, derivations := 0#u64 } := by
    by_cases hgap : entry.refined.control.receive_sequence.val + 51 < target.val
    · exact plan_receive_until_reject_of_gap_gt _ _ hgap
    · exact plan_receive_until_reject_of_cache_full _ _ hfuture (by omega) hcapacity
  simp only [begin_receive, hplan, bind_tc_ok, receive_rejected]

/-- An admitted cached target prepares a complete structurally valid transaction. -/
theorem begin_receive_cached_valid {Context : Type}
    (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (hpast : target.val ≤ entry.refined.control.receive_sequence.val)
    (slot : Std.U8)
    (hlookup : lookup_receive_key entry.refined.control target = ok (core.option.Option.Some slot)) :
    ∃ prepared,
      begin_receive entry target context = ok (ReceiveEffect.ReceiveOpenRequested
        { entry, context, prepared := .PreparedReceiveCachedCase prepared }) ∧
      ratchet.refined.CachedPreparationFacts entry.refined target prepared := by
  obtain ⟨prepared, hprepare, hfacts⟩ := hvalid.prepare_cached_receive entry.refined target slot hlookup
  exact ⟨prepared, by simp only [begin_receive, plan_receive_until_replay entry.refined.control target hpast,
    bind_tc_ok, if_true, hprepare], hfacts⟩

/-- The prepared authentication request is tied to the original target and exact cached or future transaction. -/
def PreparedReceiveRefines {AD PT CT Context : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (entry : ConcreteRatchetKernel) (context : Context) (target : Std.U64) (opened : ReceiveOpen Context) : Prop :=
  (∃ prepared, opened.entry = entry ∧ opened.context = context ∧
    opened.prepared = ratchet.refined.PreparedReceive.PreparedReceiveCachedCase prepared ∧
    ratchet.refined.CachedPreparationFacts entry.refined target prepared) ∨
  RelativeFutureOpen cr entry context target opened

/-- Every returned plaintext has an exact production trace, prepared target, callback result, and publication witness. -/
def SuccessfulReceive {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (result : ConcreteRatchetKernel) (plaintext : Output) : Prop :=
  ratchet.refined.ValidRefined entry.refined ∧ ∃ effect opened count,
    begin_receive entry target context = ok effect ∧
    ReceiveKdfTrace execute effect (ReceiveEffect.ReceiveOpenRequested opened) count ∧
    PreparedReceiveRefines (withInterpreter cr execute) entry context target opened ∧
    openReply opened = core.option.Option.Some plaintext ∧
    opened.finish (core.option.Option.Some plaintext) = ok (result, core.option.Option.Some plaintext)

/-- Every structurally valid receive completes; every successful result consumes its target. -/
theorem receiveRun_exists_classified {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hvalid : ratchet.refined.ValidRefined entry.refined) :
    ∃ next output, ReceiveRun execute openReply entry target context next output ∧
      ratchet.refined.ValidRefined next.refined ∧
      (∀ plaintext, output = core.option.Option.Some plaintext → ReceiveSuccess target next ∧
        SuccessfulReceive cr execute entry target context openReply next plaintext) := by
  by_cases hfuture : entry.refined.control.receive_sequence.val < target.val
  · by_cases hcapacity : entry.refined.control.receive_cache.len.val +
        (target.val - entry.refined.control.receive_sequence.val - 1) ≤ 50
    · obtain ⟨pending, opened, hbegin, htrace, hopen⟩ :=
        relative_begin_receive_future_trace cr execute entry context target hvalid hfuture hcapacity
      cases hreply : openReply opened with
      | none =>
          have hentry : opened.entry = entry := by obtain ⟨_, he, _, _, _⟩ := hopen; exact he
          have hfinish : opened.finish (openReply opened) = ok (entry, core.option.Option.None) := by
            simp only [hreply, ReceiveOpen.finish, hentry]
          exact ⟨entry, .None, ⟨_, hbegin, htrace.complete (.opened opened entry .None hfinish)⟩,
            hvalid, by simp⟩
      | some plaintext =>
          obtain ⟨published, hfinish, hresult⟩ := hopen.finish_some
            (withInterpreter cr execute) entry context target opened plaintext
          refine ⟨{ refined := published }, .Some plaintext,
            ⟨_, hbegin, htrace.complete (.opened opened _ _ (by simpa only [hreply] using hfinish))⟩,
            hresult.valid, ?_⟩
          intro returned heq
          cases heq
          exact ⟨⟨hresult.valid, by omega,
            by simp only [hresult.receiveSequence]; exact Nat.le_refl _, hresult.targetAbsent⟩,
            hvalid, _, opened, _, hbegin, htrace, Or.inr hopen, hreply, hfinish⟩
    · exact ⟨entry, .None,
        ⟨_, begin_receive_capacity_rejected entry target context hfuture (by omega), .rejected entry context⟩,
        hvalid, by simp⟩
  · obtain ⟨found, hlookup⟩ := lookup_receive_key_total entry.refined.control target
    cases found with
    | none =>
        exact ⟨entry, .None,
          ⟨_, begin_receive_old_missing entry target context (by omega) hlookup, .rejected entry context⟩,
          hvalid, by simp⟩
    | some slot =>
        obtain ⟨prepared, hbegin, hfacts⟩ := begin_receive_cached_valid entry target context hvalid (by omega) slot hlookup
        let opened : ReceiveOpen Context := { entry, context, prepared := .PreparedReceiveCachedCase prepared }
        cases hreply : openReply opened with
        | none =>
            exact ⟨entry, .None, ⟨_, hbegin,
              .opened opened entry .None (by simp only [hreply, ReceiveOpen.finish, opened])⟩,
              hvalid, by simp⟩
        | some plaintext =>
            obtain ⟨next, hfinish, hsuccess⟩ := finish_cached_success opened target prepared hvalid rfl hfacts plaintext
            refine ⟨next, .Some plaintext,
              ⟨_, hbegin, .opened opened next _ (by simpa only [hreply] using hfinish)⟩,
              hsuccess.valid, ?_⟩
            intro returned heq
            cases heq
            exact ⟨hsuccess, hvalid, _, opened, 0, hbegin, .refl _,
              Or.inl ⟨prepared, rfl, rfl, rfl, hfacts⟩, hreply, hfinish⟩

/-- Project structural validity and target consumption from the exact execution classification. -/
theorem receiveRun_exists_valid {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hvalid : ratchet.refined.ValidRefined entry.refined) :
    ∃ next output, ReceiveRun execute openReply entry target context next output ∧
      ratchet.refined.ValidRefined next.refined ∧
      (∀ plaintext, output = core.option.Option.Some plaintext → ReceiveSuccess target next) := by
  obtain ⟨next, output, run, hv, hs⟩ := receiveRun_exists_classified cr execute entry target context openReply hvalid
  exact ⟨next, output, run, hv, fun p hp => (hs p hp).1⟩

/-- Every actual successful output carries the prepared-target and exact publication witness. -/
theorem receiveNext_successful_receive {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (next : ConcreteRatchetKernel) (plaintext : Output)
    (hrun : receiveNext execute entry target context openReply = ok (next, core.option.Option.Some plaintext)) :
    SuccessfulReceive cr execute entry target context openReply next plaintext := by
  obtain ⟨result, output, run, _, hsuccess⟩ :=
    receiveRun_exists_classified cr execute entry target context openReply hvalid
  have heq := RustM.ok.inj (run.driver_eq.symm.trans hrun)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact (hsuccess plaintext rfl).2

/-- The actual unbounded receive driver preserves validity and consumes every successfully opened target. -/
theorem receiveNext_preserves_validity {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hvalid : ratchet.refined.ValidRefined entry.refined) :
    ∃ next output, receiveNext execute entry target context openReply = ok (next, output) ∧
      ratchet.refined.ValidRefined next.refined ∧
      (∀ plaintext, output = core.option.Option.Some plaintext → ReceiveSuccess target next) := by
  obtain ⟨next, output, run, hnext, hsuccess⟩ := receiveRun_exists_valid cr execute entry target context openReply hvalid
  exact ⟨next, output, run.driver_eq, hnext, hsuccess⟩

/-- A successful actual operation consumes its target, independently of initial material provenance. -/
theorem receiveNext_success {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (next : ConcreteRatchetKernel) (plaintext : Output)
    (hrun : receiveNext execute entry target context openReply = ok (next, core.option.Option.Some plaintext)) :
    ReceiveSuccess target next := by
  obtain ⟨result, output, hresult, _, hsuccess⟩ :=
    receiveNext_preserves_validity cr execute entry target context openReply hvalid
  have heq := RustM.ok.inj (hresult.symm.trans hrun)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact hsuccess plaintext rfl

/-- Any successful receive is followed by neutral replay, even with different interpreters and callbacks. -/
theorem receiveNext_success_replay {AD PT CT Context Output RetryContext RetryOutput : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute retryExecute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (openReply : ReceiveOpen Context → core.option.Option Output)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (next : ConcreteRatchetKernel) (plaintext : Output)
    (hrun : receiveNext execute entry target context openReply = ok (next, core.option.Option.Some plaintext))
    (retryContext : RetryContext) (retryReply : ReceiveOpen RetryContext → core.option.Option RetryOutput) :
    receiveNext retryExecute next target retryContext retryReply = ok (next, core.option.Option.None) :=
  (receiveNext_success cr execute entry target context openReply hvalid next plaintext hrun).replay retryExecute retryContext retryReply

/-- A successful publication witness reconstructs the exact complete production execution. -/
theorem SuccessfulReceive.run {AD PT CT Context Output : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {execute : KdfInterpreter} {entry : ConcreteRatchetKernel} {target : Std.U64} {context : Context}
    {openReply : ReceiveOpen Context → core.option.Option Output}
    {result : ConcreteRatchetKernel} {plaintext : Output}
    (h : SuccessfulReceive cr execute entry target context openReply result plaintext) :
    ReceiveRun execute openReply entry target context result (core.option.Option.Some plaintext) := by
  obtain ⟨_, effect, opened, _, hbegin, htrace, _, hreply, hfinish⟩ := h
  exact ⟨effect, hbegin, htrace.complete (.opened opened result _ (by simpa only [hreply] using hfinish))⟩

/-- Every success witness entails consumed-target validity, without an additional operation equation. -/
theorem SuccessfulReceive.consumes {AD PT CT Context Output : Type}
    {cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT}
    {execute : KdfInterpreter} {entry : ConcreteRatchetKernel} {target : Std.U64} {context : Context}
    {openReply : ReceiveOpen Context → core.option.Option Output}
    {result : ConcreteRatchetKernel} {plaintext : Output}
    (h : SuccessfulReceive cr execute entry target context openReply result plaintext) :
    ReceiveSuccess target result :=
  receiveNext_success cr execute entry target context openReply h.1 result plaintext h.run.driver_eq

/-- Fifty planned derivations retain exactly forty-nine keys from any structurally valid empty entry. -/
theorem fresh_maximum_gap_success_publishes_exactly_49 {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (execute : KdfInterpreter) (entry : ConcreteRatchetKernel) (target : Std.U64) (context : Context)
    (hvalid : ratchet.refined.ValidRefined entry.refined)
    (hempty : entry.refined.control.receive_cache.len.val = 0)
    (hplan : plan_receive_until entry.refined.control target =
      ok { sequence := core.option.Option.Some target, derivations := 50#u64 })
    (callback : ratchet.RatchetMaterial → Std.U64 → Context → core.option.Option Output)
    (plaintext : Output)
    (hcallback : callback (Ratchet.msgKeyAt (withInterpreter cr execute) entry.refined.receive_chain 49) target context =
      core.option.Option.Some plaintext) :
    ∃ result,
      receiveNext execute entry target context (receiveMaterialOpenReply callback) = ok (result, core.option.Option.Some plaintext) ∧
      ratchet.refined.ValidRefined result.refined ∧ result.refined.control.receive_sequence = target ∧
      result.refined.control.receive_cache.len.val = 49 ∧
      lookup_receive_key result.refined.control target = ok core.option.Option.None := by
  obtain ⟨_, _, hmax⟩ := plan_receive_until_bound entry.refined.control target
    { sequence := core.option.Option.Some target, derivations := 50#u64 } hvalid.control.capacity hplan rfl
  have hsteps : target.val = entry.refined.control.receive_sequence.val + 50 := by scalar_tac
  obtain ⟨pending, opened, hbegin, htrace, hopen⟩ := relative_begin_receive_future_trace cr execute
    entry context target hvalid (by omega) (by omega)
  have hreply : receiveMaterialOpenReply callback opened = core.option.Option.Some plaintext := by
    obtain ⟨transaction, _, hcontext, hphase, htransaction⟩ := hopen
    simp only [receiveMaterialOpenReply, ReceiveOpen.material, ReceiveOpen.sequence, hphase,
      htransaction.targetMaterial, htransaction.targetSequence, hcontext,
      show target.val - entry.refined.control.receive_sequence.val - 1 = 49 by omega, hcallback]
  obtain ⟨published, hfinish, hresult⟩ := hopen.finish_some
    (withInterpreter cr execute) entry context target opened plaintext
  refine ⟨{ refined := published }, ?_, hresult.valid, hresult.receiveSequence, ?_, hresult.targetAbsent⟩
  · exact (show ReceiveRun execute (receiveMaterialOpenReply callback) entry target context
      { refined := published } (core.option.Option.Some plaintext) from
      ⟨_, hbegin, htrace.complete (.opened opened _ _ (by simpa only [hreply] using hfinish))⟩).driver_eq
  · simpa only [hresult.length, hempty, hsteps] using (show 0 +
      (entry.refined.control.receive_sequence.val + 50 - entry.refined.control.receive_sequence.val - 1) = 49 by omega)

/-- Arbitrary finite mixed histories preserve structural validity from any structurally valid entry. -/
theorem executeHistory_preserves_validity {AD PT CT Context Output : Type}
    (cr : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (interpret : KdfInterpreter) (actions : List (RoleAction Context Output)) :
    ∀ entry, ratchet.refined.ValidRefined entry.refined →
      ∃ finalState outputs, executeHistory interpret entry actions = ok (finalState, outputs) ∧
        outputs.length = actions.length ∧ ratchet.refined.ValidRefined finalState.refined := by
  induction actions with
  | nil => intro entry h; exact ⟨entry, [], rfl, rfl, h⟩
  | cons action actions ih =>
      intro entry h
      have hstep : ∃ next output, action.execute interpret entry = ok (next, output) ∧
          ratchet.refined.ValidRefined next.refined := by
        cases action with
        | send context sealReply => exact sealNext_preserves_validity interpret entry context sealReply h
        | receive target context openReply =>
            obtain ⟨next, output, hrun, hnext, _⟩ :=
              receiveNext_preserves_validity cr interpret entry target context openReply h
            exact ⟨next, output, hrun, hnext⟩
      obtain ⟨next, output, hrun, hnext⟩ := hstep
      obtain ⟨finalState, outputs, htail, hlength, hfinal⟩ := ih next hnext
      exact ⟨finalState, output :: outputs, by simp! only [executeHistory, hrun, bind_tc_ok, htail],
        by simp only [List.length_cons, hlength], hfinal⟩

end beaconcrypt_core.ratchet.concrete

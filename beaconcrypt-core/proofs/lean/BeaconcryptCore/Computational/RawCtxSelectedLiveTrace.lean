import BeaconcryptCore.Computational.RawCtxSelectedLiveRead
import BeaconcryptCore.Computational.RawCtxSelectedAliasCoupling

/-!
A complete selected-owner continuation interleaves the original record/public source with actual current-chain/skipped-key read replies. Every operation ticks the existing disclosure chronology. Known read values append to the same source input list; unavailable current-chain reads set a separate sticky direct-exposure flag. The target-free reader preserves every earlier complete transition and returns rejection only for an unavailable chain. Candidate logging does not turn that direct exposure into a finite-byte guess.

The full-state identical-until-bad theorem applies with internally proved good transitions and sticky flags. It bounds the original target-reading selected continuation against target-free reads and preserves the probability of the same direct-exposure event. Both complete owner chains, materials, original optional results, shared cache/auxiliary state, candidate list and timestamped reply history remain in the comparison. The original all-reply source caps supply S+51R+K+E candidates, including retries and rejected reads, for either reader.

This is one selected established-owner/public/read continuation, with the actual read/source field relation supplied by RawCtxSelectedLiveRead. The challenge response is arbitrary here; its fixed-source specialization and the complete reached-prefix/role-family linkage require their separate source equations. No sampled-cut law, earlier ancestor/root/identity/KEM disclosure policy, finite-byte independence or small exposure probability is asserted. Actual first32 aliases, additional owners, initial64 requests and complete challenger work remain to be composed. All interpreter state is private. Snapshots, persistence and restoration are excluded.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedLiveTrace
open RawCtxSelectedChain RawCtxSelectedLiveRead PqxdhSecretInputKdf

abbrev SourceSpec := RawCtxSelectedPublicTrace.SourceSpec + ReadSpec
abbrev BaseState (Metadata Auxiliary : Type) (serverCount beaconCount : Nat) :=
  RawCtxSelectedTraceOwner.State Metadata Auxiliary × RawCtxProtocolReveals.History serverCount beaconCount
abbrev State (Metadata Auxiliary : Type) (serverCount beaconCount : Nat) :=
  BaseState Metadata Auxiliary serverCount beaconCount × Bool

abbrev Reader := (read : Read) → Option Kernel → ReadSpec.Range read

noncomputable def nativeReader (target : RatchetChain) : Reader :=
  fun read entry => nativeRead read (entry.map (nativeKernel target))

def direct {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (query : SourceSpec.Domain) (state : BaseState Metadata Auxiliary serverCount beaconCount) : Bool :=
  match query with
  | .inl _ => false
  | .inr read => exposed read (some state.1.1.kernel)

noncomputable def observedImpl {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : Reader) :
    QueryImpl SourceSpec (StateT (State Metadata Auxiliary serverCount beaconCount) ProbComp) :=
  fun query state => match query with
  | .inl request =>
      (fun result => (result.1, ((result.2, RawCtxProtocolReveals.tick state.1.2), state.2))) <$>
        (RawCtxSelectedPublicTrace.sourceImpl source writer challenge sender decode request).run state.1.1
  | .inr read =>
      let entry := some state.1.1.1.kernel
      let reply := reader read entry
      pure (reply,
        (((state.1.1.1, (state.1.1.2.1, state.1.1.2.2 ++ candidates read entry)),
          RawCtxProtocolReveals.note (observation owner read reply) state.1.2),
          state.2 || exposed read entry))

/-- Every non-exposing read and every original record/public step has the same complete transition. -/
theorem query_safe {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (query : SourceSpec.Domain) (state : State Metadata Auxiliary serverCount beaconCount)
    (safe : direct query state.1 = false) :
    (observedImpl source writer challenge sender decode owner (nativeReader target) query).run state =
      (observedImpl source writer challenge sender decode owner labelRead query).run state := by
  cases query with
  | inl request => rfl
  | inr read =>
    simp only [observedImpl, StateT.run, nativeReader]
    rw [before_exposure read target (some state.1.1.1.kernel) safe]

/-- Direct exposure remains marked through all subsequent original effects and optional replies. -/
theorem sticky {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : Reader)
    (query : SourceSpec.Domain) (state : State Metadata Auxiliary serverCount beaconCount)
    (bad : state.2 = true) (result : SourceSpec.Range query × State Metadata Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((observedImpl source writer challenge sender decode owner reader query).run state)) :
    result.2.2 = true := by
  cases query <;> simp only [observedImpl, StateT.run, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case inl =>
    rcases supported with ⟨_, _, rfl⟩
    exact bad
  case inr => simp [supported, bad]

/-- The first direct exposure is marked even when its actual and simulated optional replies differ. -/
theorem hit_marked {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : Reader)
    (query : SourceSpec.Domain) (state : State Metadata Auxiliary serverCount beaconCount)
    (hit : direct query state.1 = true) (result : SourceSpec.Range query × State Metadata Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((observedImpl source writer challenge sender decode owner reader query).run state)) :
    result.2.2 = true := by
  cases query with
  | inl request => simp [direct] at hit
  | inr read =>
    simp only [observedImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp only [direct] at hit
    simp [hit]

/-- Before exposure, both complete good-output transition distributions are identical. -/
theorem agree_good {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (query : SourceSpec.Domain) (state : BaseState Metadata Auxiliary serverCount beaconCount)
    (reply : SourceSpec.Range query) (next : BaseState Metadata Auxiliary serverCount beaconCount) :
    Pr[= (reply, (next, false)) |
      (observedImpl source writer challenge sender decode owner (nativeReader target) query).run (state, false)] =
    Pr[= (reply, (next, false)) |
      (observedImpl source writer challenge sender decode owner labelRead query).run (state, false)] := by
  by_cases hit : direct query state = true
  · have zero (reader : Reader) :
        Pr[= (reply, (next, false)) |
          (observedImpl source writer challenge sender decode owner reader query).run (state, false)] = 0 := by
      apply probOutput_eq_zero_of_not_mem_support
      intro supported
      exact Bool.false_ne_true (hit_marked source writer challenge sender decode owner reader
        query (state, false) hit (reply, (next, false)) supported)
    rw [zero, zero]
  · rw [query_safe source writer challenge sender decode owner target query (state, false)
      (by simpa using hit)]

/-- The same full adaptive source continuation differs from target-free reads by at most its actual direct-exposure event. -/
theorem exposure_distance {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (client : OracleComp SourceSpec Result) (state : BaseState Metadata Auxiliary serverCount beaconCount) :
    tvDist ((simulateQ (observedImpl source writer challenge sender decode owner (nativeReader target)) client).run (state, false))
      ((simulateQ (observedImpl source writer challenge sender decode owner labelRead) client).run (state, false)) ≤
      Pr[fun result => result.2.2 = true |
        (simulateQ (observedImpl source writer challenge sender decode owner (nativeReader target)) client).run (state, false)].toReal := by
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    _ _ client state (agree_good source writer challenge sender decode owner target)
    (sticky source writer challenge sender decode owner (nativeReader target))
    (sticky source writer challenge sender decode owner labelRead)

/-- Masking the first unavailable reply preserves the probability of that same first exposure, without a second sampler. -/
theorem exposure_probability {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (target : RatchetChain)
    (client : OracleComp SourceSpec Result) (state : BaseState Metadata Auxiliary serverCount beaconCount) :
    Pr[fun result => result.2.2 = true |
      (simulateQ (observedImpl source writer challenge sender decode owner (nativeReader target)) client).run (state, false)] =
    Pr[fun result => result.2.2 = true |
      (simulateQ (observedImpl source writer challenge sender decode owner labelRead) client).run (state, false)] := by
  exact OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq' _ _
    (agree_good source writer challenge sender decode owner target)
    (sticky source writer challenge sender decode owner (nativeReader target))
    (sticky source writer challenge sender decode owner labelRead) client state

def cost : SourceSpec.Domain → Nat
  | .inl query => RawCtxSelectedPublicTrace.cost query
  | .inr _ => 1

/-- Record/public inputs keep their actual allowance; every attempted read adds at most one available value. -/
theorem step_length {Metadata Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : Reader)
    (query : SourceSpec.Domain) (state : State Metadata Auxiliary serverCount beaconCount)
    (result : SourceSpec.Range query × State Metadata Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((observedImpl source writer challenge sender decode owner reader query).run state)) :
    result.2.1.1.2.2.length ≤ state.1.1.2.2.length + cost query := by
  cases query <;> simp only [observedImpl, StateT.run, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case inl request =>
    rcases supported with ⟨reply, hreply, rfl⟩
    exact RawCtxSelectedPublicTrace.source_step_length source writer challenge sender decode request state.1.1 reply hreply
  case inr read =>
    subst result
    simpa only [cost, candidates, List.length_append] using
      Nat.add_le_add_left (reply_length read (labelRead read (some state.1.1.1.kernel))) state.1.1.2.2.length

def IsSend : SourceSpec.Domain → Prop
  | .inl query => RawCtxSelectedPublicTrace.IsSend query
  | .inr _ => False

def IsRaw : SourceSpec.Domain → Prop
  | .inl query => RawCtxSelectedPublicTrace.IsRaw query
  | .inr _ => False

def IsPublicKdf : SourceSpec.Domain → Prop
  | .inl query => RawCtxSelectedPublicTrace.IsPublicKdf query
  | .inr _ => False

def IsRead : SourceSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsSend := fun query => by
  cases query <;> simp only [IsSend] <;> infer_instance
instance : DecidablePred IsRaw := fun query => by
  cases query <;> simp only [IsRaw] <;> infer_instance
instance : DecidablePred IsPublicKdf := fun query => by
  cases query <;> simp only [IsPublicKdf] <;> infer_instance
instance : DecidablePred IsRead := fun query => by
  cases query <;> simp only [IsRead] <;> infer_instance

/-- The same adaptive record/public/read source supplies its whole candidate bill, including every rejected attempt. -/
theorem source_length {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (challenge : RatchetKdfResponse) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount) (reader : Reader)
    (client : OracleComp SourceSpec Result) (qSend qRaw qKdf qRead : Nat)
    (sendBound : client.IsQueryBoundP IsSend qSend)
    (rawBound : client.IsQueryBoundP IsRaw qRaw)
    (kdfBound : client.IsQueryBoundP IsPublicKdf qKdf)
    (readBound : client.IsQueryBoundP IsRead qRead)
    (state : State Metadata Auxiliary serverCount beaconCount)
    (result : Result × State Metadata Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((simulateQ (observedImpl source writer challenge sender decode owner reader) client).run state)) :
    result.2.1.1.2.2.length ≤ state.1.1.2.2.length + qSend + 51*qRaw + qKdf + qRead := by
  induction client using OracleComp.inductionOn generalizing qSend qRaw qKdf qRead state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _ |>.trans (Nat.le_add_right _ _) |>.trans (Nat.le_add_right _ _) |>.trans (Nat.le_add_right _ _)
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at sendBound rawBound kdfBound readBound
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, headSupport, tailSupport⟩
    have head := step_length source writer challenge sender decode owner reader query state reply headSupport
    have tail := ih reply.1 _ _ _ _ (sendBound.2 reply.1) (rawBound.2 reply.1)
      (kdfBound.2 reply.1) (readBound.2 reply.1) reply.2 result tailSupport
    rcases query with ((send | raw) | (coin | (hash | view))) | read
    all_goals simp only [IsSend, IsRaw, IsPublicKdf, IsRead, RawCtxSelectedPublicTrace.IsSend,
      RawCtxSelectedPublicTrace.IsRaw, RawCtxSelectedPublicTrace.IsPublicKdf,
      RawCtxSelectedPublicTrace.isKdf, cost, RawCtxSelectedPublicTrace.cost, Sum.isLeft, Sum.isRight,
      if_true, if_false, Bool.false_eq_true, not_true_eq_false, false_or] at head tail sendBound rawBound kdfBound readBound
    all_goals omega

end BeaconcryptCore.Computational.RawCtxSelectedLiveTrace

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.query_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.query_safe

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.sticky

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.hit_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.hit_marked

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.agree_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.agree_good

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.exposure_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.exposure_distance

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.exposure_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.exposure_probability

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.step_length

/--
info: 'BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.source_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedLiveTrace.source_length

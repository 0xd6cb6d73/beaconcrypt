import BeaconcryptCore.Computational.RawCtxLiveLineage
import BeaconcryptCore.Computational.StatefulGoodEvent

/-!
The finite live-disclosure freshness ledger is interpreted over the original native role/source experiment. The private arbitrary-predicate induction is the same complete-output sum argument used by StatefulGoodEvent, specialized through source-derived monotonicity below. Every actual optional reply, native role state, shared primitive state and timestamp remains present. Freshness can only be lost as history grows; no allowed later operation removes earlier knowledge. The fixed source and prior root/public disclosure list are unchanged. These statements supply operational freshness interfaces, not the missing cryptographic distribution or the complete global reveal policy.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxLiveSourceFreshness
open RawCtxProtocolReveals RawCtxLiveLineage

abbrev NativeState (Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type)
    (serverCount beaconCount : Nat) :=
  RawCtxProtocolReveals.State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
    RawCtxSharedPrimitive.SharedState Auxiliary

/-- A masked read rejects with the original optional result type. -/
def rejected {serverCount beaconCount : Nat}
    (request : (RevealSpec serverCount beaconCount).Domain) :
    (RevealSpec serverCount beaconCount).Range request :=
  match request with
  | .sendChain _ | .receiveChain _ | .skippedKey _ _ => .None

/-- Private history retains the actual reply even when the delivered reply is suppressed. -/
noncomputable def maskedImpl {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (blocked : List RatchetChain) :
    QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount) ProbComp) :=
  fun query state => match query with
  | .inl request => (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
      senderId route decode (.inl request)).run state
  | .inr request =>
      let actual := reveal request state.1.1
      let reply := if exposed blocked ⟨request, actual⟩ then rejected request else actual
      pure (reply, ((state.1.1, note ⟨request, actual⟩ state.1.2), state.2))

/-- A fresh actual source poststate implies a fresh prestate, including failed operations and optional reveal rejection. -/
theorem source_step_fresh {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (blocked prior : List RatchetChain)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (result : (SourceSpec serverCount beaconCount).Range query ×
      NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
      senderId route decode query).run state)) (fresh : Fresh blocked prior result.2.1.2) :
    Fresh blocked prior state.1.2 := by
  cases query with
  | inl request =>
    simp only [RawCtxProtocolReveals.sourceImpl, StateT.run, mem_support_bind_iff,
      mem_support_pure_iff] at supported
    rcases supported with ⟨child, _, rfl⟩
    exact (fresh_tick blocked prior state.1.2).mp fresh
  | inr request =>
    simp only [RawCtxProtocolReveals.sourceImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    exact ((fresh_note blocked prior state.1.2 ⟨request, reveal request state.1.1⟩).mp fresh).1

/-- Freshness at the end of any actual adaptive schedule excludes forbidden knowledge from its original history. -/
theorem source_schedule_fresh {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (blocked prior : List RatchetChain)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (result : Result × NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((simulateQ (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
      senderId route decode) client).run state)) (fresh : Fresh blocked prior result.2.1.2) :
    Fresh blocked prior state.1.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    simpa only [supported] using fresh
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, head, tail⟩
    exact source_step_fresh source writer senderId route decode blocked prior query state reply head
      (ih reply.1 reply.2 result tail fresh)

/-- Masking cannot erase earlier forbidden knowledge: the original actual reply remains in private history. -/
theorem masked_step_fresh {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (blocked prior : List RatchetChain)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (result : (SourceSpec serverCount beaconCount).Range query ×
      NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (supported : result ∈ support ((maskedImpl source writer serverCount beaconCount
      senderId route decode blocked query).run state)) (fresh : Fresh blocked prior result.2.1.2) :
    Fresh blocked prior state.1.2 := by
  cases query with
  | inl request =>
    exact source_step_fresh source writer senderId route decode blocked prior (.inl request)
      state result supported fresh
  | inr request =>
    simp only [maskedImpl, StateT.run, mem_support_pure_iff] at supported
    subst result
    exact ((fresh_note blocked prior state.1.2 ⟨request, reveal request state.1.1⟩).mp fresh).1

/-- Every complete fresh native transition has exactly the same probability after suppressing forbidden reveal replies. -/
theorem step_agree {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (blocked prior : List RatchetChain)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (result : (SourceSpec serverCount beaconCount).Range query ×
      NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (fresh : Fresh blocked prior result.2.1.2) :
    Pr[= result | (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
      senderId route decode query).run state] =
    Pr[= result | (maskedImpl source writer serverCount beaconCount
      senderId route decode blocked query).run state] := by
  cases query with
  | inl request => rfl
  | inr request =>
    by_cases hit : exposed blocked ⟨request, reveal request state.1.1⟩ = true
    · have notFresh : ¬ Fresh blocked prior (note ⟨request, reveal request state.1.1⟩ state.1.2) := by
        simp only [fresh_note, hit, Bool.true_eq_false, and_false, not_false_eq_true]
      have leftZero : Pr[= result | (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
          senderId route decode (.inr request)).run state] = 0 := by
        apply probOutput_eq_zero_of_not_mem_support
        intro supported
        simp only [RawCtxProtocolReveals.sourceImpl, StateT.run, mem_support_pure_iff] at supported
        subst result
        exact notFresh fresh
      have rightZero : Pr[= result | (maskedImpl source writer serverCount beaconCount
          senderId route decode blocked (.inr request)).run state] = 0 := by
        apply probOutput_eq_zero_of_not_mem_support
        intro supported
        simp only [maskedImpl, StateT.run, mem_support_pure_iff] at supported
        subst result
        exact notFresh fresh
      rw [leftZero, rightZero]
    · simp only [maskedImpl, RawCtxProtocolReveals.sourceImpl, StateT.run, hit, Bool.false_eq_true, ↓reduceIte]

private theorem supported_fresh {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (good : σ → Prop)
    (step : ∀ query state result, result ∈ support ((impl query).run state) → good result.2 → good state)
    (client : OracleComp spec α) (state : σ) (result : α × σ)
    (supported : result ∈ support ((simulateQ impl client).run state)) (fresh : good result.2) : good state := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    simpa only [supported] using fresh
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, head, tail⟩
    exact step query state reply head (ih reply.1 reply.2 result tail fresh)

private theorem output_fresh_zero {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (good : σ → Prop)
    (step : ∀ query state result, result ∈ support ((impl query).run state) → good result.2 → good state)
    (client : OracleComp spec α) (state : σ) (bad : ¬ good state) (result : α × σ) (fresh : good result.2) :
    Pr[= result | (simulateQ impl client).run state] = 0 := by
  exact probOutput_eq_zero_of_not_mem_support fun supported =>
    bad (supported_fresh impl good step client state result supported fresh)

private theorem outputs_fresh {ι σ α : Type} {spec : OracleSpec ι}
    (left right : QueryImpl spec (StateT σ ProbComp)) (good : σ → Prop)
    (stepLeft : ∀ query state result, result ∈ support ((left query).run state) → good result.2 → good state)
    (stepRight : ∀ query state result, result ∈ support ((right query).run state) → good result.2 → good state)
    (agree : ∀ query state result, good result.2 →
      Pr[= result | (left query).run state] = Pr[= result | (right query).run state])
    (client : OracleComp spec α) (state : σ) (result : α × σ) (fresh : good result.2) :
    Pr[= result | (simulateQ left client).run state] =
      Pr[= result | (simulateQ right client).run state] := by
  classical
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
    refine tsum_congr ?_
    rintro ⟨reply, nextState⟩
    by_cases nextFresh : good nextState
    · rw [agree query state (reply, nextState) nextFresh, ih reply nextState]
    · rw [output_fresh_zero left good stepLeft (next reply) nextState nextFresh result fresh,
        output_fresh_zero right good stepRight (next reply) nextState nextFresh result fresh,
        mul_zero, mul_zero]

/-- Masking forbidden live replies preserves every complete final native output whose actual private history is fresh. -/
theorem output_fresh {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (blocked prior : List RatchetChain)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (result : Result × NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (fresh : Fresh blocked prior result.2.1.2) :
    Pr[= result | (simulateQ (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
      senderId route decode) client).run state] =
    Pr[= result | (simulateQ (maskedImpl source writer serverCount beaconCount
      senderId route decode blocked) client).run state] := by
  exact outputs_fresh _ _ (fun state => Fresh blocked prior state.1.2)
    (source_step_fresh source writer senderId route decode blocked prior)
    (masked_step_fresh source writer senderId route decode blocked prior)
    (step_agree source writer senderId route decode blocked prior) client state result fresh

/-- The final-fresh event is unconditioned: forbidden disclosures excluded by that event incur no additive probability term. -/
theorem event_fresh {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    {serverCount beaconCount : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (blocked prior : List RatchetChain)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result)
    (state : NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount)
    (event : Result × NativeState Metadata PeerMetadata Identity DhPair KemPair Auxiliary serverCount beaconCount → Prop) :
    Pr[fun result => event result ∧ Fresh blocked prior result.2.1.2 |
      (simulateQ (RawCtxProtocolReveals.sourceImpl source writer serverCount beaconCount
        senderId route decode) client).run state] =
    Pr[fun result => event result ∧ Fresh blocked prior result.2.1.2 |
      (simulateQ (maskedImpl source writer serverCount beaconCount
        senderId route decode blocked) client).run state] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr ?_
  intro result
  by_cases fresh : Fresh blocked prior result.2.1.2
  · simp [fresh, output_fresh source writer senderId route decode blocked prior client state result fresh]
  · simp [fresh]

end BeaconcryptCore.Computational.RawCtxLiveSourceFreshness

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.source_step_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.source_step_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.source_schedule_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.source_schedule_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.masked_step_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.masked_step_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.step_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.step_agree

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.output_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.output_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.event_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxLiveSourceFreshness.event_fresh

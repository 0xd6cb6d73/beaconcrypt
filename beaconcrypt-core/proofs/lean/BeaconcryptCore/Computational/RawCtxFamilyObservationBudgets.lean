import BeaconcryptCore.Computational.FinitePartitionQueryBounds
import BeaconcryptCore.Computational.RawCtxFamilyPrimitiveBudgets
import BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets

/-!
The original finite-family observer's uniform budget is U+64(S+R+H). Its actual opening and sealing adapters each reserve one possible 64-byte shared commitment-cache miss, preserving parser rejection, AEAD failure, optional plaintext/ciphertext and writer failure. Caller coins cost one; private KDF, real public fixed HKDF and live reads add no uniform sampling. These are uniform-query counts, not claims that deterministic cryptographic, parser, lookup or serialization work is free.

The same original all-reply source budget supplies a candidate increment cap S+51R+K+E. The trace retains its entire initial candidate prefix and every duplicate, rejected attempt and actual optional disclosed value. Candidate bounds hold for an arbitrary callback implementation and direct-read flag; uniform bounds use the concrete target-free retained-parent handler. Complete actual family results, role state, chronology, shared primitive state and instrumentation are retained. A reached stopped context must separately supply original outside-client budget provenance and the in-progress operation completion bill; neither follows merely from a Context type. Prior cache/history candidates remain an explicit initial prefix to be counted by that consuming source theorem.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf
open RawCtxFamilyPrimitiveBudgets

/-- The actual fixed native backend spends uniform calls only on its shared commitment-cache misses. -/
theorem native_uniform {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (budget : Nat)
    (bounded : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) budget)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (RawCtxSourceMaterialLabels.nativeImpl source writer) client).run state).IsTotalQueryBound (64 * budget) := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure result => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply (isTotalQueryBound_bind (RawCtxSelectiveChainBudgets.native_uniform source writer query state)
        (fun reply => ih reply.1 _ (bounded.2 reply.1) reply.2)).mono
      have available := bounded.1
      by_cases hash : RawCtxMixedOwner.callKind query = .hash
      all_goals simp [hash] at available ⊢
      all_goals omega

/-- The actual raw opening executor reserves one shared commitment miss and retains all parser and AEAD rejection paths. -/
theorem open_uniform {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxWholeOwner.OpenInput) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ RawCtxMixedOwner.receiveAdapter) (.inr input)).run state).IsTotalQueryBound 64 := by
  change ((simulateQ (RawCtxSourceMaterialLabels.nativeImpl source writer)
    (simulateQ RawCtxMixedOwner.receiveLift
      (simulateQ RawCtxSourceOpen.openLift (RawCtxSourceOpen.openInput input)))).run state).IsTotalQueryBound (64 * 1)
  apply native_uniform
  apply RawCtxMixedOwner.receiveLift_bound
  apply RawCtxSourceOpen.simulate_bound RawCtxSourceOpen.openLift
    (fun query => query.isLeft = true) _ _ 1 (RawCtxSourceOpen.openInput_bounds input).1
  intro query
  cases query <;> exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [RawCtxMixedOwner.receiveKind])

/-- The actual sealing executor reserves one shared commitment miss, including AEAD and writer failure. -/
theorem seal_uniform {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (input : RawCtxSourceSend.SealInput) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((RawCtxSourceMaterialLabels.nativeImpl source writer ∘ₛ RawCtxMixedOwner.sendAdapter) (.inr input)).run state).IsTotalQueryBound 64 := by
  change ((simulateQ (RawCtxSourceMaterialLabels.nativeImpl source writer)
    (simulateQ RawCtxMixedOwner.sendLift
      (simulateQ RawCtxSourceSeal.sealLift (RawCtxSourceSeal.sealInput input)))).run state).IsTotalQueryBound (64 * 1)
  apply native_uniform
  apply RawCtxMixedOwner.sendLift_bound
  apply RawCtxSourceOpen.simulate_bound RawCtxSourceSeal.sealLift
    (fun query => RawCtxSourceSeal.callKind query = .hash) _ _ 1 (RawCtxSourceSeal.sealInput_bound input .hash)
  intro query
  rcases query with aead | (hash | writer)
  all_goals exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [RawCtxMixedOwner.sendKind, RawCtxSourceSeal.callKind])

/-- The source opening adapter keeps its no-material rejection and reserves the same one inner opening. -/
theorem receive_open_uniform {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((RawCtxSourceChainHandles.receiveNative source writer (.inr pending)).run state).IsTotalQueryBound 64 := by
  simp only [RawCtxSourceChainHandles.receiveNative, QueryImpl.apply_compose, RawCtxWholeOwner.adapter]
  split
  · simp [IsTotalQueryBound]
  · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
    exact open_uniform source writer _ state

/-- The source sealing adapter retains the exact source getter arguments and returned optional ciphertext. -/
theorem send_seal_uniform {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (pending : SendSeal RawCtxSourceSend.SealContext) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((RawCtxSourceChainHandles.sendNative source writer (.inr pending)).run state).IsTotalQueryBound 64 := by
  simp only [RawCtxSourceChainHandles.sendNative, QueryImpl.apply_compose, RawCtxSourceSend.adapter,
    bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
  exact seal_uniform source writer _ state

def uniformCost : Class → Nat
  | .coin => 1
  | .seal | .open | .hash => 64
  | _ => 0

set_option backward.isDefEq.respectTransparency false in
/-- Each actual target-free callback has its explicit uniform cost; private KDF and public fixed HKDF evaluations remain real local work. -/
theorem handler_uniform {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
    (query : RawCtxSelectedLiveCompiler.Spec.Domain) (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((RawCtxSelectedParentLive.handler source writer prior entry output reader view query).run state).IsTotalQueryBound
      (uniformCost (liveClass query)) := by
  rcases query with ((kdf | opening) | ((kdf | sealing) | (coin | (hash | hkdf)))) | read
  all_goals simp only [liveClass, primitiveClass, uniformCost]
  case inl.inl.inr => exact receive_open_uniform source writer _ state
  case inl.inr.inl.inr => exact send_seal_uniform source writer _ state
  case inl.inr.inr.inr.inl =>
    simp only [RawCtxSelectedParentLive.handler, QueryImpl.apply_compose, RawCtxServerServices.publicLift]
    rw [_root_.simulateQ_spec_query]
    change ((RawCtxMixedShared.sharedImpl source.crypto writer (RawCtxSourceHkdf.kdfImpl source)
      (.inr (.inr (.inr (.inl hash))))).run state).IsTotalQueryBound 64
    simpa only [RawCtxMixedOwner.callKind, if_true, Nat.mul_one] using
      RawCtxSelectiveChainBudgets.native_uniform source writer (.inr (.inr (.inr (.inl hash)))) state
  case inl.inr.inr.inl =>
    simp only [RawCtxSelectedParentLive.handler, QueryImpl.apply_compose, RawCtxServerServices.publicLift]
    rw [_root_.simulateQ_spec_query]
    change ((fun value => (value, state)) <$> (liftM (unifSpec.query coin) : ProbComp _)).IsTotalQueryBound 1
    simp [IsTotalQueryBound]
  all_goals simp [RawCtxSelectedParentLive.handler, RawCtxSelectedParentSource.labelReceive,
    RawCtxSelectedParentSource.labelSend, IsTotalQueryBound]

/-- Candidate recording and the sticky read flag add no hidden random calls to an actual callback. -/
theorem observed_uniform {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
    (query : RawCtxSelectedLiveCompiler.Spec.Domain) (state : RawCtxSelectedParentLive.State Auxiliary) :
    ((RawCtxSelectedParentReadMask.observed source writer prior entry output reader view query).run state).IsTotalQueryBound
      (uniformCost (liveClass query)) := by
  simpa only [RawCtxSelectedParentReadMask.observed, RawCtxFlaggedQueryTrace.trace, StateT.run,
    bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    handler_uniform source writer prior entry output reader view query state.1.1

private instance : Fintype Class :=
  ⟨{.kdf, .seal, .open, .coin, .hash, .hkdf, .read}, by intro selected; cases selected <;> simp⟩

/-- The complete adaptive target-free continuation pays the exact class-weighted coin and commitment bill, retaining all private trace state. -/
theorem complete_uniform {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
    (client : OracleComp RawCtxSelectedLiveCompiler.Spec Result) (budget : Class → Nat)
    (bounded : ∀ selected, client.IsQueryBoundP (fun query => liveClass query = selected) (budget selected))
    (state : RawCtxSelectedParentLive.State Auxiliary) :
    ((simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view) client).run state).IsTotalQueryBound
      (budget .coin + 64 * (budget .seal + budget .open + budget .hash)) := by
  have cap := FinitePartitionQueryBounds.weighted_bound liveClass uniformCost budget
    (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view)
    (fun _ => True) client bounded
    (fun query state => (observed_uniform source writer prior entry output reader view query state).isQueryBoundP) state
  have enumeration : (Finset.univ : Finset Class) = {.kdf, .seal, .open, .coin, .hash, .hkdf, .read} := rfl
  simpa [enumeration, uniformCost, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    IsTotalQueryBound, IsQueryBoundP] using cap

def candidateCost : Class → Nat
  | .kdf | .hkdf | .read => 1
  | _ => 0

/-- Only actual known private inputs, real public HKDF inputs and optional disclosed values add candidate entries, at most one per callback. -/
theorem inputs_length (query : RawCtxSelectedLiveCompiler.Spec.Domain) :
    (RawCtxSelectedLiveCompiler.inputs query).length ≤ candidateCost (liveClass query) := by
  rcases query with ((kdf | opening) | ((kdf | sealing) | (coin | (hash | hkdf)))) | read
  all_goals simp only [RawCtxSelectedLiveCompiler.inputs, RawCtxSelectedAliasPrimitives.inputs,
    liveClass, primitiveClass, candidateCost]
  case inl.inl.inl => exact RawCtxSelectedQueryTrace.inputs_bound (.inl kdf)
  case inl.inr.inl.inl => exact RawCtxSelectedQueryTrace.inputs_bound (.inl kdf)
  case inl.inr.inr.inr.inr => exact RawCtxSelectedPublicTrace.inputs_bound (.inr (.inr hkdf))
  case inr => exact RawCtxSelectedLiveRead.reply_length read.1 (RawCtxSelectedLiveRead.labelRead read.1 read.2)
  all_goals simp [RawCtxSelectedQueryTrace.inputs, RawCtxSelectedPublicTrace.inputs]

/-- Every supported complete candidate trace retains its initial prefix and charges the three actual candidate-producing classes, including repetitions and rejected operations. -/
theorem trace_length {State Result : Type}
    (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT State ProbComp))
    (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
    (client : OracleComp RawCtxSelectedLiveCompiler.Spec Result) (budget : Class → Nat)
    (bounded : ∀ selected, client.IsQueryBoundP (fun query => liveClass query = selected) (budget selected))
    (state : (State × List RootOutput) × Bool) (result : Result × ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct) client).run state)) :
    result.2.1.2.length ≤ state.1.2.length + (budget .kdf + budget .hkdf + budget .read) := by
  induction client using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Nat.le_add_right _ _
  | query_bind query next ih =>
      simp only [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      simp only [RawCtxFlaggedQueryTrace.trace, StateT.run, bind_assoc, pure_bind] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, _, tailSupport⟩ := supported
      have tail := ih reply.1 (fun selected => if liveClass query = selected then budget selected - 1 else budget selected)
        (fun selected => (bounded selected).2 reply.1) _ result tailSupport
      have head := inputs_length query
      have kdf := (bounded .kdf).1
      have hkdf := (bounded .hkdf).1
      have read := (bounded .read).1
      simp only [List.length_append] at tail
      cases classified : liveClass query
      all_goals simp [classified, candidateCost] at head tail kdf hkdf read
      all_goals try omega
      all_goals simpa only [head, List.length_nil, Nat.add_zero] using tail

variable {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type} {serverCount beaconCount : Nat}

/-- The actual finite-family observer pays U+64(S+R+H), derived from the original adaptive source budget with every read and callback retained. -/
theorem source_uniform
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (entry : RawCtxSelectedParentEntry.Entry)
    (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxGenericFamilyLive.State RawCtxSelectedChain.Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : RawCtxSelectedParentLive.State Auxiliary) :
    ((simulateQ (RawCtxSelectedParentReadMask.observed source writer prior entry output reader view)
      ((simulateQ (RawCtxFamilySourceFreshness.compiler RawCtxSelectedAliasCompiler.calls RawCtxSelectedAliasCompiler.publicForward
        senderId route decode) client).run state)).run primitive).IsTotalQueryBound
      (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  exact complete_uniform source writer prior entry output reader view _ (fun selected => sourceCost selected budget)
    (source_class senderId route decode client budget bounded state) primitive

/-- The actual family continuation retains all prior candidates and adds at most S+51R+K+E, without dropping duplicate guesses or failed attempts. -/
theorem source_candidates {State : Type}
    (handler : QueryImpl RawCtxSelectedLiveCompiler.Spec (StateT State ProbComp))
    (direct : RawCtxSelectedLiveCompiler.Spec.Domain → Bool)
    (senderId : Metadata → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec serverCount beaconCount) Result)
    (budget : RawCtxRevealBudgets.Budget) (bounded : RawCtxRevealBudgets.Bounded client budget)
    (state : RawCtxGenericFamilyLive.State RawCtxSelectedChain.Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (primitive : (State × List RootOutput) × Bool)
    (result : (Result × RawCtxGenericFamilyLive.State RawCtxSelectedChain.Kernel Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) ×
      ((State × List RootOutput) × Bool))
    (supported : result ∈ support ((simulateQ (RawCtxFlaggedQueryTrace.trace handler RawCtxSelectedLiveCompiler.inputs direct)
      ((simulateQ (RawCtxFamilySourceFreshness.compiler RawCtxSelectedAliasCompiler.calls RawCtxSelectedAliasCompiler.publicForward
        senderId route decode) client).run state)).run primitive)) :
    result.2.1.2.length ≤ primitive.1.2.length + ((budget.1 .send + 51 * budget.1 .raw) + budget.1 .hkdf + budget.2) := by
  exact trace_length handler direct _ (fun selected => sourceCost selected budget)
    (source_class senderId route decode client budget bounded state) primitive result supported

end BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.native_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.open_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.open_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.seal_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.seal_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.receive_open_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.receive_open_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.send_seal_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.send_seal_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.handler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.handler_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.observed_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.observed_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.complete_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.complete_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.inputs_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.inputs_length
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.trace_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.trace_length
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.source_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.source_uniform
/-- info: 'BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.source_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxFamilyObservationBudgets.source_candidates

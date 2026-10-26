import BeaconcryptCore.Computational.RawCtxSelectedAcceptanceOrigins

/-!
Actual selected-source opening replies agree with the plaintext of every matching prior successful CTX production. This uses ordinary functional AEAD correctness inside the existing interpreter, not a protocol-origin or primitive security assumption. The full tuple still does not identify the required role, installation or cryptographic session.
-/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins
open CtxRomAuth AdaptiveCtxReceive
open RawCtxSelectedAuthenticationObserver

def HistoryCorrect (c : Pqxdh.Crypto) (key : CtxKey) (history : List CtxSuccessfulSeal) : Prop :=
  ∀ entry ∈ history, c.aeadOpen key.toList entry.input.nonce.toList entry.input.context.ad.bytes
    entry.record.body entry.record.tag = some entry.input.plaintext

def AttemptCorrect (decode : RawDecoder) (attempt : Attempt) : Prop :=
  ∀ target, decode attempt.raw = some target → ∀ entry ∈ attempt.sealsBefore,
    target.toLegacy.sameFullTupleAsSuccessfulSeal entry → attempt.plaintext ≠ none →
      attempt.plaintext = some entry.input.plaintext

def LocalGood (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (observer : State) (localState : AdaptiveCtxSharedHash.Local) : Prop :=
  observer.seals = localState.successfulSeals ∧
    HistoryCorrect c key observer.seals ∧ ∀ attempt ∈ observer.attempts, AttemptCorrect decode attempt

def Good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  LocalGood decode c key state.1 state.2.selected.1

/-- Exact matched frame fields and the ordinary issued-ciphertext correctness invariant determine the actual successful optional opening plaintext. -/
theorem matching_open (c : Pqxdh.Crypto) (key : CtxKey) (history : List CtxSuccessfulSeal)
    (correct : HistoryCorrect c key history) (target : CtxUnclaimedAcceptance.Target)
    (entry : CtxSuccessfulSeal) (member : entry ∈ history)
    (same : target.toLegacy.sameFullTupleAsSuccessfulSeal entry)
    (expected : CtxDigest) (plaintext : Pqxdh.Bytes)
    (opened : AdaptiveCtxCanonical.targetOpen c key target expected = some plaintext) :
    plaintext = entry.input.plaintext := by
  unfold AdaptiveCtxCanonical.targetOpen at opened
  split at opened
  · obtain ⟨nonce, ad, record⟩ := AdaptiveCtxReplayDictionary.fullTuple_fields target entry same
    exact Option.some.inj (opened.symm.trans (by
      simpa only [nonce, ad, show target.record.body = entry.record.body from congrArg Pqxdh.RecordCipher.body record,
        show target.record.tag = entry.record.tag from congrArg Pqxdh.RecordCipher.tag record] using correct entry member))
  · cases opened

/-- Every actual raw reply keeps the selected sealing history and makes any full-tuple match return the exact originally sealed plaintext, including malformed and rejected attempts. -/
theorem raw_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) (before : State) (entry : AdaptiveCtxSharedHash.Local) (cache : CtxRO.QueryCache)
    (good : LocalGood decode c key before entry)
    (result : (Option Pqxdh.Bytes × AdaptiveCtxSharedHash.Local) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl
      (AdaptiveCtxSharedHash.localRaw decode c key raw entry)).run cache)) :
    LocalGood decode c key (step (.inl (.inr raw)) result.1.1 before) result.1.2 := by
  cases parsed : decode raw with
  | none =>
    simp only [AdaptiveCtxSharedHash.localRaw, parsed, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    simpa [LocalGood, step, AttemptCorrect, parsed] using good
  | some target =>
    simp only [AdaptiveCtxSharedHash.localRaw, parsed, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
    rcases supported with ⟨lookup, _, rfl⟩
    refine ⟨good.1, good.2.1, ?_⟩
    simp only [step, List.mem_cons, forall_eq_or_imp]
    refine ⟨fun actual decoded issued member same present => ?_, good.2.2⟩
    cases Option.some.inj (parsed.symm.trans decoded)
    obtain ⟨plaintext, opened⟩ := Option.ne_none_iff_exists'.mp present
    exact opened.trans (congrArg some (matching_open c key before.seals good.2.1 target issued member same lookup.1 plaintext opened))

/-- A genuine successful seal extends the interpreter and observer histories with the same ciphertext and its ordinary correct plaintext; nonce refusal preserves both. -/
theorem seal_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (input : CtxSealInput) (before : State) (entry : AdaptiveCtxSharedHash.Local) (cache : CtxRO.QueryCache)
    (good : LocalGood decode c key before entry)
    (result : (Option CtxRomRecord × AdaptiveCtxSharedHash.Local) × CtxRO.QueryCache)
    (supported : result ∈ support ((simulateQ AdaptiveCtxSharedHash.hashImpl
      (AdaptiveCtxSharedHash.localSeal c key input entry)).run cache)) :
    LocalGood decode c key (step (.inl (.inl (.inr (.inr input)))) result.1.1 before) result.1.2 := by
  by_cases used : input.nonce ∈ entry.usedNonces
  · simp only [AdaptiveCtxSharedHash.localSeal, used, ite_true, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact good
  · simp only [AdaptiveCtxSharedHash.localSeal, used, ite_false, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at supported
    rcases supported with ⟨lookup, _, rfl⟩
    simpa [LocalGood, step, HistoryCorrect, c.aead_open_seal] using good

private theorem state_bind_apply {X Y σ : Type} {m : Type → Type} [Monad m]
    (head : StateT σ m X) (tail : X → StateT σ m Y) (state : σ) :
    (head >>= tail) state = (head state >>= fun result => tail result.1 result.2) := rfl

/-- Every actual selected or dynamically known-key callback preserves the complete matched-plaintext invariant. Known-key aliases remain permitted and all cache effects are retained. -/
theorem step_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain) (state : State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good decode c key state)
    (result : AdaptiveCtxDynamicKnownKeys.Spec.Range query × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((observed true decode c key query).run state)) :
    Good decode c key result.2 := by
  simp only [observed, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨actual, reached, rfl⟩
  cases query with
  | inr known =>
    simp only [AdaptiveCtxDynamicKnownKeys.sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
    rcases reached with ⟨localResult, _, rfl⟩
    exact good
  | inl request =>
    simp only [AdaptiveCtxDynamicKnownKeys.sourceImpl, StateT.run, mem_support_bind_iff, mem_support_pure_iff] at reached
    rcases reached with ⟨localResult, localReached, rfl⟩
    simp only [AdaptiveCtxSharedModes.localImpl, ite_true, simulateQ_bind, simulateQ_pure, state_bind_apply,
      mem_support_bind_iff] at localReached
    rcases localReached with ⟨localStep, reached, rfl⟩
    rcases request with (coin | (hash | input)) | raw
    · simp only [StateT.run, AdaptiveCtxSharedHash.localImpl, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        state_bind_apply, mem_support_bind_iff] at reached
      rcases reached with ⟨answer, _, rfl⟩
      exact good
    · simp only [StateT.run, AdaptiveCtxSharedHash.localImpl, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        state_bind_apply, mem_support_bind_iff] at reached
      rcases reached with ⟨answer, _, rfl⟩
      exact good
    · exact seal_good decode c key input state.1 state.2.selected.1 state.2.cache good localStep reached
    · exact raw_good decode c key raw state.1 state.2.selected.1 state.2.cache good localStep reached

/-- The concrete invariant holds through the complete adaptive dynamic-key schedule, preserving every original selected and known-key history and shared cache. -/
theorem schedule_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (good : Good decode c key state)
    (result : Result × (State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ (observed true decode c key) client).run state)) :
    Good decode c key result.2 := by
  exact simulateQ_run_preservesInv (observed true decode c key) (Good decode c key)
    (step_good decode c key) client state good result supported

/-- Empty ordinary endpoint histories satisfy the concrete invariant for every selected key, without a distribution or independence premise. -/
theorem initial_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey) :
    Good decode c key (initialState, AdaptiveCtxDynamicKnownKeys.initialSource) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro entry member
    cases member
  · intro attempt member
    cases member

/-- Interpreting the unchanged executable monitor by the real dynamic CTX source yields the same complete matched-plaintext invariant. -/
theorem monitored_good (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    {Result : Type} (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (state : State × AdaptiveCtxDynamicKnownKeys.SourceState) (good : Good decode c key state)
    (result : (Result × State) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true decode c key)
      (monitor client state.1)).run state.2)) :
    Good decode c key (result.1.2, result.2) := by
  have actual : PqxdhSelectedStateInterpreter.pair result ∈ support
      ((simulateQ (observed true decode c key) client).run state) := by
    rw [← monitored_program true decode c key client state, support_map]
    exact ⟨result, supported, rfl⟩
  exact schedule_good decode c key client state good _ actual

open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry

/-- The literal adaptive source production audit inherits the invariant from its checked erasure into the unchanged executable monitor. -/
theorem audited_good {M P I D K Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxSelectedProductionAudit.Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder read) c key (state.observer, component))
    (result : (Option Result × RawCtxSelectedProductionAudit.Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder read) c key)
      (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state)).run component)) :
    Good (RawCtxUniversalDecoder.decoder read) c key (result.1.2.observer, result.2) := by
  have actual : (RawCtxSelectedProductionAudit.erase result.1, result.2) ∈ support
      ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
        (monitor (RawCtxSelectedFamilyLiveCompiler.client source writer prior parent target nonce next sender route read
          original state.front) state.observer)).run component) := by
    rw [← RawCtxSelectedProductionAudit.client_erase, simulateQ_map, StateT.run_map, support_map]
    exact ⟨result, supported, rfl⟩
  exact monitored_good (RawCtxUniversalDecoder.decoder read) c key _ (state.observer, component) good _ actual

/-- Actual later source calls retain every prior opening receipt; in particular they retain its original optional plaintext and the sealing history that existed at that attempt. -/
theorem trace_attempts {M P I D K : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    {before after : State} {records : List (RawCtxSelectedProductionAudit.Record M P I D K S B)}
    (edges : RawCtxSelectedProductionAudit.Edges before records after)
    (actual : ∀ record ∈ records, RawCtxSelectedProductionAudit.Recorded source writer prior parent target nonce next sender route read record) :
    before.attempts ⊆ after.attempts := by
  induction edges with
  | nil => exact List.Subset.refl _
  | cons record rest ih =>
    exact fun attempt member => ih (fun later found => actual later (List.mem_cons_of_mem record found))
      (RawCtxSelectedAcceptedRecord.monitor_attempts
        (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read record.query record.roles)
        record.before (record.reply, record.after) (actual record List.mem_cons_self) member)

/-- At every actual chronological query position, the interpreted source supplies correct matched plaintext and strict earlier production origins together, preserving the initial receipt prefix. -/
theorem current_correct {M P I D K Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxSelectedProductionAudit.Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder read) c key (state.observer, component))
    (result : (Option Result × RawCtxSelectedProductionAudit.Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder read) c key)
      (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state)).run component))
    (preceding suffix : List (RawCtxSelectedProductionAudit.Record M P I D K S B))
    (current : RawCtxSelectedProductionAudit.Record M P I D K S B)
    (position : result.1.2.records = state.records ++ (preceding ++ current :: suffix)) :
    RawCtxSelectedProductionAudit.Recorded source writer prior parent target nonce next sender route read current ∧
      (∀ attempt ∈ current.after.attempts, AttemptCorrect (RawCtxUniversalDecoder.decoder read) attempt) ∧
      ∀ entry ∈ current.before.seals, RawCtxSelectedAcceptanceOrigins.PriorProduction
        source writer prior parent target nonce next sender route read state.observer preceding entry := by
  have originalSupport : result.1 ∈ support (RawCtxSelectedProductionAudit.client
      source writer prior parent target nonce next sender route read original state) := by
    apply support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
      _ component
    rw [StateT.run'_eq, support_map]
    exact ⟨result, supported, rfl⟩
  have contextual := RawCtxSelectedAcceptanceOrigins.current_record source writer prior parent target nonce next sender route read
    original state result.1 originalSupport preceding suffix current position
  refine ⟨contextual.1, ?_, contextual.2.2⟩
  obtain ⟨generated, appended, edges, actual⟩ := RawCtxSelectedProductionAudit.client_trace
    source writer prior parent target nonce next sender route read original state result.1 originalSupport
  have same : generated = preceding ++ current :: suffix := List.append_cancel_left (appended.symm.trans position)
  rw [same] at edges actual
  exact fun attempt member => (audited_good source writer prior parent target nonce next sender route read c key
    original state component good result supported).2.2 attempt
      (trace_attempts source writer prior parent target nonce next sender route read
        (RawCtxSelectedProductionAudit.edges_cut preceding suffix current edges).2
        (fun later found => actual later (List.mem_append_right _ (List.mem_cons_of_mem current found))) member)

/-- The component target retains the exact parsed C/T/commitment payload, without asserting canonical Cap'n Proto serialization. -/
theorem record_payload (frame : RawCtxReceive.DecodedFrame) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload frame.payload = some slices) :
    (RawCtxKeyFreeDecoder.record frame slices parsed).encode = frame.payload := by
  exact (RawCtxFrameDecoding.fromPayload_record frame.payload slices parsed).choose_spec.2.2.2.2.2.2.2

/-- An actual matched selected acceptance has the exact prior production's plaintext, AD, sequence, sender and parsed ciphertext payload. These fields still do not identify its installation or cryptographic session. -/
theorem matching_plaintext {P : Type}
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P)
    (decrypted : RawCtxWholeOwner.Decrypted) (before after : State)
    (matching : RawCtxSelectedAcceptanceOrigins.Matching prior parent target nonce next read bytes owner decrypted before after)
    (correct : ∀ attempt ∈ after.attempts, AttemptCorrect (RawCtxUniversalDecoder.decoder read) attempt) :
    ∃ entry ∈ before.seals, decrypted.plaintext = entry.input.plaintext ∧
      owner.associatedData = entry.input.context.ad.bytes ∧
      decrypted.sequence.val = entry.input.context.ad.seq ∧ decrypted.keyId.val = entry.input.context.ad.sid ∧
      ∃ frame, read bytes = some frame ∧ frame.payload = entry.record.encode := by
  obtain ⟨frame, pending, actualNonce, width, slices, parsed, plaintext, nonempty, decoded, valid,
    reached, getter, value, observed, entry, member, same⟩ := matching
  have receipt : AttemptCorrect (RawCtxUniversalDecoder.decoder read)
      ⟨RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope actualNonce ⟨bytes, frame, owner.associatedData⟩ width),
        some plaintext, before.seals⟩ := correct _ (by rw [observed]; exact List.mem_cons_self)
  have opened : some plaintext = some entry.input.plaintext := receipt _
    (RawCtxUniversalDecoder.decoder_pack read
      (RawCtxUniversalDecoder.envelope actualNonce ⟨bytes, frame, owner.associatedData⟩ width)
      frame slices nonempty decoded parsed) entry member same (Option.some_ne_none _)
  cases value
  exact ⟨entry, member, Option.some.inj opened, congrArg Pqxdh.RecordAD.bytes same.2.1,
    congrArg Pqxdh.RecordAD.seq same.2.1, congrArg Pqxdh.RecordAD.sid same.2.1,
    frame, decoded, (record_payload frame slices parsed).symm.trans same.2.2⟩

/-- A matched accepted record at an actual adaptive source position has the exact earlier source production's plaintext and decoded frame fields. The retained initial prefix and possible failed writer remain explicit in that production witness. -/
theorem current_matching {M P I D K Result : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (c : Pqxdh.Crypto) (key : CtxKey)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : RawCtxSelectedProductionAudit.Audit M P I D K S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState)
    (good : Good (RawCtxUniversalDecoder.decoder read) c key (state.observer, component))
    (result : (Option Result × RawCtxSelectedProductionAudit.Audit M P I D K S B) × AdaptiveCtxDynamicKnownKeys.SourceState)
    (supported : result ∈ support ((simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true
      (RawCtxUniversalDecoder.decoder read) c key)
      (RawCtxSelectedProductionAudit.client source writer prior parent target nonce next sender route read original state)).run component))
    (preceding suffix : List (RawCtxSelectedProductionAudit.Record M P I D K S B))
    (current : RawCtxSelectedProductionAudit.Record M P I D K S B)
    (position : result.1.2.records = state.records ++ (preceding ++ current :: suffix))
    (bytes : Pqxdh.Bytes) (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel P)
    (decrypted : RawCtxWholeOwner.Decrypted)
    (matching : RawCtxSelectedAcceptanceOrigins.Matching prior parent target nonce next read bytes owner decrypted current.before current.after) :
    ∃ entry ∈ current.before.seals, RawCtxSelectedAcceptanceOrigins.PriorProduction
        source writer prior parent target nonce next sender route read state.observer preceding entry ∧
      decrypted.plaintext = entry.input.plaintext ∧ owner.associatedData = entry.input.context.ad.bytes ∧
      decrypted.sequence.val = entry.input.context.ad.seq ∧ decrypted.keyId.val = entry.input.context.ad.sid ∧
      ∃ frame, read bytes = some frame ∧ frame.payload = entry.record.encode := by
  have contextual := current_correct source writer prior parent target nonce next sender route read c key original
    state component good result supported preceding suffix current position
  obtain ⟨entry, member, fields⟩ := matching_plaintext prior parent target nonce next read bytes owner
    decrypted current.before current.after matching contextual.2.1
  exact ⟨entry, member, contextual.2.2 entry member, fields⟩

end BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.matching_open' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.matching_open
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.raw_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.raw_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.seal_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.seal_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.step_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.step_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.schedule_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.initial_good' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.initial_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.monitored_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.monitored_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.audited_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.audited_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.trace_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.trace_attempts
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.current_correct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.current_correct
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.record_payload' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.record_payload
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.matching_plaintext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.matching_plaintext
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.current_matching' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedPlaintextOrigins.current_matching

import BeaconcryptCore.Computational.RawCtxSelectedAuthenticationObserver

/-!
Concrete selected source opening observations use the actual getter, private context framing and returned optional API plaintext. The observer stores the same native target before the reply and keeps successful accepted attempts through every later continuation. Original publication and byte-freshness predicates remain additional event conjuncts; neither predicate alone asserts an authentication failure.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedMessageKey RawCtxInterpretedArguments
open CtxRomAuth AdaptiveCtxReceive
open RawCtxSelectedAuthenticationObserver

/-- A reached hidden-material source callback is exactly its original API reply plus the concrete selected raw-attempt observation. -/
theorem selected_service (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (present : openArguments pending = some ⟨.hidden nonce, sequence, context⟩)
    (width : context.associatedData.length = 153) (before : State) :
    monitor (RawCtxSelectedOpenConsumer.service slot read expected pending) before =
      (do let reply ← AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inr
            (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width))))
          pure (RawCtxSharedOpeningConsumer.apiReply sequence context reply,
            step (.inl (.inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width)))) reply before)) := by
  simp only [RawCtxSelectedOpenConsumer.service, present, RawCtxUniversalOpening.call, dite_eq_left width]
  simp only [monitor, simulateQ_map, StateT.run_map, simulateQ_spec_query]
  simp only [handler, StateT.run, map_bind, map_pure]

/-- A successful source API callback contains exactly the actual challenger plaintext, original sender/sequence and unchanged framed raw request in the attempted-opening history. -/
theorem selected_service_receipt (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (present : openArguments pending = some ⟨.hidden nonce, sequence, context⟩)
    (width : context.associatedData.length = 153) (before : State)
    (decrypted : RawCtxWholeOwner.Decrypted) (after : State)
    (supported : (.Some decrypted, after) ∈ support
      (monitor (RawCtxSelectedOpenConsumer.service slot read expected pending) before)) :
    ∃ plaintext, decrypted = ⟨plaintext, context.frame.sender, sequence⟩ ∧
      after = step (.inl (.inr (RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width))))
        (some plaintext) before := by
  rw [selected_service slot read expected pending nonce sequence context present width before] at supported
  simp only [mem_support_bind_iff, mem_support_pure_iff] at supported
  rcases supported with ⟨reply, _, equal⟩
  cases reply with
  | none => cases equal
  | some plaintext =>
    cases equal
    exact ⟨plaintext, rfl, rfl⟩

/-- A source API acceptance with an authentication tuple absent before this actual call produces the concrete ordinary component winner. The plaintext comes from the supported callback output. -/
theorem selected_service_forgery (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (present : openArguments pending = some ⟨.hidden nonce, sequence, context⟩)
    (width : context.associatedData.length = 153) (before : State)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (slices : RawCtxFrameDecoding.Slices) (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices)
    (decrypted : RawCtxWholeOwner.Decrypted) (after : State)
    (supported : (.Some decrypted, after) ∈ support
      (monitor (RawCtxSelectedOpenConsumer.service slot read expected pending) before))
    (fresh : ∀ entry ∈ before.seals, ¬(RawCtxKeyFreeDecoder.target nonce context.frame.sequence
      context.frame context.associatedData slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    won (RawCtxUniversalDecoder.decoder read) after = true := by
  obtain ⟨plaintext, _, rfl⟩ := selected_service_receipt slot read expected pending nonce sequence context present width before decrypted after supported
  apply (won_iff _ _).mpr
  refine ⟨⟨RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width), some plaintext, before.seals⟩,
    List.mem_cons_self, _, ?_, Option.some_ne_none _, fresh⟩
  exact RawCtxUniversalDecoder.decoder_pack read (RawCtxUniversalDecoder.envelope nonce context width)
    context.frame slices nonempty decoded parsed

/-- Every actual component operation preserves all earlier attempted-opening receipts, independently of later seals and all optional failures. -/
theorem step_attempts (query : AdaptiveCtxDynamicKnownKeys.Spec.Domain)
    (reply : AdaptiveCtxDynamicKnownKeys.Spec.Range query) (before : State) :
    before.attempts ⊆ (step query reply before).attempts := by
  cases query with
  | inr known => exact List.Subset.refl _
  | inl query =>
    cases query with
    | inr raw => exact fun _ present => List.mem_cons_of_mem _ present
    | inl query =>
      cases query with
      | inl coin => exact List.Subset.refl _
      | inr query =>
        cases query with
        | inl hash => exact List.Subset.refl _
        | inr input => cases reply <;> exact List.Subset.refl _

/-- An arbitrary complete continuation retains every actual accepted-attempt receipt, so adaptive stopping or later chosen sealing cannot remove the event. -/
theorem monitor_attempts {Result : Type} (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (before : State) (result : Result × State) (supported : result ∈ support (monitor client before)) :
    before.attempts ⊆ result.2.attempts := by
  induction client using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [monitor, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact List.Subset.refl _
  | query_bind query continuation ih =>
    rw [monitor_query] at supported
    simp only [mem_support_bind_iff] at supported
    obtain ⟨reply, _, reached⟩ := supported
    exact fun _ present => ih reply (step query reply before) result reached (step_attempts query reply before present)

/-- The same concrete winner persists through every later actual component continuation; its freshness history is the one recorded at the original attempt. -/
theorem monitor_won {Result : Type} (decode : RawDecoder) (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (before : State) (winning : won decode before = true) (result : Result × State)
    (supported : result ∈ support (monitor client before)) : won decode result.2 = true := by
  obtain ⟨attempt, present, target, parsed, opened, fresh⟩ := (won_iff decode before).mp winning
  exact (won_iff decode result.2).mpr ⟨attempt, monitor_attempts client before result supported present,
    target, parsed, opened, fresh⟩

/-- Erasing only the added observer recovers the actual native source opening, including optional plaintext and the complete shared source cache. All reached context facts are the original owner-prelude facts. -/
theorem native_service_erase {A : Type} (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (key : RootOutput) (c : Pqxdh.Crypto)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (ambient : A) (state : AdaptiveCtxDynamicKnownKeys.SourceState) (before : State)
    (nonempty : pending.context.raw.isEmpty = false) (decoded : read pending.context.raw = some pending.context.frame)
    (valid : RawCtxReceive.ValidFrame expected pending.context.associatedData pending.context.frame)
    (prepared : RawCtxInterpretedOpening.sequence pending = ok pending.context.frame.sequence)
    (slices : RawCtxFrameDecoding.Slices) (parsed : RawCtxFrameDecoding.fromPayload pending.context.frame.payload = some slices) :
    (simulateQ (RawCtxSharedPrimitive.nativeImpl c kdf)
      (RawCtxSourceOpen.ownerAdapter (.inr (RawCtxInterpretedOpening.toNative
        (RawCtxInterpretedOpening.mapOpening (interpret key) pending))))).run (ambient, state.cache) =
      (fun result => (result.1.1, (ambient, result.2.cache))) <$>
        (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key)
          (monitor (RawCtxSelectedOpenConsumer.service slot read expected pending) before)).run state := by
  rw [RawCtxSelectedOpenConsumer.service_source slot read expected key c kdf pending ambient state
    nonempty decoded valid prepared slices parsed]
  have erase := congrArg (fun work =>
    (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) c key) work).run state)
    (monitor_erase (RawCtxSelectedOpenConsumer.service slot read expected pending) before)
  simp only [simulateQ_map, StateT.run_map] at erase
  rw [← erase]
  simp only [Functor.map_map]

/-- A concrete native record receipt retains original network context, actual plaintext and the authentication history from that attempt. -/
def RecordEvent (read : RawCtxReceive.FrameDecoder) (observations : State) : Prop :=
  ∃ (nonce : NonceOutput) (context : RawCtxWholeOwner.OpenContext)
    (width : context.associatedData.length = 153) (slices : RawCtxFrameDecoding.Slices)
    (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices)
    (plaintext : Pqxdh.Bytes) (history : List CtxSuccessfulSeal),
    ⟨RawCtxUniversalDecoder.pack (RawCtxUniversalDecoder.envelope nonce context width), some plaintext, history⟩ ∈ observations.attempts ∧
    context.raw.isEmpty = false ∧ read context.raw = some context.frame ∧
    ∀ entry ∈ history, ¬(RawCtxKeyFreeDecoder.target nonce context.frame.sequence context.frame
      context.associatedData slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry

/-- Successful selected source opening supplies the actual native accepted-record event, including the original context and exact optional challenger plaintext. -/
theorem selected_service_record (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (present : openArguments pending = some ⟨.hidden nonce, sequence, context⟩)
    (width : context.associatedData.length = 153) (before : State)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (slices : RawCtxFrameDecoding.Slices) (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices)
    (decrypted : RawCtxWholeOwner.Decrypted) (after : State)
    (supported : (.Some decrypted, after) ∈ support
      (monitor (RawCtxSelectedOpenConsumer.service slot read expected pending) before))
    (fresh : ∀ entry ∈ before.seals, ¬(RawCtxKeyFreeDecoder.target nonce context.frame.sequence
      context.frame context.associatedData slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    RecordEvent read after := by
  obtain ⟨plaintext, _, rfl⟩ := selected_service_receipt slot read expected pending nonce sequence context present width before decrypted after supported
  exact ⟨nonce, context, width, slices, parsed, plaintext, before.seals, List.mem_cons_self, nonempty, decoded, fresh⟩

/-- Every source-shaped accepted-record receipt is an ordinary observer win, with the same full CTX tuple. -/
theorem record_wins (read : RawCtxReceive.FrameDecoder) (observations : State)
    (recorded : RecordEvent read observations) : won (RawCtxUniversalDecoder.decoder read) observations = true := by
  obtain ⟨nonce, context, width, slices, parsed, plaintext, history, present, nonempty, decoded, fresh⟩ := recorded
  exact (won_iff _ _).mpr ⟨_, present, _, RawCtxUniversalDecoder.decoder_pack read
    (RawCtxUniversalDecoder.envelope nonce context width) context.frame slices nonempty decoded parsed,
    Option.some_ne_none _, fresh⟩

/-- The exact original source receipt remains recorded after every adaptive continuation; its original network bytes and attempt-time freshness history do not change. -/
theorem record_persists {Result : Type} (read : RawCtxReceive.FrameDecoder)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) (before : State)
    (recorded : RecordEvent read before) (result : Result × State)
    (supported : result ∈ support (monitor client before)) : RecordEvent read result.2 := by
  obtain ⟨nonce, context, width, slices, parsed, plaintext, history, present, nonempty, decoded, fresh⟩ := recorded
  exact ⟨nonce, context, width, slices, parsed, plaintext, history,
    monitor_attempts client before result supported present, nonempty, decoded, fresh⟩

/-- Pure native result construction changes no observer state or oracle effect. -/
theorem monitor_map {X Y : Type} (f : X → Y) (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec X) (before : State) :
    monitor (f <$> client) before = (fun result => (f result.1, result.2)) <$> monitor client before := by
  simp only [monitor, simulateQ_map, StateT.run_map]

/-- The actual cached/future finish followed by whole-owner publication preserves the same successful API reply and recorded source forgery. -/
theorem selected_publication_record {Metadata : Type}
    (slot : Nat) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64)
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Slot RawCtxWholeOwner.OpenContext)
    (nonce : NonceOutput) (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (present : openArguments pending = some ⟨.hidden nonce, sequence, context⟩)
    (width : context.associatedData.length = 153) (before : State)
    (nonempty : context.raw.isEmpty = false) (decoded : read context.raw = some context.frame)
    (slices : RawCtxFrameDecoding.Slices) (parsed : RawCtxFrameDecoding.fromPayload context.frame.payload = some slices)
    (owner afterOwner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata)
    (decrypted : RawCtxWholeOwner.Decrypted) (after : State)
    (supported : ((.Some decrypted, afterOwner), after) ∈ support (monitor
      ((fun reply => RawCtxChainOwner.publish owner (RawCtxInterpretedReceive.normalFinish pending reply)) <$>
        RawCtxSelectedOpenConsumer.service slot read expected pending) before))
    (fresh : ∀ entry ∈ before.seals, ¬(RawCtxKeyFreeDecoder.target nonce context.frame.sequence
      context.frame context.associatedData slices parsed width).toLegacy.sameFullTupleAsSuccessfulSeal entry) :
    RecordEvent read after ∧ afterOwner.rawAttempts = owner.rawAttempts + 1 := by
  rw [monitor_map] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨result, reached, equal⟩ := supported
  have value : result.1 = .Some decrypted := congrArg (fun value => value.1.1) equal
  have observed : result.2 = after := congrArg Prod.snd equal
  have counter : afterOwner.rawAttempts = owner.rawAttempts + 1 := by
    have same := congrArg (fun value => value.1.2.rawAttempts) equal
    exact same.symm
  refine ⟨selected_service_record slot read expected pending nonce sequence context present width before
    nonempty decoded slices parsed decrypted after ?_ fresh, counter⟩
  have same : result = (.Some decrypted, after) := Prod.ext value observed
  rwa [same] at reached

abbrev PublishedResult (Chain M P I D K : Type) (S B : Nat) :=
  Bool × (PqxdhInitialPendingPost.Front Chain M P I D K S B × PqxdhInitialOriginPost.Trace Bool S B)

/-- The original publication gate and original byte-based freshness remain explicit restrictions on the actual source accepted-record event. -/
def GatedFreshRecord {Chain M P I D K : Type} {S B : Nat}
    (read : RawCtxReceive.FrameDecoder) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (blocked disclosed : List RatchetChain) (result : PublishedResult Chain M P I D K S B × State) : Prop :=
  PqxdhInitialPublishedEvent.Gate selected number result.1 ∧
    RawCtxLiveLineage.Fresh blocked disclosed result.1.2.1.roles.2 ∧ RecordEvent read result.2

/-- Restricting to the original publication and byte-freshness event cannot create another authentication winner; the concrete accepted-record witness supplies the win. -/
theorem gated_wins {Chain M P I D K : Type} {S B : Nat}
    (read : RawCtxReceive.FrameDecoder) (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64)
    (blocked disclosed : List RatchetChain) (result : PublishedResult Chain M P I D K S B × State)
    (event : GatedFreshRecord read selected number blocked disclosed result) :
    won (RawCtxUniversalDecoder.decoder read) result.2 = true := record_wins read result.2 event.2.2

/-- The full source game with the retained observer has exactly the executable ordinary decision's winning distribution. -/
theorem game_decision (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) :
    (fun result => won decode result.1.2) <$>
      AdaptiveCtxDynamicKnownKeys.sourceGame real decode c (monitor client initialState) =
      Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame real decode c (decision decode client) := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, decision, map_bind, simulateQ_map,
    StateT.run_map, Functor.map_map]

/-- Original Gate and Fresh are retained as restrictions on actual recorded source forgeries. The primitive endpoint still receives only its concrete key-free observer bit. -/
theorem gated_probability {Chain M P I D K : Type} {S B : Nat}
    (read : RawCtxReceive.FrameDecoder) (c : Pqxdh.Crypto)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (blocked disclosed : List RatchetChain)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (PublishedResult Chain M P I D K S B)) :
    RawCtxSelectedNativeFreshLift.mass (fun result => GatedFreshRecord read selected number blocked disclosed result.1)
      (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder read) c (monitor client initialState)) ≤
      𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder read) c
        (decision (RawCtxUniversalDecoder.decoder read) client)] {true} := by
  rw [← game_decision]
  unfold RawCtxSelectedNativeFreshLift.mass
  simp only [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def, decide_eq_true_eq]
  exact probEvent_mono'' fun result event => gated_wins read selected number blocked disclosed result.1 event

open AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxSharedReplayBounds
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The actual accepted-record event with the original publication and byte-freshness restrictions consumes precisely the ordinary observer reductions and every original query allowance. -/
theorem gated_authentication_bound {Chain M P I D K : Type} {S B : Nat}
    (read : RawCtxReceive.FrameDecoder) (c : Pqxdh.Crypto) (fallback : ModifiedNonceAeadForgery)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (blocked disclosed : List RatchetChain)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec (PublishedResult Chain M P I D K S B))
    (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    RawCtxSelectedNativeFreshLift.mass (fun result => GatedFreshRecord read selected number blocked disclosed result.1)
      (AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder read) c (monitor client initialState)) ≤
      ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
        (AdaptiveCtxPrefixValidation.validationReduction (RawCtxUniversalDecoder.decoder read) c
          (AdaptiveCtxDynamicKnownKeys.decisionClient c (decision (RawCtxUniversalDecoder.decoder read) client)) qHash)) +
      (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
      2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
        (AdaptiveRawNonceAead.indexedReduction (baseDecoder (RawCtxUniversalDecoder.decoder read)) fallback
          (AdaptiveCtxReceive.wrapped (RawCtxUniversalDecoder.decoder read)
            (AdaptiveCtxDynamicKnownKeys.decisionClient c (decision (RawCtxUniversalDecoder.decoder read) client))) index) +
      (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) :=
  (gated_probability read c selected number blocked disclosed client).trans
    (authentication_bound (RawCtxUniversalDecoder.decoder read) c fallback client qHash qSeal qRaw hashBound sealBound rawBound small)

end BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service_receipt

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service_forgery' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service_forgery

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.step_attempts' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.step_attempts

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.monitor_attempts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.monitor_attempts

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.monitor_won' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.monitor_won

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.native_service_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.native_service_erase

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_service_record

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.record_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.record_wins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.record_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.record_persists

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.monitor_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.monitor_map

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_publication_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.selected_publication_record

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.gated_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.gated_wins

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.game_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.game_decision

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.gated_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.gated_probability

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.gated_authentication_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedAcceptedRecord.gated_authentication_bound

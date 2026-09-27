import BeaconcryptCore.Computational.CtxNonceAeadIntCtxt
import VCVio.ProgramLogic.Relational.SimulateQ

/-!
# Adaptive optional-plaintext opening and stopped integrity reductions

The adversary supplies raw bytes and receives optional recovered plaintext. A public decoder supplies the nonce, associated data, and detached ciphertext. This is the one-key primitive interface needed below the protocol's raw receive interpreter; it does not yet instantiate Cap'n Proto, CTX, ratchet key selection, consumption, or multiple sessions.

The real challenger alone evaluates opening under its hidden key. The reduction answers previous encryption outputs from their public encryption log and rejects all other inputs. Stopped reductions preserve the encryption history at the selected receive attempt, so later encryptions cannot destroy the selected target's freshness.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.AdaptiveRawNonceAead

open CtxRomAuth CtxNonceAeadIntCtxt

abbrev RawDecoder := Pqxdh.Bytes → Option ModifiedNonceAeadForgery
abbrev RawOpenSpec := Pqxdh.Bytes →ₒ Option Pqxdh.Bytes
abbrev AdaptiveSpec := ModifiedNonceAeadAdversarySpec + RawOpenSpec
abbrev SealHistory := List ModifiedNonceAeadSuccessfulSeal

/-- Exact tuple equality used by the ordinary strong ciphertext-freshness game. -/
def entryMatches (target : ModifiedNonceAeadForgery) (entry : ModifiedNonceAeadSuccessfulSeal) : Bool :=
  decide (target.nonce = entry.input.nonce ∧ target.ad = entry.input.ad ∧
    target.ciphertext = entry.ciphertext)

/-- The simulator uses only plaintexts previously supplied to its encryption oracle. -/
def loggedPlaintext (history : SealHistory) (target : ModifiedNonceAeadForgery) : Option Pqxdh.Bytes :=
  (history.find? (entryMatches target)).map (fun entry => entry.input.plaintext)

/-- Absence from the log is exactly the existing primitive game's freshness predicate. -/
theorem loggedPlaintext_none_iff_fresh (history : SealHistory) (target : ModifiedNonceAeadForgery) :
    loggedPlaintext history target = none ↔ ModifiedNonceAeadFresh history target := by
  simp [loggedPlaintext, ModifiedNonceAeadFresh, entryMatches]

/-- The log correctness invariant records primitive correctness for every issued ciphertext. -/
def HistoryCorrect (c : Pqxdh.Crypto) (key : CtxKey) (history : SealHistory) : Prop :=
  ∀ entry ∈ history,
    c.aeadOpen key.toList entry.input.nonce.toList entry.input.ad
      entry.ciphertext.body entry.ciphertext.tag = some entry.input.plaintext

/-- A log hit returns precisely the plaintext produced by challenger opening. -/
theorem loggedPlaintext_correct (c : Pqxdh.Crypto) (key : CtxKey) (history : SealHistory)
    (correct : HistoryCorrect c key history) (target : ModifiedNonceAeadForgery)
    (plaintext : Pqxdh.Bytes) (found : loggedPlaintext history target = some plaintext) :
    c.aeadOpen key.toList target.nonce.toList target.ad
      target.ciphertext.body target.ciphertext.tag = some plaintext := by
  obtain ⟨entry, hentry, hplain⟩ := Option.map_eq_some_iff.mp found
  have hmatch : target.nonce = entry.input.nonce ∧ target.ad = entry.input.ad ∧
      target.ciphertext = entry.ciphertext := by
    simpa [entryMatches] using List.find?_some hentry
  simpa only [hmatch.1, hmatch.2.1, hmatch.2.2, hplain] using
    correct entry (List.mem_of_find?_eq_some hentry)

def simulatedOpen (decode : RawDecoder) (history : SealHistory)
    (raw : Pqxdh.Bytes) : Option Pqxdh.Bytes :=
  (decode raw).bind (loggedPlaintext history)

/-- Only the real game has this function's hidden-key argument. -/
def actualOpen (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (raw : Pqxdh.Bytes) : Option Pqxdh.Bytes := do
  let target ← decode raw
  c.aeadOpen key.toList target.nonce.toList target.ad
    target.ciphertext.body target.ciphertext.tag

/-- A real accepted raw request is fresh against the encryption history at this attempt. -/
def FreshAcceptance (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (history : SealHistory) (raw : Pqxdh.Bytes) : Prop :=
  ∃ target, decode raw = some target ∧ ModifiedNonceAeadFresh history target ∧
    c.aeadOpen key.toList target.nonce.toList target.ad target.ciphertext.body target.ciphertext.tag ≠ none

/-- Under the proved log invariant, discrepancy means actual fresh acceptance, never a plaintext guess. -/
theorem discrepancy_iff_fresh (decode : RawDecoder) (c : Pqxdh.Crypto) (key : CtxKey)
    (history : SealHistory) (correct : HistoryCorrect c key history) (raw : Pqxdh.Bytes) :
    actualOpen decode c key raw ≠ simulatedOpen decode history raw ↔
      FreshAcceptance decode c key history raw := by
  cases parsed : decode raw with
  | none => simp [actualOpen, simulatedOpen, FreshAcceptance, parsed]
  | some target =>
      cases logged : loggedPlaintext history target with
      | none =>
          simp [actualOpen, simulatedOpen, FreshAcceptance, parsed,
            (loggedPlaintext_none_iff_fresh history target).mp logged, logged]
      | some plaintext =>
          have notFresh : ¬ModifiedNonceAeadFresh history target := by
            simp [← loggedPlaintext_none_iff_fresh, logged]
          simp [actualOpen, simulatedOpen, FreshAcceptance, parsed, logged, notFresh,
            loggedPlaintext_correct c key history correct target plaintext logged]

/-- Updating a reduction's public log requires only the supplied encryption request and returned ciphertext. -/
def recordPrimitiveAnswer (query : ModifiedNonceAeadAdversarySpec.Domain)
    (answer : ModifiedNonceAeadAdversarySpec.Range query) (history : SealHistory) : SealHistory :=
  match query with
  | .inl _ => history
  | .inr input => match answer with
    | none => history
    | some ciphertext => ⟨input, ciphertext⟩ :: history

/-- The primitive challenger and the key-free reduction retain the same complete encryption log. -/
theorem primitiveAnswer_history (c : Pqxdh.Crypto) (key : CtxKey)
    (query : ModifiedNonceAeadAdversarySpec.Domain) (state : ModifiedNonceAeadHandlerState)
    (result : ModifiedNonceAeadAdversarySpec.Range query × ModifiedNonceAeadHandlerState)
    (supported : result ∈ support ((modifiedNonceAeadINTCTXTImpl c key query).run state)) :
    result.2.successfulSeals = recordPrimitiveAnswer query result.1 state.successfulSeals := by
  cases query with
  | inl coin =>
      change result ∈ support (do let answer ← liftM (unifSpec.query coin); pure (answer, state)) at supported
      obtain ⟨answer, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      rfl
  | inr input =>
      change result ∈ support ((modifiedNonceAeadSealOracle c key input).run state) at supported
      rw [modifiedNonceAeadSealOracle_run] at supported
      split at supported <;> obtain rfl := eq_of_mem_support_pure supported <;> rfl

/-- Ordinary encryption correctness establishes the entire reachable plaintext log invariant. -/
theorem primitive_preserves_historyCorrect (c : Pqxdh.Crypto) (key : CtxKey) :
    QueryImpl.PreservesInv (modifiedNonceAeadINTCTXTImpl c key)
      (fun state => HistoryCorrect c key state.successfulSeals) := by
  intro query state correct result supported
  cases query with
  | inl coin =>
      change result ∈ support (do let answer ← liftM (unifSpec.query coin); pure (answer, state)) at supported
      obtain ⟨answer, _, supported⟩ := (mem_support_bind_iff _ _ _).mp supported
      obtain rfl := eq_of_mem_support_pure supported
      exact correct
  | inr input =>
      change result ∈ support ((modifiedNonceAeadSealOracle c key input).run state) at supported
      rw [modifiedNonceAeadSealOracle_run] at supported
      split at supported
      · obtain rfl := eq_of_mem_support_pure supported
        exact correct
      · obtain rfl := eq_of_mem_support_pure supported
        simpa [HistoryCorrect, ModifiedNonceAeadHandlerState.addSeal, c.aead_open_seal] using correct

/-- Stop at the selected zero-based raw delivery. No hidden key, opening operation, or challenger recovery is available here. -/
def stopAtRaw {Result : Type} (decode : RawDecoder) (fallback : ModifiedNonceAeadForgery)
    (adversary : OracleComp AdaptiveSpec Result) :
    ℕ → SealHistory → OracleComp ModifiedNonceAeadAdversarySpec ModifiedNonceAeadForgery :=
  OracleComp.recOn adversary
    (fun _ _ _ => pure fallback)
    (fun query _ recurse remaining history =>
      match query with
      | .inl primitive => do
          let answer ← liftM (ModifiedNonceAeadAdversarySpec.query primitive)
          recurse answer remaining (recordPrimitiveAnswer primitive answer history)
      | .inr raw => match remaining with
        | 0 => pure ((decode raw).getD fallback)
        | remaining + 1 => recurse (simulatedOpen decode history raw) remaining history)

/-- The indexed family is an ordinary primitive forger; index selection adds no primitive query. -/
def indexedReduction {Result : Type} (decode : RawDecoder) (fallback : ModifiedNonceAeadForgery)
    (adversary : OracleComp AdaptiveSpec Result) (index : ℕ) : ModifiedNonceAeadAdversary :=
  ⟨stopAtRaw decode fallback adversary index []⟩

@[simp] theorem stopAtRaw_pure {Result : Type} (decode : RawDecoder)
    (fallback : ModifiedNonceAeadForgery) (result : Result) (index : ℕ) (history : SealHistory) :
    stopAtRaw decode fallback (pure result) index history = pure fallback := rfl

/-- Primitive calls before the stopping point are forwarded with their actual returned answers. -/
theorem stopAtRaw_primitive {Result : Type} (decode : RawDecoder)
    (fallback : ModifiedNonceAeadForgery) (query : ModifiedNonceAeadAdversarySpec.Domain)
    (next : ModifiedNonceAeadAdversarySpec.Range query → OracleComp AdaptiveSpec Result)
    (index : ℕ) (history : SealHistory) :
    stopAtRaw decode fallback (liftM (AdaptiveSpec.query (.inl query)) >>= next) index history =
      (do let answer ← liftM (ModifiedNonceAeadAdversarySpec.query query)
          stopAtRaw decode fallback (next answer) index (recordPrimitiveAnswer query answer history)) := rfl

/-- Selection stops before the chosen raw request is answered or later encryption is queried. -/
theorem stopAtRaw_receive {Result : Type} (decode : RawDecoder)
    (fallback : ModifiedNonceAeadForgery) (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp AdaptiveSpec Result) (index : ℕ) (history : SealHistory) :
    stopAtRaw decode fallback (liftM (AdaptiveSpec.query (.inr raw)) >>= next) index history =
      match index with
      | 0 => pure ((decode raw).getD fallback)
      | index + 1 => stopAtRaw decode fallback (next (simulatedOpen decode history raw)) index history := rfl

/-- Lift an explicit primitive resource class to the raw adaptive interface. -/
def primitiveClass (p : ModifiedNonceAeadAdversarySpec.Domain → Prop) : AdaptiveSpec.Domain → Prop
  | .inl query => p query
  | .inr _ => False

instance (p : ModifiedNonceAeadAdversarySpec.Domain → Prop) [DecidablePred p] :
    DecidablePred (primitiveClass p)
  | .inl query => inferInstanceAs (Decidable (p query))
  | .inr _ => isFalse id

/-- Every selected reduction inherits each primitive/uniform resource cap; stopping adds no oracle calls. -/
theorem stopAtRaw_query_bound {Result : Type} (decode : RawDecoder)
    (fallback : ModifiedNonceAeadForgery) (p : ModifiedNonceAeadAdversarySpec.Domain → Prop)
    [DecidablePred p] (adversary : OracleComp AdaptiveSpec Result) {bound : ℕ}
    (bounded : adversary.IsQueryBoundP (primitiveClass p) bound) (index : ℕ) (history : SealHistory) :
    (stopAtRaw decode fallback adversary index history).IsQueryBoundP p bound := by
  induction adversary using OracleComp.inductionOn generalizing bound index history with
  | pure result => simp
  | query_bind query next ih =>
      cases query with
      | inl primitive =>
          rw [stopAtRaw_primitive, OracleComp.isQueryBoundP_query_bind_iff]
          rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
          exact ⟨bounded.1, fun answer => ih answer (bounded.2 answer) index _⟩
      | inr raw =>
          rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
          have later : ∀ answer, (next answer).IsQueryBoundP (primitiveClass p) bound := by
            intro answer
            simpa only [ite_eq_right (show ¬ primitiveClass p (.inr raw) from id)] using
              bounded.2 answer
          cases index with
          | zero =>
              rw [stopAtRaw_receive]
              exact OracleComp.isQueryBoundP_pure _ _ _
          | succ index => exact ih _ (later _) index history

/-- This challenger-only monitor stops at the first discrepancy while following the simulator's optional replies. -/
noncomputable def firstDiscrepancy {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (adversary : OracleComp AdaptiveSpec Result) :
    ModifiedNonceAeadHandlerState → ProbComp Bool :=
  OracleComp.recOn adversary
    (fun _ _ => pure false)
    (fun query _ recurse state =>
      match query with
      | .inl primitive => do
          let (answer, next) ← (modifiedNonceAeadINTCTXTImpl c key primitive).run state
          recurse answer next
      | .inr raw =>
          if actualOpen decode c key raw ≠ simulatedOpen decode state.successfulSeals raw then
            pure true
          else recurse (simulatedOpen decode state.successfulSeals raw) state)

/-- Ordinary final verification of the selected reduction, preserving the actual stopping-time encryption history. -/
noncomputable def indexedBeforeVerify {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveSpec Result)
    (index : ℕ) (state : ModifiedNonceAeadHandlerState) : ProbComp ModifiedNonceAeadBeforeVerify := do
  let (target, finalState) ← (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
    (stopAtRaw decode fallback adversary index state.successfulSeals)).run state
  pure ⟨key, target, finalState.successfulSeals, finalState.usedNonces⟩

/-- The selected reduction forwards each earlier primitive query with its exact joint answer and new history. -/
theorem indexedBeforeVerify_primitive {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (fallback : ModifiedNonceAeadForgery)
    (query : ModifiedNonceAeadAdversarySpec.Domain)
    (next : ModifiedNonceAeadAdversarySpec.Range query → OracleComp AdaptiveSpec Result)
    (index : ℕ) (state : ModifiedNonceAeadHandlerState) :
    Pr[ModifiedNonceAeadINTCTXTWin c | indexedBeforeVerify decode c key fallback
      (liftM (AdaptiveSpec.query (.inl query)) >>= next) index state] =
    Pr[ModifiedNonceAeadINTCTXTWin c | do
      let (answer, nextState) ← (modifiedNonceAeadINTCTXTImpl c key query).run state
      indexedBeforeVerify decode c key fallback (next answer) index nextState] := by
  unfold indexedBeforeVerify
  rw [stopAtRaw_primitive]
  simp only [simulateQ_query_bind, OracleQuery.input_query,
    StateT.run_bind, bind_assoc]
  change Pr[ModifiedNonceAeadINTCTXTWin c | do
    let (answer, nextState) ← (modifiedNonceAeadINTCTXTImpl c key query).run state
    let (target, finalState) ← (simulateQ (modifiedNonceAeadINTCTXTImpl c key)
      (stopAtRaw decode fallback (next answer) index
        (recordPrimitiveAnswer query answer state.successfulSeals))).run nextState
    pure (⟨key, target, finalState.successfulSeals, finalState.usedNonces⟩ : ModifiedNonceAeadBeforeVerify)] = _
  apply probEvent_bind_congr
  intro result supported
  rcases result with ⟨answer, nextState⟩
  dsimp only
  rw [← primitiveAnswer_history c key query state ⟨answer, nextState⟩ supported]

/-- Taking an expectation preserves a finite family of reduction charges without a hidden worst-case step. -/
theorem probEvent_bind_le_sum {A B C : Type} (sample : ProbComp A)
    (left : A → ProbComp B) (right : ℕ → A → ProbComp C)
    (leftEvent : B → Prop) (rightEvent : C → Prop) (count : ℕ)
    (bounded : ∀ value ∈ support sample,
      Pr[leftEvent | left value] ≤ ∑ index ∈ Finset.range count, Pr[rightEvent | right index value]) :
    Pr[leftEvent | sample >>= left] ≤
      ∑ index ∈ Finset.range count, Pr[rightEvent | sample >>= right index] := by
  simp only [probEvent_bind_eq_tsum]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun value => ?_
  by_cases supported : value ∈ support sample
  · rw [← Finset.mul_sum]
    exact mul_le_mul' le_rfl (bounded value supported)
  · simp [probOutput_eq_zero_of_not_mem_support supported]

/-- Source raw-attempt accounting includes rejected decoding and every repeated candidate. -/
def IsRawQuery : AdaptiveSpec.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance : DecidablePred IsRawQuery
  | .inl _ => isFalse id
  | .inr _ => isTrue trivial

@[simp] theorem firstDiscrepancy_pure {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (value : Result) (state : ModifiedNonceAeadHandlerState) :
    firstDiscrepancy decode c key (pure value) state = pure false := rfl

theorem firstDiscrepancy_primitive {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : ModifiedNonceAeadAdversarySpec.Domain)
    (next : ModifiedNonceAeadAdversarySpec.Range query → OracleComp AdaptiveSpec Result)
    (state : ModifiedNonceAeadHandlerState) :
    firstDiscrepancy decode c key (liftM (AdaptiveSpec.query (.inl query)) >>= next) state = (do
      let result ← (modifiedNonceAeadINTCTXTImpl c key query).run state
      firstDiscrepancy decode c key (next result.1) result.2) := rfl

theorem firstDiscrepancy_receive {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (raw : Pqxdh.Bytes) (next : Option Pqxdh.Bytes → OracleComp AdaptiveSpec Result)
    (state : ModifiedNonceAeadHandlerState) :
    firstDiscrepancy decode c key (liftM (AdaptiveSpec.query (.inr raw)) >>= next) state =
      if actualOpen decode c key raw ≠ simulatedOpen decode state.successfulSeals raw then pure true
      else firstDiscrepancy decode c key (next (simulatedOpen decode state.successfulSeals raw)) state := rfl

theorem indexedBeforeVerify_receive_succ {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (fallback : ModifiedNonceAeadForgery) (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp AdaptiveSpec Result)
    (index : ℕ) (state : ModifiedNonceAeadHandlerState) :
    indexedBeforeVerify decode c key fallback (liftM (AdaptiveSpec.query (.inr raw)) >>= next)
      (index + 1) state =
    indexedBeforeVerify decode c key fallback (next (simulatedOpen decode state.successfulSeals raw))
      index state := rfl

/-- At a genuine first discrepancy, stopping before this reply already wins the ordinary final-forgery game. -/
theorem indexedBeforeVerify_receive_zero_wins {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (fallback : ModifiedNonceAeadForgery) (raw : Pqxdh.Bytes)
    (next : Option Pqxdh.Bytes → OracleComp AdaptiveSpec Result)
    (state : ModifiedNonceAeadHandlerState) (correct : HistoryCorrect c key state.successfulSeals)
    (discrepancy : actualOpen decode c key raw ≠ simulatedOpen decode state.successfulSeals raw) :
    Pr[ModifiedNonceAeadINTCTXTWin c | indexedBeforeVerify decode c key fallback
      (liftM (AdaptiveSpec.query (.inr raw)) >>= next) 0 state] = 1 := by
  obtain ⟨target, parsed, fresh, opens⟩ :=
    (discrepancy_iff_fresh decode c key state.successfulSeals correct raw).mp discrepancy
  unfold indexedBeforeVerify
  rw [stopAtRaw_receive]
  simp [parsed, ModifiedNonceAeadINTCTXTWin, fresh, opens]

/-- Each possible first fresh acceptance is charged once in the indexed family; all raw attempts count. -/
theorem firstDiscrepancy_le_indexed_sum {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveSpec Result)
    (count : ℕ) (state : ModifiedNonceAeadHandlerState)
    (bounded : adversary.IsQueryBoundP IsRawQuery count)
    (correct : HistoryCorrect c key state.successfulSeals) :
    Pr[fun bad => bad = true | firstDiscrepancy decode c key adversary state] ≤
      ∑ index ∈ Finset.range count,
        Pr[ModifiedNonceAeadINTCTXTWin c | indexedBeforeVerify decode c key fallback adversary index state] := by
  induction adversary using OracleComp.inductionOn generalizing count state with
  | pure value => simp
  | query_bind query next ih =>
      cases query with
      | inl primitive =>
          rw [firstDiscrepancy_primitive]
          simp_rw [indexedBeforeVerify_primitive]
          apply probEvent_bind_le_sum
          intro result supported
          rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
          exact ih result.1 count result.2
            (by simpa only [ite_eq_right (show ¬ IsRawQuery (.inl primitive) from id)] using
              bounded.2 result.1)
            (primitive_preserves_historyCorrect c key primitive state correct result supported)
      | inr raw =>
          rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
          have positive : 0 < count := by simpa only [IsRawQuery, not_true_eq_false, false_or] using bounded.1
          obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : count ≠ 0)
          rw [firstDiscrepancy_receive]
          by_cases discrepancy : actualOpen decode c key raw ≠ simulatedOpen decode state.successfulSeals raw
          · rw [if_pos discrepancy]
            calc
              Pr[fun bad => bad = true | (pure true : ProbComp Bool)] = 1 := by simp
              _ = Pr[ModifiedNonceAeadINTCTXTWin c | indexedBeforeVerify decode c key fallback
                    (liftM (AdaptiveSpec.query (.inr raw)) >>= next) 0 state] :=
                (indexedBeforeVerify_receive_zero_wins decode c key fallback raw next state correct discrepancy).symm
              _ ≤ ∑ index ∈ Finset.range (remaining + 1),
                    Pr[ModifiedNonceAeadINTCTXTWin c | indexedBeforeVerify decode c key fallback
                      (liftM (AdaptiveSpec.query (.inr raw)) >>= next) index state] :=
                Finset.single_le_sum
                  (f := fun index => Pr[ModifiedNonceAeadINTCTXTWin c | indexedBeforeVerify decode c key fallback
                    (liftM (AdaptiveSpec.query (.inr raw)) >>= next) index state])
                  (fun _ _ => zero_le) (Finset.mem_range.mpr (by omega))
          · rw [if_neg discrepancy]
            have remainingBound : (next (simulatedOpen decode state.successfulSeals raw)).IsQueryBoundP
                IsRawQuery remaining := by
              simpa only [ite_eq_left (show IsRawQuery (.inr raw) from trivial), Nat.succ_sub_one] using
                bounded.2 (simulatedOpen decode state.successfulSeals raw)
            have tail := ih (simulatedOpen decode state.successfulSeals raw) remaining state remainingBound correct
            rw [Finset.sum_range_succ']
            simp only [indexedBeforeVerify_receive_succ]
            exact tail.trans (le_add_of_nonneg_right zero_le)

/-- Private challenger instrumentation includes every raw delivery, including parser failures. -/
structure ReceiveState where
  seals : ModifiedNonceAeadHandlerState
  attempts : ℕ

def initialState : ReceiveState := ⟨emptyModifiedNonceAeadHandlerState, 0⟩

/-- A sticky discrepancy flag permits the games to diverge on the first fresh acceptance itself. -/
noncomputable def receiveStep (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (raw : Pqxdh.Bytes) (state : ReceiveState × Bool) :
    ProbComp (Option Pqxdh.Bytes × (ReceiveState × Bool)) :=
  let actual := actualOpen decode c key raw
  let simulated := simulatedOpen decode state.1.seals.successfulSeals raw
  pure (if real then actual else simulated,
    (⟨state.1.seals, state.1.attempts + 1⟩,
      state.2 || decide (actual ≠ simulated)))

/-- Encryption and randomness are the existing ordinary primitive challenger; opening is the new adaptive interface. -/
noncomputable def adaptiveImpl (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) : QueryImpl AdaptiveSpec (StateT (ReceiveState × Bool) ProbComp) :=
  fun query state =>
    match query with
    | .inl primitive => do
        let (answer, seals) ← (modifiedNonceAeadINTCTXTImpl c key primitive).run state.1.seals
        pure (answer, (⟨seals, state.1.attempts⟩, state.2))
    | .inr raw => receiveStep real decode c key raw state

noncomputable def adaptiveGame (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp AdaptiveSpec Result) :
    ProbComp (Result × (ReceiveState × Bool)) :=
  (simulateQ (adaptiveImpl real decode c key) adversary).run (initialState, false)

/-- On each receive, outputs that leave the discrepancy flag unset agree exactly. -/
theorem receiveStep_agree_good (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (raw : Pqxdh.Bytes) (state next : ReceiveState)
    (answer : Option Pqxdh.Bytes) :
    Pr[= (answer, (next, false)) | receiveStep true decode c key raw (state, false)] =
      Pr[= (answer, (next, false)) | receiveStep false decode c key raw (state, false)] := by
  classical
  letI : DecidableEq ReceiveState := Classical.decEq _
  by_cases equal : actualOpen decode c key raw = simulatedOpen decode state.seals.successfulSeals raw
  · simp [receiveStep, equal]
  · simp [receiveStep, equal]

/-- All primitive queries agree; receive agreement uses the complete optional answer and retained state. -/
theorem adaptiveImpl_agree_good (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : AdaptiveSpec.Domain) (state : ReceiveState)
    (answer : AdaptiveSpec.Range query) (next : ReceiveState) :
    Pr[= (answer, (next, false)) | (adaptiveImpl true decode c key query).run (state, false)] =
      Pr[= (answer, (next, false)) | (adaptiveImpl false decode c key query).run (state, false)] := by
  cases query with
  | inl primitive => rfl
  | inr raw => exact receiveStep_agree_good decode c key raw state next answer

/-- Discrepancy instrumentation is sticky even after the adversary's two continuations diverge. -/
theorem adaptiveImpl_bad_mono (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) (query : AdaptiveSpec.Domain) (state : ReceiveState × Bool)
    (bad : state.2 = true) :
    ∀ result ∈ support ((adaptiveImpl real decode c key query).run state), result.2.2 = true := by
  intro result hresult
  cases query with
  | inl primitive =>
      change result ∈ support ((modifiedNonceAeadINTCTXTImpl c key primitive).run state.1.seals >>= fun pair =>
        pure (pair.1, (⟨pair.2, state.1.attempts⟩, state.2))) at hresult
      obtain ⟨pair, _, hresult⟩ := (mem_support_bind_iff _ _ _).mp hresult
      exact (congrArg (fun p => p.2.2) (eq_of_mem_support_pure hresult)).trans bad
  | inr raw =>
      change result ∈ support (pure (if real then actualOpen decode c key raw else
        simulatedOpen decode state.1.seals.successfulSeals raw,
        (⟨state.1.seals, state.1.attempts + 1⟩, state.2 ||
          decide (actualOpen decode c key raw ≠ simulatedOpen decode state.1.seals.successfulSeals raw)))) at hresult
      have hresult := eq_of_mem_support_pure hresult
      simpa only [bad, Bool.true_or] using congrArg (fun p => p.2.2) hresult

/-- Every continuation retains an already-raised discrepancy; the ordinary probability monad has no failure mass. -/
theorem adaptive_bad_probability_one (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp AdaptiveSpec Result) (state : ReceiveState) :
    Pr[fun result => result.2.2 = true |
      (simulateQ (adaptiveImpl real decode c key) adversary).run (state, true)] = 1 := by
  rw [probEvent_eq_one_iff]
  refine ⟨by simp, ?_⟩
  exact simulateQ_run_preservesInv (adaptiveImpl real decode c key) (fun pair => pair.2 = true)
    (adaptiveImpl_bad_mono real decode c key) adversary (state, true) rfl

/-- The complete simulator's bad marginal is exactly the stopped first-discrepancy monitor. -/
theorem simulated_bad_eq_firstDiscrepancy (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp AdaptiveSpec Result) (state : ReceiveState) :
    Pr[fun result => result.2.2 = true |
      (simulateQ (adaptiveImpl false decode c key) adversary).run (state, false)] =
    Pr[fun bad => bad = true | firstDiscrepancy decode c key adversary state.seals] := by
  induction adversary using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      cases query with
      | inl primitive =>
          rw [firstDiscrepancy_primitive]
          simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
          change Pr[fun result => result.2.2 = true | do
            let result ← (do
              let pair ← (modifiedNonceAeadINTCTXTImpl c key primitive).run state.seals
              pure (pair.1, ((⟨pair.2, state.attempts⟩ : ReceiveState), false)))
            (simulateQ (adaptiveImpl false decode c key) (next result.1)).run result.2] = _
          simp only [bind_assoc, pure_bind]
          simp only [probEvent_bind_eq_tsum]
          apply tsum_congr
          intro result
          rw [ih result.1 ⟨result.2, state.attempts⟩]
      | inr raw =>
          rw [firstDiscrepancy_receive]
          simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
          change Pr[fun result => result.2.2 = true |
            (simulateQ (adaptiveImpl false decode c key)
              (next (simulatedOpen decode state.seals.successfulSeals raw))).run
                (⟨state.seals, state.attempts + 1⟩,
                  decide (actualOpen decode c key raw ≠ simulatedOpen decode state.seals.successfulSeals raw))] = _
          by_cases discrepancy : actualOpen decode c key raw ≠ simulatedOpen decode state.seals.successfulSeals raw
          · rw [if_pos discrepancy]
            have decision : decide (actualOpen decode c key raw ≠ simulatedOpen decode state.seals.successfulSeals raw) = true :=
              decide_eq_true discrepancy
            rw [decision, adaptive_bad_probability_one]
            simp
          · simp only [discrepancy, decide_false]
            exact ih _ ⟨state.seals, state.attempts + 1⟩

/-- Real and simulated complete runs raise discrepancy with exactly equal probability. -/
theorem adaptiveGame_bad_eq (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp AdaptiveSpec Result) :
    Pr[fun result => result.2.2 = true | adaptiveGame true decode c key adversary] =
      Pr[fun result => result.2.2 = true | adaptiveGame false decode c key adversary] :=
  OracleComp.ProgramLogic.Relational.probEvent_output_bad_eq'
    (adaptiveImpl true decode c key) (adaptiveImpl false decode c key)
    (adaptiveImpl_agree_good decode c key) (adaptiveImpl_bad_mono true decode c key)
    (adaptiveImpl_bad_mono false decode c key) adversary initialState

/-- The ordinary primitive key is uniformly generated once and remains inside the receive challenger. -/
noncomputable def uniformAdaptiveGame (real : Bool) (decode : RawDecoder) (c : Pqxdh.Crypto)
    {Result : Type} (adversary : OracleComp AdaptiveSpec Result) :
    ProbComp (Result × (ReceiveState × Bool)) := do
  let key ← $ᵗ CtxKey
  adaptiveGame real decode c key adversary

/-- Uniform-key adaptive fresh acceptance reduces to the explicit family of ordinary INT-CTXT forgers. -/
theorem uniformAdaptive_bad_le_intctxt_sum {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveSpec Result)
    (count : ℕ) (bounded : adversary.IsQueryBoundP IsRawQuery count) :
    Pr[fun result => result.2.2 = true | uniformAdaptiveGame true decode c adversary] ≤
      ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c (indexedReduction decode fallback adversary index) := by
  change Pr[fun result => result.2.2 = true | ($ᵗ CtxKey) >>= fun key => adaptiveGame true decode c key adversary] ≤
    ∑ index ∈ Finset.range count, Pr[ModifiedNonceAeadINTCTXTWin c |
      ($ᵗ CtxKey) >>= fun key => indexedBeforeVerify decode c key fallback adversary index emptyModifiedNonceAeadHandlerState]
  apply probEvent_bind_le_sum
  intro key _
  rw [adaptiveGame_bad_eq]
  change Pr[fun result => result.2.2 = true |
    (simulateQ (adaptiveImpl false decode c key) adversary).run (initialState, false)] ≤ _
  rw [simulated_bad_eq_firstDiscrepancy]
  exact firstDiscrepancy_le_indexed_sum decode c key fallback adversary count
    emptyModifiedNonceAeadHandlerState bounded (by simp [HistoryCorrect, emptyModifiedNonceAeadHandlerState])

/-- The complete adaptive transcript and state can differ only after an actual optional-plaintext discrepancy. -/
theorem adaptiveGame_distance_le_discrepancy (decode : RawDecoder) (c : Pqxdh.Crypto)
    (key : CtxKey) {Result : Type} (adversary : OracleComp AdaptiveSpec Result) :
    tvDist (adaptiveGame true decode c key adversary)
        (adaptiveGame false decode c key adversary) ≤
      Pr[fun result => result.2.2 = true | adaptiveGame true decode c key adversary].toReal := by
  exact OracleComp.ProgramLogic.Relational.tvDist_simulateQ_run_le_probEvent_output_bad
    (adaptiveImpl true decode c key) (adaptiveImpl false decode c key) adversary initialState
    (adaptiveImpl_agree_good decode c key) (adaptiveImpl_bad_mono true decode c key)
    (adaptiveImpl_bad_mono false decode c key)

/-- Mixing over the challenger's uniformly generated secret key preserves the full-state discrepancy bound. -/
theorem uniformAdaptiveGame_distance_le_bad {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (adversary : OracleComp AdaptiveSpec Result) :
    tvDist (uniformAdaptiveGame true decode c adversary) (uniformAdaptiveGame false decode c adversary) ≤
      Pr[fun result => result.2.2 = true | uniformAdaptiveGame true decode c adversary].toReal := by
  have convex := tvDist_bind_left_le ($ᵗ CtxKey)
    (fun key => adaptiveGame true decode c key adversary)
    (fun key => adaptiveGame false decode c key adversary)
  rw [tsum_fintype] at convex
  calc
    tvDist (uniformAdaptiveGame true decode c adversary) (uniformAdaptiveGame false decode c adversary)
        ≤ ∑ key : CtxKey, Pr[= key | ($ᵗ CtxKey)].toReal *
          (Pr[fun result => result.2.2 = true | adaptiveGame true decode c key adversary]).toReal := by
      refine convex.trans (Finset.sum_le_sum fun key _ => ?_)
      exact mul_le_mul_of_nonneg_left (adaptiveGame_distance_le_discrepancy decode c key adversary)
        ENNReal.toReal_nonneg
    _ = Pr[fun result => result.2.2 = true | uniformAdaptiveGame true decode c adversary].toReal := by
      unfold uniformAdaptiveGame
      rw [probEvent_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum]
      · simp only [ENNReal.toReal_mul]
      · intro key _
        exact ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top

/-- Full adaptive optional-plaintext simulation, with every possible first acceptance charged to an ordinary primitive forger. -/
theorem uniformAdaptiveGame_distance_le_intctxt_sum {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveSpec Result)
    (count : ℕ) (bounded : adversary.IsQueryBoundP IsRawQuery count) :
    ENNReal.ofReal (tvDist (uniformAdaptiveGame true decode c adversary)
      (uniformAdaptiveGame false decode c adversary)) ≤
      ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c (indexedReduction decode fallback adversary index) := by
  calc
    ENNReal.ofReal (tvDist (uniformAdaptiveGame true decode c adversary)
        (uniformAdaptiveGame false decode c adversary))
      ≤ ENNReal.ofReal (Pr[fun result => result.2.2 = true |
          uniformAdaptiveGame true decode c adversary].toReal) :=
        ENNReal.ofReal_le_ofReal (uniformAdaptiveGame_distance_le_bad decode c adversary)
    _ = Pr[fun result => result.2.2 = true | uniformAdaptiveGame true decode c adversary] :=
      ENNReal.ofReal_toReal probEvent_ne_top
    _ ≤ _ := uniformAdaptive_bad_le_intctxt_sum decode c fallback adversary count bounded

/-- Primitive-side private-randomness requests are counted separately from encryption requests. -/
def IsPrimitiveUniformQuery : ModifiedNonceAeadAdversarySpec.Domain → Prop
  | .inl _ => True
  | .inr _ => False

instance : DecidablePred IsPrimitiveUniformQuery
  | .inl _ => isTrue trivial
  | .inr _ => isFalse id

/-- Every indexed forger uses at most the source's uniform and sealing queries; final verification is one challenger opening. -/
theorem indexedReduction_query_bounds {Result : Type} (decode : RawDecoder)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveSpec Result)
    (uniformQueries sealQueries index : ℕ)
    (uniformBound : adversary.IsQueryBoundP (primitiveClass IsPrimitiveUniformQuery) uniformQueries)
    (sealBound : adversary.IsQueryBoundP (primitiveClass IsModifiedNonceAeadSealQuery) sealQueries) :
    (indexedReduction decode fallback adversary index).main.IsQueryBoundP IsPrimitiveUniformQuery uniformQueries ∧
      (indexedReduction decode fallback adversary index).MakesAtMostSealQueries sealQueries :=
  ⟨stopAtRaw_query_bound decode fallback IsPrimitiveUniformQuery adversary uniformBound index [],
    stopAtRaw_query_bound decode fallback IsModifiedNonceAeadSealQuery adversary sealBound index []⟩

/-- A common primitive integrity envelope gives the explicit raw-attempt loss, including every adaptive acceptance attempt. -/
theorem uniformAdaptiveGame_distance_le_raw_count {Result : Type} (decode : RawDecoder) (c : Pqxdh.Crypto)
    (fallback : ModifiedNonceAeadForgery) (adversary : OracleComp AdaptiveSpec Result)
    (count : ℕ) (bounded : adversary.IsQueryBoundP IsRawQuery count) (epsilon : ℝ≥0∞)
    (primitiveBound : ∀ index < count,
      modifiedNonceAeadINTCTXTAdvantage c (indexedReduction decode fallback adversary index) ≤ epsilon) :
    ENNReal.ofReal (tvDist (uniformAdaptiveGame true decode c adversary)
      (uniformAdaptiveGame false decode c adversary)) ≤ (count : ℝ≥0∞) * epsilon := by
  refine (uniformAdaptiveGame_distance_le_intctxt_sum decode c fallback adversary count bounded).trans ?_
  calc
    ∑ index ∈ Finset.range count,
        modifiedNonceAeadINTCTXTAdvantage c (indexedReduction decode fallback adversary index)
      ≤ ∑ _index ∈ Finset.range count, epsilon :=
        Finset.sum_le_sum fun index member => primitiveBound index (Finset.mem_range.mp member)
    _ = (count : ℝ≥0∞) * epsilon := by simp [nsmul_eq_mul]

end BeaconcryptCore.Computational.AdaptiveRawNonceAead

/--
info: 'BeaconcryptCore.Computational.AdaptiveRawNonceAead.uniformAdaptiveGame_distance_le_intctxt_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawNonceAead.uniformAdaptiveGame_distance_le_intctxt_sum

/--
info: 'BeaconcryptCore.Computational.AdaptiveRawNonceAead.uniformAdaptiveGame_distance_le_raw_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawNonceAead.uniformAdaptiveGame_distance_le_raw_count

/--
info: 'BeaconcryptCore.Computational.AdaptiveRawNonceAead.indexedReduction_query_bounds' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.AdaptiveRawNonceAead.indexedReduction_query_bounds

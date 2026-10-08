-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxBills

/-!
# Record-lift ideal-world hiding: `idealRecords_hiding` (items 4 and 5, stage S5)

**Statement.** `idealRecords_hiding` proves `PqxdhRecordLiftIdeal.HidingStatement` as defined: for every environment and every mode-P adversary (no `Frame` or budget premise), replacing every hidden seal plaintext by one of equal length leaves the law of the hiding projection `hidingView` of `idealRecords` unchanged, as an equality of the mapped computations. `hiding_replace` states the same for any two replacements that agree on lengths.

**Method: a syntactic coupling.** `Coupled Rr Ro x y` says that two oracle computations make the same queries in the same order, that replies related by `Rr` lead to related continuations, and that the final values are related by `Ro`. With equal coin replies, maps that agree on related final values give equal mapped computations (`Coupled.map_eq`), and simulation through implementations whose single queries are coupled preserves couplings (`Coupled.simulateQ_run`, `Coupled.simulateQ`). The proof runs the same mode-P adversary through every layer of the world, with the replacing world and the identity world side by side. Interpreter (`interpreter_couple`): in random mode a seal reads only the plaintext's length (body and tag are fresh coins, the commitment a private-suffix lookup), so the same coins give the same record, frame, writer result and state, except that the replay dictionary records the replaced plaintext (`randomSeal_couple`, `sealing_couple`); a raw opening replays the plaintext of the first matching dictionary entry, whose existence does not depend on recorded plaintexts (`replay_isSome`, `localRaw_couple`), so opening replies agree on success (`SuccessRel`) and private states agree up to recorded plaintexts (`PrivRel`); every other service is the chain world's on the same base state (`base_couple`). Compiled client (`handler_couple`, `schedule_couple`): a hidden receive's kernel update depends on the opening reply only through success (`normalFinish_couple`, from the source `finish`); requests without hidden openings (every request but a raw receive, by `PqxdhRecordLiftCtxBills.handler_categories` with raw bill zero) are coupled with themselves (`refl_noOpening`); the control state stays equal. Environment and native commands (`native_couple`, `environmentStep_couple`): the environment sees only registration effects, whose replies are equal, so its state stays equal. Secrecy ledger (`ledger_couple`): transcripts agree in their mode-P view (`PqxdhDeploymentTranscript.SameView`), so the test-session check agrees (`sameSession_view`, from `designate_view`), and the test session with its bit and the fresh messages are equal (`LedgerRel`). Mode-P observation (`observeFull_couple`, `adversary_couple`): raw-receive replies that agree on success are observed equally, so the adversary receives equal replies throughout. `ctxRun_couple` assembles the layers, and the hiding projection reads only fields that agree on related results (`hidingView_rel`).

**Contracts.** No theorem of this module has an assumption or contract hypothesis, and no proof step uses a contract (per-theorem closure probe): random-mode seals use no AEAD primitive, and no security game enters. Fields of the primitive record are reached only inside definitions (the setup's DH interface, the KDF definitions and the real-mode CTX code that the CTX interpreter's definition contains but random mode never runs), as structural facts. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftHiding

/-! ### Syntactic couplings of oracle computations -/

section Coupling
variable {ι : Type} {spec : OracleSpec ι}

/-- Two computations make the same queries in the same order; replies related by `Rr` lead to related continuations, and the final values are related by `Ro`. -/
inductive Coupled (Rr : (q : spec.Domain) → spec.Range q → spec.Range q → Prop) :
    {α β : Type} → (α → β → Prop) → OracleComp spec α → OracleComp spec β → Prop
  | pure {α β : Type} {Ro : α → β → Prop} (a : α) (b : β) : Ro a b → Coupled Rr Ro (pure a) (pure b)
  | query_bind {α β : Type} {Ro : α → β → Prop} (q : spec.Domain) (k₁ : spec.Range q → OracleComp spec α)
      (k₂ : spec.Range q → OracleComp spec β) :
      (∀ r₁ r₂, Rr q r₁ r₂ → Coupled Rr Ro (k₁ r₁) (k₂ r₂)) →
      Coupled Rr Ro ((spec.query q : OracleComp spec _) >>= k₁) ((spec.query q : OracleComp spec _) >>= k₂)

variable {Rr : (q : spec.Domain) → spec.Range q → spec.Range q → Prop}

/-- Couplings weaken to any larger relation on final values. -/
theorem Coupled.mono {α β : Type} {Ro Ro' : α → β → Prop} {x : OracleComp spec α} {y : OracleComp spec β}
    (h : Coupled Rr Ro x y) (weaker : ∀ a b, Ro a b → Ro' a b) : Coupled Rr Ro' x y := by
  induction h with
  | pure a b hab => exact .pure a b (weaker a b hab)
  | query_bind q k₁ k₂ _ ih => exact .query_bind q k₁ k₂ fun r₁ r₂ hr => ih r₁ r₂ hr

/-- Couplings compose with continuations that are coupled on related values. -/
theorem Coupled.bind {α β γ δ : Type} {Ro : α → β → Prop} {Ro' : γ → δ → Prop} {x : OracleComp spec α}
    {y : OracleComp spec β} (h : Coupled Rr Ro x y) {f : α → OracleComp spec γ} {g : β → OracleComp spec δ}
    (next : ∀ a b, Ro a b → Coupled Rr Ro' (f a) (g b)) : Coupled Rr Ro' (x >>= f) (y >>= g) := by
  induction h with
  | pure a b hab => simpa only [pure_bind] using next a b hab
  | query_bind q k₁ k₂ _ ih =>
      simp only [bind_assoc]
      exact .query_bind q _ _ fun r₁ r₂ hr => ih r₁ r₂ hr

/-- Couplings survive maps that send related values to related values. -/
theorem Coupled.map {α β γ δ : Type} {Ro : α → β → Prop} {Ro' : γ → δ → Prop} {x : OracleComp spec α}
    {y : OracleComp spec β} (h : Coupled Rr Ro x y) {f : α → γ} {g : β → δ}
    (related : ∀ a b, Ro a b → Ro' (f a) (g b)) : Coupled Rr Ro' (f <$> x) (g <$> y) := by
  simp only [map_eq_bind_pure_comp]
  exact h.bind fun a b hab => .pure _ _ (related a b hab)

/-- A single query is coupled with itself, with its replies related by `Rr`. -/
theorem Coupled.query (q : spec.Domain) :
    Coupled Rr (Rr q) (spec.query q : OracleComp spec _) (spec.query q : OracleComp spec _) := by
  have h := Coupled.query_bind (Rr := Rr) (Ro := Rr q) q (fun r => (Pure.pure r : OracleComp spec (spec.Range q)))
    (fun r => (Pure.pure r : OracleComp spec (spec.Range q))) fun r₁ r₂ hr => .pure r₁ r₂ hr
  simpa only [bind_pure] using h

/-- A computation is coupled with itself when related replies are equal. -/
theorem Coupled.refl {α : Type} (x : OracleComp spec α) (eqReplies : ∀ q r₁ r₂, Rr q r₁ r₂ → r₁ = r₂)
    {Ro : α → α → Prop} (diag : ∀ a, Ro a a) : Coupled Rr Ro x x := by
  induction x using OracleComp.inductionOn with
  | pure a => exact .pure a a (diag a)
  | query_bind q k ih =>
      exact .query_bind q k k fun r₁ r₂ hr => by
        cases eqReplies q r₁ r₂ hr
        exact ih r₁

/-- Two maps of one computation are coupled when related replies are equal and the maps are pointwise related. -/
theorem Coupled.of_map {α β γ : Type} (x : OracleComp spec α) (eqReplies : ∀ q r₁ r₂, Rr q r₁ r₂ → r₁ = r₂)
    {Ro : β → γ → Prop} (f : α → β) (g : α → γ) (related : ∀ a, Ro (f a) (g a)) :
    Coupled Rr Ro (f <$> x) (g <$> x) :=
  (Coupled.refl x eqReplies (Ro := Eq) fun _ => rfl).map fun a _ hab => hab ▸ related a

/-- A coupling with equal replies identifies the images under maps that agree on related values. -/
theorem Coupled.map_eq {α β γ : Type} {Ro : α → β → Prop} {x : OracleComp spec α} {y : OracleComp spec β}
    (h : Coupled (fun _ r₁ r₂ => r₁ = r₂) Ro x y) (f : α → γ) (g : β → γ) (agree : ∀ a b, Ro a b → f a = g b) :
    f <$> x = g <$> y := by
  induction h with
  | pure a b hab => simp only [map_pure, agree a b hab]
  | query_bind q k₁ k₂ _ ih =>
      simp only [map_bind]
      exact bind_congr fun r => ih r r rfl

/-- Simulation through stateful implementations whose single queries are coupled preserves couplings. -/
theorem Coupled.simulateQ_run {κ : Type} {spec' : OracleSpec κ}
    {Rr' : (q : spec'.Domain) → spec'.Range q → spec'.Range q → Prop} {σ τ : Type}
    (first : QueryImpl spec (StateT σ (OracleComp spec'))) (second : QueryImpl spec (StateT τ (OracleComp spec')))
    (S : σ → τ → Prop)
    (step : ∀ q s t, S s t → Coupled Rr' (fun p₁ p₂ => Rr q p₁.1 p₂.1 ∧ S p₁.2 p₂.2) ((first q).run s) ((second q).run t))
    {α β : Type} {Ro : α → β → Prop} {x : OracleComp spec α} {y : OracleComp spec β} (h : Coupled Rr Ro x y)
    (s : σ) (t : τ) (related : S s t) :
    Coupled Rr' (fun p₁ p₂ => Ro p₁.1 p₂.1 ∧ S p₁.2 p₂.2) ((simulateQ first x).run s) ((simulateQ second y).run t) := by
  induction h generalizing s t with
  | pure a b hab => simpa only [simulateQ_pure, StateT.run_pure] using Coupled.pure (Rr := Rr') _ _ ⟨hab, related⟩
  | query_bind q k₁ k₂ _ ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact (step q s t related).bind fun p₁ p₂ hp => ih p₁.1 p₂.1 hp.1 p₁.2 p₂.2 hp.2

/-- Simulation through stateless implementations whose single queries are coupled preserves couplings. -/
theorem Coupled.simulateQ {κ : Type} {spec' : OracleSpec κ}
    {Rr' : (q : spec'.Domain) → spec'.Range q → spec'.Range q → Prop}
    (first second : QueryImpl spec (OracleComp spec')) (step : ∀ q, Coupled Rr' (Rr q) (first q) (second q))
    {α β : Type} {Ro : α → β → Prop} {x : OracleComp spec α} {y : OracleComp spec β} (h : Coupled Rr Ro x y) :
    Coupled Rr' Ro (simulateQ first x) (simulateQ second y) := by
  induction h with
  | pure a b hab => simpa only [simulateQ_pure] using Coupled.pure (Rr := Rr') _ _ hab
  | query_bind q k₁ k₂ _ ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (step q).bind fun r₁ r₂ hr => ih r₁ r₂ hr

/-- A computation with a zero weighted bound is coupled with itself when every query of cost zero has equal related replies. -/
theorem Coupled.refl_weighted {α : Type} (cost : spec.Domain → Nat) (x : OracleComp spec α)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted cost x 0)
    (eqReplies : ∀ q, cost q = 0 → ∀ r₁ r₂, Rr q r₁ r₂ → r₁ = r₂) {Ro : α → α → Prop} (diag : ∀ a, Ro a a) :
    Coupled Rr Ro x x := by
  induction x using OracleComp.inductionOn with
  | pure a => exact .pure a a (diag a)
  | query_bind q k ih =>
      rw [PqxdhRecordLiftCtxProgramBounds.Weighted, isQueryBound_query_bind_iff] at bounded
      have free : cost q = 0 := Nat.le_zero.mp bounded.1
      refine .query_bind q k k fun r₁ r₂ hr => ?_
      cases eqReplies q free r₁ r₂ hr
      have next := bounded.2 r₁
      rw [free] at next
      exact ih r₁ next

end Coupling

/-! ### The random-mode CTX interpreter up to recorded seal plaintexts -/

section Interpreter
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat}

/-- Equal replies. -/
def EqRel {κ : Type} {spec : OracleSpec κ} : (q : spec.Domain) → spec.Range q → spec.Range q → Prop :=
  fun _ r₁ r₂ => r₁ = r₂

/-- Replies related by `EqRel` are equal. -/
theorem eqRel_eq {κ : Type} {spec : OracleSpec κ} (q : spec.Domain) (r₁ r₂ : spec.Range q)
    (h : EqRel q r₁ r₂) : r₁ = r₂ := h

/-- A recorded seal with its plaintext erased. -/
def eraseSeal (sealed : CtxSuccessfulSeal) : CtxSuccessfulSeal := ⟨{ sealed.input with plaintext := [] }, sealed.record⟩

/-- The fields of a one-key CTX local state, with every recorded seal plaintext erased. -/
def eraseEntry (entry : KeyEntry) :=
  (entry.1.usedNonces, entry.1.successfulSeals.map eraseSeal, entry.1.publicInputs, entry.1.rawAttempts,
    entry.1.privateInputs, entry.2)

/-- Two private CTX-world states agree up to recorded seal plaintexts. -/
def PrivRel (s t : CtxPrivate n) : Prop :=
  s.base = t.base ∧ ∀ label, eraseEntry (s.keys label) = eraseEntry (t.keys label)

/-- Replay acceptance does not read recorded plaintexts. -/
theorem replay_isSome (e₁ e₂ : KeyEntry) (same : eraseEntry e₁ = eraseEntry e₂)
    (target : CtxUnclaimedAcceptance.Target) :
    (AdaptiveCtxReplayDictionary.replayPlaintext (AdaptiveCtxSharedReplay.install e₁ ∅).ctx target).isSome =
      (AdaptiveCtxReplayDictionary.replayPlaintext (AdaptiveCtxSharedReplay.install e₂ ∅).ctx target).isSome := by
  have seals : e₁.1.successfulSeals.map eraseSeal = e₂.1.successfulSeals.map eraseSeal := by
    simp only [eraseEntry, Prod.mk.injEq] at same
    exact same.2.1
  have key : ∀ l : List CtxSuccessfulSeal, (l.find? (fun entry => decide (target.nonce = entry.input.nonce ∧
      target.context.ad = entry.input.context.ad ∧ target.record.encode = entry.record.encode))).isSome =
      ((l.map eraseSeal).find? (fun entry => decide (target.nonce = entry.input.nonce ∧
        target.context.ad = entry.input.context.ad ∧ target.record.encode = entry.record.encode))).isSome := by
    intro l
    rw [List.find?_map, Option.isSome_map]
    rfl
  simp only [AdaptiveCtxReplayDictionary.replayPlaintext, AdaptiveCtxSharedReplay.install, Option.isSome_map]
  rw [key, seals, ← key]

/-- One random-mode raw opening on two states that agree up to recorded plaintexts. -/
theorem localRaw_couple (decode : RawDecoder) (raw : Pqxdh.Bytes) (e₁ e₂ : KeyEntry)
    (same : eraseEntry e₁ = eraseEntry e₂) :
    Coupled EqRel (fun p₁ p₂ => p₁.1.isSome = p₂.1.isSome ∧ eraseEntry p₁.2 = eraseEntry p₂.2)
      (AdaptiveCtxSharedReplay.localRaw decode raw e₁) (AdaptiveCtxSharedReplay.localRaw decode raw e₂) := by
  have parts := same
  simp only [eraseEntry, Prod.mk.injEq] at parts
  obtain ⟨hn, hs, hp, hr, hi, hc⟩ := parts
  unfold AdaptiveCtxSharedReplay.localRaw
  cases decode raw with
  | none => exact .pure _ _ ⟨rfl, by simp only [eraseEntry, hn, hs, hp, hr, hi, hc]⟩
  | some target =>
      simp only [AdaptiveCtxSharedReplay.localPrivate, bind_assoc, pure_bind]
      rw [hc]
      refine Coupled.bind (Coupled.refl _ eqRel_eq (Ro := Eq) fun _ => rfl) ?_
      rintro a b rfl
      exact .pure _ _ ⟨replay_isSome e₁ e₂ same target, by simp only [eraseEntry, hn, hs, hp, hr, hi]⟩

/-- Random-mode sealing of two inputs that differ only in plaintext bytes of equal length, on two states that agree up to recorded plaintexts: the same coins give the same record. -/
theorem randomSeal_couple (input₁ input₂ : CtxSealInput) (nonce : input₁.nonce = input₂.nonce)
    (context : input₁.context = input₂.context) (length : input₁.plaintext.length = input₂.plaintext.length)
    (e₁ e₂ : KeyEntry) (same : eraseEntry e₁ = eraseEntry e₂) :
    Coupled EqRel (fun p₁ p₂ => p₁.1 = p₂.1 ∧ eraseEntry p₁.2 = eraseEntry p₂.2)
      (randomSeal input₁ e₁) (randomSeal input₂ e₂) := by
  obtain ⟨n₁, c₁, m₁⟩ := input₁
  obtain ⟨n₂, c₂, m₂⟩ := input₂
  simp only at nonce context length
  subst nonce context
  have parts := same
  simp only [eraseEntry, Prod.mk.injEq] at parts
  obtain ⟨hn, hs, hp, hr, hi, hc⟩ := parts
  unfold randomSeal
  rw [hn]
  by_cases used : n₁ ∈ e₂.1.usedNonces
  · simp only [used, ↓reduceIte]
    exact .pure _ _ ⟨rfl, same⟩
  · simp only [used, ↓reduceIte]
    rw [length]
    refine Coupled.bind (Coupled.refl _ eqRel_eq (Ro := Eq) fun _ => rfl) ?_
    rintro body _ rfl
    refine Coupled.bind (Coupled.refl _ eqRel_eq (Ro := Eq) fun _ => rfl) ?_
    rintro tag _ rfl
    simp only [AdaptiveCtxSharedReplay.localPrivate, bind_assoc, pure_bind]
    rw [hc]
    refine Coupled.bind (Coupled.refl _ eqRel_eq (Ro := Eq) fun _ => rfl) ?_
    rintro result _ rfl
    exact .pure _ _ ⟨rfl, by simp only [eraseEntry, eraseSeal, List.map_cons, hn, hs, hp, hr, hi]⟩

/-- Replies of a one-key CTX request: raw openings agree on success, everything else is equal. -/
def ReceiveRel : (q : ReceiveSpec.Domain) → ReceiveSpec.Range q → ReceiveSpec.Range q → Prop
  | .inr _ => fun r₁ r₂ => r₁.isSome = r₂.isSome
  | _ => fun r₁ r₂ => r₁ = r₂

/-- Every random-mode one-key request on two states that agree up to recorded plaintexts. -/
theorem randomImpl_couple (decode : RawDecoder) (q : ReceiveSpec.Domain) (e₁ e₂ : KeyEntry)
    (same : eraseEntry e₁ = eraseEntry e₂) :
    Coupled EqRel (fun p₁ p₂ => ReceiveRel q p₁.1 p₂.1 ∧ eraseEntry p₁.2 = eraseEntry p₂.2)
      ((randomImpl decode q).run e₁) ((randomImpl decode q).run e₂) := by
  have parts := same
  simp only [eraseEntry, Prod.mk.injEq] at parts
  obtain ⟨hn, hs, hp, hr, hi, hc⟩ := parts
  rcases q with (coin | (hash | input)) | raw
  · exact (Coupled.query _).bind fun a b h => .pure _ _ ⟨h, same⟩
  · exact (Coupled.query _).bind fun a b h => .pure _ _ ⟨h, by simp only [eraseEntry, hn, hs, hp, hr, hi, hc]⟩
  · exact randomSeal_couple input input rfl rfl rfl e₁ e₂ same
  · exact localRaw_couple decode raw e₁ e₂ same

/-- The shared BLAKE2b cache simulation preserves couplings with equal coins. -/
theorem hash_couple {α β : Type} {R : α → β → Prop} {x : OracleComp AdaptiveCtxSharedHash.HashSpec α}
    {y : OracleComp AdaptiveCtxSharedHash.HashSpec β} (h : Coupled EqRel R x y) (cache : CtxRO.QueryCache) :
    Coupled EqRel (fun p₁ p₂ => R p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      ((simulateQ AdaptiveCtxSharedHash.hashImpl x).run cache) ((simulateQ AdaptiveCtxSharedHash.hashImpl y).run cache) :=
  Coupled.simulateQ_run _ _ Eq (fun _ _ _ hc => hc ▸ Coupled.refl _ eqRel_eq fun _ => ⟨rfl, rfl⟩) h cache cache rfl

/-- The counted sampler preserves couplings with equal coins. -/
theorem sampled_couple {α β : Type} {R : α → β → Prop} {x : ProbComp α} {y : ProbComp β}
    (h : Coupled EqRel R x y) (secret : PqxdhRecordLiftProtocol.Private n) :
    Coupled EqRel (fun p₁ p₂ => R p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      ((PqxdhRecordLiftProtocol.sampled x).run secret) ((PqxdhRecordLiftProtocol.sampled y).run secret) := by
  unfold PqxdhRecordLiftProtocol.sampled
  exact (Coupled.simulateQ_run _ _ Eq (fun _ _ _ hc => hc ▸ Coupled.refl _ eqRel_eq fun _ => ⟨rfl, rfl⟩) h _ _
    rfl).bind fun p₁ p₂ hp => .pure _ _ ⟨hp.1, by rw [hp.2]⟩

/-- Keyed replies: a raw opening's replies agree on success, everything else is equal. -/
def KeyedRel : (q : (KeyedSpec n).Domain) → (KeyedSpec n).Range q → (KeyedSpec n).Range q → Prop :=
  fun q => ReceiveRel q.2

/-- Updating one coordinate's local state by erase-equal values preserves `PrivRel`. -/
theorem privRel_update (s t : CtxPrivate n) (related : PrivRel s t) (base : PqxdhRecordLiftProtocol.Private n)
    (label : Label n) (e₁ e₂ : KeyEntry) (same : eraseEntry e₁ = eraseEntry e₂) :
    PrivRel ⟨base, Function.update s.keys label e₁⟩ ⟨base, Function.update t.keys label e₂⟩ := by
  refine ⟨rfl, fun other => ?_⟩
  by_cases hit : other = label
  · subst hit
    simp only [Function.update_self]
    exact same
  · simp only [Function.update_of_ne hit]
    exact related.2 other

/-- Every random-mode keyed request on two private states that agree up to recorded plaintexts. -/
theorem keyed_couple (decode : RawDecoder) (crypto : Pqxdh.Crypto) (q : (KeyedSpec n).Domain)
    (s t : CtxPrivate n) (related : PrivRel s t) :
    Coupled EqRel (fun p₁ p₂ => KeyedRel q p₁.1 p₂.1 ∧ PrivRel p₁.2 p₂.2)
      ((keyed (fun _ => .random) decode crypto q).run s) ((keyed (fun _ => .random) decode crypto q).run t) := by
  obtain ⟨base, keys⟩ := related
  have inner := sampled_couple (hash_couple (randomImpl_couple decode q.2 (s.keys q.1) (t.keys q.1) (keys q.1))
    s.base.primitive.2) s.base
  simp only [keyed, keyImpl, StateT.run]
  rw [← base]
  exact inner.bind fun p₁ p₂ hp => .pure _ _ ⟨hp.1.1.1, by
    rw [hp.1.2, hp.2]
    exact privRel_update s t ⟨base, keys⟩ _ q.1 _ _ hp.1.1.2⟩

/-- Random-mode seals of two inputs that differ only in plaintext bytes of equal length, through the keyed service. -/
theorem keyed_seal_couple (decode : RawDecoder) (crypto : Pqxdh.Crypto) (label : Label n)
    (input₁ input₂ : CtxSealInput) (nonce : input₁.nonce = input₂.nonce) (context : input₁.context = input₂.context)
    (length : input₁.plaintext.length = input₂.plaintext.length) (s t : CtxPrivate n) (related : PrivRel s t) :
    Coupled EqRel (fun (p₁ p₂ : Option CtxRomRecord × CtxPrivate n) => p₁.1 = p₂.1 ∧ PrivRel p₁.2 p₂.2)
      ((keyed (fun _ => .random) decode crypto (label, .inl (.inr (.inr input₁)))).run s)
      ((keyed (fun _ => .random) decode crypto (label, .inl (.inr (.inr input₂)))).run t) := by
  obtain ⟨base, keys⟩ := related
  have inner := sampled_couple (hash_couple (randomSeal_couple input₁ input₂ nonce context length (s.keys label)
    (t.keys label) (keys label)) s.base.primitive.2) s.base
  simp only [keyed, keyImpl, StateT.run]
  rw [← base]
  exact inner.bind fun p₁ p₂ hp => .pure _ _ ⟨hp.1.1.1, by
    rw [hp.1.2, hp.2]
    exact privRel_update s t ⟨base, keys⟩ _ label _ _ hp.1.1.2⟩

/-- Opening replies agree on success. -/
def SuccessRel (r₁ r₂ : core.option.Option RawCtxWholeOwner.Decrypted) : Prop :=
  PqxdhDeploymentInterface.succeeded r₁ = PqxdhDeploymentInterface.succeeded r₂

/-- Replies of a private service: openings agree on success, everything else is equal. -/
def ServiceRel : (q : PqxdhRecordLiftProtocol.Service n) → (PqxdhRecordLiftProtocol.ServiceSpec n).Range q →
    (PqxdhRecordLiftProtocol.ServiceSpec n).Range q → Prop
  | .opening _ => SuccessRel
  | _ => fun r₁ r₂ => r₁ = r₂

/-- The source API reply of an opening succeeds exactly when the keyed reply is present. -/
theorem succeeded_apiReply (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) (reply : Option Pqxdh.Bytes) :
    PqxdhDeploymentInterface.succeeded (RawCtxSharedOpeningConsumer.apiReply sequence context reply) = reply.isSome := by
  cases reply <;> rfl

/-- The hidden opening program is coupled with itself: keyed replies that agree on success give API replies that agree on success. -/
theorem hiddenOpening_couple (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (pending : PqxdhRecordLiftProtocol.Opening n) :
    Coupled KeyedRel SuccessRel (hiddenOpening seeds table pending) (hiddenOpening seeds table pending) := by
  unfold hiddenOpening
  split
  · exact .pure _ _ rfl
  · split
    · exact .pure _ _ rfl
    · split
      · exact (Coupled.query _).map fun r₁ r₂ h => by
          simp only [SuccessRel, succeeded_apiReply]
          exact h
      · exact .pure _ _ rfl

/-- A hidden opening in random mode, with any plaintext replacements, on private states that agree up to recorded plaintexts. -/
theorem opening_couple {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Opening n)
    (s t : CtxPrivate n) (related : PrivRel s t) :
    Coupled EqRel (fun p₁ p₂ => SuccessRel p₁.1 p₂.1 ∧ PrivRel p₁.2 p₂.2)
      ((ctxInterpreter (fun _ => .random) replace₁ setup codec (.opening pending)).run s)
      ((ctxInterpreter (fun _ => .random) replace₂ setup codec (.opening pending)).run t) := by
  simp only [ctxInterpreter, StateT.run]
  rw [related.1]
  exact Coupled.simulateQ_run _ _ PrivRel (fun q s' t' h => keyed_couple _ _ q s' t' h)
    (hiddenOpening_couple _ _ _) s t related

/-- The CTX world's hidden sealing service, unfolded: the keyed simulation of the hidden sealing program on the pending frame log, then the frame log written back. -/
theorem sealing_run (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) {ι : Type}
    {baseSpec : OracleSpec ι} {KemSK Reader Response : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (state : CtxPrivate n) :
    (ctxInterpreter modes replace setup codec (.sealing pending)).run state =
      (simulateQ (keyed modes (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto)
        ((hiddenSealing codec.frameWrite state.base.chain replace pending).run state.base.pending)).run state >>=
        fun result => pure (result.1.1, { result.2 with base := { result.2.base with pending := result.1.2 } }) := rfl

/-- A hidden sealing of an associated datum of the protocol width is one keyed seal request followed by the frame log and the writer result. -/
theorem hiddenSealing_wide (writer : RawCtxMixedShared.Writer) (table : PqxdhRecordLiftChainTable.Table (Slot n))
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (pending : PqxdhRecordLiftProtocol.Sealing n)
    (frames : PqxdhRecordLiftLoggedAdapters.Frames) (width : pending.context.associatedData.length = 153) :
    (hiddenSealing writer table replace pending).run frames = (do
      let reply ← ((KeyedSpec n).query (pending.material, .inl (.inr (.inr
        (RawCtxSelectedMessageSealing.selectedInput (materialAt table pending.material).2 pending.sequence
          (replaceContext replace pending.context) width)))) : OracleComp (KeyedSpec n) (Option CtxRomRecord))
      match reply with
      | none => pure (none, frames)
      | some record =>
          let frame : RawCtxReceive.DecodedFrame :=
            ⟨pending.sequence, pending.context.senderId, record.encode⟩
          pure ((writer frame).map fun ciphertext => ⟨ciphertext, pending.context.targetId, pending.sequence⟩,
            frames ++ [frame])) :=
  dite_eq_left_of_eq_true (eq_true width)

/-- A hidden sealing in random mode with two replacements that agree on lengths, on private states that agree up to recorded plaintexts: the same coins give the same reply, frames and state. -/
theorem sealing_couple {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (lengths : ∀ m, (replace₁ m).length = (replace₂ m).length)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (pending : PqxdhRecordLiftProtocol.Sealing n) (s t : CtxPrivate n) (related : PrivRel s t) :
    Coupled EqRel (fun p₁ p₂ => p₁.1 = p₂.1 ∧ PrivRel p₁.2 p₂.2)
      ((ctxInterpreter (fun _ => .random) replace₁ setup codec (.sealing pending)).run s)
      ((ctxInterpreter (fun _ => .random) replace₂ setup codec (.sealing pending)).run t) := by
  rw [sealing_run, sealing_run, related.1]
  refine Coupled.bind (Ro := fun p₁ p₂ => p₁.1 = p₂.1 ∧ PrivRel p₁.2 p₂.2) ?_ fun p₁ p₂ hp => .pure _ _ ⟨by rw [hp.1], ?_⟩
  · by_cases width : pending.context.associatedData.length = 153
    · rw [hiddenSealing_wide _ _ _ _ _ width, hiddenSealing_wide _ _ _ _ _ width]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have sealed := keyed_seal_couple (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        pending.material
        (RawCtxSelectedMessageSealing.selectedInput (materialAt t.base.chain pending.material).2 pending.sequence
          (replaceContext replace₁ pending.context) width)
        (RawCtxSelectedMessageSealing.selectedInput (materialAt t.base.chain pending.material).2 pending.sequence
          (replaceContext replace₂ pending.context) width) rfl rfl (lengths pending.context.plaintext) s t related
      refine sealed.bind ?_
      rintro ⟨reply₁, s₁⟩ ⟨reply₂, s₂⟩ ⟨same, hs⟩
      simp only at same
      subst same
      cases reply₁
      · simpa only [simulateQ_pure, StateT.run_pure] using Coupled.pure (Rr := EqRel) _ _ ⟨rfl, hs⟩
      · simpa only [simulateQ_pure, StateT.run_pure] using Coupled.pure (Rr := EqRel) _ _ ⟨rfl, hs⟩
    · rw [hiddenSealing_narrow _ _ _ _ _ width, hiddenSealing_narrow _ _ _ _ _ width]
      simpa only [simulateQ_pure, StateT.run_pure] using Coupled.pure (Rr := EqRel) _ _ ⟨rfl, related⟩
  · exact ⟨by rw [hp.2.1, hp.1], hp.2.2⟩

/-- `ServiceRel` is reflexive at every service other than a hidden opening. -/
theorem serviceRel_refl (q : PqxdhRecordLiftProtocol.Service n) (notOpening : ∀ pending, q ≠ .opening pending)
    (reply : (PqxdhRecordLiftProtocol.ServiceSpec n).Range q) : ServiceRel q reply reply := by
  cases q
  case opening pending => exact absurd rfl (notOpening pending)
  all_goals rfl

/-- Every non-record service is the chain world's service on the base state, in both worlds. -/
theorem base_couple {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (q : PqxdhRecordLiftProtocol.Service n)
    (notOpening : ∀ pending, q ≠ .opening pending) (notSealing : ∀ pending, q ≠ .sealing pending)
    (s t : CtxPrivate n) (related : PrivRel s t) :
    Coupled EqRel (fun p₁ p₂ => ServiceRel q p₁.1 p₂.1 ∧ PrivRel p₁.2 p₂.2)
      ((ctxInterpreter (fun _ => .random) replace₁ setup codec q).run s)
      ((ctxInterpreter (fun _ => .random) replace₂ setup codec q).run t) := by
  rw [ctxInterpreter_base _ _ _ _ q notOpening notSealing, ctxInterpreter_base _ _ _ _ q notOpening notSealing,
    related.1]
  exact Coupled.of_map _ eqRel_eq _ _ fun a => ⟨serviceRel_refl q notOpening a.1, rfl, related.2⟩

/-- **Interpreter coupling.** The random-mode CTX interpreters with two plaintext replacements that agree on lengths answer every private service with the same coins: replies agree (openings on success only) and the private states agree up to recorded seal plaintexts. -/
theorem interpreter_couple {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (lengths : ∀ m, (replace₁ m).length = (replace₂ m).length)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (q : PqxdhRecordLiftProtocol.Service n) (s t : CtxPrivate n) (related : PrivRel s t) :
    Coupled EqRel (fun p₁ p₂ => ServiceRel q p₁.1 p₂.1 ∧ PrivRel p₁.2 p₂.2)
      ((ctxInterpreter (fun _ => .random) replace₁ setup codec q).run s)
      ((ctxInterpreter (fun _ => .random) replace₂ setup codec q).run t) := by
  cases q
  case opening pending => exact opening_couple replace₁ replace₂ setup codec pending s t related
  case sealing pending => exact sealing_couple replace₁ replace₂ lengths setup codec pending s t related
  all_goals exact base_couple replace₁ replace₂ setup codec _ (fun _ h => by cases h) (fun _ h => by cases h) s t related

end Interpreter

/-! ### The compiled client: receive replies matter only through their success -/

section Client
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label StoredKernel Owner)
open PqxdhRecordLiftCtxProtocolBounds (categoryCost)
variable {n : Nat}

/-- A service program without hidden openings is coupled with itself. -/
theorem refl_noOpening {α : Type} (x : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) α)
    (bounded : PqxdhRecordLiftCtxProgramBounds.Weighted (categoryCost .raw) x 0) {Ro : α → α → Prop}
    (diag : ∀ a, Ro a a) : Coupled ServiceRel Ro x x :=
  Coupled.refl_weighted _ x bounded (fun q free r₁ r₂ hr => by
    cases q
    case opening pending => simp [categoryCost] at free
    all_goals exact hr) diag

/-- An opening's publication depends on its reply only through success. -/
theorem normalFinish_couple {Send Receive Material Context : Type}
    (pending : RawCtxInterpretedOpening.Opening Send Receive Material Context)
    (r₁ r₂ : core.option.Option RawCtxWholeOwner.Decrypted) (related : SuccessRel r₁ r₂) :
    (RawCtxChainReceive.normalFinish pending r₁).1 = (RawCtxChainReceive.normalFinish pending r₂).1 ∧
      SuccessRel (RawCtxChainReceive.normalFinish pending r₁).2 (RawCtxChainReceive.normalFinish pending r₂).2 := by
  have e₁ := RawCtxChainReceive.normalFinish_exact pending r₁
  have e₂ := RawCtxChainReceive.normalFinish_exact pending r₂
  generalize RawCtxChainReceive.normalFinish pending r₁ = x₁ at e₁ ⊢
  generalize RawCtxChainReceive.normalFinish pending r₂ = x₂ at e₂ ⊢
  cases r₁ <;> cases r₂
  · simp only [RawCtxInterpretedOpening.finish] at e₁ e₂
    cases e₁
    cases e₂
    exact ⟨rfl, rfl⟩
  · exact absurd related (by simp [SuccessRel, PqxdhDeploymentInterface.succeeded])
  · exact absurd related (by simp [SuccessRel, PqxdhDeploymentInterface.succeeded])
  · simp only [RawCtxInterpretedOpening.finish] at e₁ e₂
    cases prepared : pending.prepared <;> simp only [prepared] at e₁ e₂
    · rename_i cached
      cases published : ratchet.refined.publish_cached_receive pending.entry cached <;> simp_all
      cases e₁
      cases e₂
      exact ⟨rfl, rfl⟩
    · rename_i future
      cases published : ratchet.refined.publish_future_receive pending.entry future <;> simp_all
      cases e₁
      cases e₂
      exact ⟨rfl, rfl⟩

/-- Replies of a local labeled service: openings agree on success, everything else is equal. -/
def LocalRel : (q : (PqxdhRecordLiftProtocol.LocalSpec n).Domain) → (PqxdhRecordLiftProtocol.LocalSpec n).Range q →
    (PqxdhRecordLiftProtocol.LocalSpec n).Range q → Prop
  | .inr (.inl _) => SuccessRel
  | _ => fun r₁ r₂ => r₁ = r₂

/-- The opaque source receive is coupled with itself: the same kernel and replies that agree on success. -/
theorem receiveProgram_couple
    (effect : RawCtxChainReceive.Effect (Label n) (Label n) (Label n) RawCtxWholeOwner.OpenContext) :
    Coupled LocalRel (fun p₁ p₂ => p₁.1 = p₂.1 ∧ SuccessRel p₁.2 p₂.2)
      (PqxdhRecordLiftOpaqueDrivers.receiveProgram (Plaintext := RawCtxWholeOwner.Decrypted)
        (SealContext := RawCtxSourceSend.SealContext) (Output := RawCtxSourceSend.Encrypted) effect)
      (PqxdhRecordLiftOpaqueDrivers.receiveProgram (Plaintext := RawCtxWholeOwner.Decrypted)
        (SealContext := RawCtxSourceSend.SealContext) (Output := RawCtxSourceSend.Encrypted) effect) := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
        simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        exact .pure _ _ ⟨rfl, rfl⟩
    | openRequested pending =>
        simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        exact (Coupled.query _).bind fun r₁ r₂ hr => .pure _ _ (normalFinish_couple pending r₁ r₂ hr)
    | kdfRequested pending =>
        simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        exact (Coupled.query _).bind fun _ _ _ =>
          ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending _) _ rfl

/-- A record receive on a stored kernel is coupled with itself: the same kernel and replies that agree on success. -/
theorem kernelReceive_couple (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Coupled ServiceRel (fun p₁ p₂ => p₁.1 = p₂.1 ∧ SuccessRel p₁.2 p₂.2)
      (PqxdhRecordLiftProtocol.kernelReceive stored target context)
      (PqxdhRecordLiftProtocol.kernelReceive stored target context) := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive]
      exact (Coupled.query _).bind fun r₁ r₂ hr => by
        cases (show r₁ = r₂ from hr)
        exact .pure _ _ ⟨rfl, rfl⟩
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive]
      refine (Coupled.simulateQ (Rr := LocalRel) _ _ (fun q => ?_)
        (receiveProgram_couple (RawCtxChainReceive.normalBegin kernel target context))).bind
        fun p₁ p₂ hp => .pure _ _ ⟨by rw [hp.1], hp.2⟩
      rcases q with coordinate | pending | pending
      · exact Coupled.query (Rr := ServiceRel) (.lookup coordinate)
      · exact Coupled.query (Rr := ServiceRel) (.opening pending)
      · exact Coupled.query (Rr := ServiceRel) (.sealing pending)

/-- An owner's raw receive is coupled with itself: the same owner state and replies that agree on success. -/
theorem ownerReceive_couple (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n) :
    Coupled ServiceRel (fun p₁ p₂ => SuccessRel p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      (PqxdhRecordLiftProtocol.ownerReceive decode raw owner) (PqxdhRecordLiftProtocol.ownerReceive decode raw owner) := by
  unfold PqxdhRecordLiftProtocol.ownerReceive
  split
  · exact .pure _ _ ⟨rfl, rfl⟩
  · split
    · exact .pure _ _ ⟨rfl, rfl⟩
    · split
      · exact (kernelReceive_couple _ _ _).bind fun p₁ p₂ hp => .pure _ _ ⟨hp.2, by rw [hp.1]⟩
      · exact .pure _ _ ⟨rfl, rfl⟩

/-- An owner's raw receive with its publication is coupled with itself. -/
theorem ownerRun_raw_couple (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n) :
    Coupled ServiceRel (fun (p₁ p₂ : core.option.Option RawCtxWholeOwner.Decrypted × Owner n) =>
        SuccessRel p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      (PqxdhRecordLiftProtocol.ownerRun tag sender decode (.inr raw) owner)
      (PqxdhRecordLiftProtocol.ownerRun tag sender decode (.inr raw) owner) := by
  unfold PqxdhRecordLiftProtocol.ownerRun PqxdhRecordLiftProtocol.ownerStep
  exact (ownerReceive_couple decode raw owner).bind fun p₁ p₂ hp =>
    (Coupled.query _).bind fun _ _ _ => .pure _ _ hp

/-- Replies of a world request: raw receives agree on success, everything else is equal. -/
def WorldRel : (q : (WorldSpec n).Domain) → (WorldSpec n).Range q → (WorldSpec n).Range q → Prop
  | .inr (.inr (.inl (.inr _))) => SuccessRel
  | .inr (.inr (.inr (_, .inr _))) => SuccessRel
  | _ => fun r₁ r₂ => r₁ = r₂

/-- **Handler coupling.** Every world request is coupled with itself: the same control state and replies related by `WorldRel`, whenever the services' replies are related by `ServiceRel`. -/
theorem handler_couple (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (q : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) :
    Coupled ServiceRel (fun p₁ p₂ => WorldRel q p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      ((PqxdhRecordLiftProtocol.handler decode route q).run control)
      ((PqxdhRecordLiftProtocol.handler decode route q).run control) := by
  have plain : ∀ q, PqxdhRecordLiftCtxBills.worldBill .raw q = 0 → (∀ r, WorldRel q r r) →
      Coupled ServiceRel (fun p₁ p₂ => WorldRel q p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
        ((PqxdhRecordLiftProtocol.handler decode route q).run control)
        ((PqxdhRecordLiftProtocol.handler decode route q).run control) := fun q free diag => by
    have bounded := PqxdhRecordLiftCtxBills.handler_categories .raw decode route q control
    rw [free] at bounded
    exact refl_noOpening _ bounded fun a => ⟨diag a.1, rfl⟩
  rcases q with created | effect | (send | raw) | ⟨owner, send | raw⟩
  · exact plain _ rfl fun _ => rfl
  · exact plain _ (by simp [PqxdhRecordLiftCtxBills.worldBill, PqxdhRecordLiftCtxBills.effectBill]) fun _ => rfl
  · exact plain _ (by simp [PqxdhRecordLiftCtxBills.worldBill, PqxdhRecordLiftBudget.recordKind,
      PqxdhRecordLiftCtxProgramBounds.operationBill, PqxdhRecordLiftCtxProgramBounds.lookupCost,
      PqxdhRecordLiftCtxProgramBounds.sealingCost]) fun _ => rfl
  · change Coupled ServiceRel _ (PqxdhRecordLiftProtocol.serverStep decode route (.inr raw) control)
      (PqxdhRecordLiftProtocol.serverStep decode route (.inr raw) control)
    unfold PqxdhRecordLiftProtocol.serverStep
    split
    · exact .pure _ _ ⟨rfl, rfl⟩
    · dsimp only
      split
      · exact .pure _ _ ⟨rfl, rfl⟩
      · split
        · exact .pure _ _ ⟨rfl, rfl⟩
        · exact (ownerRun_raw_couple _ _ _ _ _).bind fun p₁ p₂ hp => .pure _ _ ⟨hp.1, by rw [hp.2]⟩
  · exact plain _ (by simp [PqxdhRecordLiftCtxBills.worldBill, PqxdhRecordLiftBudget.recordKind,
      PqxdhRecordLiftCtxProgramBounds.operationBill, PqxdhRecordLiftCtxProgramBounds.lookupCost,
      PqxdhRecordLiftCtxProgramBounds.sealingCost]) fun _ => rfl
  · change Coupled ServiceRel _ (PqxdhRecordLiftProtocol.beaconStep decode owner (.inr raw) control)
      (PqxdhRecordLiftProtocol.beaconStep decode owner (.inr raw) control)
    unfold PqxdhRecordLiftProtocol.beaconStep
    split
    · exact .pure _ _ ⟨rfl, rfl⟩
    · exact .pure _ _ ⟨rfl, rfl⟩
    · exact (ownerRun_raw_couple _ _ _ _ _).bind fun p₁ p₂ hp => .pure _ _ ⟨hp.1, by rw [hp.2]⟩

/-- The compiled schedule of a world program: coupled world programs give coupled service programs with equal control states. -/
theorem schedule_couple (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    {α β : Type} {Ro : α → β → Prop} {x : OracleComp (WorldSpec n) α} {y : OracleComp (WorldSpec n) β}
    (h : Coupled WorldRel Ro x y) (control : PqxdhRecordLiftProtocol.Control n) :
    Coupled ServiceRel (fun p₁ p₂ => Ro p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      (PqxdhRecordLiftProtocol.schedule decode route x control) (PqxdhRecordLiftProtocol.schedule decode route y control) :=
  Coupled.simulateQ_run _ _ Eq (fun q c₁ _ hc => hc ▸ handler_couple decode route q c₁) h control control rfl

/-- Replies of a native command: raw receives agree on success, everything else is equal. -/
def SpecRel : (q : PqxdhDeploymentInterface.Spec.Domain) → PqxdhDeploymentInterface.Spec.Range q →
    PqxdhDeploymentInterface.Spec.Range q → Prop
  | .inr (.serverRaw _) => SuccessRel
  | .inr (.beaconRaw _ _) => SuccessRel
  | _ => fun r₁ r₂ => r₁ = r₂

/-- An environment step is coupled with itself: it issues only restricted effects, whose replies are equal. -/
theorem environmentStep_couple {E : Type} (env : Environment n E) (query : EnvQuery) (state : E) :
    Coupled WorldRel (fun p₁ p₂ => p₁ = p₂) ((environmentStep env query).run state)
      ((environmentStep env query).run state) :=
  Coupled.simulateQ (Rr := EqRel) _ _ (fun q => Coupled.query (Rr := WorldRel) (.inr (.inl q)))
    (Coupled.refl _ eqRel_eq fun _ => rfl)

/-- **Native coupling.** Every native command is coupled with itself: the same environment state and replies related by `SpecRel`, whenever world replies are related by `WorldRel`. -/
theorem native_couple {E : Type} (env : Environment n E) (q : PqxdhDeploymentInterface.Spec.Domain) (state : E) :
    Coupled WorldRel (fun p₁ p₂ => SpecRel q p₁.1 p₂.1 ∧ p₁.2 = p₂.2) ((native env q).run state)
      ((native env q).run state) := by
  rcases q with coin | command
  · simp only [native, coinLift, StateT.run_lift]
    exact (Coupled.query _).bind fun r₁ r₂ hr => .pure _ _ ⟨hr, rfl⟩
  · cases command
    case create pin keyId =>
      exact (environmentStep_couple env ⟨.create pin keyId, trivial⟩ state).mono fun a b hab => hab ▸ ⟨rfl, rfl⟩
    case bundle owner =>
      exact (environmentStep_couple env ⟨.bundle owner, trivial⟩ state).mono fun a b hab => hab ▸ ⟨rfl, rfl⟩
    case accept raw =>
      exact (environmentStep_couple env ⟨.accept raw, trivial⟩ state).mono fun a b hab => hab ▸ ⟨rfl, rfl⟩
    case build session payload =>
      exact (environmentStep_couple env ⟨.build session payload, trivial⟩ state).mono fun a b hab => hab ▸ ⟨rfl, rfl⟩
    case finish owner raw =>
      exact (environmentStep_couple env ⟨.finish owner raw, trivial⟩ state).mono fun a b hab => hab ▸ ⟨rfl, rfl⟩
    case hmac key message =>
      exact (environmentStep_couple env ⟨.hmac key message, trivial⟩ state).mono fun a b hab => hab ▸ ⟨rfl, rfl⟩
    all_goals
      simp only [native, effectLift, StateT.run_lift]
      exact (Coupled.query _).bind fun r₁ r₂ hr => .pure _ _ ⟨hr, rfl⟩

/-- Replies of a mode-O full-interface query: raw receives agree on success, everything else is equal. -/
def FullRel : (q : PqxdhDeploymentInterface.FullSpec.Domain) → PqxdhDeploymentInterface.FullSpec.Range q →
    PqxdhDeploymentInterface.FullSpec.Range q → Prop
  | .inl q => SpecRel q
  | .inr _ => fun r₁ r₂ => r₁ = r₂

/-- Replies related by `SpecRel` have the same mode-P view. -/
theorem view_spec (q : PqxdhDeploymentInterface.Spec.Domain) (r₁ r₂ : PqxdhDeploymentInterface.Spec.Range q)
    (related : SpecRel q r₁ r₂) :
    PqxdhDeploymentInterface.Entry.view .P ⟨.inl q, r₁⟩ = PqxdhDeploymentInterface.Entry.view .P ⟨.inl q, r₂⟩ := by
  rcases q with coin | command
  · cases (show r₁ = r₂ from related)
    rfl
  · cases command
    case serverRaw raw =>
      simp only [PqxdhDeploymentInterface.Entry.view, PqxdhDeploymentInterface.project]
      rw [show PqxdhDeploymentInterface.succeeded r₁ = PqxdhDeploymentInterface.succeeded r₂ from related]
    case beaconRaw owner raw =>
      simp only [PqxdhDeploymentInterface.Entry.view, PqxdhDeploymentInterface.project]
      rw [show PqxdhDeploymentInterface.succeeded r₁ = PqxdhDeploymentInterface.succeeded r₂ from related]
    all_goals
      cases (show r₁ = r₂ from related)
      rfl

/-- Two ledgers agree on the mode-P view of their transcripts, their test session and their fresh messages. -/
def LedgerRel (first second : PqxdhDeploymentSecrecy.Ledger) : Prop :=
  PqxdhDeploymentTranscript.SameView first.transcript second.transcript ∧ first.test = second.test ∧
    first.fresh = second.fresh

/-- Recording two entries with the same mode-P view keeps two ledgers related. -/
theorem ledgerRel_record (first second : PqxdhDeploymentSecrecy.Ledger) (related : LedgerRel first second)
    (q : PqxdhDeploymentInterface.Query) (r₁ r₂ : PqxdhDeploymentInterface.FullSpec.Range q)
    (view : PqxdhDeploymentInterface.Entry.view .P ⟨q, r₁⟩ = PqxdhDeploymentInterface.Entry.view .P ⟨q, r₂⟩) :
    LedgerRel (first.record q r₁) (second.record q r₂) := by
  refine ⟨?_, related.2.1, related.2.2⟩
  have same := related.1
  simp only [PqxdhDeploymentTranscript.SameView] at same ⊢
  simp only [PqxdhDeploymentSecrecy.Ledger.record, List.map_append, List.map_cons, List.map_nil, same, view]

/-- The test-session check reads a transcript only through its mode-P view. -/
theorem sameSession_view (crypto : Pqxdh.Crypto) {Reader Response : Type}
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (first second : List PqxdhDeploymentInterface.Entry) (same : PqxdhDeploymentTranscript.SameView first second)
    (designated handle : PqxdhDeploymentInterface.Handle) :
    PqxdhDeploymentSecrecy.SameSession crypto codec serverKid first designated handle ↔
      PqxdhDeploymentSecrecy.SameSession crypto codec serverKid second designated handle := by
  unfold PqxdhDeploymentSecrecy.SameSession
  rw [(PqxdhDeploymentTranscript.designate_view crypto codec serverKid first second same).1]

/-- A ledger send is coupled with itself with equal replies. -/
theorem send_couple (handle : PqxdhDeploymentInterface.Handle) (plaintext : Pqxdh.Bytes) :
    Coupled SpecRel (fun r₁ r₂ => r₁ = r₂) (PqxdhDeploymentSecrecy.send handle plaintext)
      (PqxdhDeploymentSecrecy.send handle plaintext) := by
  cases handle with
  | peer keyId => exact Coupled.query (Rr := SpecRel) (.inr (.serverSend keyId plaintext))
  | owner index => exact Coupled.query (Rr := SpecRel) (.inr (.beaconSend index plaintext))

/-- The hidden test bit's draw is coupled with itself with equal values. -/
theorem drawBit_couple :
    Coupled SpecRel (fun r₁ r₂ => r₁ = r₂) PqxdhDeploymentSecrecy.drawBit PqxdhDeploymentSecrecy.drawBit :=
  (Coupled.query (Rr := SpecRel) (.inl 1)).map fun a b h => by
    cases (show a = b from h)
    rfl

/-- A fresh message's draw is coupled with itself with equal values. -/
theorem uniformBytes_couple (length : Nat) :
    Coupled SpecRel (fun r₁ r₂ => r₁ = r₂) (PqxdhDeploymentSecrecy.uniformBytes length)
      (PqxdhDeploymentSecrecy.uniformBytes length) := by
  induction length with
  | zero => exact .pure _ _ rfl
  | succ length ih =>
      simp only [PqxdhDeploymentSecrecy.uniformBytes, PqxdhDeploymentSecrecy.coin]
      exact (Coupled.query (Rr := SpecRel) (.inl 255)).bind fun a b h => by
        cases (show a = b from h)
        exact ih.bind fun r₁ r₂ h' => by
          cases h'
          exact .pure _ _ rfl

/-- **Ledger coupling.** The secrecy layer on two ledgers that agree up to raw-receive plaintexts answers every query with replies related by `FullRel` and ledgers that again agree, whenever native replies are related by `SpecRel`. -/
theorem ledger_couple (crypto : Pqxdh.Crypto) {Reader Response : Type}
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (q : PqxdhDeploymentInterface.FullSpec.Domain)
    (first second : PqxdhDeploymentSecrecy.Ledger) (related : LedgerRel first second) :
    Coupled SpecRel (fun p₁ p₂ => FullRel q p₁.1 p₂.1 ∧ LedgerRel p₁.2 p₂.2)
      ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds q).run first)
      ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds q).run second) := by
  rcases q with query | secrecy
  · exact (Coupled.query (Rr := SpecRel) query).map fun r₁ r₂ hr =>
      ⟨hr, ledgerRel_record first second related (.inl query) r₁ r₂ (view_spec query r₁ r₂ hr)⟩
  · cases secrecy with
    | test handle left right =>
        simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
        by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
        · simp only [admissible, ↓reduceIte]
          rw [related.2.1]
          cases hsession : second.test with
          | none =>
              exact drawBit_couple.bind fun bit _ hbit => by
                cases hbit
                exact (send_couple _ _).bind fun reply _ hreply => by
                  cases hreply
                  exact .pure _ _ ⟨rfl, (ledgerRel_record first second related (.inr (.test handle left right)) reply reply rfl).1, rfl,
                    (ledgerRel_record first second related (.inr (.test handle left right)) reply reply rfl).2.2⟩
          | some session =>
              by_cases same : PqxdhDeploymentSecrecy.SameSession crypto codec serverKid second.transcript
                session.first handle
              · have same₁ := (sameSession_view crypto codec serverKid first.transcript second.transcript related.1
                  session.first handle).2 same
                simp only [same, same₁, ↓reduceIte]
                exact (send_couple _ _).bind fun reply _ hreply => by
                  cases hreply
                  exact .pure _ _ ⟨rfl, (ledgerRel_record first second related (.inr (.test handle left right)) reply reply rfl).1, rfl,
                    (ledgerRel_record first second related (.inr (.test handle left right)) reply reply rfl).2.2⟩
              · have same₁ : ¬PqxdhDeploymentSecrecy.SameSession crypto codec serverKid first.transcript
                    session.first handle := fun hit =>
                  same ((sameSession_view crypto codec serverKid first.transcript second.transcript related.1
                    session.first handle).1 hit)
                simp only [same, same₁, ↓reduceIte]
                exact .pure _ _ ⟨rfl, ledgerRel_record first second related (.inr (.test handle left right)) none none rfl⟩
        · simp only [admissible, ↓reduceIte]
          exact .pure _ _ ⟨rfl, ledgerRel_record first second related (.inr (.test handle left right)) none none rfl⟩
    | fresh handle length =>
        simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
        by_cases inRange : bounds.min ≤ length ∧ length ≤ bounds.max
        · simp only [inRange, and_self, ↓reduceIte]
          exact (uniformBytes_couple length).bind fun message _ hmessage => by
            cases hmessage
            exact (send_couple _ _).bind fun reply _ hreply => by
              cases hreply
              exact .pure _ _ ⟨rfl, (ledgerRel_record first second related (.inr (.fresh handle length)) reply reply rfl).1,
                (ledgerRel_record first second related (.inr (.fresh handle length)) reply reply rfl).2.1, by
                  simp only [related.2.2]⟩
        · simp only [inRange, ↓reduceIte]
          exact .pure _ _ ⟨rfl, ledgerRel_record first second related (.inr (.fresh handle length)) none none rfl⟩

/-- Mode P observes coupled mode-O replies as equal replies. -/
theorem observeFull_couple (q : PqxdhDeploymentInterface.FullSuccessSpec.Domain) :
    Coupled FullRel (EqRel q) (PqxdhDeploymentInterface.observeFull q) (PqxdhDeploymentInterface.observeFull q) := by
  rcases q with (coin | command) | secrecy
  · exact Coupled.query (Rr := FullRel) (.inl (.inl coin))
  · cases command
    case serverRaw raw =>
      exact (Coupled.query (Rr := FullRel) (.inl (.inr (.serverRaw raw)))).map fun _ _ h => h
    case beaconRaw owner raw =>
      exact (Coupled.query (Rr := FullRel) (.inl (.inr (.beaconRaw owner raw)))).map fun _ _ h => h
    case create pin keyId => exact Coupled.query (Rr := FullRel) (.inl (.inr (.create pin keyId)))
    case bundle owner => exact Coupled.query (Rr := FullRel) (.inl (.inr (.bundle owner)))
    case accept raw => exact Coupled.query (Rr := FullRel) (.inl (.inr (.accept raw)))
    case build session payload => exact Coupled.query (Rr := FullRel) (.inl (.inr (.build session payload)))
    case finish owner raw => exact Coupled.query (Rr := FullRel) (.inl (.inr (.finish owner raw)))
    case hmac key message => exact Coupled.query (Rr := FullRel) (.inl (.inr (.hmac key message)))
    case hash bytes => exact Coupled.query (Rr := FullRel) (.inl (.inr (.hash bytes)))
    case serverSend keyId plaintext => exact Coupled.query (Rr := FullRel) (.inl (.inr (.serverSend keyId plaintext)))
    case beaconSend owner plaintext => exact Coupled.query (Rr := FullRel) (.inl (.inr (.beaconSend owner plaintext)))
  · exact Coupled.query (Rr := FullRel) (.inr secrecy)

/-- The mode-P adversary, run as a mode-O program, is coupled with itself. -/
theorem adversary_couple {X : Type} (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) :
    Coupled FullRel (fun a b => a = b) (PqxdhDeploymentInterface.asModeO .P adversary)
      (PqxdhDeploymentInterface.asModeO .P adversary) :=
  Coupled.simulateQ (Rr := EqRel) _ _ observeFull_couple (Coupled.refl _ eqRel_eq fun _ => rfl)

/-- The secrecy wrapper of the mode-P adversary is coupled with itself. -/
theorem wrap_couple (crypto : Pqxdh.Crypto) {Reader Response : Type}
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) {X : Type}
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) :
    Coupled SpecRel (fun p₁ p₂ => p₁.1 = p₂.1 ∧ LedgerRel p₁.2 p₂.2)
      (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (PqxdhDeploymentInterface.asModeO .P adversary))
      (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (PqxdhDeploymentInterface.asModeO .P adversary)) :=
  Coupled.simulateQ_run _ _ LedgerRel (ledger_couple crypto codec serverKid bounds) (adversary_couple adversary)
    _ _ ⟨rfl, rfl, rfl⟩

/-- Client results agree on the creation, the output, the environment state and the ledger up to raw-receive plaintexts. -/
def ResultRel {E X : Type} :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E) →
      Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E) → Prop
  | none, none => True
  | some first, some second => first.1 = second.1 ∧ first.2.1.1 = second.2.1.1 ∧ LedgerRel first.2.1.2 second.2.1.2 ∧
      first.2.2 = second.2.2
  | _, _ => False

/-- The frozen world program with the mode-P adversary is coupled with itself. -/
theorem worldProgram_couple {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) :
    Coupled WorldRel ResultRel (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds .P adversary)
      (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds .P adversary) := by
  unfold PqxdhRecordLiftInterface.program
  refine (Coupled.simulateQ (Rr := EqRel) _ _ (fun q => Coupled.query (Rr := WorldRel) (.inr (.inl (.inl q))))
    (Coupled.refl env.start eqRel_eq (Ro := Eq) fun _ => rfl)).bind fun born _ hborn => ?_
  cases hborn
  rcases born with _ | ⟨created, initial⟩
  · exact .pure _ _ trivial
  · refine (Coupled.query (Rr := WorldRel) (.inl created)).bind fun _ _ _ => ?_
    refine (Coupled.simulateQ_run _ _ Eq (fun q e₁ _ he => he ▸ native_couple env q e₁)
      (wrap_couple crypto codec serverKid bounds adversary) initial initial rfl).bind fun p₁ p₂ hp => ?_
    exact .pure _ _ ⟨rfl, hp.1.1, hp.1.2, hp.2⟩

/-- The compiled protocol program with the mode-P adversary is coupled with itself. -/
theorem program_couple {E X Reader Response : Type} (env : Environment n E) (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) :
    Coupled ServiceRel (fun p₁ p₂ => ResultRel p₁.1 p₂.1 ∧ p₁.2 = p₂.2)
      (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds .P adversary)
      (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds .P adversary) :=
  schedule_couple _ route (worldProgram_couple env crypto codec serverKid bounds adversary) _

/-- **World coupling.** In the random-ciphertext CTX world, two plaintext replacements that agree on lengths give, with the same coins, client results that agree up to raw-receive plaintexts, the same control state and private states that agree up to recorded seal plaintexts. -/
theorem ctxRun_couple {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes) (lengths : ∀ m, (replace₁ m).length = (replace₂ m).length)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) :
    Coupled EqRel (fun p₁ p₂ => (ResultRel p₁.1.1 p₂.1.1 ∧ p₁.1.2 = p₂.1.2) ∧ PrivRel p₁.2 p₂.2)
      (ctxRun (fun _ => .random) replace₁ setup codec route env serverKid bounds .P adversary)
      (ctxRun (fun _ => .random) replace₂ setup codec route env serverKid bounds .P adversary) :=
  Coupled.simulateQ_run _ _ PrivRel (interpreter_couple replace₁ replace₂ lengths setup codec)
    (program_couple env setup.source.crypto codec route serverKid bounds adversary) _ _ ⟨rfl, fun _ => rfl⟩

/-- Related final results have the same hiding projection. -/
theorem hidingView_rel {E X : Type} (p₁ p₂ : Client n E X × CtxPrivate n)
    (related : (ResultRel p₁.1.1 p₂.1.1 ∧ p₁.1.2 = p₂.1.2) ∧ PrivRel p₁.2 p₂.2) :
    hidingView (ctxView p₁) = hidingView (ctxView p₂) := by
  obtain ⟨⟨result₁, control₁⟩, state₁⟩ := p₁
  obtain ⟨⟨result₂, control₂⟩, state₂⟩ := p₂
  obtain ⟨⟨results, controls⟩, base, _⟩ := related
  simp only at results controls base
  subst controls
  simp only [ctxView, viewOf, hidingView, base]
  rcases result₁ with _ | first <;> rcases result₂ with _ | second <;> simp only [ResultRel] at results
  · rfl
  · obtain ⟨_, output, ledger, environment⟩ := results
    have transcript : first.2.1.2.transcript.map (PqxdhDeploymentInterface.Entry.view .P) =
        second.2.1.2.transcript.map (PqxdhDeploymentInterface.Entry.view .P) := ledger.1
    simp only [Option.map_some, output, environment, ledger.2.1, ledger.2.2, transcript]

end Client

/-! ### `idealRecords_hiding` -/

section Hiding
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Hiding for any two plaintext replacements that agree on lengths: in the random-ciphertext world in mode P, the law of the hiding projection (output, mode-P transcript, test session with its bit, fresh messages, environment state, produced frames, raw counters, handle-to-slot map) is the same. -/
theorem hiding_replace (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) {E X : Type} (env : Environment n E)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec .P) X) (replace₁ replace₂ : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ m, (replace₁ m).length = (replace₂ m).length) :
    (fun result => hidingView (ctxView result)) <$>
        ctxRun (fun _ => .random) replace₁ setup codec route env serverKid bounds .P adversary =
      (fun result => hidingView (ctxView result)) <$>
        ctxRun (fun _ => .random) replace₂ setup codec route env serverKid bounds .P adversary :=
  (ctxRun_couple replace₁ replace₂ lengths setup codec route env serverKid bounds adversary).map_eq _ _
    fun p₁ p₂ related => hidingView_rel p₁ p₂ related

/-- **`idealRecords_hiding` (H-5), delivered.** `HidingStatement` as defined in `PqxdhRecordLiftIdeal`: in mode P, replacing every hidden seal plaintext by one of equal length leaves the law of the hiding projection of `idealRecords` unchanged. No contract. -/
theorem idealRecords_hiding (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (n : Nat) :
    HidingStatement setup codec route serverKid bounds n := by
  intro E X env adversary replace lengths
  exact hiding_replace setup codec route serverKid bounds env adversary replace id lengths

end Hiding

end BeaconcryptCore.Computational.PqxdhRecordLiftHiding

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.query' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.refl' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.of_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.of_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.map_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.map_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.simulateQ_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.simulateQ_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.simulateQ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.simulateQ

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.refl_weighted' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.Coupled.refl_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.eqRel_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.eqRel_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.replay_isSome' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.replay_isSome

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.localRaw_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.localRaw_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.randomSeal_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.randomSeal_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.randomImpl_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.randomImpl_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hash_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hash_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sampled_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sampled_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.privRel_update' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.privRel_update

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.keyed_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.keyed_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.keyed_seal_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.keyed_seal_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.succeeded_apiReply' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.succeeded_apiReply

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hiddenOpening_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hiddenOpening_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.opening_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.opening_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sealing_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sealing_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hiddenSealing_wide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hiddenSealing_wide

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sealing_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sealing_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.serviceRel_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.serviceRel_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.base_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.base_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.interpreter_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.interpreter_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.refl_noOpening' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.refl_noOpening

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.normalFinish_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.normalFinish_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.receiveProgram_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.receiveProgram_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.kernelReceive_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.kernelReceive_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ownerReceive_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ownerReceive_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ownerRun_raw_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ownerRun_raw_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.handler_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.handler_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.schedule_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.schedule_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.environmentStep_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.environmentStep_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.native_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.native_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.view_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.view_spec

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ledgerRel_record' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ledgerRel_record

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sameSession_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.sameSession_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.send_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.send_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.drawBit_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.drawBit_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.uniformBytes_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.uniformBytes_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ledger_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ledger_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.observeFull_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.observeFull_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.adversary_couple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.adversary_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.wrap_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.wrap_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.worldProgram_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.worldProgram_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.program_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.program_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ctxRun_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.ctxRun_couple

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hidingView_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hidingView_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hiding_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.hiding_replace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftHiding.idealRecords_hiding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftHiding.idealRecords_hiding

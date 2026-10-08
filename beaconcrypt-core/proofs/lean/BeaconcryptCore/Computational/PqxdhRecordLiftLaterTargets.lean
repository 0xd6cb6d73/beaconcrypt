-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds

/-!
# Record-lift later-quantum targets: the lifts and hiding with the generic post phase (items 4 and 5, stage S6, R6)

Definitions of the later-quantum forms of the targets of `PqxdhRecordLiftIdeal`, over the later worlds of `PqxdhRecordLiftLaterWorlds` (the compiled two-phase program `PqxdhRecordLiftLater.program` under every lookup policy and CTX mode), and the relations between them. No target is proved here; `PqxdhRecordLiftLaterChain`, `PqxdhRecordLiftLaterCtx`, `PqxdhRecordLiftLaterPriv`, `PqxdhRecordLiftLaterHiding` and `PqxdhRecordLiftLaterLift` prove them.

**Quantifiers.** Every later lift is quantified, like its run-phase target, over every environment with `Frame env startup allowance`, every observation mode and run-phase adversary `first` with `Budget.Respects`, and additionally over every reveal function `reveal : E → R` of the run-final environment state, every post adversary `second : X → R → OracleComp PostSpec Out` and every post budget `PostBudget` that `second output disclosed` respects for every run-phase output and every disclosed value (the premise of `PqxdhRecordLiftLater.program_effect_bound`). Decisions read the later view: the post adversary's output, the run-phase ledger, the environment's state after the post phase, the produced frames, the raw-attempt counters and the handle-to-slot map; chain decisions may also read the final shared BLAKE2b cache, which includes the post phase's hashes (decision D4 unchanged).

**Losses and bills.** The losses are the run-phase losses (`hopLoss`, `integrityLoss`, `privacyLoss`) of explicit reductions, summed with coefficient one over the same `hops n budget` ordered indices: the post phase makes no record request, so it derives no further hidden coordinate. Reductions (`LaterChainReduction`, `LaterCtxReduction`) are built from the environment, the observation mode, the reveal, both adversaries, the decision, the run budget and the post budget; bills (`LaterChainBills`, `LaterCtxBills`) are functions of `LaterBillInput`, the run-phase `BillInput` with the post budget. `postHash` is the post phase's shared-hash work (its own BLAKE2b requests plus the environment's class-six hash allowance per post HMAC request, `PqxdhRecordLiftLater.postCost`), the `qHash₂` term of the hash route, and `laterSharedHashTotal` adds it to the run-phase total `sharedHashTotal`.

**Targets.** `LaterChainLiftStatement`, `LaterCtxAuthLiftStatement`, `LaterCtxPrivLiftStatement`, `LaterCtxLiftStatement`, `LaterRecordAuthLiftStatement` and `LaterRecordLiftStatement`, each two-sided with a `boolDistAdvantage` form and an event form, and `LaterHidingStatement` (mode P, plaintext replacement leaves the law of `hidingView` of `laterIdealRecords` unchanged); the `...Target` abbreviations fix the aliasing and refusal terms to zero (decision D3). No later origin, binding, fresh-guess or left-or-right statement is defined. Origin and binding are excluded by design: the later mode claims confidentiality only. `PqxdhRecordLiftLaterWorlds.laterReal_event` carries every event of the run-phase projection `runEventView` over to the later real world, but not the record-lift origin and binding events, which also read the handle-to-slot map that the post phase can extend. The later fresh-guess and left-or-right forms are open, as are their run-phase forms. The event forms follow from the Boolean forms (`laterChainLiftStatement_of_bool` and the five siblings), the composed lifts from their parts by the triangle inequality with coefficient one (`laterRecordLiftBool_of_parts`, `laterCtxLiftBool_of_parts`, `laterRecordAuthLiftBool_of_parts`), and the hiding target gives advantage zero (`laterHiding_advantage`, `laterHiding_event`).

**Contracts.** The definitions name only contracts of the brief's H-7 list: `SourceFullCorrect` (chain and record lifts); IND$, INT-CTXT, HMAC-PRF and Extract-on-`uniform32` enter only as advantage terms. No theorem of this module has an assumption or contract hypothesis. The five relation theorems about the chain and record targets carry `SourceFullCorrect` only as the premise inside the target statements they relate; otherwise the theorems of this module reach contract fields only inside definitions (structurally: the DH-interface fields `dh_comm`, `xpub_length` and `x25519_length` through the type of `setup`, `hkdf_length` through the KDF definitions behind the real chain table, and `aeadSeal_tag_length` through the AEAD record-building definitions of the CTX worlds); per-theorem closure probe. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal PqxdhRecordLiftLaterWorlds
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhServerAuthExperiment (Setup Codec)
open CtxRomAuth AdaptiveCtxReceive
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X Out R : Type}

/-! ### Bills and reductions of the later forms -/

/-- Everything a later bill may depend on: the run-phase bill input and the separate post-phase budget. -/
structure LaterBillInput where
  base : BillInput
  post : PostBudget

/-- The post phase's shared-hash work: its own BLAKE2b requests plus the environment's class-six hash allowance for each post HMAC request (`PqxdhRecordLiftLater.postCost`), the `qHash₂` term of the hash route. -/
def postHash (input : LaterBillInput) : Nat :=
  PqxdhRecordLiftLater.postCost input.base.allowance input.post .hash

/-- The later shared-hash total: the run-phase total of `PqxdhRecordLiftIdeal.sharedHashTotal` plus the post phase's shared-hash work (`PqxdhRecordLiftLater.run_hash`). -/
def laterSharedHashTotal (input : LaterBillInput) : Nat :=
  sharedHashTotal input.base + postHash input

/-- A later chain reduction family: for every environment, observation mode, reveal function, run-phase adversary, post adversary, chain decision, run budget and post budget, one explicit full76 observer per ordered hybrid index. -/
abbrev LaterChainReduction (n : Nat) :=
  ∀ {E X Out R : Type}, Environment n E → (mode : Mode) → (E → R) → OracleComp (ModeSpec mode) X →
    (X → R → OracleComp PostSpec Out) → (View n E Out → CtxRO.QueryCache → ProbComp Bool) → (budget : Budget) →
      PostBudget → Fin (hops n budget) → PqxdhFullSecretInputKdf.FullObserver Unit

/-- A later CTX reduction family: for every environment, observation mode, reveal function, run-phase adversary, post adversary, cache-free decision, run budget and post budget, one explicit ordinary one-key CTX adversary per target key index. -/
abbrev LaterCtxReduction (n : Nat) :=
  ∀ {E X Out R : Type}, Environment n E → (mode : Mode) → (E → R) → OracleComp (ModeSpec mode) X →
    (X → R → OracleComp PostSpec Out) → (View n E Out → ProbComp Bool) → (budget : Budget) → PostBudget →
      Fin (hops n budget) → OracleComp ReceiveSpec Bool

/-- Later chain bills: the uniform coins of each hop's observer, as a function of the later bill input. -/
structure LaterChainBills where
  observer : LaterBillInput → Nat

/-- Later CTX bills: uniform, shared-hash, seal and raw caps of each per-key adversary, as functions of the later bill input. -/
structure LaterCtxBills where
  uniform : LaterBillInput → Nat
  hash : LaterBillInput → Nat
  seals : LaterBillInput → Nat
  raw : LaterBillInput → Nat

/-- A per-key CTX adversary respects its later bills. -/
def LaterCtxBounded (client : OracleComp ReceiveSpec Bool) (bills : LaterCtxBills) (input : LaterBillInput) : Prop :=
  client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceUniform (bills.uniform input) ∧
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceHash (bills.hash input) ∧
    client.IsQueryBoundP AdaptiveCtxQueryBounds.SourceSeal (bills.seals input) ∧
    client.IsQueryBoundP IsRawQuery (bills.raw input)

/-- The zero term of the later forms (decision D3). -/
def laterNoTerm : LaterBillInput → ℝ≥0∞ := fun _ => 0

/-! ### Later target statements -/

section Targets
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- Later `chain_lift`, Boolean form: for every environment with `Frame`, reveal function, run-phase adversary with `Budget.Respects`, post adversary within its `PostBudget` for every output and disclosure, and every decision on the later view and the final shared cache, the later real and chain-ideal worlds differ by at most the sum over the ordered hybrid indices of the hop losses of the supplied observers, plus the aliasing and refusal terms; every observer respects its bill. Contract: `SourceFullCorrect`. -/
def LaterChainLiftBool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : LaterChainReduction n)
    (bills : LaterChainBills) (aliasing refusal : LaterBillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ (decision : View n E Out → CtxRO.QueryCache → ProbComp Bool) (cost : Nat),
    (∀ view cache, (decision view cache).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((laterRealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (chainView result) (chainCache result)).boolDistAdvantage
        (laterIdealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (chainView result) (chainCache result))) ≤
      (∑ step, hopLoss hmac (reduction env mode reveal first second decision budget post step)) +
        aliasing ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩ +
        refusal ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩ ∧
    ∀ step context output, (reduction env mode reveal first second decision budget post step context output).IsTotalQueryBound
      (bills.observer ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩)

/-- Later `chain_lift`, event form: the same for every Boolean event of the later view and the final shared cache. -/
def LaterChainLiftEvent (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : LaterChainReduction n)
    (bills : LaterChainBills) (aliasing refusal : LaterBillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ event : View n E Out → CtxRO.QueryCache → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result) (chainCache result)) <$>
        laterRealChains setup codec route env serverKid bounds mode reveal first second] {true}).toReal -
      (𝒟[(fun result => event (chainView result) (chainCache result)) <$>
        laterIdealChains setup codec route env serverKid bounds mode reveal first second] {true}).toReal| ≤
      (∑ step, hopLoss hmac (reduction env mode reveal first second (fun view cache => pure (event view cache)) budget
        post step)) +
        aliasing ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩ + refusal ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩ ∧
    ∀ step context output, (reduction env mode reveal first second (fun view cache => pure (event view cache)) budget post
      step context output).IsTotalQueryBound (bills.observer ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩)

/-- Later `chain_lift`, both forms. -/
def LaterChainLiftStatement (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : LaterChainReduction n)
    (bills : LaterChainBills) (aliasing refusal : LaterBillInput → ℝ≥0∞) : Prop :=
  LaterChainLiftBool setup codec route serverKid bounds n hmac reduction bills aliasing refusal ∧
    LaterChainLiftEvent setup codec route serverKid bounds n hmac reduction bills aliasing refusal

/-- Later `ctx_lift`, integrity half, Boolean form: in either mode, the later chain-ideal and integrity-ideal worlds differ, for every cache-free decision on the later view, by at most the exact sum over target key indices of the per-key integrity losses of the supplied one-key adversaries at their hash and raw bills, plus the refusal term; every adversary respects its bills. -/
def LaterCtxAuthLiftBool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : LaterCtxReduction n) (bills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞) : Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ (decision : View n E Out → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((laterIdealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (laterIdealAuth setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (ctxView result))) ≤
      (∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
        (reduction env mode reveal first second decision budget post step)
        (bills.hash ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩)
        (bills.raw ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩)) +
        refusal ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩ ∧
    ∀ step, LaterCtxBounded (reduction env mode reveal first second decision budget post step) bills
      ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩

/-- Later `ctx_lift`, integrity half, event form. -/
def LaterCtxAuthLiftEvent (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : LaterCtxReduction n) (bills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞) : Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ event : View n E Out → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        laterIdealChains setup codec route env serverKid bounds mode reveal first second] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        laterIdealAuth setup codec route env serverKid bounds mode reveal first second] {true}).toReal| ≤
      (∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
        (reduction env mode reveal first second (fun view => pure (event view)) budget post step)
        (bills.hash ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩)
        (bills.raw ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩)) +
        refusal ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩ ∧
    ∀ step, LaterCtxBounded (reduction env mode reveal first second (fun view => pure (event view)) budget post step)
      bills ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩

/-- Later `ctx_lift`, integrity half, both forms. -/
def LaterCtxAuthLiftStatement (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : LaterCtxReduction n) (bills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞) : Prop :=
  LaterCtxAuthLiftBool setup codec route serverKid bounds n fallback reduction bills refusal ∧
    LaterCtxAuthLiftEvent setup codec route serverKid bounds n fallback reduction bills refusal

/-- Later `ctx_lift`, privacy half, Boolean form: in either mode, the later integrity-ideal world and the later random-ciphertext world differ, for every cache-free decision on the later view, by at most the exact sum over target key indices of the per-key IND$ losses of the supplied view reductions. In mode P the right world is `laterIdealRecords` (`laterIdealRecords_P`). -/
def LaterCtxPrivLiftBool (n : Nat) (reduction : LaterCtxReduction n) (bills : LaterCtxBills) : Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ (decision : View n E Out → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((laterIdealAuth setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (ctxView result)).boolDistAdvantage
        (laterRandomRecords setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (ctxView result))) ≤
      (∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (reduction env mode reveal first second decision budget post step)) ∧
    ∀ step, LaterCtxBounded (reduction env mode reveal first second decision budget post step) bills
      ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩

/-- Later `ctx_lift`, privacy half, event form. -/
def LaterCtxPrivLiftEvent (n : Nat) (reduction : LaterCtxReduction n) (bills : LaterCtxBills) : Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ event : View n E Out → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (ctxView result)) <$>
        laterIdealAuth setup codec route env serverKid bounds mode reveal first second] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        laterRandomRecords setup codec route env serverKid bounds mode reveal first second] {true}).toReal| ≤
      (∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
        (reduction env mode reveal first second (fun view => pure (event view)) budget post step)) ∧
    ∀ step, LaterCtxBounded (reduction env mode reveal first second (fun view => pure (event view)) budget post step)
      bills ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩

/-- Later `ctx_lift`, privacy half, both forms. -/
def LaterCtxPrivLiftStatement (n : Nat) (reduction : LaterCtxReduction n) (bills : LaterCtxBills) : Prop :=
  LaterCtxPrivLiftBool setup codec route serverKid bounds n reduction bills ∧
    LaterCtxPrivLiftEvent setup codec route serverKid bounds n reduction bills

/-- The later `ctx_lift` loss: the integrity loss and the refusal term and, in mode P, the privacy loss. -/
noncomputable def laterCtxLoss (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : LaterCtxReduction n) (authBills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞)
    (env : Environment n E) (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) (decision : View n E Out → ProbComp Bool) (budget : Budget)
    (post : PostBudget) (input : LaterBillInput) : ℝ≥0∞ :=
  ((∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
      (auth env mode reveal first second decision budget post step) (authBills.hash input) (authBills.raw input)) +
    refusal input) +
  (if mode = .P then ∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (privacy env mode reveal first second decision budget post step) else 0)

/-- The bills of later `ctx_lift`: the integrity adversaries and, in mode P, the privacy adversaries. -/
def LaterCtxLiftBounded (n : Nat) (auth privacy : LaterCtxReduction n) (authBills privacyBills : LaterCtxBills)
    (env : Environment n E) (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) (decision : View n E Out → ProbComp Bool) (budget : Budget)
    (post : PostBudget) (input : LaterBillInput) : Prop :=
  (∀ step, LaterCtxBounded (auth env mode reveal first second decision budget post step) authBills input) ∧
    (mode = .P → ∀ step, LaterCtxBounded (privacy env mode reveal first second decision budget post step) privacyBills
      input)

/-- Later `ctx_lift`, Boolean form: the later chain-ideal world and `laterIdealRecords` differ, for every cache-free decision on the later view, by at most `laterCtxLoss`; all reductions respect their bills. -/
def LaterCtxLiftBool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : LaterCtxReduction n) (authBills privacyBills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞) :
    Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ (decision : View n E Out → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((laterIdealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (laterIdealRecords setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (ctxView result))) ≤
      laterCtxLoss setup codec n fallback auth privacy authBills refusal env mode reveal first second decision budget post
        ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩ ∧
    LaterCtxLiftBounded n auth privacy authBills privacyBills env mode reveal first second decision budget post
      ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩

/-- Later `ctx_lift`, event form. -/
def LaterCtxLiftEvent (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : LaterCtxReduction n) (authBills privacyBills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞) :
    Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ event : View n E Out → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        laterIdealChains setup codec route env serverKid bounds mode reveal first second] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        laterIdealRecords setup codec route env serverKid bounds mode reveal first second] {true}).toReal| ≤
      laterCtxLoss setup codec n fallback auth privacy authBills refusal env mode reveal first second
        (fun view => pure (event view)) budget post ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩ ∧
    LaterCtxLiftBounded n auth privacy authBills privacyBills env mode reveal first second
      (fun view => pure (event view)) budget post ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩

/-- Later `ctx_lift`, both forms. -/
def LaterCtxLiftStatement (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : LaterCtxReduction n) (authBills privacyBills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞) :
    Prop :=
  LaterCtxLiftBool setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal ∧
    LaterCtxLiftEvent setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal

/-- The later record-lift loss: the chain loss at the cache-free decision, the aliasing and both refusal terms, the integrity loss and, in mode P, the privacy loss. -/
noncomputable def laterRecordLoss (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n)
    (auth privacy : LaterCtxReduction n) (authBills : LaterCtxBills)
    (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) (env : Environment n E) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (decision : View n E Out → ProbComp Bool) (budget : Budget) (post : PostBudget) (input : LaterBillInput) :
    ℝ≥0∞ :=
  ((∑ step, hopLoss hmac (chain env mode reveal first second (fun view _ => decision view) budget post step)) +
    aliasing input + chainRefusal input) +
  ((∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
      (auth env mode reveal first second decision budget post step) (authBills.hash input) (authBills.raw input)) +
    ctxRefusal input) +
  (if mode = .P then ∑ step, privacyLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto
      (privacy env mode reveal first second decision budget post step) else 0)

/-- The bills of the later record lift: the chain observers, the integrity adversaries and, in mode P, the privacy adversaries. -/
def LaterRecordBounded (n : Nat) (chain : LaterChainReduction n) (auth privacy : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills privacyBills : LaterCtxBills) (env : Environment n E) (mode : Mode)
    (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (decision : View n E Out → ProbComp Bool) (budget : Budget) (post : PostBudget) (input : LaterBillInput) : Prop :=
  (∀ step context output, (chain env mode reveal first second (fun view _ => decision view) budget post step context
      output).IsTotalQueryBound (chainBills.observer input)) ∧
    (∀ step, LaterCtxBounded (auth env mode reveal first second decision budget post step) authBills input) ∧
    (mode = .P → ∀ step, LaterCtxBounded (privacy env mode reveal first second decision budget post step) privacyBills
      input)

/-- Later `record_lift`, Boolean form: the later real world and `laterIdealRecords` differ, for every cache-free decision on the later view, by at most `laterRecordLoss`; all reductions respect their bills. Contract: `SourceFullCorrect`. -/
def LaterRecordLiftBool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n)
    (auth privacy : LaterCtxReduction n) (chainBills : LaterChainBills) (authBills privacyBills : LaterCtxBills)
    (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ (decision : View n E Out → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((laterRealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (laterIdealRecords setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (ctxView result))) ≤
      laterRecordLoss setup codec n hmac fallback chain auth privacy authBills aliasing chainRefusal ctxRefusal env mode
        reveal first second decision budget post ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩ ∧
    LaterRecordBounded n chain auth privacy chainBills authBills privacyBills env mode reveal first second decision
      budget post ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩

/-- Later `record_lift`, event form. -/
def LaterRecordLiftEvent (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n)
    (auth privacy : LaterCtxReduction n) (chainBills : LaterChainBills) (authBills privacyBills : LaterCtxBills)
    (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) : Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ event : View n E Out → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        laterRealChains setup codec route env serverKid bounds mode reveal first second] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        laterIdealRecords setup codec route env serverKid bounds mode reveal first second] {true}).toReal| ≤
      laterRecordLoss setup codec n hmac fallback chain auth privacy authBills aliasing chainRefusal ctxRefusal env mode
        reveal first second (fun view => pure (event view)) budget post ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩ ∧
    LaterRecordBounded n chain auth privacy chainBills authBills privacyBills env mode reveal first second
      (fun view => pure (event view)) budget post ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩

/-- Later `record_lift`, both forms. -/
def LaterRecordLiftStatement (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n)
    (auth privacy : LaterCtxReduction n) (chainBills : LaterChainBills) (authBills privacyBills : LaterCtxBills)
    (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) : Prop :=
  LaterRecordLiftBool setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal ∧
    LaterRecordLiftEvent setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal

/-- The later integrity record-lift loss: the chain loss at the cache-free decision, the aliasing and both refusal terms, and the integrity loss. -/
noncomputable def laterRecordAuthLoss (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (authBills : LaterCtxBills) (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) (env : Environment n E)
    (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (decision : View n E Out → ProbComp Bool) (budget : Budget) (post : PostBudget) (input : LaterBillInput) :
    ℝ≥0∞ :=
  ((∑ step, hopLoss hmac (chain env mode reveal first second (fun view _ => decision view) budget post step)) +
    aliasing input + chainRefusal input) +
  ((∑ step, integrityLoss (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto fallback
      (auth env mode reveal first second decision budget post step) (authBills.hash input) (authBills.raw input)) +
    ctxRefusal input)

/-- The bills of the later integrity record lift: the chain observers and the integrity adversaries. -/
def LaterRecordAuthBounded (n : Nat) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills : LaterCtxBills) (env : Environment n E) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (decision : View n E Out → ProbComp Bool) (budget : Budget) (post : PostBudget) (input : LaterBillInput) : Prop :=
  (∀ step context output, (chain env mode reveal first second (fun view _ => decision view) budget post step context
      output).IsTotalQueryBound (chainBills.observer input)) ∧
    ∀ step, LaterCtxBounded (auth env mode reveal first second decision budget post step) authBills input

/-- The later integrity record lift, Boolean form: in either mode, the later real world and `laterIdealAuth` differ, for every cache-free decision on the later view, by at most `laterRecordAuthLoss`; all reductions respect their bills. A distributional fact: the later mode claims no authentication. Contract: `SourceFullCorrect`. -/
def LaterRecordAuthLiftBool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills : LaterCtxBills) (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) :
    Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ (decision : View n E Out → ProbComp Bool) (cost : Nat), (∀ view, (decision view).IsTotalQueryBound cost) →
  ENNReal.ofReal
      ((laterRealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (chainView result)).boolDistAdvantage
        (laterIdealAuth setup codec route env serverKid bounds mode reveal first second >>= fun result =>
          decision (ctxView result))) ≤
      laterRecordAuthLoss setup codec n hmac fallback chain auth authBills aliasing chainRefusal ctxRefusal env mode
        reveal first second decision budget post ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩ ∧
    LaterRecordAuthBounded n chain auth chainBills authBills env mode reveal first second decision budget post
      ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩

/-- The later integrity record lift, event form. -/
def LaterRecordAuthLiftEvent (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills : LaterCtxBills) (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) :
    Prop :=
  PqxdhFullSecretInputKdf.SourceFullCorrect setup.source hmac →
  ∀ {E X Out R : Type} (env : Environment n E) (startup : Nat) (allowance : Fin 14 → EffectKind → Nat),
    Frame env startup allowance →
  ∀ (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (budget : Budget) (post : PostBudget), budget.Respects first →
    (∀ output disclosed, post.Respects (second output disclosed)) →
  ∀ event : View n E Out → Bool,
  ENNReal.ofReal |(𝒟[(fun result => event (chainView result)) <$>
        laterRealChains setup codec route env serverKid bounds mode reveal first second] {true}).toReal -
      (𝒟[(fun result => event (ctxView result)) <$>
        laterIdealAuth setup codec route env serverKid bounds mode reveal first second] {true}).toReal| ≤
      laterRecordAuthLoss setup codec n hmac fallback chain auth authBills aliasing chainRefusal ctxRefusal env mode
        reveal first second (fun view => pure (event view)) budget post ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩ ∧
    LaterRecordAuthBounded n chain auth chainBills authBills env mode reveal first second (fun view => pure (event view))
      budget post ⟨⟨budget, startup, allowance, bounds, n, 0⟩, post⟩

/-- The later integrity record lift, both forms. -/
def LaterRecordAuthLiftStatement (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills : LaterCtxBills) (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞) :
    Prop :=
  LaterRecordAuthLiftBool setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills aliasing
      chainRefusal ctxRefusal ∧
    LaterRecordAuthLiftEvent setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills aliasing
      chainRefusal ctxRefusal

/-- Later `idealRecords_hiding`, mode P: for every environment, reveal function, run-phase adversary and post adversary (no `Frame` or budget premise), replacing every hidden seal plaintext by one of equal length leaves the law of the hiding projection of the later random-ciphertext world unchanged. No contract. -/
def LaterHidingStatement (n : Nat) : Prop :=
  ∀ {E X Out R : Type} (env : Environment n E) (reveal : E → R) (first : OracleComp (ModeSpec .P) X)
    (second : X → R → OracleComp PostSpec Out) (replace : Pqxdh.Bytes → Pqxdh.Bytes),
    (∀ message, (replace message).length = message.length) →
  (fun result => hidingView (ctxView result)) <$>
      laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) replace =
    (fun result => hidingView (ctxView result)) <$>
      laterIdealRecords setup codec route env serverKid bounds .P reveal first second

/-- The intended later chain target (decision D3): zero alias and refusal terms. -/
def LaterChainLiftTarget (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512) (reduction : LaterChainReduction n)
    (bills : LaterChainBills) : Prop :=
  LaterChainLiftStatement setup codec route serverKid bounds n hmac reduction bills laterNoTerm laterNoTerm

/-- The intended later integrity target (decision D3): zero refusal term. -/
def LaterCtxAuthLiftTarget (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : LaterCtxReduction n) (bills : LaterCtxBills) : Prop :=
  LaterCtxAuthLiftStatement setup codec route serverKid bounds n fallback reduction bills laterNoTerm

/-- The intended later `ctx_lift` target (decision D3): zero refusal term. -/
def LaterCtxLiftTarget (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : LaterCtxReduction n) (authBills privacyBills : LaterCtxBills) : Prop :=
  LaterCtxLiftStatement setup codec route serverKid bounds n fallback auth privacy authBills privacyBills laterNoTerm

/-- The intended later `record_lift` target (decision D3): zero alias and refusal terms. -/
def LaterRecordLiftTarget (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n)
    (auth privacy : LaterCtxReduction n) (chainBills : LaterChainBills) (authBills privacyBills : LaterCtxBills) : Prop :=
  LaterRecordLiftStatement setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
    privacyBills laterNoTerm laterNoTerm laterNoTerm

/-- The intended later integrity record-lift target (decision D3): zero alias and refusal terms. -/
def LaterRecordAuthLiftTarget (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills : LaterCtxBills) : Prop :=
  LaterRecordAuthLiftStatement setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills
    laterNoTerm laterNoTerm laterNoTerm

end Targets

/-! ### Relations between the later forms -/

section Relations
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Std.U64) (bounds : FreshBounds)

/-- The event form of later `chain_lift` follows from its Boolean form. -/
theorem laterChainLiftStatement_of_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (reduction : LaterChainReduction n) (bills : LaterChainBills) (aliasing refusal : LaterBillInput → ℝ≥0∞)
    (bool : LaterChainLiftBool setup codec route serverKid bounds n hmac reduction bills aliasing refusal) :
    LaterChainLiftStatement setup codec route serverKid bounds n hmac reduction bills aliasing refusal := by
  refine ⟨bool, ?_⟩
  intro correct E X Out R env startup allowance frame mode reveal first second budget post respects postRespects event
  obtain ⟨bound, billed⟩ := bool correct env startup allowance frame mode reveal first second budget post respects
    postRespects (fun view cache => pure (event view cache)) 0 (fun _ _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result) (chainCache result))
    (fun result => event (chainView result) (chainCache result))]
  exact bound

/-- The event form of the later integrity half follows from its Boolean form. -/
theorem laterCtxAuthLiftStatement_of_bool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (reduction : LaterCtxReduction n) (bills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞)
    (bool : LaterCtxAuthLiftBool setup codec route serverKid bounds n fallback reduction bills refusal) :
    LaterCtxAuthLiftStatement setup codec route serverKid bounds n fallback reduction bills refusal := by
  refine ⟨bool, ?_⟩
  intro E X Out R env startup allowance frame mode reveal first second budget post respects postRespects event
  obtain ⟨bound, billed⟩ := bool env startup allowance frame mode reveal first second budget post respects postRespects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- The event form of the later privacy half follows from its Boolean form. -/
theorem laterCtxPrivLiftStatement_of_bool (n : Nat) (reduction : LaterCtxReduction n) (bills : LaterCtxBills)
    (bool : LaterCtxPrivLiftBool setup codec route serverKid bounds n reduction bills) :
    LaterCtxPrivLiftStatement setup codec route serverKid bounds n reduction bills := by
  refine ⟨bool, ?_⟩
  intro E X Out R env startup allowance frame mode reveal first second budget post respects postRespects event
  obtain ⟨bound, billed⟩ := bool env startup allowance frame mode reveal first second budget post respects postRespects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (ctxView result)) (fun result => event (ctxView result))]
  exact bound

/-- The event form of later `ctx_lift` follows from its Boolean form. -/
theorem laterCtxLiftStatement_of_bool (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : LaterCtxReduction n) (authBills privacyBills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞)
    (bool : LaterCtxLiftBool setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal) :
    LaterCtxLiftStatement setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal := by
  refine ⟨bool, ?_⟩
  intro E X Out R env startup allowance frame mode reveal first second budget post respects postRespects event
  obtain ⟨bound, billed⟩ := bool env startup allowance frame mode reveal first second budget post respects postRespects
    (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- The event form of later `record_lift` follows from its Boolean form. -/
theorem laterRecordLiftStatement_of_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n)
    (auth privacy : LaterCtxReduction n) (chainBills : LaterChainBills) (authBills privacyBills : LaterCtxBills)
    (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞)
    (bool : LaterRecordLiftBool setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills
      authBills privacyBills aliasing chainRefusal ctxRefusal) :
    LaterRecordLiftStatement setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal := by
  refine ⟨bool, ?_⟩
  intro correct E X Out R env startup allowance frame mode reveal first second budget post respects postRespects event
  obtain ⟨bound, billed⟩ := bool correct env startup allowance frame mode reveal first second budget post respects
    postRespects (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- The event form of the later integrity record lift follows from its Boolean form. -/
theorem laterRecordAuthLiftStatement_of_bool (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills : LaterCtxBills) (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞)
    (bool : LaterRecordAuthLiftBool setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills
      aliasing chainRefusal ctxRefusal) :
    LaterRecordAuthLiftStatement setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills
      aliasing chainRefusal ctxRefusal := by
  refine ⟨bool, ?_⟩
  intro correct E X Out R env startup allowance frame mode reveal first second budget post respects postRespects event
  obtain ⟨bound, billed⟩ := bool correct env startup allowance frame mode reveal first second budget post respects
    postRespects (fun view => pure (event view)) 0 (fun _ => trivial)
  refine ⟨?_, billed⟩
  rw [← pure_advantage _ _ (fun result => event (chainView result)) (fun result => event (ctxView result))]
  exact bound

/-- Later `record_lift` is the composition of its three parts by the triangle inequality, every term with coefficient one. -/
theorem laterRecordLiftBool_of_parts (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n)
    (auth privacy : LaterCtxReduction n) (chainBills : LaterChainBills) (authBills privacyBills : LaterCtxBills)
    (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞)
    (chainLift : LaterChainLiftBool setup codec route serverKid bounds n hmac chain chainBills aliasing chainRefusal)
    (authLift : LaterCtxAuthLiftBool setup codec route serverKid bounds n fallback auth authBills ctxRefusal)
    (privLift : LaterCtxPrivLiftBool setup codec route serverKid bounds n privacy privacyBills) :
    LaterRecordLiftBool setup codec route serverKid bounds n hmac fallback chain auth privacy chainBills authBills
      privacyBills aliasing chainRefusal ctxRefusal := by
  intro correct E X Out R env startup allowance frame mode reveal first second budget post respects postRespects decision
    cost costBound
  obtain ⟨chainBound, chainBilled⟩ := chainLift correct env startup allowance frame mode reveal first second budget post
    respects postRespects (fun view _ => decision view) cost (fun view _ => costBound view)
  obtain ⟨authBound, authBilled⟩ := authLift env startup allowance frame mode reveal first second budget post respects
    postRespects decision cost costBound
  have firstStep := ProbComp.boolDistAdvantage_triangle
    (laterRealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
      decision (chainView result))
    (laterIdealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
      decision (chainView result))
    (laterIdealRecords setup codec route env serverKid bounds mode reveal first second >>= fun result =>
      decision (ctxView result))
  cases mode with
  | O =>
      refine ⟨?_, chainBilled, authBilled, fun same => by cases same⟩
      calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal firstStep
        _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ := add_le_add chainBound authBound
        _ = _ := by simp only [laterRecordLoss, reduceCtorEq, ite_false, add_zero]
  | P =>
      obtain ⟨privBound, privBilled⟩ := privLift env startup allowance frame .P reveal first second budget post respects
        postRespects decision cost costBound
      refine ⟨?_, chainBilled, authBilled, fun _ => privBilled⟩
      have secondStep := ProbComp.boolDistAdvantage_triangle
        (laterIdealChains setup codec route env serverKid bounds .P reveal first second >>= fun result =>
          decision (chainView result))
        (laterIdealAuth setup codec route env serverKid bounds .P reveal first second >>= fun result =>
          decision (ctxView result))
        (laterIdealRecords setup codec route env serverKid bounds .P reveal first second >>= fun result =>
          decision (ctxView result))
      calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal firstStep
        _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ + ENNReal.ofReal (_ + _) := add_le_add le_rfl (ENNReal.ofReal_le_ofReal secondStep)
        _ = _ + (_ + _) := by
          congr 1
          exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ + (_ + _) := add_le_add chainBound (add_le_add authBound privBound)
        _ = _ := by simp only [laterRecordLoss, ite_true, add_assoc]

/-- Later `ctx_lift` is the composition of its two halves: in mode O `laterIdealRecords` is `laterIdealAuth` and the integrity half alone gives it; in mode P the triangle inequality through `laterIdealAuth` adds the privacy half, every term with coefficient one. -/
theorem laterCtxLiftBool_of_parts (n : Nat) (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery)
    (auth privacy : LaterCtxReduction n) (authBills privacyBills : LaterCtxBills) (refusal : LaterBillInput → ℝ≥0∞)
    (authLift : LaterCtxAuthLiftBool setup codec route serverKid bounds n fallback auth authBills refusal)
    (privLift : LaterCtxPrivLiftBool setup codec route serverKid bounds n privacy privacyBills) :
    LaterCtxLiftBool setup codec route serverKid bounds n fallback auth privacy authBills privacyBills refusal := by
  intro E X Out R env startup allowance frame mode reveal first second budget post respects postRespects decision cost
    costBound
  obtain ⟨authBound, authBilled⟩ := authLift env startup allowance frame mode reveal first second budget post respects
    postRespects decision cost costBound
  cases mode with
  | O =>
      refine ⟨?_, authBilled, fun same => by cases same⟩
      calc _ ≤ _ := authBound
        _ = _ := by simp only [laterCtxLoss, reduceCtorEq, ite_false, add_zero]
  | P =>
      obtain ⟨privBound, privBilled⟩ := privLift env startup allowance frame .P reveal first second budget post respects
        postRespects decision cost costBound
      refine ⟨?_, authBilled, fun _ => privBilled⟩
      have secondStep := ProbComp.boolDistAdvantage_triangle
        (laterIdealChains setup codec route env serverKid bounds .P reveal first second >>= fun result =>
          decision (chainView result))
        (laterIdealAuth setup codec route env serverKid bounds .P reveal first second >>= fun result =>
          decision (ctxView result))
        (laterIdealRecords setup codec route env serverKid bounds .P reveal first second >>= fun result =>
          decision (ctxView result))
      calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal secondStep
        _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ + _ := add_le_add authBound privBound
        _ = _ := by simp only [laterCtxLoss, ite_true]

/-- The later integrity record lift is the composition of the later chain lift at the cache-free decision and the later integrity half, by the triangle inequality with every term at coefficient one, in both modes and without any privacy reduction. -/
theorem laterRecordAuthLiftBool_of_parts (n : Nat) (hmac : PqxdhSecretInputKdf.HmacSha512)
    (fallback : CtxNonceAeadIntCtxt.ModifiedNonceAeadForgery) (chain : LaterChainReduction n) (auth : LaterCtxReduction n)
    (chainBills : LaterChainBills) (authBills : LaterCtxBills) (aliasing chainRefusal ctxRefusal : LaterBillInput → ℝ≥0∞)
    (chainLift : LaterChainLiftBool setup codec route serverKid bounds n hmac chain chainBills aliasing chainRefusal)
    (authLift : LaterCtxAuthLiftBool setup codec route serverKid bounds n fallback auth authBills ctxRefusal) :
    LaterRecordAuthLiftBool setup codec route serverKid bounds n hmac fallback chain auth chainBills authBills aliasing
      chainRefusal ctxRefusal := by
  intro correct E X Out R env startup allowance frame mode reveal first second budget post respects postRespects decision
    cost costBound
  obtain ⟨chainBound, chainBilled⟩ := chainLift correct env startup allowance frame mode reveal first second budget post
    respects postRespects (fun view _ => decision view) cost (fun view _ => costBound view)
  obtain ⟨authBound, authBilled⟩ := authLift env startup allowance frame mode reveal first second budget post respects
    postRespects decision cost costBound
  have firstStep := ProbComp.boolDistAdvantage_triangle
    (laterRealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
      decision (chainView result))
    (laterIdealChains setup codec route env serverKid bounds mode reveal first second >>= fun result =>
      decision (chainView result))
    (laterIdealAuth setup codec route env serverKid bounds mode reveal first second >>= fun result =>
      decision (ctxView result))
  refine ⟨?_, chainBilled, authBilled⟩
  calc _ ≤ ENNReal.ofReal (_ + _) := ENNReal.ofReal_le_ofReal firstStep
    _ = _ + _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add chainBound authBound

/-- The later hiding target gives every decision on the hiding projection advantage zero between replaced and unreplaced hidden plaintexts. -/
theorem laterHiding_advantage (n : Nat) (target : LaterHidingStatement setup codec route serverKid bounds n)
    (env : Environment n E) (reveal : E → R) (first : OracleComp (ModeSpec .P) X)
    (second : X → R → OracleComp PostSpec Out) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ message, (replace message).length = message.length) (decision : HidingView n E Out → ProbComp Bool) :
    (laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) replace >>= fun result =>
        decision (hidingView (ctxView result))).boolDistAdvantage
      (laterIdealRecords setup codec route env serverKid bounds .P reveal first second >>= fun result =>
        decision (hidingView (ctxView result))) = 0 := by
  have same := congrArg (fun work => work >>= decision) (target env reveal first second replace lengths)
  simp only [bind_map_left] at same
  rw [same]
  exact ProbComp.boolDistAdvantage_self _

/-- The later hiding target in event form. -/
theorem laterHiding_event (n : Nat) (target : LaterHidingStatement setup codec route serverKid bounds n)
    (env : Environment n E) (reveal : E → R) (first : OracleComp (ModeSpec .P) X)
    (second : X → R → OracleComp PostSpec Out) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ message, (replace message).length = message.length) (event : HidingView n E Out → Bool) :
    𝒟[(fun result => event (hidingView (ctxView result))) <$>
        laterCtxRun setup codec route env serverKid bounds .P reveal first second (fun _ => .random) replace] {true} =
      𝒟[(fun result => event (hidingView (ctxView result))) <$>
        laterIdealRecords setup codec route env serverKid bounds .P reveal first second] {true} := by
  have same := congrArg (fun work => event <$> work) (target env reveal first second replace lengths)
  simp only [Functor.map_map] at same
  rw [same]

end Relations

end BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterChainLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterChainLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxAuthLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxAuthLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxPrivLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxPrivLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordAuthLiftStatement_of_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordAuthLiftStatement_of_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordLiftBool_of_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordLiftBool_of_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxLiftBool_of_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterCtxLiftBool_of_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordAuthLiftBool_of_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterRecordAuthLiftBool_of_parts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterHiding_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterHiding_advantage

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterHiding_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets.laterHiding_event

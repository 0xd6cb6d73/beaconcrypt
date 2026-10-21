import BeaconcryptCore.Computational.PqxdhFirstRecordStopTagged
import BeaconcryptCore.Computational.RawCtxSelectedConfidentialityObserver

/-!
First-record left-or-right confidentiality (step S7). The notion is single-challenge adaptive left-or-right confidentiality of one honest session's first record, in the full multi-party protocol with state reveals and RCCA-style receive suppression: the first record sent by Beacon `b` hides which of two equal-length plaintexts it carries.

The experiment is the HB-112 actual game with all secrets sampled inside. The adversary drives the whole post-registration interface through the wrapper `confPost`, which forwards every post request and handles one challenge `(m0, m1)`. The challenge is sent as Beacon `b`'s send of `m_β` only if it is the first acceptable challenge, no send of Beacon `b` was requested before, and the two plaintexts have equal length; otherwise it is refused without any request. After the challenge, raw-receive replies whose plaintext is a challenge plaintext are reported to the adversary as failures. The wrapper returns the adversary's bit only for a fresh challenge whose reply is Beacon `b`'s unique sequence-one record. `confGame` is the accepted pending leaf of the HB-112 actual game with this post, so its event also requires Beacon `b`'s first record to be published from the selected root with the selected chain and record key undisclosed.

Each restriction excludes a trivial attack. Equal lengths are required because the ciphertext length reveals the plaintext length. Only the first acceptable challenge is forwarded, and only if no send of Beacon `b` was requested before, because this defines the attacked record as Beacon `b`'s first record. The bit counts only for a fresh challenge (`Fresh`) because the challenge reply must be the unique sequence-one record, whose key HB-112 selects. The selected chain and the record key must stay undisclosed because revealing the key that seals the challenge determines β. The raw-receive suppression is the replayable-CCA plaintext rule of Canetti, Krawczyk and Nielsen (CRYPTO 2003), with a failure reply in place of a separate symbol; without it, delivering the challenge record to its receiver returns `m_β` (`unscreened_reveals`). Receives take abstract byte strings, so suppression is by plaintext, not by ciphertext bytes, and needs no codec reasoning. It also hides unrelated records whose plaintext equals `m0` or `m1`, which is harmless because every other plaintext a receive can return is adversary-chosen or comes from an adversary-built ciphertext. The suppressed receive itself still takes effect. Restricting to the accepted pending leaf is the honest-session (freshness) condition, because in the completed branch Beacon `b` has no honest partnered session and the adversary may know its root. Replies of Beacon finish requests are not screened; a finish that opens with the selected material is charged to `collGame`.

The proof runs the first-record integrity chain in both directions. `PqxdhFirstRecordTarget.pending_bound` reaches the key-last endpoint. An instrumented compiled post `insImpl` carries the origin and publication transcript, a monitor recording whether Beacon `b`'s first send uses the selected hidden material, and a flag raised when a Beacon finish makes a selected raw opening (`pending_ideal_upper`, `pending_ideal_lower`, with the restricted stop game and the key-disclosure game `keyGame`). The key-free client construction and the key-first reordering follow C5 (`insObserve_eq`, `insSeparated_le_client`, `insClient_le_separated`, with the initial half-alias term). The output then switches to the confidentiality client (`twin_le_client`, `client_le_twin`, with `hiddenGapGame` and `collGame`), and the ordinary CTX privacy bound compares its selected-key source game with its random view (`source_random`). The hidden-gap game has mass zero (`hiddenGap_zero`): an origin invariant of the compiled run (`OriginInv`, `PublishInv`, `all_run`) shows that a published origin-`true` first record of Beacon `b` that the wrapper accepts comes from the challenge, and that the challenge then used the selected hidden material (`gap_free`); it rests on compiled receives keeping the send chain (`receive_chain`) and on the marked finish installing the supplied-response kernel (`owner_marked_origin`).

The two random views are equal (`random_views_equal`). The clients are adaptive twins (`Pre`): they are identical until the challenge and then become twin clients (`Twin`) for the chosen pair. In twin clients a hidden challenge seal differs only in its plaintext, raw replies are compared after identifying the right challenge plaintext with the left one, and runs are dead once the challenge was not hidden or a finish made a selected raw opening. `randomView_pre` shows that adaptive twin clients have equal random views, because randomized selected seals reveal only lengths. On the protocol side, `client_pre` combines the preparation prelude, which runs the post only in completed branches (`prelude_same`), the shared builder, the challenge step (`challenge_twin`) and every later step (`step_twin`, where screened receives hide identified plaintexts).

The headline `first_record_confidentiality` bounds the left-or-right difference by the two CTX privacy losses, the HB-112 target and completed-branch root losses of the two challenge-fixed posts, the explicit games `collGame` (the client event holds and a Beacon finish makes a selected raw opening) and `keyGame` (in the key-last run, the first-record event and no hidden disclosure hold while the uniform record key equals a revealed value), the nonce-repeat stop bounds of `PqxdhFirstRecordStopTagged.stop_bound` and `2 * 2^-256`. The two explicit games are intermediate terms that are not yet bounded by assumption terms. Its stop and CTX budgets are those of the certificates of the two wrapper posts; `first_record_confidentiality_budget` restates it with the adversary's own per-kind budget, each challenge counted as one Beacon `b` send, through `conf_query_bound` and `confCertificate`. `single_output` and `single_true` show at the wrapper level that the counted event is reachable. Messages are abstract byte strings that each side knows how to decode; no serialization-library behaviour is used.
-/
open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality

section Fiber

/-- A sum over a distribution of a function that factors through `e` is the sum over the pushforward. -/
theorem tsum_map_factor {γ δ : Type} (mx : ProbComp γ) (e : γ → δ) (h : δ → ℝ≥0∞) :
    ∑' x, Pr{let y ← mx}[y = x] * h (e x) = ∑' d, Pr{let x ← e <$> mx}[x = d] * h d := by
  have decEq : DecidableEq δ := Classical.decEq δ
  have pushforward : ∀ d, Pr{let x ← e <$> mx}[x = d] = ∑' x, if d = e x then Pr{let y ← mx}[y = x] else 0 :=
    fun d => by
      rw [prEvent_map, prEvent_congr mx (fun x => e x = d) (fun x => d = e x) fun _ => eq_comm,
        OracleComp.prEvent_eq_tsum_ite]
  simp only [pushforward, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  simp only [ite_mul, zero_mul]
  rw [tsum_ite_eq]

/-- Two distributions with the same pushforward under `e` give equal sums to functions that agree across `e`-related support points. -/
theorem tsum_fiber_eq {γ δ : Type} (mx my : ProbComp γ) (e : γ → δ) (same : e <$> mx = e <$> my)
    (f g : γ → ℝ≥0∞) (agree : ∀ x ∈ support mx, ∀ y ∈ support my, e x = e y → f x = g y) :
    ∑' x, Pr{let y ← mx}[y = x] * f x = ∑' y, Pr{let x ← my}[x = y] * g y := by
  have hsupport : ∀ d, (∃ x ∈ support mx, e x = d) ↔ (∃ y ∈ support my, e y = d) := by
    intro d
    have := congrArg (fun z : ProbComp δ => d ∈ support z) same
    simpa only [support_map, Set.mem_image, eq_iff_iff] using this
  let h : δ → ℝ≥0∞ := fun d => @dite _ (∃ x ∈ support mx, e x = d) (Classical.propDecidable _)
    (fun found => f found.choose) (fun _ => 0)
  have left : ∀ x ∈ support mx, f x = h (e x) := by
    intro x hx
    have found : ∃ x' ∈ support mx, e x' = e x := ⟨x, hx, rfl⟩
    simp only [h, found, _root_.dite_true]
    obtain ⟨y, hy, hye⟩ := (hsupport (e x)).mp found
    rw [agree x hx y hy hye.symm, agree found.choose found.choose_spec.1 y hy (found.choose_spec.2.trans hye.symm)]
  have right : ∀ y ∈ support my, g y = h (e y) := by
    intro y hy
    have found : ∃ x ∈ support mx, e x = e y := (hsupport (e y)).mpr ⟨y, hy, rfl⟩
    simp only [h, found, _root_.dite_true]
    exact (agree found.choose found.choose_spec.1 y hy found.choose_spec.2).symm
  have lsum : ∑' x, Pr{let y ← mx}[y = x] * f x = ∑' x, Pr{let y ← mx}[y = x] * h (e x) := by
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ support mx
    · rw [left x hx]
    · rw [(prEvent_eq_zero_of_not_mem_support _) hx, zero_mul, zero_mul]
  have rsum : ∑' y, Pr{let x ← my}[x = y] * g y = ∑' y, Pr{let x ← my}[x = y] * h (e y) := by
    refine tsum_congr fun y => ?_
    by_cases hy : y ∈ support my
    · rw [right y hy]
    · rw [(prEvent_eq_zero_of_not_mem_support _) hy, zero_mul, zero_mul]
  rw [lsum, rsum, tsum_map_factor mx e h, tsum_map_factor my e h, same]

end Fiber


section Twin
open AdaptiveCtxDynamicKnownKeys (Spec)
open CtxRomAuth

variable (m0 m1 : Pqxdh.Bytes)

/-- Plaintext identification: the right challenge plaintext is read as the left one, every other plaintext is kept. -/
def ident (plaintext : Pqxdh.Bytes) : Pqxdh.Bytes := if plaintext = m1 then m0 else plaintext

/-- A sealing input with its plaintext identified. -/
def identInput (input : CtxSealInput) : CtxSealInput := { input with plaintext := ident m0 m1 input.plaintext }

/-- A selected sealing request. -/
abbrev sealQuery (input : CtxSealInput) : Spec.Domain := .inl (.inl (.inr (.inr input)))

/-- A selected raw opening request. -/
abbrev rawQuery (raw : Pqxdh.Bytes) : Spec.Domain := .inl (.inr raw)

/-- A request that is neither a selected seal nor a selected raw opening: an explicit coin, a public hash or a known-key call. -/
def Quiet : Spec.Domain → Prop
  | .inl (.inl (.inr (.inr _))) => False
  | .inl (.inr _) => False
  | _ => True

/-- Twin CTX clients: the two programs make the same requests, except that paired selected seals may carry identified plaintexts, raw replies are compared up to identification, and either branch may end in outputs marked dead on both sides. -/
inductive Twin {α β : Type} (Out : α → β → Prop) (Dead0 : α → Prop) (Dead1 : β → Prop) :
    OracleComp Spec α → OracleComp Spec β → Prop
  | pure {a : α} {b : β} : Out a b → Twin Out Dead0 Dead1 (pure a) (pure b)
  | dead {x : OracleComp Spec α} {y : OracleComp Spec β} :
      (∀ a ∈ support x, Dead0 a) → (∀ b ∈ support y, Dead1 b) → Twin Out Dead0 Dead1 x y
  | quiet (q : Spec.Domain) {k0 : Spec.Range q → OracleComp Spec α} {k1 : Spec.Range q → OracleComp Spec β} :
      Quiet q → (∀ r, Twin Out Dead0 Dead1 (k0 r) (k1 r)) → Twin Out Dead0 Dead1 (query q >>= k0) (query q >>= k1)
  | sealing (i0 i1 : CtxSealInput) {k0 : Option CtxRomRecord → OracleComp Spec α} {k1 : Option CtxRomRecord → OracleComp Spec β} :
      identInput m0 m1 i0 = identInput m0 m1 i1 → (∀ r, Twin Out Dead0 Dead1 (k0 r) (k1 r)) →
      Twin Out Dead0 Dead1 (query (sealQuery i0) >>= k0) (query (sealQuery i1) >>= k1)
  | raw (raw : Pqxdh.Bytes) {k0 : Option Pqxdh.Bytes → OracleComp Spec α} {k1 : Option Pqxdh.Bytes → OracleComp Spec β} :
      (∀ r0 r1, Option.map (ident m0 m1) r0 = Option.map (ident m0 m1) r1 → Twin Out Dead0 Dead1 (k0 r0) (k1 r1)) →
      Twin Out Dead0 Dead1 (query (rawQuery raw) >>= k0) (query (rawQuery raw) >>= k1)

end Twin

section Semantics
open AdaptiveCtxDynamicKnownKeys (Spec)
open CtxRomAuth

variable (m0 m1 : Pqxdh.Bytes) {σ : Type} (impl : QueryImpl Spec (StateT σ ProbComp)) (E : σ → σ)

/-- A stateful interpretation is compatible with plaintext identification `E` on its states when quiet requests, identified seals and raw openings give equal distributions after identifying replies and states. -/
structure Compatible : Prop where
  quiet : ∀ q, Quiet q → ∀ s t, E s = E t → Prod.map id E <$> (impl q).run s = Prod.map id E <$> (impl q).run t
  sealing : ∀ i0 i1, identInput m0 m1 i0 = identInput m0 m1 i1 → ∀ s t, E s = E t →
    Prod.map id E <$> (impl (sealQuery i0)).run s = Prod.map id E <$> (impl (sealQuery i1)).run t
  raw : ∀ raw s t, E s = E t →
    Prod.map (Option.map (ident m0 m1)) E <$> (impl (rawQuery raw)).run s =
      Prod.map (Option.map (ident m0 m1)) E <$> (impl (rawQuery raw)).run t

/-- Twin clients interpreted by a compatible interpretation from identified states put the same mass on corresponding good outputs. -/
theorem twin_event {α β : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop}
    {x : OracleComp Spec α} {y : OracleComp Spec β} (twin : Twin m0 m1 Out Dead0 Dead1 x y)
    (G0 : α → Prop) (G1 : β → Prop) [DecidablePred G0] [DecidablePred G1] (hOut : ∀ a b, Out a b → (G0 a ↔ G1 b))
    (hDead0 : ∀ a, Dead0 a → ¬ G0 a) (hDead1 : ∀ b, Dead1 b → ¬ G1 b)
    (compatible : Compatible m0 m1 impl E) (s t : σ) (same : E s = E t) :
    Pr{let z ← (simulateQ impl x).run s}[G0 z.1] = Pr{let z ← (simulateQ impl y).run t}[G1 z.1] := by
  induction twin generalizing s t with
  | pure related =>
    rename_i a b
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure]
    by_cases good : G0 a
    · simp [good, (hOut a b related).mp good]
    · simp [good, show ¬ G1 b from fun holds => good ((hOut a b related).mpr holds)]
  | dead dead0 dead1 =>
    rename_i x y
    have zero0 : Pr{let z ← (simulateQ impl x).run s}[G0 z.1] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz good => by
        have mem : z.1 ∈ support ((simulateQ impl x).run' s) := by
          rw [StateT.run'_eq, support_map]
          exact ⟨z, hz, rfl⟩
        exact hDead0 z.1 (dead0 z.1 (support_simulateQ_run'_subset impl x s mem)) good
    have zero1 : Pr{let z ← (simulateQ impl y).run t}[G1 z.1] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz good => by
        have mem : z.1 ∈ support ((simulateQ impl y).run' t) := by
          rw [StateT.run'_eq, support_map]
          exact ⟨z, hz, rfl⟩
        exact hDead1 z.1 (dead1 z.1 (support_simulateQ_run'_subset impl y t mem)) good
    rw [zero0, zero1]
  | quiet q isQuiet _ ih =>
    simp only [simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_fiber_eq _ _ (Prod.map id E) (compatible.quiet q isQuiet s t same) _ _ ?_
    rintro ⟨r, s'⟩ _ ⟨r', t'⟩ _ related
    simp only [Prod.map, id_eq, Prod.mk.injEq] at related
    obtain ⟨rfl, states⟩ := related
    exact ih r s' t' states
  | sealing i0 i1 identified _ ih =>
    simp only [simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_fiber_eq _ _ (Prod.map id E) (compatible.sealing i0 i1 identified s t same) _ _ ?_
    rintro ⟨r, s'⟩ _ ⟨r', t'⟩ _ related
    simp only [Prod.map, id_eq, Prod.mk.injEq] at related
    obtain ⟨rfl, states⟩ := related
    exact ih r s' t' states
  | raw raw _ ih =>
    simp only [simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_fiber_eq _ _ (Prod.map (Option.map (ident m0 m1)) E) (compatible.raw raw s t same) _ _ ?_
    rintro ⟨r, s'⟩ _ ⟨r', t'⟩ _ related
    simp only [Prod.map, Prod.mk.injEq] at related
    exact ih r r' related.1 s' t' related.2

end Semantics

section Collapse
open AdaptiveCtxDynamicKnownKeys (Spec ReductionState)
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation
open CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation

/-- The logged raw-reply simulator as a stateful interpreter of the adaptive interface. -/
noncomputable def logImpl (decode : AdaptiveRawNonceAead.RawDecoder) :
    QueryImpl AdaptiveSpec (StateT SealHistory (OracleComp ModifiedNonceAeadAdversarySpec)) :=
  fun query history => match query with
  | .inl primitive => do
      let answer ← ModifiedNonceAeadAdversarySpec.query primitive
      pure (answer, recordPrimitiveAnswer primitive answer history)
  | .inr raw => pure (simulatedOpen decode history raw, history)

/-- The recursive logged simulator is the stateful interpreter `logImpl`. -/
theorem runLogged_eq {Result : Type} (decode : AdaptiveRawNonceAead.RawDecoder)
    (adversary : OracleComp AdaptiveSpec Result) (history : SealHistory) :
    runLogged decode adversary history = (simulateQ (logImpl decode) adversary).run history := by
  induction adversary using OracleComp.inductionOn generalizing history with
  | pure value => rfl
  | query_bind query next ih =>
    cases query with
    | inl primitive =>
      rw [runLogged_primitive]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run]
      exact bind_congr fun answer => ih answer _
    | inr raw =>
      rw [runLogged_raw]
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run]
      exact ih _ history

variable (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto)

/-- The IND$ random sealing oracle below the logged raw-reply simulator. -/
noncomputable def lower4 : QueryImpl AdaptiveSpec (StateT (SealHistory × ModifiedNonceAeadHandlerState) ProbComp) :=
  (modifiedNonceAeadINDDollarRandomImpl.mapStateTBase (logImpl (baseDecoder decode))).flattenStateT

/-- The key-free CTX wrapper interpreted in the random world. -/
noncomputable def lower3 : QueryImpl ReceiveSpec
    (StateT (AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) ProbComp) :=
  ((lower4 decode).mapStateTBase (AdaptiveCtxReceive.reductionImpl decode)).flattenStateT

/-- State of the random-world interpretation of selected requests. -/
abbrev LowerState := PublicHistory × (AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState))

/-- The public replay guard interpreted in the random world: the interpretation of selected CTX requests in `randomView`. -/
noncomputable def lower2 : QueryImpl ReceiveSpec (StateT LowerState ProbComp) :=
  ((lower3 decode).mapStateTBase (guard decode)).flattenStateT

/-- State of the collapsed random-world interpretation. -/
abbrev RandomState := ReductionState × LowerState

/-- The complete random-world interpretation of a selected/known-key CTX client: known-key reduction, public replay guard, key-free wrapper, logged raw replies and the IND$ random sealing oracle. -/
noncomputable def confRandomImpl : QueryImpl Spec (StateT RandomState ProbComp) :=
  ((lower2 decode).mapStateTBase (AdaptiveCtxDynamicKnownKeys.reductionImpl c)).flattenStateT

/-- The initial collapsed state. -/
def randomInitial : RandomState :=
  (AdaptiveCtxDynamicKnownKeys.initialReduction, ([], (AdaptiveCtxReceive.initialState, ([], emptyModifiedNonceAeadHandlerState))))

/-- The ordinary random view of the constructed decision client is the collapsed random-world interpretation of the client. -/
theorem randomView_collapse (client : OracleComp Spec Bool) :
    randomView decode (AdaptiveCtxDynamicKnownKeys.decisionClient c client) =
      Prod.fst <$> (simulateQ (confRandomImpl decode c) client).run randomInitial := by
  simp only [randomView, modifiedNonceAeadINDDollarRandomExp, viewReduction, sourceClient, guardedClient,
    AdaptiveCtxReceive.wrapped, AdaptiveCtxDynamicKnownKeys.decisionClient, AdaptiveCtxDynamicKnownKeys.wrapped,
    runLogged_eq, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (outer := modifiedNonceAeadINDDollarRandomImpl),
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (inner := AdaptiveCtxReceive.reductionImpl decode),
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (inner := guard decode),
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (inner := AdaptiveCtxDynamicKnownKeys.reductionImpl c)]
  simp only [Functor.map_map, bind_pure_comp]
  rfl

end Collapse

section Identification

/-- Applying a mapped state transformer is mapping its run. -/
theorem conf_state_map_apply {σ α β : Type} (f : α → β) (work : StateT σ ProbComp α) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  change (f <$> work).run state = (fun result => (f result.1, result.2)) <$> work.run state
  rw [StateT.run_map]

open AdaptiveCtxDynamicKnownKeys (Spec ReductionState)
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation
open CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation AdaptiveCtxReplayDictionary
variable (m0 m1 : Pqxdh.Bytes)

/-- Identification of one successful CTX seal. -/
def identSeal (entry : CtxSuccessfulSeal) : CtxSuccessfulSeal := ⟨identInput m0 m1 entry.input, entry.record⟩

/-- Identification of one primitive sealing input. -/
def identPrimitiveInput (input : ModifiedNonceAeadSealInput) : ModifiedNonceAeadSealInput :=
  { input with plaintext := ident m0 m1 input.plaintext }

/-- Identification of one primitive successful seal. -/
def identPrimitive (entry : ModifiedNonceAeadSuccessfulSeal) : ModifiedNonceAeadSuccessfulSeal :=
  ⟨identPrimitiveInput m0 m1 entry.input, entry.ciphertext⟩

/-- Identification of the random challenger state. -/
def identHandler (state : ModifiedNonceAeadHandlerState) : ModifiedNonceAeadHandlerState :=
  ⟨state.usedNonces, state.successfulSeals.map (identPrimitive m0 m1)⟩

/-- Identification of the logged simulator and random challenger states. -/
def identLow4 (state : SealHistory × ModifiedNonceAeadHandlerState) : SealHistory × ModifiedNonceAeadHandlerState :=
  (state.1.map (identPrimitive m0 m1), identHandler m0 m1 state.2)

/-- Identification of the key-free wrapper state. -/
def identReceive (state : AdaptiveCtxReceive.ReceiveState) : AdaptiveCtxReceive.ReceiveState :=
  { state with ctx := { state.ctx with successfulSeals := state.ctx.successfulSeals.map (identSeal m0 m1) } }

/-- Identification below the guard. -/
def identLow3 (state : AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) :
    AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState) :=
  (identReceive m0 m1 state.1, identLow4 m0 m1 state.2)

/-- Identification of the random-world state of selected requests. -/
def identLower (state : LowerState) : LowerState := (state.1.map (identSeal m0 m1), identLow3 m0 m1 state.2)

/-- Identification of the collapsed random-world state; the known-key reduction state is unchanged. -/
def identRandom (state : RandomState) : RandomState := (state.1, identLower m0 m1 state.2)

/-- Identification is idempotent on plaintexts. -/
theorem ident_ident (plaintext : Pqxdh.Bytes) : ident m0 m1 (ident m0 m1 plaintext) = ident m0 m1 plaintext := by
  unfold ident
  by_cases right : plaintext = m1
  · subst right
    by_cases same : m0 = plaintext <;> simp [same]
  · simp [right]

/-- Identification preserves lengths when the two challenge plaintexts have equal length. -/
theorem ident_length (equal : m0.length = m1.length) (plaintext : Pqxdh.Bytes) :
    (ident m0 m1 plaintext).length = plaintext.length := by
  unfold ident
  split
  · rename_i right
    rw [right, equal]
  · rfl

/-- The random challenger's ciphertext sample for a plaintext of the given length. -/
noncomputable def cipherSample (length : Nat) : ProbComp ModifiedNonceAeadCiphertext := do
  let body ← $ᵗ (FixedBytes length)
  let tag ← $ᵗ (FixedBytes 16)
  pure ⟨body.toList, tag.toList, tag.toList_length⟩

/-- The random sealing oracle samples a ciphertext that depends on the plaintext only through its length. -/
theorem randomSeal_run (input : ModifiedNonceAeadSealInput) (state : ModifiedNonceAeadHandlerState) :
    (modifiedNonceAeadINDDollarRandomSealOracle input).run state =
      if input.nonce ∈ state.usedNonces then pure (none, state)
      else (fun ciphertext => (some ciphertext, state.addSeal ⟨input, ciphertext⟩)) <$> cipherSample input.plaintext.length := by
  simp only [modifiedNonceAeadINDDollarRandomSealOracle, StateT.run, cipherSample]
  split
  · rfl
  · simp only [map_bind, map_pure]

/-- The random sealing oracle commutes with identification. -/
theorem randomSeal_ident (equal : m0.length = m1.length) (input : ModifiedNonceAeadSealInput) (state : ModifiedNonceAeadHandlerState) :
    (modifiedNonceAeadINDDollarRandomSealOracle (identPrimitiveInput m0 m1 input)).run (identHandler m0 m1 state) =
      Prod.map id (identHandler m0 m1) <$> (modifiedNonceAeadINDDollarRandomSealOracle input).run state := by
  rw [randomSeal_run, randomSeal_run]
  have nonce : (identPrimitiveInput m0 m1 input).nonce = input.nonce := rfl
  have used : (identHandler m0 m1 state).usedNonces = state.usedNonces := rfl
  have length : (identPrimitiveInput m0 m1 input).plaintext.length = input.plaintext.length :=
    ident_length m0 m1 equal input.plaintext
  rw [nonce, used, length]
  split
  · simp only [map_pure, Prod.map, id_eq]
  · simp only [Functor.map_map]
    rfl

variable (decode : AdaptiveCtxReceive.RawDecoder)

/-- One logged primitive coin keeps the logged and challenger states. -/
theorem lower4_coin (n : ℕ) (state : SealHistory × ModifiedNonceAeadHandlerState) :
    (lower4 decode (.inl (.inl n))).run state = (fun a => (a, state)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp only [lower4, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, logImpl]
  rfl

/-- One logged primitive seal is the random seal together with its log entry. -/
theorem lower4_seal (input : ModifiedNonceAeadSealInput) (history : SealHistory) (handler : ModifiedNonceAeadHandlerState) :
    (lower4 decode (.inl (.inr input))).run (history, handler) =
      (fun result => (result.1, (recordPrimitiveAnswer (.inr input) result.1 history, result.2))) <$>
        (modifiedNonceAeadINDDollarRandomSealOracle input).run handler := by
  simp [lower4, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, logImpl, modifiedNonceAeadINDDollarRandomImpl,
    conf_state_map_apply, Functor.map_map]

/-- One logged raw reply reads only the log. -/
theorem lower4_raw (raw : Pqxdh.Bytes) (history : SealHistory) (handler : ModifiedNonceAeadHandlerState) :
    (lower4 decode (.inr raw)).run (history, handler) = pure (simulatedOpen (baseDecoder decode) history raw, (history, handler)) := by
  simp only [lower4, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run, StateT.mk, logImpl]
  rfl

/-- The logged plaintext of an identified log is the identified logged plaintext. -/
theorem loggedPlaintext_ident (history : SealHistory) (target : ModifiedNonceAeadForgery) :
    loggedPlaintext (history.map (identPrimitive m0 m1)) target = Option.map (ident m0 m1) (loggedPlaintext history target) := by
  unfold loggedPlaintext
  rw [List.find?_map]
  have same : (entryMatches target ∘ identPrimitive m0 m1) = entryMatches target := by
    funext entry
    rfl
  rw [same, Option.map_map, Option.map_map]
  rfl

/-- Identified logged raw replies. -/
theorem simulatedOpen_ident (decoder : AdaptiveRawNonceAead.RawDecoder) (history : SealHistory) (raw : Pqxdh.Bytes) :
    simulatedOpen decoder (history.map (identPrimitive m0 m1)) raw = Option.map (ident m0 m1) (simulatedOpen decoder history raw) := by
  unfold simulatedOpen
  cases decoder raw with
  | none => rfl
  | some target => exact loggedPlaintext_ident m0 m1 history target

/-- Coins below the wrapper commute with identification. -/
theorem lower4_coin_ident (n : ℕ) (state : SealHistory × ModifiedNonceAeadHandlerState) :
    (lower4 decode (.inl (.inl n))).run (identLow4 m0 m1 state) =
      Prod.map id (identLow4 m0 m1) <$> (lower4 decode (.inl (.inl n))).run state := by
  rw [lower4_coin, lower4_coin, Functor.map_map]
  rfl

/-- Primitive seals below the wrapper commute with identification. -/
theorem lower4_seal_ident (equal : m0.length = m1.length) (input : ModifiedNonceAeadSealInput)
    (state : SealHistory × ModifiedNonceAeadHandlerState) :
    (lower4 decode (.inl (.inr (identPrimitiveInput m0 m1 input)))).run (identLow4 m0 m1 state) =
      Prod.map id (identLow4 m0 m1) <$> (lower4 decode (.inl (.inr input))).run state := by
  obtain ⟨history, handler⟩ := state
  rw [identLow4, lower4_seal, lower4_seal, randomSeal_ident m0 m1 equal, Functor.map_map, Functor.map_map]
  refine congrArg (fun f => f <$> (modifiedNonceAeadINDDollarRandomSealOracle input).run handler) ?_
  funext result
  rcases result with ⟨_ | ciphertext, after⟩
  · rfl
  · rfl

/-- Raw replies below the wrapper are identified with the log. -/
theorem lower4_raw_ident (raw : Pqxdh.Bytes) (state : SealHistory × ModifiedNonceAeadHandlerState) :
    (lower4 decode (.inr raw)).run (identLow4 m0 m1 state) =
      Prod.map (Option.map (ident m0 m1)) (identLow4 m0 m1) <$> (lower4 decode (.inr raw)).run state := by
  obtain ⟨history, handler⟩ := state
  rw [identLow4, lower4_raw, lower4_raw, map_pure, simulatedOpen_ident]
  rfl

end Identification

section Layer3
open AdaptiveCtxDynamicKnownKeys (Spec ReductionState)
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation
open CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation AdaptiveCtxReplayDictionary CtxIndependentTags CtxSplitCache
variable (m0 m1 : Pqxdh.Bytes) (decode : AdaptiveCtxReceive.RawDecoder)

/-- Coins lifted into the adaptive interface only consume randomness below the wrapper. -/
theorem lower4_liftComp {α : Type} (work : ProbComp α) (state : SealHistory × ModifiedNonceAeadHandlerState) :
    (simulateQ (lower4 decode) (OracleComp.liftComp work AdaptiveSpec)).run state = (fun a => (a, state)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin before
  simp only [OracleComp.liftComp_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
  change (simulateQ (lower4 decode) (AdaptiveSpec.query (.inl (.inl coin)))).run before = _
  rw [simulateQ_spec_query, lower4_coin]

/-- The wrapper's private suffix lookup below the wrapper. -/
theorem privateStep_run (suffix : Pqxdh.Bytes) (state : AdaptiveCtxReceive.ReceiveState) (low : SealHistory × ModifiedNonceAeadHandlerState) :
    (simulateQ (lower4 decode) (privateStep suffix state)).run low =
      (fun result => ((result.1, (⟨{ state.ctx with cache := result.2 }, state.rawAttempts, suffix :: state.privateInputs⟩ :
        AdaptiveCtxReceive.ReceiveState)), low)) <$> ctxKeyFreeSuffixStep suffix state.ctx.cache := by
  unfold privateStep
  rw [simulateQ_bind, StateT.run_bind, lower4_liftComp, bind_map_left]
  simp only [simulateQ_pure, StateT.run_pure, bind_pure_comp]

/-- One wrapped request below the guard is its wrapper step interpreted below the wrapper. -/
theorem lower3_run (query : ReceiveSpec.Domain) (state : AdaptiveCtxReceive.ReceiveState)
    (low : SealHistory × ModifiedNonceAeadHandlerState) :
    (lower3 decode query).run (state, low) = (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (lower4 decode) ((AdaptiveCtxReceive.reductionImpl decode query).run state)).run low := rfl

/-- Wrapped coins commute with identification. -/
theorem lower3_coin_ident (n : ℕ) (state : AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) :
    (lower3 decode (.inl (.inl n))).run (identLow3 m0 m1 state) =
      Prod.map id (identLow3 m0 m1) <$> (lower3 decode (.inl (.inl n))).run state := by
  obtain ⟨wrapper, low⟩ := state
  have step : ∀ wrapper : AdaptiveCtxReceive.ReceiveState, (AdaptiveCtxReceive.reductionImpl decode (.inl (.inl n))).run wrapper =
      (fun a => (a, wrapper)) <$> (AdaptiveSpec.query (.inl (.inl n)) : OracleComp AdaptiveSpec (Fin (n + 1))) := by
    intro wrapper
    simp [AdaptiveCtxReceive.reductionImpl, StateT.run, map_eq_bind_pure_comp]
  rw [identLow3, lower3_run, lower3_run, step, step, simulateQ_map, simulateQ_spec_query, simulateQ_map, simulateQ_spec_query,
    StateT.run_map, StateT.run_map, lower4_coin_ident, Functor.map_map, Functor.map_map, Functor.map_map, Functor.map_map]
  rfl

/-- Identification of the key-free tag state. -/
def identCtx (state : CtxIndependentTagState) : CtxIndependentTagState :=
  { state with successfulSeals := state.successfulSeals.map (identSeal m0 m1) }

/-- The public random oracle of the wrapper ignores stored seals. -/
theorem publicOracle_ident (hash : CtxRO.Domain) (state : CtxIndependentTagState) :
    (ctxIndependentPublicOracle hash).run (identCtx m0 m1 state) =
      Prod.map id (identCtx m0 m1) <$> (ctxIndependentPublicOracle hash).run state := by
  simp only [ctxIndependentPublicOracle, StateT.run, identCtx, map_bind, map_pure]
  rfl

/-- Wrapped public hashes commute with identification. -/
theorem lower3_hash_ident (hash : CtxRO.Domain)
    (state : AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) :
    (lower3 decode (.inl (.inr (.inl hash)))).run (identLow3 m0 m1 state) =
      Prod.map id (identLow3 m0 m1) <$> (lower3 decode (.inl (.inr (.inl hash)))).run state := by
  obtain ⟨wrapper, low⟩ := state
  have step : ∀ wrapper : AdaptiveCtxReceive.ReceiveState, (AdaptiveCtxReceive.reductionImpl decode (.inl (.inr (.inl hash)))).run wrapper =
      (fun result => (result.1, { wrapper with ctx := result.2 })) <$>
        OracleComp.liftComp ((ctxIndependentPublicOracle hash).run wrapper.ctx) AdaptiveSpec := by
    intro wrapper
    simp [AdaptiveCtxReceive.reductionImpl, StateT.run, publicStep, map_eq_bind_pure_comp]
  rw [identLow3, lower3_run, lower3_run, step, step, simulateQ_map, simulateQ_map, StateT.run_map, StateT.run_map,
    lower4_liftComp, lower4_liftComp]
  change _ <$> _ <$> _ <$> (ctxIndependentPublicOracle hash).run (identCtx m0 m1 wrapper.ctx) = _
  rw [publicOracle_ident]
  simp only [Functor.map_map]
  rfl

/-- A wrapped seal: the primitive seal, then on success the private commitment lookup and the seal log entry. -/
theorem sealStep_eq (input : CtxSealInput) (wrapper : AdaptiveCtxReceive.ReceiveState) :
    (AdaptiveCtxReceive.reductionImpl decode (.inl (.inr (.inr input)))).run wrapper =
      (AdaptiveSpec.query (.inl (.inr (CtxSealInput.toModifiedNonceAeadSealInput input))) : OracleComp AdaptiveSpec _) >>= fun base =>
        match base with
        | none => pure (none, wrapper)
        | some ciphertext => (fun result => (some ⟨ciphertext.body, ciphertext.tag, ciphertext.tagLength, result.1⟩,
            { result.2 with ctx := (result.2.ctx.addSeal ⟨input, ⟨ciphertext.body, ciphertext.tag, ciphertext.tagLength, result.1⟩⟩
              result.2.ctx.cache) })) <$>
            privateStep (outerSuffix input.nonce input.context ciphertext.tag) wrapper := by
  simp only [AdaptiveCtxReceive.reductionImpl, StateT.run, sealStep]
  refine bind_congr fun base => ?_
  cases base with
  | none => rfl
  | some ciphertext => simp only [map_eq_bind_pure_comp, Function.comp_def]

/-- Wrapped seals commute with identification. -/
theorem lower3_seal_ident (equal : m0.length = m1.length) (input : CtxSealInput)
    (state : AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) :
    (lower3 decode (.inl (.inr (.inr (identInput m0 m1 input))))).run (identLow3 m0 m1 state) =
      Prod.map id (identLow3 m0 m1) <$> (lower3 decode (.inl (.inr (.inr input)))).run state := by
  obtain ⟨wrapper, low⟩ := state
  rw [identLow3, lower3_run, lower3_run, sealStep_eq, sealStep_eq, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind,
    simulateQ_spec_query, simulateQ_spec_query]
  change _ <$> ((lower4 decode (.inl (.inr (identPrimitiveInput m0 m1 (CtxSealInput.toModifiedNonceAeadSealInput input))))).run
    (identLow4 m0 m1 low) >>= _) = _
  rw [lower4_seal_ident m0 m1 decode equal]
  simp only [map_bind, bind_map_left]
  refine bind_congr fun result => ?_
  rcases result with ⟨_ | ciphertext, after⟩
  · simp only [Prod.map, id_eq, simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  · simp only [Prod.map, id_eq, simulateQ_map, StateT.run_map, privateStep_run, Functor.map_map]
    rfl

/-- Wrapped raw openings are identified with the logged plaintexts; the wrapper's own raw bookkeeping ignores stored plaintexts. -/
theorem lower3_raw_ident (raw : Pqxdh.Bytes)
    (state : AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) :
    (lower3 decode (.inr raw)).run (identLow3 m0 m1 state) =
      Prod.map (Option.map (ident m0 m1)) (identLow3 m0 m1) <$> (lower3 decode (.inr raw)).run state := by
  obtain ⟨wrapper, ⟨history, handler⟩⟩ := state
  rw [identLow3, lower3_run, lower3_run]
  change _ <$> (simulateQ (lower4 decode) (rawStep decode raw (identReceive m0 m1 wrapper))).run (identLow4 m0 m1 (history, handler)) =
    _ <$> _ <$> (simulateQ (lower4 decode) (rawStep decode raw wrapper)).run (history, handler)
  unfold rawStep
  cases decode raw with
  | none =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    rfl
  | some target =>
    simp only [simulateQ_bind, StateT.run_bind, privateStep_run, bind_map_left, map_bind]
    refine bind_congr fun lookup => ?_
    by_cases hit : target.record.commit = lookup.1
    · simp only [hit, ite_true, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, identLow4, lower4_raw, pure_bind,
        simulateQ_pure, StateT.run_pure, map_pure, simulatedOpen_ident]
      rfl
    · simp only [hit, ite_false, simulateQ_pure, StateT.run_pure, map_pure]
      rfl

end Layer3

section Layer2
open AdaptiveCtxDynamicKnownKeys (Spec ReductionState)
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation
open CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation AdaptiveCtxReplayDictionary CtxIndependentTags CtxSplitCache
variable (m0 m1 : Pqxdh.Bytes) (decode : AdaptiveCtxReceive.RawDecoder)

/-- The guard's public reply on an identified history is the identified public reply. -/
theorem publicReply_ident (history : PublicHistory) (raw : Pqxdh.Bytes) :
    publicReply decode (history.map (identSeal m0 m1)) raw = Option.map (ident m0 m1) (publicReply decode history raw) := by
  unfold publicReply
  cases decode raw with
  | none => rfl
  | some target =>
    simp only [replayPlaintext, List.find?_map, Option.map_map]
    rfl

/-- One guarded request in the random world is the guard step interpreted below the guard. -/
theorem lower2_run (query : ReceiveSpec.Domain) (history : PublicHistory)
    (rest : AdaptiveCtxReceive.ReceiveState × (SealHistory × ModifiedNonceAeadHandlerState)) :
    (lower2 decode query).run (history, rest) = (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (lower3 decode) ((guard decode query).run history)).run rest := rfl

/-- A forwarded non-raw request: the guard issues it once and records its reply. -/
theorem guard_forward (request : (unifSpec + CtxAdversarySpec).Domain) (history : PublicHistory) :
    (guard decode (.inl request)).run history =
      (fun answer => (answer, recordReply (.inl request) answer history)) <$> (ReceiveSpec.query (.inl request) : OracleComp ReceiveSpec _) := by
  simp [AdaptiveCtxPrivacyGuard.guard, StateT.run, map_eq_bind_pure_comp]

/-- Guarded coins commute with identification. -/
theorem lower2_coin_ident (n : ℕ) (state : LowerState) :
    (lower2 decode (.inl (.inl n))).run (identLower m0 m1 state) =
      Prod.map id (identLower m0 m1) <$> (lower2 decode (.inl (.inl n))).run state := by
  obtain ⟨history, rest⟩ := state
  simp only [identLower, lower2_run, guard_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [lower3_coin_ident]
  simp only [Functor.map_map]
  rfl

/-- Guarded public hashes commute with identification. -/
theorem lower2_hash_ident (hash : CtxRO.Domain) (state : LowerState) :
    (lower2 decode (.inl (.inr (.inl hash)))).run (identLower m0 m1 state) =
      Prod.map id (identLower m0 m1) <$> (lower2 decode (.inl (.inr (.inl hash)))).run state := by
  obtain ⟨history, rest⟩ := state
  simp only [identLower, lower2_run, guard_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [lower3_hash_ident]
  simp only [Functor.map_map]
  rfl

/-- Guarded seals commute with identification. -/
theorem lower2_seal_ident (equal : m0.length = m1.length) (input : CtxSealInput) (state : LowerState) :
    (lower2 decode (.inl (.inr (.inr (identInput m0 m1 input))))).run (identLower m0 m1 state) =
      Prod.map id (identLower m0 m1) <$> (lower2 decode (.inl (.inr (.inr input)))).run state := by
  obtain ⟨history, rest⟩ := state
  simp only [identLower, lower2_run, guard_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [lower3_seal_ident m0 m1 decode equal]
  simp only [Functor.map_map]
  refine congrArg (fun f => f <$> (lower3 decode (.inl (.inr (.inr input)))).run rest) ?_
  funext result
  rcases result with ⟨_ | record, after⟩
  · rfl
  · rfl

/-- Guarded raw openings are answered from the public history, identified. -/
theorem lower2_raw_ident (raw : Pqxdh.Bytes) (state : LowerState) :
    (lower2 decode (.inr raw)).run (identLower m0 m1 state) =
      Prod.map (Option.map (ident m0 m1)) (identLower m0 m1) <$> (lower2 decode (.inr raw)).run state := by
  obtain ⟨history, rest⟩ := state
  have step : ∀ history : PublicHistory, (guard decode (.inr raw)).run history =
      (fun _ => (publicReply decode history raw, history)) <$> (ReceiveSpec.query (.inr raw) : OracleComp ReceiveSpec _) := by
    intro history
    simp [AdaptiveCtxPrivacyGuard.guard, StateT.run, map_eq_bind_pure_comp]
  simp only [identLower, lower2_run, step, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [lower3_raw_ident]
  simp only [Functor.map_map, publicReply_ident]
  rfl

end Layer2

section Top
open AdaptiveCtxDynamicKnownKeys (Spec ReductionState KnownCall)
open CtxRomAuth CtxNonceAeadIntCtxt AdaptiveRawNonceAead AdaptiveCtxReceive AdaptiveCtxPrivacyGuard AdaptiveCtxLogSimulation
open CtxNonceAeadIndDollar CtxNonceAeadIndDollarValidation AdaptiveCtxReplayDictionary CtxIndependentTags CtxSplitCache
variable (m0 m1 : Pqxdh.Bytes) (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto)

/-- One client request in the collapsed random world: the known-key reduction step interpreted by the random world of selected requests. -/
theorem confRandomImpl_run (query : Spec.Domain) (reduction : ReductionState) (lower : LowerState) :
    (confRandomImpl decode c query).run (reduction, lower) = (fun z => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (lower2 decode) ((AdaptiveCtxDynamicKnownKeys.reductionImpl c query).run reduction)).run lower := rfl

/-- A selected request is forwarded once by the known-key reduction, which records only public hash inputs. -/
theorem reduction_selected (request : ReceiveSpec.Domain) (reduction : ReductionState) :
    (AdaptiveCtxDynamicKnownKeys.reductionImpl c (.inl request)).run reduction =
      (fun answer => (answer, { reduction with selectedPublic := AdaptiveCtxSharedTarget.nextPublic request reduction.selectedPublic })) <$>
        (ReceiveSpec.query request : OracleComp ReceiveSpec _) := by
  simp [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, map_eq_bind_pure_comp]

/-- Forwarded coins and public hashes of known-key work commute with identification in the random world. -/
theorem forward_ident (query : AdaptiveCtxSharedHash.HashSpec.Domain) (lower : LowerState) :
    Prod.map id (identLower m0 m1) <$> ((lower2 decode ∘ₛ AdaptiveCtxSharedTarget.forward) query).run lower =
      ((lower2 decode ∘ₛ AdaptiveCtxSharedTarget.forward) query).run (identLower m0 m1 lower) := by
  rcases query with coin | hash
  · simp only [QueryImpl.compose, AdaptiveCtxSharedTarget.forward, simulateQ_spec_query]
    exact (lower2_coin_ident m0 m1 decode coin lower).symm
  · simp only [QueryImpl.compose, AdaptiveCtxSharedTarget.forward, simulateQ_spec_query]
    exact (lower2_hash_ident m0 m1 decode hash lower).symm

/-- Quiet client requests (coins, public hashes and known-key work) commute with identification in the random world. -/
theorem random_quiet_ident (query : Spec.Domain) (quiet : Quiet query) (state : RandomState) :
    (confRandomImpl decode c query).run (identRandom m0 m1 state) = Prod.map id (identRandom m0 m1) <$> (confRandomImpl decode c query).run state := by
  obtain ⟨reduction, lower⟩ := state
  rcases query with ((coin | (hash | input)) | raw) | known
  · simp only [identRandom, confRandomImpl_run, reduction_selected, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    rw [lower2_coin_ident]
    simp only [Functor.map_map]
    rfl
  · simp only [identRandom, confRandomImpl_run, reduction_selected, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    rw [lower2_hash_ident]
    simp only [Functor.map_map]
    rfl
  · exact quiet.elim
  · exact quiet.elim
  · simp only [identRandom, confRandomImpl_run]
    have step : ∀ reduction : ReductionState, (AdaptiveCtxDynamicKnownKeys.reductionImpl c (.inr known)).run reduction =
        (fun result => (result.1, { reduction with others := Function.update reduction.others known.slot result.2 })) <$>
          simulateQ AdaptiveCtxSharedTarget.forward
            ((AdaptiveCtxSharedModes.localImpl true known.decode c known.key known.request).run (reduction.others known.slot)) := by
      intro reduction
      simp [AdaptiveCtxDynamicKnownKeys.reductionImpl, StateT.run, map_eq_bind_pure_comp]
    simp only [step, simulateQ_map, StateT.run_map, ← QueryImpl.simulateQ_compose]
    rw [← map_run_simulateQ_eq_of_query_map_eq (lower2 decode ∘ₛ AdaptiveCtxSharedTarget.forward)
      (lower2 decode ∘ₛ AdaptiveCtxSharedTarget.forward) (identLower m0 m1) (forward_ident m0 m1 decode)]
    simp only [Functor.map_map]
    rfl

/-- Selected seals commute with identification of plaintexts in the random world. -/
theorem random_seal_ident (equal : m0.length = m1.length) (input : CtxSealInput) (state : RandomState) :
    (confRandomImpl decode c (sealQuery (identInput m0 m1 input))).run (identRandom m0 m1 state) =
      Prod.map id (identRandom m0 m1) <$> (confRandomImpl decode c (sealQuery input)).run state := by
  obtain ⟨reduction, lower⟩ := state
  simp only [identRandom, confRandomImpl_run, reduction_selected, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [lower2_seal_ident m0 m1 decode equal]
  simp only [Functor.map_map]
  rfl

/-- Selected raw openings are answered with identified plaintexts in the random world. -/
theorem random_raw_ident (raw : Pqxdh.Bytes) (state : RandomState) :
    (confRandomImpl decode c (rawQuery raw)).run (identRandom m0 m1 state) =
      Prod.map (Option.map (ident m0 m1)) (identRandom m0 m1) <$> (confRandomImpl decode c (rawQuery raw)).run state := by
  obtain ⟨reduction, lower⟩ := state
  simp only [identRandom, confRandomImpl_run, reduction_selected, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [lower2_raw_ident]
  simp only [Functor.map_map]
  rfl

/-- The collapsed random world is compatible with plaintext identification when the challenge plaintexts have equal length. -/
theorem random_compatible (equal : m0.length = m1.length) :
    Compatible m0 m1 (confRandomImpl decode c) (identRandom m0 m1) where
  quiet query quiet s t same := by
    rw [← random_quiet_ident m0 m1 decode c query quiet, ← random_quiet_ident m0 m1 decode c query quiet, same]
  sealing i0 i1 identified s t same := by
    rw [← random_seal_ident m0 m1 decode c equal, ← random_seal_ident m0 m1 decode c equal, identified, same]
  raw raw s t same := by
    rw [← random_raw_ident, ← random_raw_ident, same]

end Top

section RandomTwin
open AdaptiveCtxDynamicKnownKeys (Spec)
variable (m0 m1 : Pqxdh.Bytes) (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto)

/-- Twin Boolean clients have the same `true` mass in the ordinary random view when the two challenge plaintexts have equal length: randomized selected seals reveal only lengths, and replayed plaintexts are compared up to identification. -/
theorem randomView_twin (equal : m0.length = m1.length) {left right : OracleComp Spec Bool}
    (twin : Twin m0 m1 (fun a b => a = b) (fun a => a = false) (fun b => b = false) left right) :
    𝒟[AdaptiveCtxPrivacyGuard.randomView decode (AdaptiveCtxDynamicKnownKeys.decisionClient c left)] {true} =
      𝒟[AdaptiveCtxPrivacyGuard.randomView decode (AdaptiveCtxDynamicKnownKeys.decisionClient c right)] {true} := by
  rw [randomView_collapse, randomView_collapse, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  exact twin_event m0 m1 (confRandomImpl decode c) (identRandom m0 m1) twin (fun a => a = true) (fun b => b = true)
    (fun a b same => by rw [same]) (fun a dead => by simp [dead]) (fun b dead => by simp [dead])
    (random_compatible m0 m1 decode c equal) _ _ rfl

end RandomTwin

section Algebra
open AdaptiveCtxDynamicKnownKeys (Spec)
open CtxRomAuth
variable (m0 m1 : Pqxdh.Bytes)

/-- Twin programs compose by bind when related outputs have twin continuations and dead outputs stay dead. -/
theorem twin_bind {α β γ δ : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop}
    {Out' : γ → δ → Prop} {Dead0' : γ → Prop} {Dead1' : δ → Prop}
    {x : OracleComp Spec α} {y : OracleComp Spec β} (twin : Twin m0 m1 Out Dead0 Dead1 x y)
    {f : α → OracleComp Spec γ} {g : β → OracleComp Spec δ}
    (next : ∀ a b, Out a b → Twin m0 m1 Out' Dead0' Dead1' (f a) (g b))
    (dead0 : ∀ a, Dead0 a → ∀ c ∈ support (f a), Dead0' c) (dead1 : ∀ b, Dead1 b → ∀ d ∈ support (g b), Dead1' d) :
    Twin m0 m1 Out' Dead0' Dead1' (x >>= f) (y >>= g) := by
  induction twin with
  | pure related => simpa only [pure_bind] using next _ _ related
  | dead all0 all1 =>
    apply Twin.dead
    · intro c hc
      rw [mem_support_bind_iff] at hc
      obtain ⟨a, ha, hc⟩ := hc
      exact dead0 a (all0 a ha) c hc
    · intro d hd
      rw [mem_support_bind_iff] at hd
      obtain ⟨b, hb, hd⟩ := hd
      exact dead1 b (all1 b hb) d hd
  | quiet q quiet _ ih =>
    simp only [bind_assoc]
    exact Twin.quiet q quiet fun r => ih r
  | sealing i0 i1 identified _ ih =>
    simp only [bind_assoc]
    exact Twin.sealing i0 i1 identified fun r => ih r
  | raw raw _ ih =>
    simp only [bind_assoc]
    exact Twin.raw raw fun r0 r1 related => ih r0 r1 related

/-- Twin programs are preserved by mapping related outputs to related outputs. -/
theorem twin_map {α β γ δ : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop}
    {Out' : γ → δ → Prop} {Dead0' : γ → Prop} {Dead1' : δ → Prop}
    {x : OracleComp Spec α} {y : OracleComp Spec β} (twin : Twin m0 m1 Out Dead0 Dead1 x y)
    (f : α → γ) (g : β → δ) (related : ∀ a b, Out a b → Out' (f a) (g b))
    (dead0 : ∀ a, Dead0 a → Dead0' (f a)) (dead1 : ∀ b, Dead1 b → Dead1' (g b)) :
    Twin m0 m1 Out' Dead0' Dead1' (f <$> x) (g <$> y) := by
  simp only [map_eq_bind_pure_comp]
  refine twin_bind m0 m1 twin (fun a b holds => Twin.pure (related a b holds)) ?_ ?_
  · intro a dead c hc
    simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hc
    exact hc ▸ dead0 a dead
  · intro b dead d hd
    simp only [Function.comp_apply, support_pure, Set.mem_singleton_iff] at hd
    exact hd ▸ dead1 b dead

/-- A selected raw opening request. -/
def IsRaw : Spec.Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- Selected raw openings are decidable. -/
instance : DecidablePred IsRaw := fun query => by
  rcases query with ((_ | (_ | _)) | _) | _ <;> simp only [IsRaw] <;> infer_instance

/-- A program without selected raw openings is twin to itself with equal outputs. -/
theorem twin_refl {α : Type} {Dead : α → Prop} (x : OracleComp Spec α) (noRaw : x.IsQueryBoundP IsRaw 0) :
    Twin m0 m1 (fun a b => a = b) Dead Dead x x := by
  induction x using OracleComp.inductionOn with
  | pure value => exact Twin.pure rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at noRaw
    rcases query with ((coin | (hash | input)) | raw) | known
    · exact Twin.quiet _ trivial fun r => ih r (noRaw.2 r)
    · exact Twin.quiet _ trivial fun r => ih r (noRaw.2 r)
    · exact Twin.sealing input input rfl fun r => ih r (noRaw.2 r)
    · exact absurd trivial (by simpa [IsRaw] using noRaw.1)
    · exact Twin.quiet _ trivial fun r => ih r (noRaw.2 r)

/-- Forward every request unchanged and raise a sticky flag on selected raw openings. -/
noncomputable def markRaw : QueryImpl Spec (StateT Bool (OracleComp Spec)) :=
  fun query flag => do
    let reply ← Spec.query query
    pure (reply, flag || decide (IsRaw query))

/-- One marked request. -/
theorem markRaw_run (query : Spec.Domain) (flag : Bool) :
    (markRaw query).run flag = (fun reply => (reply, flag || decide (IsRaw query))) <$> (Spec.query query : OracleComp Spec _) := by
  simp [markRaw, StateT.run, map_eq_bind_pure_comp]

/-- Erasing the flag recovers the program. -/
theorem markRaw_erase {α : Type} (x : OracleComp Spec α) (flag : Bool) :
    Prod.fst <$> (simulateQ markRaw x).run flag = x := by
  induction x using OracleComp.inductionOn generalizing flag with
  | pure value => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, markRaw_run, bind_map_left, map_bind, ih]

/-- A raised flag stays raised. -/
theorem markRaw_sticky {α : Type} (x : OracleComp Spec α) (result : α × Bool)
    (supported : result ∈ support ((simulateQ markRaw x).run true)) : result.2 = true := by
  induction x using OracleComp.inductionOn generalizing result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, markRaw_run, bind_map_left, Bool.true_or,
      mem_support_bind_iff] at supported
    obtain ⟨reply, _, rest⟩ := supported
    exact ih reply result rest

/-- Any program wrapped by `markRaw` is twin to itself: equal outputs, and every continuation after a selected raw reply is dead because its flag is raised. -/
theorem twin_markRaw {α : Type} (x : OracleComp Spec α) (flag : Bool) :
    Twin m0 m1 (fun a b => a = b) (fun z : α × Bool => z.2 = true) (fun z : α × Bool => z.2 = true)
      ((simulateQ markRaw x).run flag) ((simulateQ markRaw x).run flag) := by
  induction x using OracleComp.inductionOn generalizing flag with
  | pure value => exact Twin.pure rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, markRaw_run, bind_map_left]
    rcases query with ((coin | (hash | input)) | raw) | known
    · exact Twin.quiet _ trivial fun r => ih r _
    · exact Twin.quiet _ trivial fun r => ih r _
    · exact Twin.sealing input input rfl fun r => ih r _
    · refine Twin.raw raw fun r0 r1 _ => Twin.dead ?_ ?_
      · intro z hz
        exact markRaw_sticky (next r0) z (by rwa [show (flag || decide (IsRaw (rawQuery raw))) = true from Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true trivial))] at hz)
      · intro z hz
        exact markRaw_sticky (next r1) z (by rwa [show (flag || decide (IsRaw (rawQuery raw))) = true from Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true trivial))] at hz)
    · exact Twin.quiet _ trivial fun r => ih r _

end Algebra

section Runs
open AdaptiveCtxDynamicKnownKeys (Spec)
variable (m0 m1 : Pqxdh.Bytes)

/-- Running a stateful, stoppable interpretation over the CTX interface. -/
abbrev Stepper (κ σ : Type) := StateT κ (OptionT (StateT σ (OracleComp Spec)))

/-- The complete run of a stoppable interpretation from a pair of states. -/
def runStepper {κ σ α : Type} (x : Stepper κ σ α) (c : κ) (s : σ) : OracleComp Spec (Option (α × κ) × σ) :=
  ((x.run c).run).run s

/-- One request followed by its continuation; a stopped request stops the run. -/
theorem runStepper_bind {κ σ α β : Type} (x : Stepper κ σ α) (f : α → Stepper κ σ β) (c : κ) (s : σ) :
    runStepper (x >>= f) c s = runStepper x c s >>= fun z => match z.1 with
      | none => pure (none, z.2)
      | some (a, c') => runStepper (f a) c' z.2 := by
  simp only [runStepper, StateT.run_bind, OptionT.run_bind, Option.elimM]
  refine bind_congr fun z => ?_
  rcases z with ⟨_ | ⟨a, c'⟩, s'⟩ <;> rfl

/-- A dead state stays dead along the whole run when every step keeps it dead. -/
theorem runStepper_dead {ι κ σ α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (Stepper κ σ)) (Dead : σ → Prop)
    (sticky : ∀ q c s, Dead s → ∀ z ∈ support (runStepper (impl q) c s), Dead z.2)
    (x : OracleComp spec α) (c : κ) (s : σ) (dead : Dead s) :
    ∀ z ∈ support (runStepper (simulateQ impl x) c s), Dead z.2 := by
  induction x using OracleComp.inductionOn generalizing c s with
  | pure value =>
    intro z hz
    simp only [runStepper, simulateQ_pure, StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact dead
  | query_bind query next ih =>
    intro z hz
    rw [simulateQ_bind, simulateQ_spec_query, runStepper_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have deadW := sticky query c s dead w hw
    rcases w with ⟨_ | ⟨reply, c'⟩, s'⟩
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact deadW
    · exact ih reply c' s' deadW z hz

/-- Per-request twin steps with equal outputs until a sticky dead state give twin complete runs. -/
theorem twin_run {ι κ σ α : Type} {spec : OracleSpec ι} (impl0 impl1 : QueryImpl spec (Stepper κ σ)) (Dead : σ → Prop)
    (step : ∀ q c s, ¬ Dead s → Twin m0 m1 (fun a b => a = b) (fun z => Dead z.2) (fun z => Dead z.2)
      (runStepper (impl0 q) c s) (runStepper (impl1 q) c s))
    (sticky0 : ∀ q c s, Dead s → ∀ z ∈ support (runStepper (impl0 q) c s), Dead z.2)
    (sticky1 : ∀ q c s, Dead s → ∀ z ∈ support (runStepper (impl1 q) c s), Dead z.2)
    (x : OracleComp spec α) (c : κ) (s : σ) (alive : ¬ Dead s) :
    Twin m0 m1 (fun a b => a = b) (fun z => Dead z.2) (fun z => Dead z.2)
      (runStepper (simulateQ impl0 x) c s) (runStepper (simulateQ impl1 x) c s) := by
  induction x using OracleComp.inductionOn generalizing c s with
  | pure value =>
    simp only [runStepper, simulateQ_pure, StateT.run_pure, OptionT.run_pure]
    exact Twin.pure rfl
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, runStepper_bind, runStepper_bind]
    refine twin_bind m0 m1 (step query c s alive) ?_ ?_ ?_
    · rintro z _ rfl
      by_cases dead : Dead z.2
      · refine Twin.dead ?_ ?_
        · intro w hw
          rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
          · simp only [support_pure, Set.mem_singleton_iff] at hw
            rw [hw]
            exact dead
          · exact runStepper_dead impl0 Dead sticky0 (next reply) c' s' dead w hw
        · intro w hw
          rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
          · simp only [support_pure, Set.mem_singleton_iff] at hw
            rw [hw]
            exact dead
          · exact runStepper_dead impl1 Dead sticky1 (next reply) c' s' dead w hw
      · rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
        · exact Twin.pure rfl
        · exact ih reply c' s' dead
    · intro z dead w hw
      rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
        exact dead
      · exact runStepper_dead impl0 Dead sticky0 (next reply) c' s' dead w hw
    · intro z dead w hw
      rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
        exact dead
      · exact runStepper_dead impl1 Dead sticky1 (next reply) c' s' dead w hw

end Runs


section Adaptive
open AdaptiveCtxDynamicKnownKeys (Spec)
open CtxRomAuth

/-- Identical-until-dead clients: both programs make the same requests and continue alike for every reply, or end in outputs marked dead on both sides. -/
inductive Same {α β : Type} (Out : α → β → Prop) (Dead0 : α → Prop) (Dead1 : β → Prop) :
    OracleComp Spec α → OracleComp Spec β → Prop
  | pure {a : α} {b : β} : Out a b → Same Out Dead0 Dead1 (pure a) (pure b)
  | dead {x : OracleComp Spec α} {y : OracleComp Spec β} :
      (∀ a ∈ support x, Dead0 a) → (∀ b ∈ support y, Dead1 b) → Same Out Dead0 Dead1 x y
  | step (q : Spec.Domain) {k0 : Spec.Range q → OracleComp Spec α} {k1 : Spec.Range q → OracleComp Spec β} :
      (∀ r, Same Out Dead0 Dead1 (k0 r) (k1 r)) → Same Out Dead0 Dead1 (query q >>= k0) (query q >>= k1)

/-- Adaptive twin clients: identical requests with identical continuations until a switch, where the clients become twin clients for a pair of equal-length challenge plaintexts chosen at that point. -/
inductive Pre {α β : Type} (Out : α → β → Prop) (Dead0 : α → Prop) (Dead1 : β → Prop) :
    OracleComp Spec α → OracleComp Spec β → Prop
  | pure {a : α} {b : β} : Out a b → Pre Out Dead0 Dead1 (pure a) (pure b)
  | dead {x : OracleComp Spec α} {y : OracleComp Spec β} :
      (∀ a ∈ support x, Dead0 a) → (∀ b ∈ support y, Dead1 b) → Pre Out Dead0 Dead1 x y
  | step (q : Spec.Domain) {k0 : Spec.Range q → OracleComp Spec α} {k1 : Spec.Range q → OracleComp Spec β} :
      (∀ r, Pre Out Dead0 Dead1 (k0 r) (k1 r)) → Pre Out Dead0 Dead1 (query q >>= k0) (query q >>= k1)
  | switch (m0 m1 : Pqxdh.Bytes) {x : OracleComp Spec α} {y : OracleComp Spec β} :
      m0.length = m1.length → Twin m0 m1 Out Dead0 Dead1 x y → Pre Out Dead0 Dead1 x y

/-- Every program is identical-until-dead to itself with equal outputs. -/
theorem same_refl {α : Type} {Dead : α → Prop} (x : OracleComp Spec α) : Same (fun a b => a = b) Dead Dead x x := by
  induction x using OracleComp.inductionOn with
  | pure value => exact Same.pure rfl
  | query_bind query next ih => exact Same.step query ih

/-- Identical-until-dead programs compose by bind. -/
theorem same_bind {α β γ δ : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop}
    {Out' : γ → δ → Prop} {Dead0' : γ → Prop} {Dead1' : δ → Prop}
    {x : OracleComp Spec α} {y : OracleComp Spec β} (same : Same Out Dead0 Dead1 x y)
    {f : α → OracleComp Spec γ} {g : β → OracleComp Spec δ}
    (next : ∀ a b, Out a b → Same Out' Dead0' Dead1' (f a) (g b))
    (dead0 : ∀ a, Dead0 a → ∀ c ∈ support (f a), Dead0' c) (dead1 : ∀ b, Dead1 b → ∀ d ∈ support (g b), Dead1' d) :
    Same Out' Dead0' Dead1' (x >>= f) (y >>= g) := by
  induction same with
  | pure related => simpa only [pure_bind] using next _ _ related
  | dead all0 all1 =>
    apply Same.dead
    · intro c hc
      rw [mem_support_bind_iff] at hc
      obtain ⟨a, ha, hc⟩ := hc
      exact dead0 a (all0 a ha) c hc
    · intro d hd
      rw [mem_support_bind_iff] at hd
      obtain ⟨b, hb, hd⟩ := hd
      exact dead1 b (all1 b hb) d hd
  | step q _ ih =>
    simp only [bind_assoc]
    exact Same.step q fun r => ih r

/-- An identical-until-dead prefix followed by adaptive twin continuations is adaptive twin. -/
theorem same_pre {α β γ δ : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop}
    {Out' : γ → δ → Prop} {Dead0' : γ → Prop} {Dead1' : δ → Prop}
    {x : OracleComp Spec α} {y : OracleComp Spec β} (same : Same Out Dead0 Dead1 x y)
    {f : α → OracleComp Spec γ} {g : β → OracleComp Spec δ}
    (next : ∀ a b, Out a b → Pre Out' Dead0' Dead1' (f a) (g b))
    (dead0 : ∀ a, Dead0 a → ∀ c ∈ support (f a), Dead0' c) (dead1 : ∀ b, Dead1 b → ∀ d ∈ support (g b), Dead1' d) :
    Pre Out' Dead0' Dead1' (x >>= f) (y >>= g) := by
  induction same with
  | pure related => simpa only [pure_bind] using next _ _ related
  | dead all0 all1 =>
    apply Pre.dead
    · intro c hc
      rw [mem_support_bind_iff] at hc
      obtain ⟨a, ha, hc⟩ := hc
      exact dead0 a (all0 a ha) c hc
    · intro d hd
      rw [mem_support_bind_iff] at hd
      obtain ⟨b, hb, hd⟩ := hd
      exact dead1 b (all1 b hb) d hd
  | step q _ ih =>
    simp only [bind_assoc]
    exact Pre.step q fun r => ih r

/-- Adaptive twin programs are preserved by mapping related outputs to related outputs. -/
theorem pre_map {α β γ δ : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop}
    {Out' : γ → δ → Prop} {Dead0' : γ → Prop} {Dead1' : δ → Prop}
    {x : OracleComp Spec α} {y : OracleComp Spec β} (pre : Pre Out Dead0 Dead1 x y)
    (f : α → γ) (g : β → δ) (related : ∀ a b, Out a b → Out' (f a) (g b))
    (dead0 : ∀ a, Dead0 a → Dead0' (f a)) (dead1 : ∀ b, Dead1 b → Dead1' (g b)) :
    Pre Out' Dead0' Dead1' (f <$> x) (g <$> y) := by
  induction pre with
  | pure holds => simpa only [map_pure] using Pre.pure (related _ _ holds)
  | dead all0 all1 =>
    apply Pre.dead
    · intro c hc
      rw [support_map] at hc
      obtain ⟨a, ha, rfl⟩ := hc
      exact dead0 a (all0 a ha)
    · intro d hd
      rw [support_map] at hd
      obtain ⟨b, hb, rfl⟩ := hd
      exact dead1 b (all1 b hb)
  | step q _ ih =>
    simp only [map_bind]
    exact Pre.step q fun r => ih r
  | switch m0 m1 equal twin => exact Pre.switch m0 m1 equal (twin_map m0 m1 twin f g related dead0 dead1)

variable {σ : Type} (impl : QueryImpl Spec (StateT σ ProbComp)) (E : Pqxdh.Bytes → Pqxdh.Bytes → σ → σ)

/-- Adaptive twin clients interpreted from one state by an interpretation compatible with every equal-length identification put the same mass on corresponding good outputs. -/
theorem pre_event {α β : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop}
    {x : OracleComp Spec α} {y : OracleComp Spec β} (pre : Pre Out Dead0 Dead1 x y)
    (G0 : α → Prop) (G1 : β → Prop) [DecidablePred G0] [DecidablePred G1] (hOut : ∀ a b, Out a b → (G0 a ↔ G1 b))
    (hDead0 : ∀ a, Dead0 a → ¬ G0 a) (hDead1 : ∀ b, Dead1 b → ¬ G1 b)
    (compatible : ∀ m0 m1 : Pqxdh.Bytes, m0.length = m1.length → Compatible m0 m1 impl (E m0 m1)) (s : σ) :
    Pr{let z ← (simulateQ impl x).run s}[G0 z.1] = Pr{let z ← (simulateQ impl y).run s}[G1 z.1] := by
  induction pre generalizing s with
  | pure related =>
    rename_i a b
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure]
    by_cases good : G0 a
    · simp [good, (hOut a b related).mp good]
    · simp [good, show ¬ G1 b from fun holds => good ((hOut a b related).mpr holds)]
  | dead dead0 dead1 =>
    rename_i x y
    have zero0 : Pr{let z ← (simulateQ impl x).run s}[G0 z.1] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz good => by
        have mem : z.1 ∈ support ((simulateQ impl x).run' s) := by
          rw [StateT.run'_eq, support_map]
          exact ⟨z, hz, rfl⟩
        exact hDead0 z.1 (dead0 z.1 (support_simulateQ_run'_subset impl x s mem)) good
    have zero1 : Pr{let z ← (simulateQ impl y).run s}[G1 z.1] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun z hz good => by
        have mem : z.1 ∈ support ((simulateQ impl y).run' s) := by
          rw [StateT.run'_eq, support_map]
          exact ⟨z, hz, rfl⟩
        exact hDead1 z.1 (dead1 z.1 (support_simulateQ_run'_subset impl y s mem)) good
    rw [zero0, zero1]
  | step q _ ih =>
    simp only [simulateQ_bind, simulateQ_HasQuery_query, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
    exact tsum_congr fun z => by rw [ih z.1 z.2]
  | switch m0 m1 equal twin =>
    exact twin_event m0 m1 impl (E m0 m1) twin G0 G1 hOut hDead0 hDead1 (compatible m0 m1 equal) s s rfl

set_option linter.deprecated false in set_option linter.unusedVariables false in theorem _root_.BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_event_vcvioLegacy :
    ∀ {σ : Type} (impl : QueryImpl BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.Spec (StateT σ ProbComp)) (E : Pqxdh.Bytes → Pqxdh.Bytes → σ → σ) {α β : Type} {Out : α → β → Prop} {Dead0 : α → Prop} {Dead1 : β → Prop} {x : OracleComp BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.Spec α} {y : OracleComp BeaconcryptCore.Computational.AdaptiveCtxDynamicKnownKeys.Spec β} (pre : BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.Pre Out Dead0 Dead1 x y) (G0 : α → Prop) (G1 : β → Prop) [DecidablePred G0] [DecidablePred G1] (hOut : ∀ (a : α) (b : β), Out a b → (G0 a ↔ G1 b)) (hDead0 : ∀ (a : α), Dead0 a → ¬G0 a) (hDead1 : ∀ (b : β), Dead1 b → ¬G1 b) (compatible : ∀ (m0 m1 : Pqxdh.Bytes), List.length m0 = List.length m1 → BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.Compatible m0 m1 impl (E m0 m1)) (s : σ), (probEvent ((simulateQ impl x).run s) fun (z : α × σ) => G0 z.1) = probEvent ((simulateQ impl y).run s) fun (z : β × σ) => G1 z.1 :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_event

/-- Adaptive twin Boolean clients have the same `true` mass in the ordinary random view: before the switch they are identical, and after it the challenge plaintexts have equal length. -/
theorem randomView_pre (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto) {left right : OracleComp Spec Bool}
    (pre : Pre (fun a b => a = b) (fun a => a = false) (fun b => b = false) left right) :
    𝒟[AdaptiveCtxPrivacyGuard.randomView decode (AdaptiveCtxDynamicKnownKeys.decisionClient c left)] {true} =
      𝒟[AdaptiveCtxPrivacyGuard.randomView decode (AdaptiveCtxDynamicKnownKeys.decisionClient c right)] {true} := by
  rw [randomView_collapse, randomView_collapse, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  exact pre_event (confRandomImpl decode c) (fun m0 m1 => identRandom m0 m1) pre (fun a => a = true) (fun b => b = true)
    (fun a b same => by rw [same]) (fun a dead => by simp [dead]) (fun b dead => by simp [dead])
    (fun m0 m1 equal => random_compatible m0 m1 decode c equal) _

end Adaptive

section RunsInvariant
open AdaptiveCtxDynamicKnownKeys (Spec)
variable (m0 m1 : Pqxdh.Bytes)

/-- Per-request twin steps with equal outputs that preserve a control invariant, until a sticky dead state, give twin complete runs from every state satisfying the invariant. -/
theorem twin_run_inv {ι κ σ α : Type} {spec : OracleSpec ι} (impl0 impl1 : QueryImpl spec (Stepper κ σ)) (Dead : σ → Prop)
    (Inv : κ → Prop)
    (step : ∀ q c s, Inv c → ¬ Dead s → Twin m0 m1 (fun z0 z1 => z0 = z1 ∧ ∀ reply c', z0.1 = some (reply, c') → Inv c')
      (fun z => Dead z.2) (fun z => Dead z.2) (runStepper (impl0 q) c s) (runStepper (impl1 q) c s))
    (sticky0 : ∀ q c s, Dead s → ∀ z ∈ support (runStepper (impl0 q) c s), Dead z.2)
    (sticky1 : ∀ q c s, Dead s → ∀ z ∈ support (runStepper (impl1 q) c s), Dead z.2)
    (x : OracleComp spec α) (c : κ) (s : σ) (inv : Inv c) (alive : ¬ Dead s) :
    Twin m0 m1 (fun a b => a = b) (fun z => Dead z.2) (fun z => Dead z.2)
      (runStepper (simulateQ impl0 x) c s) (runStepper (simulateQ impl1 x) c s) := by
  induction x using OracleComp.inductionOn generalizing c s with
  | pure value =>
    simp only [runStepper, simulateQ_pure, StateT.run_pure, OptionT.run_pure]
    exact Twin.pure rfl
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, runStepper_bind, runStepper_bind]
    refine twin_bind m0 m1 (step query c s inv alive) ?_ ?_ ?_
    · rintro z _ ⟨rfl, preserved⟩
      by_cases dead : Dead z.2
      · refine Twin.dead ?_ ?_
        · intro w hw
          rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
          · simp only [support_pure, Set.mem_singleton_iff] at hw
            rw [hw]
            exact dead
          · exact runStepper_dead impl0 Dead sticky0 (next reply) c' s' dead w hw
        · intro w hw
          rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
          · simp only [support_pure, Set.mem_singleton_iff] at hw
            rw [hw]
            exact dead
          · exact runStepper_dead impl1 Dead sticky1 (next reply) c' s' dead w hw
      · rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
        · exact Twin.pure rfl
        · exact ih reply c' s' (preserved reply c' rfl) dead
    · intro z dead w hw
      rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
        exact dead
      · exact runStepper_dead impl0 Dead sticky0 (next reply) c' s' dead w hw
    · intro z dead w hw
      rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hw
        rw [hw]
        exact dead
      · exact runStepper_dead impl1 Dead sticky1 (next reply) c' s' dead w hw

end RunsInvariant

section Experiment
variable {ι : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The adversary's post-registration interface. -/
abbrev ConfPostSpec (extra : OracleSpec ι) (S B : Nat) := PqxdhInitialGenericPost.Spec extra S B

/-- The challenge interface: two plaintexts in, the record returned by the challenge send (if any) out. -/
abbrev ChallengeSpec := (Pqxdh.Bytes × Pqxdh.Bytes) →ₒ Option RawCtxSourceSend.Encrypted

/-- The left-or-right adversary's interface: every post request and one challenge. -/
abbrev AdvSpec (extra : OracleSpec ι) (S B : Nat) := ConfPostSpec extra S B + ChallengeSpec

/-- A send request of Beacon `b` with the given plaintext. -/
abbrev beaconSend (b : Fin B) (plaintext : Pqxdh.Bytes) : (ConfPostSpec extra S B).Domain :=
  .inl (.inl (.inl (.inr (.inl ⟨b, .inl plaintext⟩))))

/-- The wrapper's public record of the experiment. -/
structure ConfState where
  /-- The challenge plaintexts, once the challenge was forwarded. -/
  pair : Option (Pqxdh.Bytes × Pqxdh.Bytes)
  /-- The reply of the forwarded challenge send. -/
  reply : Option (Option RawCtxSourceSend.Encrypted)
  /-- A send of Beacon `b` was requested (by the adversary or by the challenge). -/
  beaconSent : Bool
  /-- A send of Beacon `b` requested by the adversary returned a record of sequence one. -/
  otherFirst : Bool

/-- The initial wrapper record. -/
def confInitial : ConfState := ⟨none, none, false, false⟩

/-- A receive reply whose plaintext is one of the challenge plaintexts is reported as a failure. -/
def suppress (pair : Option (Pqxdh.Bytes × Pqxdh.Bytes)) (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    core.option.Option RawCtxWholeOwner.Decrypted :=
  match pair, reply with
  | some (m0, m1), .Some decrypted => if decrypted.plaintext = m0 ∨ decrypted.plaintext = m1 then .None else reply
  | _, _ => reply

/-- The reply given to the adversary: Server and Beacon raw-receive replies are screened by `suppress`; every other reply, including a Beacon finish reply, is unchanged. -/
def screen (state : ConfState) : (request : (ConfPostSpec extra S B).Domain) → (ConfPostSpec extra S B).Range request →
    (ConfPostSpec extra S B).Range request
  | .inl (.inl (.inl (.inl ⟨_, .inr _⟩))), reply => suppress state.pair reply
  | .inl (.inl (.inl (.inr (.inl ⟨_, .inr _⟩)))), reply => suppress state.pair reply
  | _, reply => reply

/-- Whether a send reply is a record of sequence one. -/
def firstRecord (reply : Option RawCtxSourceSend.Encrypted) : Bool :=
  match reply with
  | some sent => decide (sent.sequence = 1#u64)
  | none => false

/-- The wrapper's bookkeeping after an adversary request: sends of Beacon `b` are noted, and a sequence-one reply to such a send is noted. -/
def observe (b : Fin B) (state : ConfState) : (request : (ConfPostSpec extra S B).Domain) →
    (ConfPostSpec extra S B).Range request → ConfState
  | .inl (.inl (.inl (.inr (.inl ⟨index, .inl _⟩)))), reply =>
      if index = b then { state with beaconSent := true, otherFirst := state.otherFirst || firstRecord reply } else state
  | _, _ => state

/-- The left-or-right wrapper for challenge bit `β`. Post requests are forwarded and screened. The challenge `(m0, m1)` is forwarded as a send of Beacon `b` with `m_β` only if it is the first acceptable challenge (no challenge was forwarded before), no send of Beacon `b` was requested before and the two plaintexts have equal length; otherwise it is refused without any request and without using up the challenge. -/
noncomputable def confImpl (b : Fin B) (β : Bool) :
    QueryImpl (AdvSpec extra S B) (StateT ConfState (OracleComp (ConfPostSpec extra S B))) :=
  fun query state => match query with
  | .inl request => do
      let reply ← (ConfPostSpec extra S B).query request
      pure (screen state request reply, observe b state request reply)
  | .inr (m0, m1) =>
      if state.pair.isSome ∨ state.beaconSent ∨ m0.length ≠ m1.length then pure (none, state)
      else do
        let reply ← (ConfPostSpec extra S B).query (beaconSend b (if β then m1 else m0))
        pure (reply, { state with pair := some (m0, m1), reply := some reply, beaconSent := true })

/-- The challenge was forwarded, answered with a record of sequence one, and no adversary send of Beacon `b` returned a sequence-one record. -/
def Fresh (state : ConfState) : Prop :=
  state.pair.isSome ∧ (∃ sent, state.reply = some (some sent) ∧ sent.sequence = 1#u64) ∧ state.otherFirst = false

/-- Freshness is decided classically. -/
noncomputable instance (state : ConfState) : Decidable (Fresh state) := Classical.propDecidable _

/-- The wrapper's output: the adversary's guess, counted only for a fresh challenge. -/
noncomputable def confOutput (result : Bool × ConfState) : Bool := result.1 && decide (Fresh result.2)

/-- The left-or-right post for challenge bit `β`: an ordinary post program that runs the adversary through the wrapper. -/
noncomputable def confPost {Selection : Type} (A : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
    OracleComp (AdvSpec extra S B) Bool) (b : Fin B) (β : Bool) :
    Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (ConfPostSpec extra S B) Bool :=
  fun selection reply => confOutput <$> (simulateQ (confImpl b β) (A selection reply)).run confInitial

/-- A wrapper-side request predicate lifted to the adversary's interface: adversary post requests keep it, and a challenge counts when either challenge send would count. -/
def liftPred (b : Fin B) (q : (ConfPostSpec extra S B).Domain → Prop) : (AdvSpec extra S B).Domain → Prop
  | .inl request => q request
  | .inr (m0, m1) => q (beaconSend b m0) ∨ q (beaconSend b m1)

/-- The lifted predicate is decidable. -/
noncomputable instance (b : Fin B) (q : (ConfPostSpec extra S B).Domain → Prop) : DecidablePred (liftPred b q) :=
  fun _ => Classical.propDecidable _

/-- Every query budget of the adversary, with each challenge counted as the Beacon `b` send it may become, is a query budget of the wrapper run: adversary post requests are forwarded one for one, and a challenge makes at most one send. -/
theorem conf_query_bound (b : Fin B) (β : Bool) (q : (ConfPostSpec extra S B).Domain → Prop) [DecidablePred q]
    (adversary : OracleComp (AdvSpec extra S B) Bool) (n : Nat) (bounded : adversary.IsQueryBoundP (liftPred b q) n)
    (state : ConfState) : ((simulateQ (confImpl b β) adversary).run state).IsQueryBoundP q n := by
  classical
  refine IsQueryBoundP.simulateQ_run_StateT_of_step bounded ?_ state
  intro query current
  rcases query with request | ⟨m0, m1⟩
  · simp only [confImpl, liftPred, StateT.run]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨?_, fun _ => trivial⟩
    by_cases counted : q request <;> simp [counted]
  · simp only [confImpl, StateT.run]
    split
    · trivial
    · rw [isQueryBoundP_query_bind_iff]
      refine ⟨?_, fun _ => trivial⟩
      by_cases counted : q (beaconSend b (if β then m1 else m0))
      · refine Or.inr ?_
        have lifted : liftPred b q (.inr (m0, m1)) := by
          cases β
          · exact Or.inl counted
          · exact Or.inr counted
        simp [lifted]
      · exact Or.inl counted

/-- The single-challenge adversary: one challenge `(m0, m1)`, then a guess computed from the returned record. -/
noncomputable def singleChallenge (m0 m1 : Pqxdh.Bytes) (guess : Option RawCtxSourceSend.Encrypted → Bool) :
    OracleComp (AdvSpec extra S B) Bool :=
  guess <$> (liftM ((AdvSpec extra S B).query (.inr (m0, m1))) : OracleComp (AdvSpec extra S B) (Option RawCtxSourceSend.Encrypted))

set_option backward.isDefEq.respectTransparency false in
/-- Non-vacuity: for equal-length plaintexts the wrapper forwards the single challenge as Beacon `b`'s send of `m_β`, and its output is the adversary's guess exactly when the reply is a sequence-one record. -/
theorem single_output (b : Fin B) (β : Bool) (m0 m1 : Pqxdh.Bytes) (equal : m0.length = m1.length)
    (guess : Option RawCtxSourceSend.Encrypted → Bool) :
    confOutput <$> (simulateQ (confImpl b β) (singleChallenge (extra := extra) (S := S) m0 m1 guess)).run confInitial =
      (fun reply => guess reply && firstRecord reply) <$>
        (liftM ((ConfPostSpec extra S B).query (beaconSend b (if β then m1 else m0))) :
          OracleComp (ConfPostSpec extra S B) (Option RawCtxSourceSend.Encrypted)) := by
  have accepted : ¬ (confInitial.pair.isSome ∨ confInitial.beaconSent ∨ m0.length ≠ m1.length) := by
    simp [confInitial, equal]
  simp only [singleChallenge, simulateQ_map, StateT.run_map, Functor.map_map, simulateQ_query]
  change (fun a => confOutput (guess a.1, a.2)) <$> (confImpl (extra := extra) (S := S) b β (.inr (m0, m1))).run confInitial = _
  simp only [confImpl, StateT.run]
  rw [ite_eq_right_iff.mpr fun holds => absurd holds accepted]
  simp only [map_bind, map_pure]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun reply => ?_
  simp only [Function.comp_apply]
  congr 1
  simp only [confOutput]
  congr 1
  rcases reply with _ | sent
  · simp [Fresh, firstRecord]
  · simp [Fresh, firstRecord, confInitial]

/-- Non-vacuity: the single challenge with the constant guess `true` is counted exactly when the challenge reply is a sequence-one record. -/
theorem single_true (b : Fin B) (β : Bool) (m0 m1 : Pqxdh.Bytes) (equal : m0.length = m1.length)
    (sent : RawCtxSourceSend.Encrypted) (first : sent.sequence = 1#u64) :
    true ∈ support ((confOutput <$> (simulateQ (confImpl b β) (singleChallenge (extra := extra) (S := S) m0 m1
      (fun _ => true))).run confInitial) : OracleComp (ConfPostSpec extra S B) Bool) := by
  rw [single_output b β m0 m1 equal, support_map]
  exact ⟨some sent, mem_support_query _ _, by simp [firstRecord, first]⟩

/-- Receive screening after the challenge hides both challenge plaintexts, so a delivered challenge record gives the same reply for both challenge bits. -/
theorem suppress_challenge (m0 m1 : Pqxdh.Bytes) (β : Bool) (keyId sequence : Std.U64) :
    suppress (some (m0, m1)) (.Some ⟨if β then m1 else m0, keyId, sequence⟩) = .None := by
  cases β <;> simp [suppress]

/-- Receive screening passes every other plaintext unchanged. -/
theorem suppress_other (m0 m1 : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted)
    (other : decrypted.plaintext ≠ m0 ∧ decrypted.plaintext ≠ m1) :
    suppress (some (m0, m1)) (.Some decrypted) = .Some decrypted := by
  simp [suppress, other.1, other.2]

/-- Negative control: without screening, the reply of a raw receive that opens the challenge record reveals the challenge bit whenever the two plaintexts differ. -/
theorem unscreened_reveals (m0 m1 : Pqxdh.Bytes) (distinct : m0 ≠ m1) (β : Bool) (keyId sequence : Std.U64) :
    (match (core.option.Option.Some ⟨if β then m1 else m0, keyId, sequence⟩ : core.option.Option RawCtxWholeOwner.Decrypted) with
      | .Some decrypted => decide (decrypted.plaintext = m1)
      | .None => false) = β := by
  cases β <;> simp [distinct]

end Experiment


section GenericCoupling

/-- Along a complete run, a good final state was reached only from a good start when every step preserves goodness backwards. -/
theorem run_good_back {ι σ X : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT σ ProbComp)) (Good : σ → Prop)
    (back : ∀ q s z, z ∈ support ((impl q).run s) → Good z.2 → Good s)
    (work : OracleComp spec X) (s : σ) (result : X × σ) (supported : result ∈ support ((simulateQ impl work).run s))
    (good : Good result.2) : Good s := by
  induction work using OracleComp.inductionOn generalizing s with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact good
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, stepSupported, rest⟩ := supported
    exact back query s step stepSupported (ih step.1 step.2 rest)

/-- Two interpretations that agree except on disclosing steps, after which no good state is reachable, give the same probability to every good final result. -/
theorem good_output_eq {ι σ X : Type} {spec : OracleSpec ι} (normal original : QueryImpl spec (StateT σ ProbComp))
    (Good : σ → Prop) (Discloses : spec.Domain → σ → Prop)
    (agree : ∀ q s, ¬ Discloses q s → (normal q).run s = (original q).run s)
    (backNormal : ∀ q s z, z ∈ support ((normal q).run s) → Good z.2 → Good s)
    (backOriginal : ∀ q s z, z ∈ support ((original q).run s) → Good z.2 → Good s)
    (badNormal : ∀ q s, Discloses q s → ∀ z ∈ support ((normal q).run s), ¬ Good z.2)
    (badOriginal : ∀ q s, Discloses q s → ∀ z ∈ support ((original q).run s), ¬ Good z.2)
    (work : OracleComp spec X) (s : σ) (result : X × σ) (good : Good result.2) :
    Pr{let x ← (simulateQ normal work).run s}[x = result] = Pr{let x ← (simulateQ original work).run s}[x = result] := by
  classical
  induction work using OracleComp.inductionOn generalizing s with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases clear : Discloses query s
    · rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      have zero : ∀ (impl : QueryImpl spec (StateT σ ProbComp)),
          (∀ q s z, z ∈ support ((impl q).run s) → Good z.2 → Good s) →
          (∀ z ∈ support ((impl query).run s), ¬ Good z.2) →
          ∑' z, Pr{let x ← (impl query).run s}[x = z] * Pr{let x ← (simulateQ impl (next z.1)).run z.2}[x = result] = 0 := by
        intro impl back bad
        refine ENNReal.tsum_eq_zero.mpr fun z => ?_
        by_cases hz : z ∈ support ((impl query).run s)
        · rw [(prEvent_eq_zero_of_not_mem_support _) fun reached =>
            bad z hz (run_good_back impl Good back (next z.1) z.2 result reached good), mul_zero]
        · rw [(prEvent_eq_zero_of_not_mem_support _) hz, zero_mul]
      rw [zero normal backNormal (badNormal query s clear), zero original backOriginal (badOriginal query s clear)]
    · rw [agree query s clear, OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
      exact tsum_congr fun z => by rw [ih z.1 z.2]

/-- The event form: every final event conjoined with goodness has equal probability under the two interpretations. -/
theorem good_event_eq {ι σ X : Type} {spec : OracleSpec ι} (normal original : QueryImpl spec (StateT σ ProbComp))
    (Good : σ → Prop) (Discloses : spec.Domain → σ → Prop)
    (agree : ∀ q s, ¬ Discloses q s → (normal q).run s = (original q).run s)
    (backNormal : ∀ q s z, z ∈ support ((normal q).run s) → Good z.2 → Good s)
    (backOriginal : ∀ q s z, z ∈ support ((original q).run s) → Good z.2 → Good s)
    (badNormal : ∀ q s, Discloses q s → ∀ z ∈ support ((normal q).run s), ¬ Good z.2)
    (badOriginal : ∀ q s, Discloses q s → ∀ z ∈ support ((original q).run s), ¬ Good z.2)
    (work : OracleComp spec X) (s : σ) (event : X × σ → Prop) :
    Pr{let result ← (simulateQ normal work).run s}[event result ∧ Good result.2] =
      Pr{let result ← (simulateQ original work).run s}[event result ∧ Good result.2] := by
  classical
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
  refine tsum_congr fun result => ?_
  by_cases good : Good result.2
  · simp only [good, and_true]
    rw [good_output_eq normal original Good Discloses agree backNormal backOriginal badNormal badOriginal work s result good]
  · simp only [good, and_false, ite_false]

end GenericCoupling

section Traced
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf RawCtxSelectedParentEntry
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhJointKdfGame
variable {ι M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool)

/-- The trace update of one record reply; a stopped record keeps the trace. -/
def traceRecord (before : PqxdhInitialOriginPost.Trace Bool S B) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (reply : Option ((RawCtxProtocolReveals.SourceSpec S B).Range request)) : PqxdhInitialOriginPost.Trace Bool S B :=
  match reply with
  | some value => PqxdhInitialOriginPost.record before request value
  | none => before

/-- The hidden-disclosure-stopped selected source post interpreter with the private origin and publication transcript. -/
noncomputable def trOriginal :
    QueryImpl (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)) (StateT (Traced M P I D K A N C S B) ProbComp)
  | .inl (.inl request) => fun before =>
      (fun result => (result.1, (({ before.1.1 with roles := result.2.1 }, result.2.2), traceRecord before.2 request result.1))) <$>
        (RawCtxSelectedFamilyNonceCoupling.original source writer prior parent key target nonce next sender route decode request).run
          (before.1.1.roles, before.1.2)
  | .inl (.inr request) => fun before =>
      (fun result => (some result.1, ((before.1.1, result.2), before.2))) <$>
        (PqxdhSelectedInitialOwnerCompiler.sourceExternal (extra := extra) pre application initial selector aux
          (.inr (.inr (.inr (.inl request))))).run before.1.2
  | .inr (.finish index raw) => fun before =>
      (fun result => (some result.1.1.1, ((PqxdhSelectedPostCompiler.install index before.1.1 result.1.1.2, result.2),
          PqxdhInitialOriginPost.finish before.2 index result.1.2))) <$>
        (selectedFinish pre application initial selector aux source writer prior parent key target nonce next decode mark raw
          (before.1.1.roles.1.2 index)).run before.1.2

/-- Erasing the transcript of the traced stopped source gives the stopped source. -/
theorem trOriginal_erase (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : Traced M P I D K A N C S B) :
    Prod.map id Prod.fst <$> (trOriginal pre application initial selector aux source writer prior parent key target nonce next sender
      route decode mark query).run before =
      (PqxdhSelectedPostCompiler.original pre application initial selector aux source writer prior parent key target nonce next sender
        route decode query).run before.1 := by
  rcases query with (request | request) | ⟨index, raw⟩
  · simp only [trOriginal, PqxdhSelectedPostCompiler.original, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  · simp only [trOriginal, PqxdhSelectedPostCompiler.original, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  · simp only [trOriginal, PqxdhSelectedPostCompiler.original, StateT.run, Functor.map_map, Prod.map_def, id_eq]
    rw [← finish_erase pre application initial selector aux source writer prior parent key target nonce next decode mark raw,
      PqxdhSelectedFirstRecord.state_map_apply, Functor.map_map]

/-- Before a hidden disclosure, the traced ordinary source and the traced stopped source agree on every request. -/
theorem traced_agree (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : Traced M P I D K A N C S B) (clear : ¬ PqxdhSelectedPostDisclosure.Discloses (extra := extra) query before.1) :
    (traced pre application initial selector aux source writer prior parent key target nonce next sender route decode mark query).run before =
      (trOriginal pre application initial selector aux source writer prior parent key target nonce next sender route decode mark query).run before := by
  rcases query with (request | request) | ⟨index, raw⟩
  · cases request with
    | inl request =>
      simp only [traced, tracedPlain, trOriginal, RawCtxSelectedFamilyNonceCoupling.original, RawCtxSelectedMessageStopping.normal,
        RawCtxSelectedMessageStopping.stopping, OptionT.run_mk, StateT.run, Functor.map_map]
      rfl
    | inr request =>
      cases emitted : RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.1.roles).1 with
      | none => exact False.elim (clear emitted)
      | some value =>
        simp only [traced, tracedPlain, trOriginal, RawCtxSelectedFamilyNonceCoupling.original, RawCtxSelectedMessageStopping.normal,
          RawCtxSelectedMessageStopping.stopping, OptionT.run_mk, StateT.run, map_pure, emitted,
          RawCtxSelectedMessageReveals.emit_exact key request _ value emitted, traceRecord]
  · simp only [traced, tracedPlain, trOriginal, StateT.run, Functor.map_map]
  · simp only [traced, tracedPlain, trOriginal, StateT.run, Functor.map_map]

/-- The traced ordinary source step at a hidden disclosure. -/
theorem traced_read (request : RawCtxProtocolReveals.Request S B) (before : Traced M P I D K A N C S B) :
    (traced pre application initial selector aux source writer prior parent key target nonce next sender route decode mark
      (.inl (.inl (.inr request)))).run before =
      pure (some (RawCtxSelectedMessageReveals.interpretReply key request (RawCtxSelectedMessageReveals.step request before.1.1.roles).1),
        (PqxdhSelectedPostDisclosure.afterRead request before.1, PqxdhInitialOriginPost.record before.2 (.inr request)
          (RawCtxSelectedMessageReveals.interpretReply key request (RawCtxSelectedMessageReveals.step request before.1.1.roles).1))) := by
  simp only [traced, tracedPlain, RawCtxSelectedMessageStopping.normal, StateT.run, map_pure]
  rfl

/-- The traced stopped source step at a hidden disclosure. -/
theorem trOriginal_read (request : RawCtxProtocolReveals.Request S B) (before : Traced M P I D K A N C S B) :
    (trOriginal pre application initial selector aux source writer prior parent key target nonce next sender route decode mark
      (.inl (.inl (.inr request)))).run before =
      pure (RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.1.roles).1,
        (PqxdhSelectedPostDisclosure.afterRead request before.1, traceRecord before.2 (.inr request)
          (RawCtxSelectedMessageReveals.emit request (RawCtxSelectedMessageReveals.step request before.1.1.roles).1))) := by
  simp only [trOriginal, RawCtxSelectedFamilyNonceCoupling.original, RawCtxSelectedMessageStopping.stopping, OptionT.run_mk,
    StateT.run, map_pure]
  rfl

/-- Every final event conjoined with the absence of hidden disclosure has the same probability in the traced ordinary source and the traced stopped source. -/
theorem traced_event_good {Result : Type} (work : OracleComp (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Traced M P I D K A N C S B) (event : Result × Traced M P I D K A N C S B → Prop) :
    Pr{let result ← ((simulateQ (traced pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
          work).run before)}[event result ∧ PqxdhSelectedPostDisclosure.Good result.2.1] =
      Pr{let result ← ((simulateQ (trOriginal pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
          work).run before)}[event result ∧ PqxdhSelectedPostDisclosure.Good result.2.1] := by
  refine good_event_eq _ _ (fun state => PqxdhSelectedPostDisclosure.Good state.1)
    (fun query state => PqxdhSelectedPostDisclosure.Discloses (extra := extra) query state.1)
    (traced_agree pre application initial selector aux source writer prior parent key target nonce next sender route decode mark)
    ?_ ?_ ?_ ?_ work before event
  · intro query state result supported good
    have erased := traced_erase pre application initial selector aux source writer prior parent key target nonce next sender route decode mark
      query state
    have mem : (result.1, result.2.1) ∈ support ((PqxdhSelectedPostDisclosure.normal pre application initial selector aux source writer
        prior parent key target nonce next sender route decode query).run state.1) := by
      rw [← erased, support_map]
      exact ⟨result, supported, rfl⟩
    exact PqxdhSelectedPostDisclosure.normal_good pre application initial selector aux source writer prior parent key target nonce next
      sender route decode query state.1 _ mem good
  · intro query state result supported good
    have erased := trOriginal_erase pre application initial selector aux source writer prior parent key target nonce next sender route decode
      mark query state
    have mem : (result.1, result.2.1) ∈ support ((PqxdhSelectedPostCompiler.original pre application initial selector aux source writer
        prior parent key target nonce next sender route decode query).run state.1) := by
      rw [← erased, support_map]
      exact ⟨result, supported, rfl⟩
    exact PqxdhSelectedPostDisclosure.original_good pre application initial selector aux source writer prior parent key target nonce next
      sender route decode query state.1 _ mem good
  · intro query state disclosed result supported
    rcases query with ((request | request) | request) | request
    · exact False.elim disclosed
    · rw [traced_read, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact PqxdhSelectedPostDisclosure.disclosed_bad request state.1 disclosed
    · exact False.elim disclosed
    · cases request
      exact False.elim disclosed
  · intro query state disclosed result supported
    rcases query with ((request | request) | request) | request
    · exact False.elim disclosed
    · rw [trOriginal_read, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact PqxdhSelectedPostDisclosure.disclosed_bad request state.1 disclosed
    · exact False.elim disclosed
    · cases request
      exact False.elim disclosed

end Traced

section MarkedFinish
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix PqxdhInitialGenericBeacon
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedInitialOwnerCompiler PqxdhInitialFinishOrigin
variable {ι I D K X Response Shared A N C : Type} {extra : OracleSpec ι}

/-- The key-free compiled Beacon finish with its private installation marker: the marker of the prepared initializer request, recorded only when the finish publishes. -/
noncomputable def ownerMarked (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (raw : Pqxdh.Bytes)
    (before : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    OracleComp (PqxdhSelectedInitialOwnerCompiler.Spec extra I D K X Response Shared)
      (PqxdhInitialFinishOrigin.Result PqxdhSelectedInitialOwnerCompiler.Kernel Bool I D K) :=
  match before.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ preForward
        (PqxdhBeaconPhase2Shared.prepare control before.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (finish control before none, none)
      | some pending => do
          let kernel ← (PqxdhSelectedInitialOwnerCompiler.Spec extra I D K X Response Shared).query (.inl (.inr (.inr (.inl pending.root))))
          match kernel with
          | none => pure (tag (mark pending.root) (finish control before none))
          | some kernel => do
              let application ← (PqxdhSelectedInitialOwnerCompiler.Spec extra I D K X Response Shared).query (.inl (.inr (.inl pending.response)))
              tag (mark pending.root) <$> (PqxdhSelectedInitialOwnerCompiler.Spec extra I D K X Response Shared).query (.inr
                ⟨control, before, PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata,
                  PqxdhSelectedMessageBeacon.knownKernel kernel, application⟩)
  | _ => pure ((none, before), none)

/-- Erasing the marker gives the compiled finish. -/
theorem ownerMarked_erase (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (raw : Pqxdh.Bytes)
    (before : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    Prod.fst <$> ownerMarked (extra := extra) (X := X) (Response := Response) mark raw before =
      PqxdhSelectedInitialOwnerCompiler.owner raw before := by
  unfold ownerMarked PqxdhSelectedInitialOwnerCompiler.owner
  cases before.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [map_bind]
    refine bind_congr fun prepared => ?_
    cases prepared with
    | none => simp only [map_pure]
    | some pending =>
      simp only [map_bind]
      refine bind_congr fun kernel => ?_
      cases kernel with
      | none => simp only [map_pure, tag]
      | some kernel =>
        simp only [map_bind, Functor.map_map, tag, id_map']
  | _ => simp only [map_pure]

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))

/-- The marked compiled finish, interpreted by the selected source, is the marked selected source finish. -/
theorem ownerMarked_source (fixed : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (raw : Pqxdh.Bytes) (before : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    simulateQ (source pre application initial selector aux fixed writer prior parent key target nonce next read) (ownerMarked mark raw before) =
      PqxdhSelectedFirstRecord.selectedFinish pre application initial selector aux fixed writer prior parent key target nonce next read
        mark raw before := by
  unfold ownerMarked PqxdhSelectedFirstRecord.selectedFinish PqxdhInitialFinishOrigin.owner
  cases phase : before.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [simulateQ_bind, ← QueryImpl.simulateQ_compose, preparation_source]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => exact simulateQ_pure _ _
    | some pending =>
      simp only [simulateQ_bind, simulateQ_spec_query, source, tail, bind_map_left, bind_assoc]
      apply bind_congr
      intro kernel
      cases kernel with
      | none => simp only [simulateQ_pure, Option.map_none, pure_bind]
      | some kernel =>
        simp only [Option.map_some, simulateQ_bind, simulateQ_spec_query, source, afterInitial,
          bind_pure_comp, map_bind, simulateQ_map, Functor.map_map]
        rfl
  all_goals exact simulateQ_pure _ _

end MarkedFinish

section StopCoupling

/-- One marked request. -/
theorem marked_run {ι σ : Type} {spec : OracleSpec ι} (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (query : spec.Domain) (state : σ × Bool) :
    (RawCtxSelectedFamilyNonceCoupling.marked handler bad query).run state =
      (fun result => (result.1, (result.2, state.2 || @decide (bad query state.1) (Classical.propDecidable _)))) <$>
        (handler query).run state.1 := by
  simp [RawCtxSelectedFamilyNonceCoupling.marked, StateT.run, map_eq_bind_pure_comp]

/-- An optional client stops at the first missing reply. -/
theorem optionalClient_bind {ι Result : Type} {spec : OracleSpec ι} (query : spec.Domain) (next : spec.Range query → OracleComp spec Result) :
    RawCtxSelectedFamilyNonceCoupling.optionalClient (liftM (spec.query query) >>= next : OracleComp spec Result) =
      (liftM ((RawCtxSelectedFamilyNonceCoupling.Optional spec).query query) : OracleComp _ _) >>= fun reply => match reply with
        | none => pure none
        | some value => RawCtxSelectedFamilyNonceCoupling.optionalClient (next value) := by
  simp only [RawCtxSelectedFamilyNonceCoupling.optionalClient, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind,
    RawCtxSelectedFamilyNonceCoupling.optionalRequests, OptionT.run_mk, Option.elimM]
  refine bind_congr fun reply => ?_
  cases reply <;> rfl

/-- If every flagged step of a handler answers `none`, then a marked optional run started unflagged ends with `none` whenever its flag is raised. -/
theorem marked_flag_none {ι σ Result : Type} {spec : OracleSpec ι}
    (handler : QueryImpl (RawCtxSelectedFamilyNonceCoupling.Optional spec) (StateT σ ProbComp))
    (bad : (RawCtxSelectedFamilyNonceCoupling.Optional spec).Domain → σ → Prop)
    (stopped : ∀ query state, bad query state → ∀ z ∈ support ((handler query).run state), z.1 = none)
    (work : OracleComp spec Result) (state : σ) (result : Option Result × σ × Bool)
    (supported : result ∈ support ((simulateQ (RawCtxSelectedFamilyNonceCoupling.marked handler bad)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (state, false)))
    (flagged : result.2.2 = true) : result.1 = none := by
  classical
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [RawCtxSelectedFamilyNonceCoupling.optionalClient, simulateQ_pure, OptionT.run_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    rw [supported] at flagged
    exact absurd flagged Bool.false_ne_true
  | query_bind query next ih =>
    rw [optionalClient_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, stepSupported, rest⟩ := supported
    simp only [RawCtxSelectedFamilyNonceCoupling.marked, StateT.run, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at stepSupported
    obtain ⟨inner, innerSupported, rfl⟩ := stepSupported
    by_cases hit : bad query state
    · have none := stopped query state hit inner innerSupported
      simp only [none, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
      rw [rest]
    · have clear : (false || decide (bad query state)) = false := by simp [hit]
      rw [clear] at rest
      rcases inner with ⟨_ | value, after⟩
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
        rw [rest]
      · exact ih value after rest

end StopCoupling

section Instrumented
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Instrumentation of the compiled post: the private origin and publication transcript, the hiddenness of the first send of the target Beacon, and a flag raised when a Beacon finish makes a selected raw opening. -/
abbrev InsExtra (S B : Nat) := PqxdhInitialOriginPost.Trace Bool S B × Option Bool × Bool

/-- Compiled post state with its instrumentation. -/
abbrev InsState (M P I D K A N C : Type) (S B : Nat) := PqxdhSelectedPostCompiler.State M P I D K A N C S B × InsExtra S B

/-- Instrumented compiled post state together with the selected-key challenger state. -/
abbrev InsFull (M P I D K A N C : Type) (S B : Nat) := InsState M P I D K A N C S B × AdaptiveCtxDynamicKnownKeys.SourceState

/-- The current send of a Beacon would derive the selected hidden material: its sending chain is the selected chain's request address. -/
def HiddenBeacon (target : RootOutput) (beacon : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) : Prop :=
  match beacon.beacon.phase with
  | .established _ _ kernel => RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target
  | _ => False

/-- The instrumented events and predicates are decided classically. -/
noncomputable instance (target : RootOutput) (beacon : PqxdhSelectedInitialOwnerCompiler.Beacon I D K) :
    Decidable (HiddenBeacon target beacon) := Classical.propDecidable _

/-- The first send request of Beacon `b` records whether that Beacon's send would use the selected hidden material. -/
noncomputable def hiddenStep (b : Fin B) (target : RootOutput) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (hidden : Option Bool) : Option Bool :=
  match hidden, request with
  | some value, _ => some value
  | none, .inl (.inr (.inl ⟨index, .inl _⟩)) => if index = b then some (decide (HiddenBeacon target (front.roles.1.2 b))) else none
  | none, _ => none

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (b : Fin B)

/-- The instrumented key-free compiled post interpreter: the compiled post (`PqxdhSelectedPostCompiler.impl`) with the marked finish wrapped by `markRaw`, recording the transcript, the first-send monitor and the finish raw flag. -/
noncomputable def insImpl :
    QueryImpl (PqxdhInitialGenericPost.Spec extra S B)
      (OptionT (StateT (InsState M P I D K A N C S B) (OracleComp AdaptiveCtxDynamicKnownKeys.Spec))) :=
  fun query => OptionT.mk fun before => match query with
  | .inl (.inl request) =>
      (fun result => (result.1, (({ before.1.1 with roles := result.2 }, before.1.2),
        (traceRecord before.2.1 request result.1, hiddenStep b target request before.1.1 before.2.2.1, before.2.2.2)))) <$>
        (((RawCtxSelectedFamilyLiveCompiler.impl source writer prior parent target nonce next sender route read request).run).run
          before.1.1.roles)
  | .inl (.inr request) =>
      (fun result => (some result.1, ((before.1.1, result.2), before.2))) <$>
        ((PqxdhSelectedCallbackCompiler.lower pre application initial selector aux
          (.inl (.inr (.inr (.inr (.inl request)))))).run before.1.2)
  | .inr (.finish index raw) =>
      (fun result => (some result.1.1.1.1, ((PqxdhSelectedPostCompiler.install index before.1.1 result.1.1.1.2, result.1.2),
        (PqxdhInitialOriginPost.finish before.2.1 index result.1.1.2, before.2.2.1, result.2)))) <$>
        (simulateQ markRaw ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target
          nonce next read) (ownerMarked mark raw (before.1.1.roles.1.2 index))).run before.1.2)).run before.2.2.2

/-- Evaluating a `markRaw`-wrapped program and dropping the flag evaluates the program. -/
theorem markRaw_evaluate {σ Result : Type} (impl : QueryImpl AdaptiveCtxDynamicKnownKeys.Spec (StateT σ ProbComp))
    (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result) (flag : Bool) (state : σ) :
    Prod.map Prod.fst id <$> (simulateQ impl ((simulateQ markRaw work).run flag)).run state = (simulateQ impl work).run state := by
  have erased := congrArg (fun program => (simulateQ impl program).run state) (markRaw_erase work flag)
  simp only [simulateQ_map, StateT.run_map] at erased
  rw [← erased]
  rfl

/-- The instrumented compiled post evaluated by the selected-key challenger. -/
noncomputable def insEvaluated :
    QueryImpl (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B))
      (StateT (InsFull M P I D K A N C S B) ProbComp) :=
  fun query => PqxdhSelectedStateInterpreter.evaluate
    (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
    ((insImpl pre application initial selector aux source writer prior parent target nonce next sender route read mark b query).run)

/-- The instrumented augmented post: record requests use the nonce-refusal ledger of `RawCtxSelectedFamilyNonceCoupling.augmented`, every other request is evaluated. -/
noncomputable def insAugmented :
    QueryImpl (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B))
      (StateT (InsFull M P I D K A N C S B) ProbComp) :=
  fun query before => match query with
  | .inl (.inl request) =>
      (fun result => (result.1, ((({ before.1.1.1 with roles := result.2.1 }, result.2.2.1),
        (traceRecord before.1.2.1 request result.1, hiddenStep b target request before.1.1.1 before.1.2.2.1, before.1.2.2.2)),
          result.2.2.2))) <$>
        (RawCtxSelectedFamilyNonceCoupling.augmented source writer prior parent key target nonce next sender route read request).run
          (before.1.1.1.roles, (before.1.1.2, before.2))
  | query => (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender route read mark b
      query).run before

/-- The traced source state of an instrumented full state: front, local state with the challenger's cache, and transcript. -/
def insProject (state : InsFull M P I D K A N C S B) : Traced M P I D K A N C S B :=
  ((state.1.1.1, (state.1.1.2, state.2.cache)), state.1.2.1)

/-- The instrumented augmented post projects to the traced stopped source for every request and every state. -/
theorem insAugmented_step (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : InsFull M P I D K A N C S B) :
    Prod.map id insProject <$> (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender
      route read mark b query).run before =
      (trOriginal pre application initial selector aux source writer prior parent key target nonce next sender route read mark query).run
        (insProject before) := by
  rcases query with (request | request) | request
  · have actual := RawCtxSelectedFamilyNonceCoupling.augmented_step source writer prior parent key target nonce next sender route read request
      (before.1.1.1.roles, (before.1.1.2, before.2))
    have mapped := congrArg (fun work => (fun result => (result.1, (({ before.1.1.1 with roles := result.2.1 }, result.2.2),
      traceRecord before.1.2.1 request result.1))) <$> work) actual
    simpa only [insAugmented, trOriginal, insProject, StateT.run, Functor.map_map, Prod.map_def, id_eq,
      RawCtxSelectedFamilyNonceCoupling.project, RawCtxSelectedReceiveCompiler.project] using mapped
  · have actual := PqxdhSelectedInitialOwnerCompiler.external_project pre application initial selector aux source key read
      (.inr (.inr (.inr (.inl request)))) (before.1.1.2, before.2)
    have mapped := congrArg (fun work => (fun result => (some result.1, ((before.1.1.1, result.2), before.1.2.1))) <$> work) actual
    convert mapped using 1 <;> simp only [insAugmented, insEvaluated, insImpl, trOriginal, insProject, OptionT.run_mk, StateT.run,
      PqxdhSelectedFirstRecord.state_map_apply, PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair, simulateQ_map, Functor.map_map,
      Prod.map_def, id_eq, RawCtxSelectedReceiveCompiler.project]
    rfl
  · cases request with
    | finish index raw =>
      have program := PqxdhSelectedInitialOwnerCompiler.program_source pre application initial selector aux source writer prior parent key target
        nonce next read (ownerMarked mark raw (before.1.1.1.roles.1.2 index)) (before.1.1.2, before.2)
      rw [ownerMarked_source] at program
      have flagged := markRaw_evaluate (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read)
          (ownerMarked mark raw (before.1.1.1.roles.1.2 index))).run before.1.1.2) before.1.2.2.2 before.2
      simp only [PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair, StateT.run, Functor.map_map,
        RawCtxSelectedReceiveCompiler.project] at program
      simp only [StateT.run] at flagged
      simp only [insAugmented, insEvaluated, insImpl, trOriginal, insProject, OptionT.run_mk, StateT.run,
        PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair, simulateQ_map, Functor.map_map, PqxdhSelectedFirstRecord.state_map_apply]
      rw [← program, ← flagged]
      simp only [Functor.map_map]
      rfl

/-- The selected-nonce stop predicate on instrumented full states. -/
noncomputable def insStops (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (state : InsFull M P I D K A N C S B) : Prop :=
  PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender query (state.1.1, state.2)

/-- Before a selected-nonce stop, the instrumented augmented and evaluated posts coincide. -/
theorem insAugmented_nonstop (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : InsFull M P I D K A N C S B)
    (clear : ¬ insStops (extra := extra) prior parent target nonce next sender query before) :
    (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b query).run before =
      (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender route read mark b query).run
        before := by
  rcases query with (request | request) | request
  · have actual := RawCtxSelectedFamilyNonceCoupling.augmented_nonstop source writer prior parent key target nonce next sender route read
      request (before.1.1.1.roles, (before.1.1.2, before.2)) clear
    have mapped := congrArg (fun work => (fun result => (result.1, ((({ before.1.1.1 with roles := result.2.1 }, result.2.2.1),
      (traceRecord before.1.2.1 request result.1, hiddenStep b target request before.1.1.1 before.1.2.2.1, before.1.2.2.2)),
        result.2.2.2))) <$> work) actual
    simpa only [insAugmented, insEvaluated, insImpl, OptionT.run_mk, StateT.run, PqxdhSelectedFirstRecord.state_map_apply,
      PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair,
      simulateQ_map, Functor.map_map, RawCtxSelectedFamilyNonceCoupling.compiled,
      RawCtxSelectedReceiveCompiler.evaluated] using mapped
  · rfl
  · cases request; rfl

/-- Evaluating the instrumented compiled post client is its instrumented evaluated interpretation over optional replies. -/
theorem insEvaluated_program {Result : Type} (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) :
    PqxdhSelectedStateInterpreter.evaluate
      (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
      (simulateQ (insImpl (P := P) pre application initial selector aux source writer prior parent target nonce next sender route read mark b)
        work).run =
      simulateQ (insEvaluated (P := P) pre application initial selector aux source writer prior parent key target nonce next sender route read
        mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work) := by
  rw [← RawCtxSelectedFamilyNonceCoupling.optional_client
    (insImpl (P := P) pre application initial selector aux source writer prior parent target nonce next sender route read mark b) work]
  exact PqxdhSelectedStateInterpreter.program _ _ _

/-- At a selected-nonce stop, the evaluated instrumented step answers `none`. -/
theorem insEvaluated_stop (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : InsFull M P I D K A N C S B) (stops : insStops (extra := extra) prior parent target nonce next sender query before)
    (result : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Range query × InsFull M P I D K A N C S B)
    (supported : result ∈ support ((insEvaluated pre application initial selector aux source writer prior parent key target nonce next
      sender route read mark b query).run before)) : result.1 = none := by
  rcases query with (request | request) | request
  · have actual := RawCtxSelectedFamilyLiveCompiler.step_source source writer prior parent key target nonce next sender route read request
      before.1.1.1.roles (before.1.1.2, before.2)
    have hit : RawCtxSelectedFamilyLiveCompiler.Stops prior parent target nonce next sender request before.1.1.1.roles before.2 := stops
    rw [ite_eq_left_of_eq_true _ _ (eq_true hit)] at actual
    simp only [insEvaluated, insImpl, PqxdhSelectedStateInterpreter.evaluate, PqxdhSelectedStateInterpreter.pair, OptionT.run_mk,
      StateT.run, simulateQ_map, PqxdhSelectedFirstRecord.state_map_apply, Functor.map_map, support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    have mem : (inner.1.1, (inner.1.2, RawCtxSelectedReceiveCompiler.project ((before.1.1.2, inner.2) :
        RawCtxSelectedReceiveCompiler.State (Local A N C)))) ∈ support
        (RawCtxSelectedFamilyLiveCompiler.output <$> (RawCtxSelectedReceiveCompiler.evaluated source key read
          (((RawCtxSelectedFamilyLiveCompiler.impl source writer prior parent target nonce next sender route read request).run).run
            before.1.1.1.roles)).run (before.1.1.2, before.2)) := by
      simp only [RawCtxSelectedReceiveCompiler.evaluated, StateT.run, Functor.map_map, support_map, Set.mem_image]
      exact ⟨inner, innerSupported, rfl⟩
    rw [actual, support_pure, Set.mem_singleton_iff] at mem
    exact congrArg Prod.fst mem
  · exact False.elim stops
  · cases request
    exact False.elim stops

/-- Erasing the instrumentation of an instrumented full state. -/
def insErase (state : InsFull M P I D K A N C S B) : PqxdhSelectedPostCompiler.Full M P I D K A N C S B := (state.1.1, state.2)

/-- The instrumented compiled post erases to the compiled post: same requests, replies and compiled state. -/
theorem insImpl_erase (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : InsState M P I D K A N C S B) :
    Prod.map id Prod.fst <$> ((insImpl pre application initial selector aux source writer prior parent target nonce next sender route read
      mark b query).run).run before =
      ((PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent target nonce next sender route read
        query).run).run before.1 := by
  rcases query with (request | request) | request
  · simp only [insImpl, PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, Functor.map_map]
    rfl
  · simp only [insImpl, PqxdhSelectedPostCompiler.impl, OptionT.run_mk, StateT.run, Functor.map_map]
    rfl
  · cases request with
    | finish index raw =>
      have erased := markRaw_erase ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent
        target nonce next read) (ownerMarked mark raw (before.1.1.roles.1.2 index))).run before.1.2) before.2.2.2
      have owner : (simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read)
          (PqxdhSelectedInitialOwnerCompiler.owner raw (before.1.1.roles.1.2 index))).run before.1.2 =
          (fun z => (z.1.1, z.2)) <$> (simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent
            target nonce next read) (ownerMarked mark raw (before.1.1.roles.1.2 index))).run before.1.2 := by
        rw [← ownerMarked_erase (extra := extra) (X := X) (Response := Response) mark raw (before.1.1.roles.1.2 index), simulateQ_map,
          StateT.run_map]
      change _ <$> (_ <$> (simulateQ markRaw ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior
          parent target nonce next read) (ownerMarked mark raw (before.1.1.roles.1.2 index))).run before.1.2)).run before.2.2.2) =
        _ <$> (simulateQ (PqxdhSelectedInitialOwnerCompiler.lower pre application initial selector aux prior parent target nonce next read)
          (PqxdhSelectedInitialOwnerCompiler.owner raw (before.1.1.roles.1.2 index))).run before.1.2
      rw [owner]
      conv_rhs => rw [← erased]
      simp only [Functor.map_map]
      rfl

/-- The instrumented evaluated post erases to the evaluated post of `PqxdhSelectedPostCompiler`. -/
theorem insEvaluated_erase (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : InsFull M P I D K A N C S B) :
    Prod.map id insErase <$> (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender
      route read mark b query).run before =
      (PqxdhSelectedPostCompiler.evaluated pre application initial selector aux source writer prior parent key target nonce next sender
        route read query).run (insErase before) := by
  have erased := insImpl_erase pre application initial selector aux source writer prior parent target nonce next sender route read mark b
    query before.1
  change Prod.map id insErase <$> (PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (((insImpl pre application initial selector aux source writer prior parent target nonce next sender route read mark b query).run).run
          before.1)).run before.2) =
    PqxdhSelectedStateInterpreter.pair <$>
      (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder read) source.crypto key)
        (((PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent target nonce next sender route read
          query).run).run before.1.1)).run before.2
  rw [← erased, simulateQ_map, StateT.run_map, Functor.map_map, Functor.map_map]
  rfl

/-- The instrumented augmented post erases to the augmented post of `PqxdhSelectedPostCompiler`. -/
theorem insAugmented_erase (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
    (before : InsFull M P I D K A N C S B) :
    Prod.map id insErase <$> (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender
      route read mark b query).run before =
      (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next sender
        route read query).run (insErase before) := by
  rcases query with (request | request) | request
  · simp only [insAugmented, PqxdhSelectedPostCompiler.augmented, insErase, StateT.run, Functor.map_map, Prod.map_def, id_eq]
  · exact insEvaluated_erase pre application initial selector aux source writer prior parent key target nonce next sender route read mark b
      (.inl (.inr request)) before
  · exact insEvaluated_erase pre application initial selector aux source writer prior parent key target nonce next sender route read mark b
      (.inr request) before

/-- Every instrumented post request makes at most one request of any class that the source-local callbacks never use. -/
theorem insPost_step (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ query state, ((PqxdhSelectedCallbackCompiler.lower (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := Shared) pre application initial selector aux (.inl query)).run state).IsQueryBoundP predicate 0)
    (query : (PqxdhInitialGenericPost.Spec extra S B).Domain) (before : InsState M P I D K A N C S B) :
    (((insImpl pre application initial selector aux source writer prior parent target nonce next sender route read mark b
      query).run).run before).IsQueryBoundP predicate 1 := by
  have bound := PqxdhFirstBeaconRecordCtx.post_step pre application initial selector aux source writer prior parent target nonce next
    sender route read predicate externalZero query before.1
  rw [← insImpl_erase pre application initial selector aux source writer prior parent target nonce next sender route read mark b query
    before] at bound
  exact (isQueryBoundP_map_iff _ _ _).mp bound

/-- The instrumented post client makes at most `qPost` requests of any class used at most once per post request. -/
theorem insPost_client (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (step : ∀ query (before : InsState M P I D K A N C S B),
      (((insImpl (extra := extra) pre application initial selector aux source writer prior parent target nonce next sender route read
        mark b query).run).run before).IsQueryBoundP predicate 1)
    {Result : Type} (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result) (qPost : Nat)
    (bounded : work.IsTotalQueryBound qPost) (before : InsState M P I D K A N C S B) :
    (((simulateQ (insImpl pre application initial selector aux source writer prior parent target nonce next sender route read mark b)
      work).run).run before).IsQueryBoundP predicate qPost := by
  induction work using OracleComp.inductionOn generalizing qPost before with
  | pure value => trivial
  | query_bind query continuation ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt bounded.1)
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    rw [Nat.succ_eq_add_one, Nat.add_comm]
    apply isQueryBoundP_bind (step query before)
    rintro ⟨none | answer, after⟩ _
    · trivial
    · exact ih answer remaining (by simpa using bounded.2 answer) after

end Instrumented


section PostChain
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedFirstRecord
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (b : Fin B)

/-- From any instrumented start, the traced ordinary source post and the instrumented augmented post give the same probability to every transcript event conjoined with the absence of hidden disclosure. -/
theorem post_source_augmented (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (start : InsFull M P I D K A N C S B) (event : Option Bool × Traced M P I D K A N C S B → Prop) :
    Pr{let result ← ((simulateQ (traced pre application initial selector aux source writer prior parent key target nonce next sender route read mark)
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (insProject start))}[event result ∧ PqxdhSelectedPostDisclosure.Good result.2.1] =
      Pr{let result ← ((simulateQ (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read
          mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run start)}[event (result.1, insProject result.2) ∧ PqxdhSelectedPostDisclosure.Good (insProject result.2).1] := by
  rw [traced_event_good]
  have projected := map_run_simulateQ_eq_of_query_map_eq
    (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
    (trOriginal pre application initial selector aux source writer prior parent key target nonce next sender route read mark)
    insProject (insAugmented_step pre application initial selector aux source writer prior parent key target nonce next sender route read
      mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work) start
  rw [← projected, prEvent_map]
  rfl

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.post_source_augmented_vcvioLegacy :
    ∀ {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : ℕ} (pre : QueryImpl (BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp)) (application : Response → BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.LocalCallback A N C (Option Pqxdh.Bytes)) (initial : BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Secrets Shared → BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.LocalCallback A N C BeaconcryptCore.Computational.PqxdhInitialNativeAudit.InitialReply) (selector : QueryImpl extra (StateT (BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp)) (aux : QueryImpl BeaconcryptCore.Computational.PqxdhServerRegistrationPublication.AuxSpec (StateT (BeaconcryptCore.Computational.PqxdhNativeSharedPrefix.ExternalState A N C) ProbComp)) (source : BeaconcryptCore.Computational.PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : BeaconcryptCore.Computational.RawCtxMixedShared.Writer) (prior : BeaconcryptCore.Computational.RawCtxSelectedParentTable.Prior) (parent : Option BeaconcryptCore.Computational.RawCtxSelectedParentEntry.Entry) (key target : BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput) (nonce : BeaconcryptCore.Computational.PqxdhFullSecretInputKdf.NonceOutput) (next : BeaconcryptCore.Computational.PqxdhSecretInputKdf.RootOutput) (sender : M → Aeneas.Std.U64) (route : BeaconcryptCore.Computational.RawCtxServerRouting.SenderDecoder) (read : BeaconcryptCore.Computational.RawCtxReceive.FrameDecoder) (mark : BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (b : Fin B) (work : OracleComp (BeaconcryptCore.Computational.PqxdhInitialGenericPost.Spec extra S B) Bool) (start : BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.InsFull M P I D K A N C S B) (event : Option Bool × BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.Traced M P I D K A N C S B → Prop), (probEvent ((simulateQ (BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.traced pre application initial selector aux source writer prior parent key target nonce next sender route read mark) (BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insProject start)) fun (result : Option Bool × BeaconcryptCore.Computational.PqxdhSelectedFirstRecord.Traced M P I D K A N C S B) => event result ∧ BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.Good result.2.1) = probEvent ((simulateQ (BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b) (BeaconcryptCore.Computational.RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run start) fun (result : Option Bool × BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.InsFull M P I D K A N C S B) => event (result.1, BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insProject result.2) ∧ BeaconcryptCore.Computational.PqxdhSelectedPostDisclosure.Good (BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insProject result.2).1 :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.post_source_augmented

/-- Unflagged: the instrumented augmented post exceeds the instrumented evaluated post on an event by at most the flagged event mass of the augmented run. -/
theorem augmented_le_evaluated (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (start : InsFull M P I D K A N C S B) (event : Option Bool × InsFull M P I D K A N C S B → Bool) :
    𝒟[event <$> (simulateQ (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route
        read mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run start] {true} ≤
      𝒟[event <$> (simulateQ (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender route
        read mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run start] {true} +
      𝒟[(fun result => result.2.2 && event (result.1, result.2.1)) <$>
        (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
          (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
          (insStops (extra := extra) prior parent target nonce next sender))
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (start, false)] {true} := by
  have bound := PqxdhFirstBeaconRecordIntegrity.restricted_le
    (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
    (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
    (insStops (extra := extra) prior parent target nonce next sender)
    (insAugmented_nonstop pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
    (RawCtxSelectedFamilyNonceCoupling.optionalClient work) start event
  rw [← RawCtxSelectedFamilyNonceCoupling.marked_client _ (insStops (extra := extra) prior parent target nonce next sender)
      _ (start, false),
    ← RawCtxSelectedFamilyNonceCoupling.marked_client _ (insStops (extra := extra) prior parent target nonce next sender)
      _ (start, false), Functor.map_map, Functor.map_map]
  exact bound

/-- The instrumented evaluated post never exceeds the instrumented augmented post on an event that requires a `true` result: a flagged evaluated run has stopped. -/
theorem evaluated_le_augmented (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (start : InsFull M P I D K A N C S B) (event : Option Bool × InsFull M P I D K A N C S B → Bool)
    (returned : ∀ result, event result = true → result.1 = some true) :
    𝒟[event <$> (simulateQ (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender route
        read mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run start] {true} ≤
      𝒟[event <$> (simulateQ (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route
        read mark b) (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run start] {true} := by
  have bound := PqxdhFirstBeaconRecordIntegrity.restricted_le
    (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
    (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
    (insStops (extra := extra) prior parent target nonce next sender)
    (fun query state clear => (insAugmented_nonstop pre application initial selector aux source writer prior parent key target nonce next
      sender route read mark b query state clear).symm)
    (RawCtxSelectedFamilyNonceCoupling.optionalClient work) start event
  have zero : 𝒟[(fun result => result.2.2 && event (result.1, result.2.1)) <$>
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
        (insEvaluated pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
        (insStops (extra := extra) prior parent target nonce next sender))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (start, false)] {true} = 0 := by
    rw [← prEvent_eq_evalDist_singleton _ true]
    refine prEvent_eq_zero_of_not_mem_support _ fun supported => ?_
    rw [support_map, Set.mem_image] at supported
    obtain ⟨result, reached, hit⟩ := supported
    rw [Bool.and_eq_true] at hit
    have stopped := marked_flag_none _ _ (insEvaluated_stop pre application initial selector aux source writer prior parent key target nonce
      next sender route read mark b) work start result reached hit.1
    have some := returned _ hit.2
    rw [stopped] at some
    cases some
  rw [zero, add_zero] at bound
  rw [← RawCtxSelectedFamilyNonceCoupling.marked_client _ (insStops (extra := extra) prior parent target nonce next sender)
      _ (start, false),
    ← RawCtxSelectedFamilyNonceCoupling.marked_client _ (insStops (extra := extra) prior parent target nonce next sender)
      _ (start, false), Functor.map_map, Functor.map_map]
  exact bound

/-- The flagged event mass of the instrumented augmented run is at most the flagged mass of the undisclosure event in the augmented run of `PqxdhSelectedPostCompiler` from the erased start. -/
theorem flagged_le_stop (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (start : InsFull M P I D K A N C S B) (event : Option Bool × InsFull M P I D K A N C S B → Bool)
    (undisclosed : PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B → Bool)
    (implies : ∀ result, event result = true → undisclosed (PqxdhSelectedPostCompiler.project (insErase result.2)) = true) :
    𝒟[(fun result => result.2.2 && event (result.1, result.2.1)) <$>
        (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
          (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
          (insStops (extra := extra) prior parent target nonce next sender))
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (start, false)] {true} ≤
      𝒟[(fun result => result.2.2 && undisclosed (PqxdhSelectedPostCompiler.project result.2.1)) <$>
        (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
          (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next sender
            route read)
          (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender))
          (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (insErase start, false)] {true} := by
  have step : ∀ (query : (PqxdhSelectedPostCompiler.Optional (PqxdhInitialGenericPost.Spec extra S B)).Domain)
      (state : InsFull M P I D K A N C S B × Bool),
      Prod.map id (Prod.map insErase id) <$> (RawCtxSelectedFamilyNonceCoupling.marked
        (insAugmented pre application initial selector aux source writer prior parent key target nonce next sender route read mark b)
        (insStops (extra := extra) prior parent target nonce next sender) query).run state =
      (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next sender
          route read)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender) query).run (Prod.map insErase id state) := by
    intro query state
    have erased := insAugmented_erase pre application initial selector aux source writer prior parent key target nonce next sender route
      read mark b query state.1
    rw [marked_run, marked_run]
    simp only [Prod.map_fst, Prod.map_snd, id_eq]
    rw [← erased, Functor.map_map, Functor.map_map]
    rfl
  have projected := map_run_simulateQ_eq_of_query_map_eq _ _ (Prod.map insErase id) step
    (RawCtxSelectedFamilyNonceCoupling.optionalClient work) (start, false)
  rw [← show Prod.map insErase id (start, false) = (insErase start, false) from rfl, ← projected, Functor.map_map]
  refine PqxdhFirstBeaconRecordIntegrity.map_mono _ _ _ fun result holds => ?_
  rw [Bool.and_eq_true] at holds
  simp only [Bool.and_eq_true]
  exact ⟨holds.1, implies _ holds.2⟩

end PostChain

/-- The `true` mass of a decided event is the event's probability. -/
theorem true_mass_eq {α : Type} (mx : ProbComp α) (p : α → Prop) [DecidablePred p] :
    𝒟[(fun x => decide (p x)) <$> mx] {true} = Pr{let x ← mx}[p x] := by
  rw [← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  exact prEvent_congr _ _ _ fun _ => decide_eq_true_iff

set_option linter.deprecated false in theorem _root_.BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.true_mass_eq_vcvioLegacy :
    ∀ {α : Type} (mx : ProbComp α) (p : α → Prop) [DecidablePred p], 𝒟[(fun (x : α) => Decidable.decide (p x)) <$> mx] {Bool.true} = probEvent mx p :=
  by simpa only [BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent] using @BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.true_mass_eq

/-- One event dominated pointwise by the disjunction of two events has at most their added masses. -/
theorem map_le_add {α : Type} (mx : ProbComp α) (f g h : α → Bool) (split : ∀ a, f a = true → g a = true ∨ h a = true) :
    𝒟[f <$> mx] {true} ≤ 𝒟[g <$> mx] {true} + 𝒟[h <$> mx] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true]
  simp only [prEvent_map]
  calc Pr{let x ← mx}[f x = true] ≤ Pr{let x ← mx}[g x = true ∨ h x = true] :=
        prEvent_mono _ _ _ fun a holds => split a holds
    _ ≤ Pr{let x ← mx}[g x = true] + Pr{let x ← mx}[h x = true] := prEvent_or_le _ _ _

section First
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

local notation "target" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected

/-- The instrumented post start after the selected builder: front and local state, the transcript entry of the first Server response, no first-send record, no finish raw attempt, and the CTX challenger state carrying the builder's hash cache. -/
def insStart (built : Built M P I D K A N S B) : InsFull M P I D K A N RootOracle.QueryCache S B :=
  (((built.1.2, built.2.1), (selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1, none, false)),
    { AdaptiveCtxDynamicKnownKeys.initialSource with cache := built.2.2 })

/-- The first-record transcript event: the post returned `true`, the selected owner published its record `number` with the selected origin, and the selected chain and ancestors are undisclosed. -/
def FirstEvent (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × Traced M P I D K A N RootOracle.QueryCache S B) : Prop :=
  result.1 = some true ∧ ((selected, number), true) ∈ result.2.2.published ∧
    Undisclosed target ancestors disclosed result.2.1

/-- The same event on an instrumented full state, together with the absence of hidden disclosure; it reads only the front and the transcript. -/
def InsEvent (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × InsFull M P I D K A N RootOracle.QueryCache S B) : Prop :=
  FirstEvent source previousRoot response64 selected number ancestors disclosed (result.1, insProject result.2) ∧
    PqxdhSelectedPostDisclosure.Good (insProject result.2).1

/-- The instrumented events and predicates are decided classically. -/
noncomputable instance (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × InsFull M P I D K A N RootOracle.QueryCache S B) :
    Decidable (InsEvent source previousRoot response64 selected number ancestors disclosed result) := Classical.propDecidable _

/-- The instrumented events and predicates are decided classically. -/
noncomputable instance (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × Traced M P I D K A N RootOracle.QueryCache S B) :
    Decidable (FirstEvent source previousRoot response64 selected number ancestors disclosed result) := Classical.propDecidable _

/-- The instrumented events and predicates are decided classically. -/
scoped instance goodDecidable (state : PqxdhSelectedPostCompiler.SourceState M P I D K A N RootOracle.QueryCache S B) :
    Decidable (PqxdhSelectedPostDisclosure.Good state) :=
  inferInstanceAs (Decidable (RawCtxSelectedMessageFreshness.hidden state.1.roles.2 = false))

/-- The instrumented compiled first-record run: the selected builder, then the instrumented evaluated post; the event is `InsEvent`. -/
noncomputable def insCompiledRun (number : Std.U64) (ancestors disclosed : List RatchetChain) : ProbComp Bool := do
  let built ← firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
    before selected shared privateState cache store key nonce next
  (fun result => decide (InsEvent source previousRoot response64 selected number ancestors disclosed result)) <$>
    (simulateQ (insEvaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
      sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insStart index built)

/-- The key-disclosure run: the selected first-record run in which the transcript event and the absence of hidden disclosure hold but the selected message key is among the disclosed values. -/
noncomputable def keyRun (number : Std.U64) (ancestors disclosed : List RatchetChain) : ProbComp Bool :=
  (fun result => @decide (FirstEvent source previousRoot response64 selected number ancestors disclosed result ∧
      PqxdhSelectedPostDisclosure.Good result.2.1 ∧
      RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2)
    (Classical.propDecidable _)) <$>
    firstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
      index metadata ready post before selected shared privateState cache store key nonce next

/-- Per selected builder result: the traced source event is dominated by the instrumented evaluated event plus the restricted stop integrand of `PqxdhFirstBeaconRecordIntegrity.stopRun`. -/
theorem built_upper (number : Std.U64) (ancestors disclosed : List RatchetChain) (built : Built M P I D K A N S B) :
    𝒟[(fun result => decide (FirstEvent source previousRoot response64 selected number ancestors disclosed result ∧
        PqxdhSelectedPostDisclosure.Good result.2.1)) <$>
      (simulateQ (traced pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run
        ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1)] {true} ≤
    𝒟[(fun result => decide (InsEvent source previousRoot response64 selected number ancestors disclosed result)) <$>
      (simulateQ (insEvaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insStart index built)] {true} +
    𝒟[(fun result => result.2.2 && decide (Undisclosed target ancestors disclosed (PqxdhSelectedPostCompiler.project result.2.1))) <$>
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer (productionStream source.crypto) none key
          target nonce next sender route decode)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) (productionStream source.crypto) none target nonce next sender))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (startOf built, false)] {true} := by
  have same := post_source_augmented pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    (FirstEvent source previousRoot response64 selected number ancestors disclosed)
  rw [true_mass_eq]
  rw [show ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1) =
    insProject (insStart index built) from rfl, same]
  refine le_of_eq_of_le (prEvent_congr _ _ (InsEvent source previousRoot response64 selected number ancestors disclosed)
    fun _ => Iff.rfl) ?_
  rw [← true_mass_eq]
  refine (augmented_le_evaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce
    next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    (fun result => decide (InsEvent source previousRoot response64 selected number ancestors disclosed result))).trans ?_
  refine add_le_add le_rfl ?_
  exact flagged_le_stop pre application initial selector aux source writer (productionStream source.crypto) none key target nonce
    next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    (fun result => decide (InsEvent source previousRoot response64 selected number ancestors disclosed result))
    (fun state => decide (Undisclosed target ancestors disclosed state)) (fun result holds => by
      rw [decide_eq_true_iff] at holds ⊢
      exact holds.1.2.2)

/-- Per selected builder result: the instrumented evaluated event never exceeds the traced source event. -/
theorem built_lower (number : Std.U64) (ancestors disclosed : List RatchetChain) (built : Built M P I D K A N S B) :
    𝒟[(fun result => decide (InsEvent source previousRoot response64 selected number ancestors disclosed result)) <$>
      (simulateQ (insEvaluated pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (insStart index built)] {true} ≤
    𝒟[(fun result => decide (FirstEvent source previousRoot response64 selected number ancestors disclosed result ∧
        PqxdhSelectedPostDisclosure.Good result.2.1)) <$>
      (simulateQ (traced pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
        sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run
        ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1)] {true} := by
  refine (evaluated_le_augmented pre application initial selector aux source writer (productionStream source.crypto) none key target nonce
    next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    (fun result => decide (InsEvent source previousRoot response64 selected number ancestors disclosed result))
    (fun result holds => (decide_eq_true_iff.mp holds).1.1)).trans (le_of_eq ?_)
  have same := post_source_augmented pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (post built.1.1) (insStart index built)
    (FirstEvent source previousRoot response64 selected number ancestors disclosed)
  rw [true_mass_eq, true_mass_eq]
  exact same.symm

/-- The selected first-record run is the selected builder followed by the traced post, as a bind over `firstBuild`. -/
theorem firstRun_bind {α : Type} (f : Option Bool × Traced M P I D K A N RootOracle.QueryCache S B → α) :
    f <$> firstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
      index metadata ready post before selected shared privateState cache store key nonce next =
      firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
        before selected shared privateState cache store key nonce next >>= fun built => f <$>
          (simulateQ (traced pre application initial selector aux source writer (productionStream source.crypto) none key target nonce next
            sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage))
            (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run
            ((built.1.2, built.2), selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1) := by
  simp only [firstRun, selectedRun, firstBuild, map_bind]

/-- The first randomized source decision is dominated by the instrumented compiled run plus the restricted stop run. -/
theorem first_upper (number : Std.U64) (position : number.val = 1) (ancestors disclosed : List RatchetChain) :
    𝒟[(fun result => PqxdhInitialSourceRandom.decision source previousRoot response64 selected
        (RawCtxSelectedMessageKdf.response key nonce next) number ancestors disclosed (nativeView key result)) <$>
      firstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
        index metadata ready post before selected shared privateState cache store key nonce next] {true} ≤
    𝒟[insCompiledRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed] {true} +
    𝒟[stopRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store key nonce next ancestors disclosed] {true} := by
  refine (PqxdhFirstBeaconRecordIntegrity.map_mono _ _ (fun result => decide (FirstEvent source previousRoot response64 selected number
    ancestors disclosed result ∧ PqxdhSelectedPostDisclosure.Good result.2.1)) ?_).trans ?_
  · intro result holds
    have characterized := (first_selected_decision source previousRoot response64 selected key nonce next number position
      ancestors disclosed result).mp holds
    rw [decide_eq_true_iff]
    exact ⟨⟨characterized.1.1, characterized.1.2, characterized.2.2.1⟩, characterized.2.1⟩
  · rw [firstRun_bind]
    exact PqxdhFirstBeaconRecordIntegrity.true_bind_le _ _ _ _ fun built =>
      built_upper pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
        post selected key nonce next b number ancestors disclosed built

/-- The instrumented compiled run is dominated by the first randomized source decision plus the key-disclosure run. -/
theorem first_lower (number : Std.U64) (position : number.val = 1) (ancestors disclosed : List RatchetChain) :
    𝒟[insCompiledRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed] {true} ≤
    𝒟[(fun result => PqxdhInitialSourceRandom.decision source previousRoot response64 selected
        (RawCtxSelectedMessageKdf.response key nonce next) number ancestors disclosed (nativeView key result)) <$>
      firstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
        index metadata ready post before selected shared privateState cache store key nonce next] {true} +
    𝒟[keyRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next number ancestors disclosed] {true} := by
  refine le_trans ?_ (map_le_add _ (fun result => decide (FirstEvent source previousRoot response64 selected number ancestors disclosed
    result ∧ PqxdhSelectedPostDisclosure.Good result.2.1)) _ _ ?_)
  · unfold insCompiledRun
    rw [firstRun_bind]
    exact PqxdhFirstBeaconRecordCtx.true_bind_mono _ _ _ fun built =>
      built_lower pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
        post selected key nonce next b number ancestors disclosed built
  · intro result holds
    rw [decide_eq_true_iff] at holds
    by_cases known : RawCtxFreshChainCut.concreteChain key ∈ RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2
    · exact Or.inr (by simp only [decide_eq_true_iff]; exact ⟨holds.1, holds.2, known⟩)
    · refine Or.inl ((first_selected_decision source previousRoot response64 selected key nonce next number position
        ancestors disclosed result).mpr ⟨⟨holds.1.1, holds.1.2.1⟩, holds.2, holds.1.2.2, known⟩)

end First

section Prepared
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The instrumented compiled continuation of one prepared context: completed preparations give `false`; a pending preparation runs the selected builder and the instrumented evaluated post with the prepared callbacks of its own KEM secret and challenge. -/
noncomputable def insCompiledObserve (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input => insCompiledRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter input.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore key nonce chain b
      target.number target.ancestors target.disclosed

/-- The key-disclosure continuation of one prepared context. -/
noncomputable def keyObserve (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input => keyRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter input.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore key nonce chain
      target.number target.ancestors target.disclosed

/-- The instrumented compiled first-record game: the actual preparation, the initializer block, the selected nonce and next chain, then the selected key, then the instrumented compiled continuation. -/
noncomputable def insCompiledGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  insCompiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post b target context initialBlock nonce chain key

/-- The explicit key-disclosure game `keyGame`: the same samples; in the key-last run, the first-record event and no hidden disclosure hold while the uniform record key equals a revealed value. -/
noncomputable def keyGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  keyObserve setup env callbacks baseImpl kem attachedVerify primitives program post target context initialBlock nonce chain key

/-- The pending source-observer mass of the first-record key-last endpoint is dominated by the instrumented compiled game plus the restricted stop game. -/
theorem pending_ideal_upper (target : Target S (B + 1)) (position : target.number.val = 1) :
    𝒟[PqxdhFirstRecordTarget.pendingIdeal env0 baseImpl kem attachedVerify primitives program post target] {true} ≤
    𝒟[insCompiledGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} +
    𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} := by
  unfold PqxdhFirstRecordTarget.pendingIdeal PqxdhAdaptiveMessageKeySource.firstPrepare insCompiledGame stopGame
  rw [PqxdhFirstRecordTarget.mapPost_choose]
  simp only [bind_assoc, pure_bind, PqxdhFirstRecordTarget.unitTargets, PqxdhInitialPreparedSourceInput.prior, bind_map_left]
  refine true_bind_le _ _ _ _ fun context => ?_
  refine true_bind_le _ _ _ _ fun initialBlock => ?_
  refine true_bind_le _ _ _ _ fun nonce => ?_
  refine true_bind_le _ _ _ _ fun chain => ?_
  refine true_bind_le _ _ _ _ fun key => ?_
  unfold insCompiledObserve stopObserve
  cases hstate : context.state with
  | completed decision =>
    simp only [PqxdhInitialPreparedSourceInput.input, hstate]
    simp
  | pending prepared ephemeral =>
    simp only [PqxdhInitialPreparedSourceInput.input, hstate, PqxdhAdaptiveMessageKeySource.firstObserve,
      PqxdhAdaptiveFirstMaterial.observe]
    change 𝒟[PqxdhInitialSourceRandom.decision _ _ _ _ (RawCtxSelectedMessageKdf.response key nonce chain) _ _ _ <$>
      PqxdhInitialSourceRandom.randomRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RawCtxSelectedMessageKdf.response key nonce chain)] {true} ≤ _
    rw [randomRun_prepared setup env callbacks ∅ baseImpl kem attachedVerify primitives context.secretKey context.ciphertext,
      Functor.map_map]
    exact first_upper _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ position _ _

set_option maxRecDepth 20000 in
/-- The instrumented compiled game is dominated by the pending source-observer mass of the first-record key-last endpoint plus the key-disclosure game. -/
theorem pending_ideal_lower (target : Target S (B + 1)) (position : target.number.val = 1) :
    𝒟[insCompiledGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} ≤
    𝒟[PqxdhFirstRecordTarget.pendingIdeal env0 baseImpl kem attachedVerify primitives program post target] {true} +
    𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} := by
  unfold PqxdhFirstRecordTarget.pendingIdeal PqxdhAdaptiveMessageKeySource.firstPrepare insCompiledGame keyGame
  rw [PqxdhFirstRecordTarget.mapPost_choose]
  simp only [bind_assoc, pure_bind, PqxdhFirstRecordTarget.unitTargets, PqxdhInitialPreparedSourceInput.prior, bind_map_left]
  refine true_bind_le _ _ _ _ fun context => ?_
  refine true_bind_le _ _ _ _ fun initialBlock => ?_
  refine true_bind_le _ _ _ _ fun nonce => ?_
  refine true_bind_le _ _ _ _ fun chain => ?_
  refine true_bind_le _ _ _ _ fun key => ?_
  unfold insCompiledObserve keyObserve
  cases hstate : context.state with
  | completed decision =>
    simp only [PqxdhInitialPreparedSourceInput.input, hstate]
    simp
  | pending prepared ephemeral =>
    simp only [PqxdhInitialPreparedSourceInput.input, hstate, PqxdhAdaptiveMessageKeySource.firstObserve,
      PqxdhAdaptiveFirstMaterial.observe]
    change _ ≤ 𝒟[PqxdhInitialSourceRandom.decision _ _ _ _ (RawCtxSelectedMessageKdf.response key nonce chain) _ _ _ <$>
      PqxdhInitialSourceRandom.randomRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (RawCtxSelectedMessageKdf.response key nonce chain)] {true} + _
    rw [randomRun_prepared setup env callbacks ∅ baseImpl kem attachedVerify primitives context.secretKey context.ciphertext,
      Functor.map_map]
    exact first_lower _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ position _ _

end Prepared

section Client
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhFirstBeaconRecordCtx
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

local notation "target" => PqxdhInitialSourceExperiment.root source previousRoot response64 selected
local notation "challenger" => AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key

/-- The client-side first-record event on an instrumented compiled state: the post returned `true`, the selected owner published record `number` with the selected origin, the selected chain and ancestors are undisclosed, and no hidden material was disclosed. It reads only the front and the transcript. -/
def ClientEvent (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B) : Prop :=
  result.1 = some true ∧ ((selected, number), true) ∈ result.2.2.1.published ∧
    RawCtxLiveLineage.FreshValues (RawCtxFreshChainCut.concreteChain target :: ancestors)
      (RawCtxSelectedMessageFreshness.known disclosed result.2.1.1.roles.2) ∧
    RawCtxSelectedMessageFreshness.hidden result.2.1.1.roles.2 = false

/-- The instrumented events and predicates are decided classically. -/
noncomputable instance (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B) :
    Decidable (ClientEvent source previousRoot response64 selected number ancestors disclosed result) := Classical.propDecidable _

/-- The instrumented full event is the client event of the compiled state. -/
theorem insEvent_client (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × InsFull M P I D K A N RootOracle.QueryCache S B) :
    InsEvent source previousRoot response64 selected number ancestors disclosed result ↔
      ClientEvent source previousRoot response64 selected number ancestors disclosed (result.1, result.2.1) := by
  simp only [InsEvent, FirstEvent, ClientEvent, Undisclosed, PqxdhSelectedPostDisclosure.Good, insProject]
  tauto

/-- The key-free instrumented first-record CTX client with output `out`: the compiled first Server builder, then the instrumented compiled post from the builder's state with the first transcript entry. -/
noncomputable def insFirstClient (out : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B → Bool) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool := do
  let built ← ((compiledBuild pre application initial selector aux source writer (productionStream source.crypto) none target
    nonce next sender (initialKernel response64) index metadata ready).run (initialFront before)).run
      (initialShared shared privateState cache store).1
  let result ← ((simulateQ (insImpl pre application initial selector aux source writer (productionStream source.crypto) none target
    nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b) (post built.1.1)).run).run
      ((built.1.2, built.2), (selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1, none, false))
  pure (out result)

/-- The raw result of the instrumented first-record client: the compiled first Server builder, then the instrumented compiled post, returning the post result and the final instrumented state. -/
noncomputable def insFirstRun :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (Option Bool × InsState M P I D K A N RootOracle.QueryCache S B) := do
  let built ← ((compiledBuild pre application initial selector aux source writer (productionStream source.crypto) none target
    nonce next sender (initialKernel response64) index metadata ready).run (initialFront before)).run
      (initialShared shared privateState cache store).1
  ((simulateQ (insImpl pre application initial selector aux source writer (productionStream source.crypto) none target
    nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b) (post built.1.1)).run).run
      ((built.1.2, built.2), (selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1, none, false))

/-- The instrumented first client is its output function applied to the raw run. -/
theorem insFirstClient_run (out : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B → Bool) :
    insFirstClient pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
      index metadata ready post before selected shared privateState cache store nonce next b out =
      out <$> insFirstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route
        decode index metadata ready post before selected shared privateState cache store nonce next b := by
  simp only [insFirstClient, insFirstRun, map_bind, bind_pure_comp]

/-- The instrumented post bit from a full instrumented state. -/
noncomputable def insPostBit (out : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B → Bool)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (start : InsFull M P I D K A N RootOracle.QueryCache S B) : ProbComp Bool :=
  (fun result => out (result.1, result.2.1)) <$>
    (evaluate challenger (simulateQ (insImpl pre application initial selector aux source writer (productionStream source.crypto) none
      target nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b) (post reply)).run).run start

/-- The instrumented post bit reads no selected public-hash log. -/
theorem insPostBit_ghost (out : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B → Bool)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (state : InsState M P I D K A N RootOracle.QueryCache S B) (component : AdaptiveCtxDynamicKnownKeys.SourceState) :
    insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post selected
        key nonce next b out reply (state, component) =
      insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post selected
        key nonce next b out reply (state, clearLog component) := by
  have ghost := congrArg (fun work => (fun result : (Option Bool × InsState M P I D K A N RootOracle.QueryCache S B) ×
      AdaptiveCtxDynamicKnownKeys.SourceState => out result.1) <$> work)
    (source_ghost (RawCtxUniversalDecoder.decoder decode) source.crypto key
      (((simulateQ (insImpl pre application initial selector aux source writer (productionStream source.crypto) none target
        nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b) (post reply)).run).run state) component)
  simp only [Functor.map_map, Prod.map_fst, id_eq] at ghost
  simp only [insPostBit, PqxdhSelectedStateInterpreter.evaluate, StateT.run, Functor.map_map, PqxdhSelectedStateInterpreter.pair]
  convert ghost using 3
  all_goals rfl

/-- The instrumented compiled first-record run, written with the instrumented post bit. -/
theorem insCompiledRun_postBit (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    insCompiledRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed =
    firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next >>= fun built =>
      insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
        selected key nonce next b (fun result => decide (ClientEvent source previousRoot response64 selected number ancestors disclosed result))
        built.1.1 (insStart index built) := by
  unfold insCompiledRun insPostBit
  refine bind_congr fun built => ?_
  rw [← insEvaluated_program]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  exact decide_eq_decide.mpr (insEvent_client source previousRoot response64 selected number ancestors disclosed result)

/-- When every first send of the initial Server kernel is known, the instrumented compiled first-record run is the key-free instrumented client evaluated by the selected-key challenger from any start that differs from the initial challenger only by the preparation cache and a public-hash log. -/
theorem insRun_client (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (known : ∀ kernel, initialKernel response64 = .ok kernel → ∀ context,
      KnownSend (productionStream source.crypto) none target nonce next kernel context)
    (log : List Pqxdh.Bytes) :
    insCompiledRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store key nonce next b number ancestors disclosed =
      Prod.fst <$> (simulateQ challenger (insFirstClient pre application initial selector aux source writer selectedMessage previousRoot
        response64 sender route decode index metadata ready post before selected shared privateState cache store nonce next b
        (fun result => decide (ClientEvent source previousRoot response64 selected number ancestors disclosed result)))).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) := by
  have related := build_rel pre application initial selector aux source writer (productionStream source.crypto) none key target
    nonce next decode sender (initialKernel response64) index metadata ready (initialFront before) known
    ((initialShared shared privateState cache store).1,
      RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log))
  simp only [evaluate, StateT.run] at related
  have clientEq : Prod.fst <$> (simulateQ challenger (insFirstClient pre application initial selector aux source writer selectedMessage
      previousRoot response64 sender route decode index metadata ready post before selected shared privateState cache store nonce next b
        (fun result => decide (ClientEvent source previousRoot response64 selected number ancestors disclosed result)))).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) =
      (simulateQ challenger (((compiledBuild pre application initial selector aux source writer (productionStream source.crypto) none
        target nonce next sender (initialKernel response64) index metadata ready).run (initialFront before)).run
          (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b (fun result => decide (ClientEvent source previousRoot response64 selected number ancestors disclosed
            result)) result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            result.2) := by
    simp only [insFirstClient, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    refine bind_congr fun result => ?_
    simp only [insPostBit, bind_pure_comp]
    change _ = (fun result => decide (ClientEvent source previousRoot response64 selected number ancestors disclosed
        (result.1, result.2.1))) <$>
      (pair <$> (simulateQ challenger (((simulateQ (insImpl pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage)
          b) (post result.1.1.1)).run).run ((result.1.1.2, result.1.2),
            (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)))).run result.2)
    rw [Functor.map_map]
    rfl
  have cleaned : ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b (fun result => decide (ClientEvent source previousRoot response64 selected number ancestors disclosed
            result)) result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            result.2)) =
      ((simulateQ challenger (((compiledBuild pre application initial selector aux source writer
      (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
        (initialFront before)).run (initialShared shared privateState cache store).1)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log)) >>= fun result =>
        insPostBit pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode post
          selected key nonce next b (fun result => decide (ClientEvent source previousRoot response64 selected number ancestors disclosed
            result)) result.1.1.1
          (((result.1.1.2, result.1.2), (selectedAfter PqxdhInitialSourcePublication.empty result.1.1.2 index true result.1.1.1, none, false)),
            { AdaptiveCtxDynamicKnownKeys.initialSource with cache := result.2.cache })) := by
    refine bind_congr_of_forall_mem_support _ fun result supported => ?_
    obtain ⟨shared', clean⟩ := related.2 (pair result) (by
      simp only [support_map, Set.mem_image]
      exact ⟨result, supported, rfl⟩)
    rw [insPostBit_ghost]
    change result.2 = _ at clean
    rw [clean]
    rfl
  have build : firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
      before selected shared privateState cache store key nonce next =
      Prod.map id project <$> (pair <$> (simulateQ challenger (((compiledBuild pre application initial selector aux source writer
        (productionStream source.crypto) none target nonce next sender (initialKernel response64) index metadata ready).run
          (initialFront before)).run (initialShared shared privateState cache store).1)).run
          (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (shared.2, log))) :=
    related.1.symm
  rw [clientEq, cleaned, insCompiledRun_postBit, build, bind_map_left, bind_map_left]
  rfl

/-- The instrumented first run's request budget in any class that the source-local callbacks never use: one builder request and the post budget. -/
theorem insFirstRun_uses (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ query state, ((PqxdhSelectedCallbackCompiler.lower (extra := extra) (I := I) (D := D) (K := K) (X := X)
      (Response := Response) (Shared := PqxdhPhase2DecapsulationRouting.Shared) pre application initial selector aux
        (.inl query)).run state).IsQueryBoundP predicate 0)
    (qPost : Nat) (postBound : ∀ reply, (post reply).IsTotalQueryBound qPost) :
    (insFirstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
      metadata ready post before selected shared privateState cache store nonce next b).IsQueryBoundP predicate (1 + qPost) := by
  unfold insFirstRun
  refine isQueryBoundP_bind ((uses_map predicate _ (ready_uses pre application initial selector aux source writer
    (productionStream source.crypto) none target nonce next predicate externalZero (initialKernel response64) _ ready metadata _))
      (initialShared shared privateState cache store).1) fun built _ => ?_
  exact insPost_client pre application initial selector aux source writer (productionStream source.crypto) none target nonce next
    sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b predicate
    (insPost_step pre application initial selector aux source writer (productionStream source.crypto) none target nonce next
      sender route decode (PqxdhInitialSelectedOrigin.mark source selectedMessage) b predicate externalZero)
    (post built.1.1) qPost (postBound _) _

end Client

section InsPrepared
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The raw result type of the instrumented prepared client: `none` for completed preparations, otherwise the selected owner, the initializer response and the instrumented first-client result. -/
abbrev PrepResult (M P I D K A : Type) (S B : Nat) :=
  Option (RawCtxProtocolReveals.Owner S B × PqxdhInitialRootLabelService.Response ×
    (Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1)
      RootOracle.QueryCache S B))

/-- Reading an output bit from a prepared result; completed preparations give `false`. -/
def readOut {M P I D K A : Type} {S B : Nat}
    (out : RawCtxProtocolReveals.Owner S B → PqxdhInitialRootLabelService.Response →
      Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1)
        RootOracle.QueryCache S B → Bool) :
    PrepResult M P I D K A S B → Bool
  | none => false
  | some result => out result.1 result.2.1 result.2.2


/-- The key-free instrumented suffix run after the prelude: completed preparations give `none`; a pending preparation runs the instrumented first client and returns the selected owner, the initializer response and the raw result. -/
noncomputable def insSuffixRun (target : Target S (B + 1))
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (PrepResult M P I (DhPair setup) K A S (B + 1)) :=
  match PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      target.owner target.number target.ancestors target.disclosed sample.1 with
  | .inl _ => pure none
  | .inr input => (fun result => some (input.selected, RawCtxSelectedInitialConstructor.response64 sample.2.1, result)) <$>
    insFirstRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        sample.1.secretKey sample.1.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        sample.1.secretKey sample.1.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 sample.2.1))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem sample.1.secretKey sample.1.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter input.selectedMessage zeroRoot (RawCtxSelectedInitialConstructor.response64 sample.2.1)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore sample.2.2.1 sample.2.2.2 b

/-- The key-free instrumented suffix with output function `out`. -/
noncomputable def insSuffix (target : Target S (B + 1))
    (out : RawCtxProtocolReveals.Owner S (B + 1) → PqxdhInitialRootLabelService.Response →
      Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
        (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1) → Bool)
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  readOut out <$> insSuffixRun setup env callbacks baseImpl kem attachedVerify primitives program post b target sample

/-- The constructed key-free instrumented CTX client with output function `out`: the forwarded preparation prelude followed by the instrumented suffix. -/
noncomputable def insFullClient (target : Target S (B + 1))
    (out : RawCtxProtocolReveals.Owner S (B + 1) → PqxdhInitialRootLabelService.Response →
      Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
        (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1) → Bool) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec Bool :=
  simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post) >>=
    insSuffix setup env callbacks baseImpl kem attachedVerify primitives program post b target out

/-- The first-record output function of the chain: the client event of the target with the selected owner and the initializer response. -/
noncomputable def clientOut (target : Target S (B + 1)) (owner : RawCtxProtocolReveals.Owner S (B + 1))
    (response64 : PqxdhInitialRootLabelService.Response)
    (result : Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
      (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)) : Bool :=
  decide (ClientEvent (env0).source zeroRoot response64 owner target.number target.ancestors target.disclosed result)

/-- Outside the initial half alias, the instrumented compiled continuation of the first Beacon record equals the key-free instrumented suffix with the client-event output, evaluated by the selected-key challenger from the reached cache and public log. -/
theorem insObserve_eq
    (sample : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program × HmacBlock × NonceOutput × RootOutput)
    (cache : CtxRO.QueryCache) (log : List Pqxdh.Bytes) (key : RootOutput)
    (aliased : ¬ RawCtxSendLineageCollision.InitialAlias sample.2.1) :
    insCompiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
        (restoreSample setup env callbacks kem attachedVerify primitives program post sample cache).1
        sample.2.1 sample.2.2.1 sample.2.2.2 key =
      Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
        (env0).source.crypto key) (insSuffix setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
          (clientOut setup env callbacks (firstBeacon b)) sample)).run
        (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource (cache, log)) := by
  unfold insCompiledObserve insSuffix insSuffixRun restoreSample
  rw [← PqxdhSourceSharedInput.input_cache setup env callbacks program post attachedVerify primitives baseImpl kem]
  cases pending : PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      (firstBeacon b).owner (firstBeacon b).number (firstBeacon b).ancestors (firstBeacon b).disclosed sample.1 with
  | inl decision => simp [PqxdhSourceSharedInput.restore, readOut]
  | inr input =>
    have owner := input_selected setup env callbacks baseImpl kem attachedVerify primitives program post _ _ _ _ sample.1 input pending
    simp only [PqxdhSourceSharedInput.restore]
    have known : ∀ kernel, initialKernel (RawCtxSelectedInitialConstructor.response64 sample.2.1) = .ok kernel → ∀ context,
        KnownSend (productionStream (env0).source.crypto) none (PqxdhInitialSourceExperiment.root (env0).source zeroRoot
          (RawCtxSelectedInitialConstructor.response64 sample.2.1) (firstBeacon b).owner) sample.2.2.1 sample.2.2.2 kernel context :=
      fun kernel initialized context => initial_known (S := S) (env0).source sample.2.1 b sample.2.2.1 sample.2.2.2
        aliased kernel initialized context
    rw [owner] at *
    rw [insRun_client (known := known) (log := log), insFirstClient_run, Functor.map_map]
    rfl

/-- Regrouping the prepared samples through the shared-ROM prelude: the actual preparation, the four uniform draws and a continuation equal the prelude run from the empty shared state, a key draw and the continuation at the restored sample. -/
theorem prepared_reorder
    (F : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post → HmacBlock → NonceOutput → RootOutput →
      RootOutput → ProbComp Bool) :
    (do
      let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
        (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
      let initialBlock ← $ᵗ HmacBlock
      let nonce ← $ᵗ NonceOutput
      let chain ← $ᵗ RootOutput
      let key ← $ᵗ RootOutput
      F context initialBlock nonce chain key) =
    (do
      let result ← (simulateQ AdaptiveCtxSharedTarget.sharedImpl
        (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).run (∅, [])
      let key ← $ᵗ RootOutput
      F (restoreSample setup env callbacks kem attachedVerify primitives program post result.1 result.2.1).1
        result.1.2.1 result.1.2.2.1 result.1.2.2.2 key) := by
  have shared := AdaptiveCtxSharedTarget.cache_schedule (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)
    (∅, [])
  have source := prelude_source setup env callbacks baseImpl kem attachedVerify primitives program post
  rw [← shared, Functor.map_map] at source
  have regroup : (do
      let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
        (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
      let initialBlock ← $ᵗ HmacBlock
      let nonce ← $ᵗ NonceOutput
      let chain ← $ᵗ RootOutput
      let key ← $ᵗ RootOutput
      F context initialBlock nonce chain key) =
      (do
        let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
          (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
        let initialBlock ← $ᵗ HmacBlock
        let nonce ← $ᵗ NonceOutput
        let chain ← $ᵗ RootOutput
        pure (context, initialBlock, nonce, chain)) >>= fun sample => (do
          let key ← $ᵗ RootOutput
          F sample.1 sample.2.1 sample.2.2.1 sample.2.2.2 key) := by
    simp only [bind_assoc, pure_bind]
  rw [regroup, ← source, bind_map_left]
  rfl

/-- The instrumented compiled game with the initial half-alias runs mapped to `false`. -/
noncomputable def insSeparatedGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  @ite _ (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _) (pure false)
    (insCompiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post b target context initialBlock nonce chain key)

/-- The instrumented compiled game is dominated by the initial half-alias term `2^-256` plus the separated instrumented game. -/
theorem insCompiled_le_separated (target : Target S (B + 1)) :
    𝒟[insCompiledGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} ≤
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) +
        𝒟[insSeparatedGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} := by
  refine le_trans ?_ (add_le_add (alias_bound setup env callbacks baseImpl kem attachedVerify primitives program post) le_rfl)
  unfold insCompiledGame insSeparatedGame aliasGame
  refine true_bind_le _ _ _ _ fun context => ?_
  refine true_bind_le _ _ _ _ fun initialBlock => ?_
  refine true_bind_le _ _ _ _ fun nonce => ?_
  refine true_bind_le _ _ _ _ fun chain => ?_
  refine true_bind_le _ _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias initialBlock
  · rw [ite_eq_left_iff.mpr fun impossible => absurd aliased impossible,
      show (@decide (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _)) = true from
        @decide_eq_true _ (Classical.propDecidable _) aliased]
    refine le_add_right ?_
    rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_pure]
    simp only [↓reduceIte]
    exact prEvent_le_one _
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased]
    exact le_add_self

/-- The separated instrumented game is dominated by the instrumented compiled game. -/
theorem insSeparated_le_compiled (target : Target S (B + 1)) :
    𝒟[insSeparatedGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} ≤
      𝒟[insCompiledGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} := by
  unfold insCompiledGame insSeparatedGame
  refine true_bind_mono _ _ _ fun context => ?_
  refine true_bind_mono _ _ _ fun initialBlock => ?_
  refine true_bind_mono _ _ _ fun nonce => ?_
  refine true_bind_mono _ _ _ fun chain => ?_
  refine true_bind_mono _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias initialBlock
  · rw [ite_eq_left_iff.mpr fun impossible => absurd aliased impossible]
    simp [-evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased]

/-- Sampling the selected key after the forwarded prelude: the ordinary selected-key CTX source game of the instrumented client is the prelude run, a key draw and the suffix from the reached shared state. -/
theorem insClient_source (target : Target S (B + 1))
    (out : RawCtxProtocolReveals.Owner S (B + 1) → PqxdhInitialRootLabelService.Response →
      Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
        (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1) → Bool) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target out)] =
    𝒟[do
      let result ← (simulateQ AdaptiveCtxSharedTarget.sharedImpl
        (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).run (∅, [])
      let key ← $ᵗ RootOutput
      Prod.fst <$> (simulateQ (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
        (env0).source.crypto key) (insSuffix setup env callbacks baseImpl kem attachedVerify primitives program post b target out
          result.1)).run (RawCtxSourceSharedRom.install AdaptiveCtxDynamicKnownKeys.initialSource result.2)] := by
  have exchanged := RawCtxPrefixKeyOrder.source_game true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)
    (insSuffix setup env callbacks baseImpl kem attachedVerify primitives program post b target out)
  have mapped := exchanged.map Prod.fst
  simp only [map_bind] at mapped
  exact mapped.evalDist_eq

/-- The separated instrumented game is dominated by the instrumented client-event client in the ordinary selected-key CTX source game. -/
theorem insSeparated_le_client :
    𝒟[insSeparatedGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true} ≤
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
        (clientOut setup env callbacks (firstBeacon b)))] {true} := by
  have reorder := prepared_reorder setup env callbacks baseImpl kem attachedVerify primitives program post
    (fun context initialBlock nonce chain key =>
      @ite _ (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _) (pure false)
        (insCompiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) context
          initialBlock nonce chain key))
  change insSeparatedGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) = _ at reorder
  rw [reorder, insClient_source]
  refine true_bind_mono _ _ _ fun result => true_bind_mono _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias result.1.2.1
  · rw [ite_eq_left_iff.mpr fun impossible => absurd aliased impossible]
    simp [-evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased,
      insObserve_eq setup env callbacks baseImpl kem attachedVerify primitives program post b result.1 result.2.1 result.2.2 key aliased]

/-- The instrumented client-event client in the ordinary selected-key CTX source game is dominated by the separated instrumented game plus the initial half-alias term `2^-256`. -/
theorem insClient_le_separated :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
        (clientOut setup env callbacks (firstBeacon b)))] {true} ≤
    𝒟[insSeparatedGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true} +
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  refine le_trans ?_ (add_le_add le_rfl (alias_bound setup env callbacks baseImpl kem attachedVerify primitives program post))
  have reorder := prepared_reorder setup env callbacks baseImpl kem attachedVerify primitives program post
    (fun context initialBlock nonce chain key =>
      @ite _ (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _) (pure false)
        (insCompiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) context
          initialBlock nonce chain key))
  change insSeparatedGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) = _ at reorder
  have aliasReorder := prepared_reorder setup env callbacks baseImpl kem attachedVerify primitives program post
    (fun _ initialBlock _ _ _ => pure (@decide (RawCtxSendLineageCollision.InitialAlias initialBlock) (Classical.propDecidable _)))
  change aliasGame setup env callbacks baseImpl kem attachedVerify primitives program post = _ at aliasReorder
  rw [reorder, aliasReorder, insClient_source]
  refine true_bind_le _ _ _ _ fun result => true_bind_le _ _ _ _ fun key => ?_
  classical
  by_cases aliased : RawCtxSendLineageCollision.InitialAlias result.1.2.1
  · rw [show (@decide (RawCtxSendLineageCollision.InitialAlias result.1.2.1) (Classical.propDecidable _)) = true from
        @decide_eq_true _ (Classical.propDecidable _) aliased]
    refine le_add_left ?_
    rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_pure]
    simp only [↓reduceIte]
    exact prEvent_le_one _
  · rw [ite_eq_right_iff.mpr fun holds => absurd holds aliased,
      insObserve_eq setup env callbacks baseImpl kem attachedVerify primitives program post b result.1 result.2.1 result.2.2 key aliased]
    exact le_self_add

/-- The instrumented client's request budget in any class that the source-local callbacks never use: the forwarded prelude's budget, one builder request and the post budget. The output function does not matter. -/
theorem insFullClient_uses (target : Target S (B + 1))
    (out : RawCtxProtocolReveals.Owner S (B + 1) → PqxdhInitialRootLabelService.Response →
      Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
        (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1) → Bool)
    (predicate : AdaptiveCtxDynamicKnownKeys.Spec.Domain → Prop) [DecidablePred predicate]
    (externalZero : ∀ (secret : KemSK) (challenge : MlKem768Ciphertext) (selectedMessage : Message) (response : PqxdhInitialRootLabelService.Response)
      query state, ((PqxdhSelectedCallbackCompiler.lower (extra := SelectorSpec baseSpec)
        (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem secret challenge)
        (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem secret challenge)
        (initialLocal (A := A) (N := BareState 1) (env0).source selectedMessage zeroRoot response)
        (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
          (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem secret challenge))
        (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks) (.inl query)).run state).IsQueryBoundP predicate 0)
    (qPrelude : Nat)
    (preludeBound : (simulateQ RawCtxSourceSharedRom.forward
      (prelude setup env callbacks baseImpl kem attachedVerify primitives program post)).IsQueryBoundP predicate qPrelude)
    (qPost : Nat) (postBound : ∀ selection reply, (post selection reply).IsTotalQueryBound qPost) :
    (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target out).IsQueryBoundP predicate
      (qPrelude + (1 + qPost)) := by
  refine isQueryBoundP_bind preludeBound fun sample _ => ?_
  unfold insSuffix insSuffixRun
  split
  · simp
  · rename_i input pending
    obtain ⟨selection, selected⟩ := input_post setup env callbacks baseImpl kem attachedVerify primitives program post _ _ _ _
      sample.1 input pending
    rw [isQueryBoundP_map_iff, isQueryBoundP_map_iff]
    apply insFirstRun_uses (predicate := predicate) (externalZero := externalZero _ _ _ _) (qPost := qPost)
    exact fun reply => selected ▸ postBound selection reply

end InsPrepared

section ConfRuns
open AdaptiveCtxDynamicKnownKeys (Spec)

/-- An identical prefix followed by adaptive twin continuations on its support is adaptive twin. -/
theorem pre_bind_refl {α γ δ : Type} {Out : γ → δ → Prop} {Dead0 : γ → Prop} {Dead1 : δ → Prop}
    (x : OracleComp Spec α) {f : α → OracleComp Spec γ} {g : α → OracleComp Spec δ}
    (next : ∀ a ∈ support x, Pre Out Dead0 Dead1 (f a) (g a)) : Pre Out Dead0 Dead1 (x >>= f) (x >>= g) := by
  induction x using OracleComp.inductionOn with
  | pure a => simpa only [pure_bind] using next a (by simp)
  | query_bind q k ih =>
    simp only [bind_assoc]
    exact Pre.step q fun r => ih r fun a ha => next a (by
      rw [mem_support_bind_iff]
      exact ⟨r, mem_support_query q r, ha⟩)

variable {ι : Type} {extra : OracleSpec ι} {S B : Nat} {σ : Type}

/-- The wrapper's steps interpreted by a stoppable post interpreter. -/
noncomputable def confIns (b : Fin B) (β : Bool)
    (impl : QueryImpl (ConfPostSpec extra S B) (OptionT (StateT σ (OracleComp Spec)))) :
    QueryImpl (AdvSpec extra S B) (Stepper ConfState σ) :=
  fun query => StateT.mk fun state => simulateQ impl ((confImpl b β query).run state)

/-- Interpreting the wrapper's run by a post interpreter is the run of the composed steps. -/
theorem conf_run (b : Fin B) (β : Bool) (impl : QueryImpl (ConfPostSpec extra S B) (OptionT (StateT σ (OracleComp Spec))))
    {α : Type} (X : OracleComp (AdvSpec extra S B) α) (c : ConfState) :
    simulateQ impl ((simulateQ (confImpl b β) X).run c) = (simulateQ (confIns b β impl) X).run c := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure v => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change _ = simulateQ impl ((confImpl b β q).run c) >>= _
    exact bind_congr fun z => ih z.1 z.2


/-- The wrapper post interpreted by a stoppable post interpreter is the mapped run of the composed steps. -/
theorem conf_post_run {Selection : Type} (b : Fin B) (β : Bool)
    (impl : QueryImpl (ConfPostSpec extra S B) (OptionT (StateT σ (OracleComp Spec))))
    (A : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (selection : Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (s : σ) :
    ((simulateQ impl (confPost A b β selection reply)).run).run s =
      (fun z => (z.1.map confOutput, z.2)) <$> runStepper (simulateQ (confIns b β impl) (A selection reply)) confInitial s := by
  unfold confPost
  rw [simulateQ_map, conf_run]
  simp only [runStepper, OptionT.run_map, StateT.run_map]

variable (b : Fin B) (impl : QueryImpl (ConfPostSpec extra S B) (OptionT (StateT σ (OracleComp Spec)))) (Dead : σ → Prop)
    (Link : ConfState → σ → Prop)

/-- Before the challenge the two wrappers' runs are identical; the accepted challenge switches to twin runs for its pair. Hypotheses: adversary requests keep the challenge pair, the accepted challenge step and every later step are twin for the pair, and dead states are sticky. -/
theorem pre_run
    (keep : ∀ request c s, Link c s → ∀ z ∈ support (runStepper (confIns b false impl (.inl request)) c s), ∀ reply c',
      z.1 = some (reply, c') → c'.pair = c.pair ∧ Link c' z.2)
    (challenge : ∀ m0 m1 c s, Link c s → c.pair = none → c.beaconSent = false → m0.length = m1.length → ¬ Dead s →
      Twin m0 m1 (fun z0 z1 => z0 = z1 ∧ ∀ reply c', z0.1 = some (reply, c') → c'.pair = some (m0, m1))
        (fun z => Dead z.2) (fun z => Dead z.2)
        (runStepper (confIns b false impl (.inr (m0, m1))) c s) (runStepper (confIns b true impl (.inr (m0, m1))) c s))
    (step : ∀ m0 m1 q c s, c.pair = some (m0, m1) → ¬ Dead s →
      Twin m0 m1 (fun z0 z1 => z0 = z1 ∧ ∀ reply c', z0.1 = some (reply, c') → c'.pair = some (m0, m1))
        (fun z => Dead z.2) (fun z => Dead z.2)
        (runStepper (confIns b false impl q) c s) (runStepper (confIns b true impl q) c s))
    (sticky : ∀ β q c s, Dead s → ∀ z ∈ support (runStepper (confIns b β impl q) c s), Dead z.2)
    {α : Type} (X : OracleComp (AdvSpec extra S B) α) (c : ConfState) (s : σ) (link : Link c s) (fresh : c.pair = none) :
    Pre (fun a b => a = b) (fun z => Dead z.2) (fun z => Dead z.2)
      (runStepper (simulateQ (confIns b false impl) X) c s) (runStepper (simulateQ (confIns b true impl) X) c s) := by
  induction X using OracleComp.inductionOn generalizing c s with
  | pure value =>
    simp only [runStepper, simulateQ_pure, StateT.run_pure, OptionT.run_pure]
    exact Pre.pure rfl
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, runStepper_bind, runStepper_bind]
    rcases query with request | ⟨m0, m1⟩
    · change Pre _ _ _ (runStepper (confIns b false impl (.inl request)) c s >>= _)
        (runStepper (confIns b false impl (.inl request)) c s >>= _)
      refine pre_bind_refl _ fun z hz => ?_
      rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
      · exact Pre.pure rfl
      · have kept := keep request c s link _ hz reply c' rfl
        exact ih reply c' s' kept.2 (by rw [kept.1]; exact fresh)
    · by_cases refused : c.pair.isSome ∨ c.beaconSent ∨ m0.length ≠ m1.length
      · have stop : ∀ β, runStepper (confIns b β impl (.inr (m0, m1))) c s = pure (some (none, c), s) := by
          intro β
          have run : (confImpl (extra := extra) (S := S) b β (.inr (m0, m1))).run c =
              (pure ((none : Option RawCtxSourceSend.Encrypted), c) :
                OracleComp (ConfPostSpec extra S B) (Option RawCtxSourceSend.Encrypted × ConfState)) := by
            simp only [confImpl, StateT.run]
            rw [ite_eq_left_iff.mpr fun impossible => absurd refused impossible]
          simp only [runStepper, confIns, StateT.run_mk, run, simulateQ_pure]
          rfl
        rw [stop false, stop true, pure_bind, pure_bind]
        exact ih none c s link fresh
      · simp only [not_or, Bool.not_eq_true, not_not] at refused
        obtain ⟨unpaired, sent, equal⟩ := refused
        have none' : c.pair = none := by
          cases hc : c.pair with
          | none => rfl
          | some v => simp [hc] at unpaired
        by_cases dead : Dead s
        · refine Pre.dead ?_ ?_
          · intro w hw
            rw [mem_support_bind_iff] at hw
            obtain ⟨z, hz, hw⟩ := hw
            have deadZ := sticky false _ c s dead z hz
            rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
            · simp only [support_pure, Set.mem_singleton_iff] at hw
              rw [hw]
              exact deadZ
            · exact runStepper_dead (confIns b false impl) Dead (sticky false) (next reply) c' s' deadZ w hw
          · intro w hw
            rw [mem_support_bind_iff] at hw
            obtain ⟨z, hz, hw⟩ := hw
            have deadZ := sticky true _ c s dead z hz
            rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
            · simp only [support_pure, Set.mem_singleton_iff] at hw
              rw [hw]
              exact deadZ
            · exact runStepper_dead (confIns b true impl) Dead (sticky true) (next reply) c' s' deadZ w hw
        · refine Pre.switch m0 m1 equal (twin_bind m0 m1 (challenge m0 m1 c s link none' sent equal dead) ?_ ?_ ?_)
          · rintro z _ ⟨rfl, paired⟩
            by_cases deadZ : Dead z.2
            · refine Twin.dead ?_ ?_
              · intro w hw
                rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
                · simp only [support_pure, Set.mem_singleton_iff] at hw
                  rw [hw]
                  exact deadZ
                · exact runStepper_dead (confIns b false impl) Dead (sticky false) (next reply) c' s' deadZ w hw
              · intro w hw
                rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
                · simp only [support_pure, Set.mem_singleton_iff] at hw
                  rw [hw]
                  exact deadZ
                · exact runStepper_dead (confIns b true impl) Dead (sticky true) (next reply) c' s' deadZ w hw
            · rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
              · exact Twin.pure rfl
              · exact twin_run_inv m0 m1 (confIns b false impl) (confIns b true impl) Dead (fun c => c.pair = some (m0, m1))
                  (step m0 m1) (sticky false) (sticky true) (next reply) c' s' (paired reply c' rfl) deadZ
          · intro z deadZ w hw
            rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
            · simp only [support_pure, Set.mem_singleton_iff] at hw
              rw [hw]
              exact deadZ
            · exact runStepper_dead (confIns b false impl) Dead (sticky false) (next reply) c' s' deadZ w hw
          · intro z deadZ w hw
            rcases z with ⟨_ | ⟨reply, c'⟩, s'⟩
            · simp only [support_pure, Set.mem_singleton_iff] at hw
              rw [hw]
              exact deadZ
            · exact runStepper_dead (confIns b true impl) Dead (sticky true) (next reply) c' s' deadZ w hw

end ConfRuns

section SendTwin
open RawCtxInterpretedSend ratchet.refined PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedMessageKey

/-- Replacing the stored context of a send admission. -/
def withContext {Material Context Context' : Type} (context : Context') : Start Material Context → Start Material Context'
  | .exhausted entry _ => .exhausted entry context
  | .requested pending => .requested ⟨pending.entry, context, pending.committed_control, pending.logical, pending.sequence,
      pending.request⟩

/-- Send admission only stores its context. -/
theorem beginSend_context {Material Context Context' : Type} (kernel : RefinedRatchet RatchetChain RatchetChain Material)
    (context : Context) (context' : Context') :
    beginSend kernel context' = withContext context' <$> beginSend kernel context := by
  unfold beginSend
  simp only [map_bind]
  congr 1
  funext advanced
  split
  · rfl
  · simp only [map_bind]
    congr 1
    funext original
    congr 1
    funext equal
    split
    · simp only [map_bind]
      congr 1
      funext sequenceNow
      split
      · simp only [map_bind]
        congr 1
      · rfl
    · rfl

/-- The chosen send admission only stores its context. -/
theorem normalBegin_context {Material Context Context' : Type} (kernel : RefinedRatchet RatchetChain RatchetChain Material)
    (context : Context) (context' : Context') :
    normalBegin kernel context' = withContext context' (normalBegin kernel context) := by
  apply RustM.ok.inj
  rw [← normalBegin_exact, beginSend_context kernel context context', normalBegin_exact]
  rfl

/-- A hidden first send of the two challenge plaintexts is twin: the selected seal inputs differ only in the plaintext, and the returned kernel and record do not depend on it. -/
theorem send_twin (m0 m1 : Pqxdh.Bytes) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (hidden : RawCtxSelectedPendingCut.requestAddress kernel.send_chain = RawCtxSelectedParentPrivatePatch.targetAddress target) :
    Twin m0 m1 (fun a b => a = b) (fun _ => False) (fun _ => False)
      (RawCtxSelectedSendCompiler.send source writer prior none target nonce next kernel { context with plaintext := m0 })
      (RawCtxSelectedSendCompiler.send source writer prior none target nonce next kernel { context with plaintext := m1 }) := by
  rw [RawCtxSelectedSendCompiler.send_cases, RawCtxSelectedSendCompiler.send_cases,
    normalBegin_context (Context' := RawCtxSourceSend.SealContext) kernel context
      ({ context with plaintext := m0 } : RawCtxSourceSend.SealContext),
    normalBegin_context (Context' := RawCtxSourceSend.SealContext) kernel context
      ({ context with plaintext := m1 } : RawCtxSourceSend.SealContext)]
  cases admitted : normalBegin kernel context with
  | exhausted entry stored => exact Twin.pure rfl
  | requested pending =>
    have address := RawCtxSelectedSendAddress.admitted_address kernel context pending admitted
    have step : RawCtxSelectedSendCompiler.deriveValue prior none target nonce next pending.request =
        (RawCtxFreshChainCut.concreteChain next, .hidden nonce) := by
      simp only [RawCtxSelectedSendCompiler.deriveValue, RawCtxSelectedMessageKdf.step, address, hidden, ite_true]
    simp only [withContext, step, RawCtxSelectedSealConsumer.sealing, RawCtxSelectedSealConsumer.call,
      RawCtxInterpretedArguments.sealArguments, ready]
    by_cases had : context.associatedData.length = 153
    · simp only [RawCtxSelectedMessageSealing.selected, had, _root_.dite_true, simulateQ_bind, simulateQ_pure, map_bind, map_pure,
        simulateQ_query, RawCtxSelectedSealConsumer.liftSelected]
      refine Twin.sealing _ _ ?_ fun r => ?_
      · simp only [identInput, ident, RawCtxSelectedMessageSealing.selectedInput, ite_true]
        split_ifs <;> simp_all
      · cases r <;> exact Twin.pure rfl
    · simp only [RawCtxSelectedMessageSealing.selected, had, _root_.dite_false, simulateQ_pure, map_pure]
      exact Twin.pure rfl

end SendTwin

section ChallengeStep
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedFirstRecord
open AdaptiveCtxDynamicKnownKeys (Spec)
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (b : Fin B)

/-- The instrumented dead states: the first send of Beacon `b` did not use the selected hidden material, or a Beacon finish made a selected raw opening. -/
def InsDead (state : InsState M P I D K A N C S B) : Prop := state.2.2.1 = some false ∨ state.2.2.2 = true

/-- The wrapper and the instrumented state agree on Beacon `b`'s first send: while the wrapper has seen no send of Beacon `b`, the monitor has recorded none. -/
def InsLink (c : ConfState) (state : InsState M P I D K A N C S B) : Prop := c.beaconSent = false → state.2.2.1 = none

set_option backward.isDefEq.respectTransparency false in
/-- One accepted challenge step: the forwarded Beacon send, with the wrapper's bookkeeping. -/
theorem challenge_run (β : Bool) (m0 m1 : Pqxdh.Bytes) (c : ConfState) (s : InsState M P I D K A N C S B)
    (fresh : c.pair = none) (sent : c.beaconSent = false) (equal : m0.length = m1.length) :
    runStepper (confIns b β (insImpl pre application initial selector aux source writer prior none target nonce next sender route read
      mark b) (.inr (m0, m1))) c s =
      (fun z => (z.1.map (fun reply => (reply, { c with pair := some (m0, m1), reply := some reply, beaconSent := true })), z.2)) <$>
        ((insImpl pre application initial selector aux source writer prior none target nonce next sender route read mark b
          (beaconSend b (if β then m1 else m0))).run).run s := by
  have accepted : ¬ (c.pair.isSome ∨ c.beaconSent ∨ m0.length ≠ m1.length) := by
    simp [fresh, sent, equal]
  have conf : (confImpl (extra := extra) (S := S) b β (.inr (m0, m1))).run c =
      ((liftM ((ConfPostSpec extra S B).query (beaconSend b (if β then m1 else m0))) : OracleComp (ConfPostSpec extra S B) _) >>= fun reply =>
        pure (reply, { c with pair := some (m0, m1), reply := some reply, beaconSent := true })) := by
    simp only [confImpl, StateT.run]
    rw [ite_eq_right_iff.mpr fun holds => absurd holds accepted]
  simp only [runStepper, confIns, StateT.run_mk, conf]
  rw [simulateQ_bind]
  simp only [simulateQ_query, simulateQ_pure, OptionT.run_bind, Option.elimM, StateT.run_bind, map_eq_bind_pure_comp]
  rw [bind_assoc]
  congr 1
  funext z
  rcases z with ⟨_ | reply, s'⟩ <;> rfl

/-- The monitor value recorded by the first send of Beacon `b`. -/
theorem hiddenStep_first (p : Pqxdh.Bytes) (front : PqxdhSelectedPostCompiler.Front M P I D K S B) :
    hiddenStep b target (.inl (.inr (.inl ⟨b, .inl p⟩))) front none =
      some (decide (HiddenBeacon target (front.roles.1.2 b))) := by
  simp [hiddenStep]

/-- Every result of an instrumented Beacon `b` send from a state without a monitor value carries the recorded hiddenness. -/
theorem ins_send_monitor (p : Pqxdh.Bytes) (s : InsState M P I D K A N C S B) (none' : s.2.2.1 = none)
    (z : Option ((ConfPostSpec extra S B).Range (beaconSend b p)) × InsState M P I D K A N C S B)
    (supported : z ∈ support (((insImpl pre application initial selector aux source writer prior none target nonce next sender route
      read mark b (beaconSend b p)).run).run s)) :
    z.2.2.2.1 = some (decide (HiddenBeacon target (s.1.1.roles.1.2 b))) := by
  simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨result, _, rfl⟩ := supported
  simp only [none']
  exact hiddenStep_first target b p s.1.1



/-- The transcript update of a Beacon `b` send reply, which does not read the plaintext. -/
def beaconTrace (t : PqxdhInitialOriginPost.Trace Bool S B) (r : Option (Option RawCtxSourceSend.Encrypted)) :
    PqxdhInitialOriginPost.Trace Bool S B :=
  match r with
  | none => t
  | some value => PqxdhInitialOriginPost.record t (.inl (.inr (.inl ⟨b, .inl []⟩))) value

/-- A Beacon `b` send updates the transcript independently of its plaintext. -/
theorem traceRecord_beacon (t : PqxdhInitialOriginPost.Trace Bool S B) (p : Pqxdh.Bytes)
    (r : Option (Option RawCtxSourceSend.Encrypted)) :
    traceRecord t (.inl (.inr (.inl ⟨b, .inl p⟩))) r = beaconTrace b t r := by
  cases r with
  | none => rfl
  | some value =>
    simp only [traceRecord, beaconTrace, PqxdhInitialOriginPost.record, RawCtxPublishedRecords.record]
    cases value <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The accepted challenge step is twin: when the first send of Beacon `b` uses the selected hidden material the two sends differ only in the selected seal's plaintext; otherwise every result is dead. -/
theorem challenge_twin (m0 m1 : Pqxdh.Bytes) (c : ConfState) (s : InsState M P I D K A N C S B)
    (link : InsLink c s) (fresh : c.pair = none) (sent : c.beaconSent = false) (equal : m0.length = m1.length) :
    Twin m0 m1 (fun z0 z1 => z0 = z1 ∧ ∀ reply c', z0.1 = some (reply, c') → c'.pair = some (m0, m1))
      (fun z => InsDead z.2) (fun z => InsDead z.2)
      (runStepper (confIns b false (insImpl pre application initial selector aux source writer prior none target nonce next sender
        route read mark b) (.inr (m0, m1))) c s)
      (runStepper (confIns b true (insImpl pre application initial selector aux source writer prior none target nonce next sender
        route read mark b) (.inr (m0, m1))) c s) := by
  have none' : s.2.2.1 = none := link sent
  rw [challenge_run pre application initial selector aux source writer prior target nonce next sender route read mark b false m0 m1 c s
      fresh sent equal,
    challenge_run pre application initial selector aux source writer prior target nonce next sender route read mark b true m0 m1 c s
      fresh sent equal]
  by_cases hidden : HiddenBeacon target (s.1.1.roles.1.2 b)
  · unfold HiddenBeacon at hidden
    split at hidden
    · rename_i control ad kernel phase
      simp only [insImpl, OptionT.run_mk, StateT.run, RawCtxSelectedFamilyLiveCompiler.impl, Functor.map_map,
        RawCtxSelectedFamilyCompiler.family_cases, RawCtxSelectedRoleCompiler.beacon_cases, phase,
        RawCtxSelectedOwnerCompiler.send_cases, Bool.false_eq_true, ite_false, ite_true]
      have sameEmpty : m1.isEmpty = m0.isEmpty := by
        cases m0 <;> cases m1 <;> simp_all
      rw [sameEmpty]
      by_cases empty : m0.isEmpty = true
      · simp only [empty, ite_true, map_pure, none', hiddenStep_first, traceRecord_beacon]
        refine Twin.pure ⟨rfl, ?_⟩
        intro reply c' holds
        simp only [Option.map_eq_some_iff] at holds
        obtain ⟨_, _, same⟩ := holds
        simp only [Prod.mk.injEq] at same
        rw [← same.2]
      · simp only [empty, Bool.false_eq_true, ite_false, Functor.map_map, none', hiddenStep_first, traceRecord_beacon]
        refine twin_map m0 m1 (send_twin m0 m1 source writer prior target nonce next kernel
          ⟨m0, (RawCtxGenericBeacon.selected (s.1.1.roles.1.2 b) control ad kernel).expectedSender,
            (s.1.1.roles.1.2 b).beacon.identityKeyId,
            (RawCtxGenericBeacon.selected (s.1.1.roles.1.2 b) control ad kernel).associatedData⟩ hidden) _ _ ?_
          (fun _ impossible => impossible.elim) (fun _ impossible => impossible.elim)
        rintro a _ rfl
        refine ⟨rfl, ?_⟩
        intro reply c' holds
        simp only [Option.map_eq_some_iff] at holds
        obtain ⟨_, _, same⟩ := holds
        simp only [Prod.mk.injEq] at same
        rw [← same.2]
    · exact absurd hidden id
  · refine Twin.dead ?_ ?_
    · intro z hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      left
      rw [ins_send_monitor pre application initial selector aux source writer prior target nonce next sender route read mark b _ s none' w hw]
      simp [hidden]
    · intro z hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      left
      rw [ins_send_monitor pre application initial selector aux source writer prior target nonce next sender route read mark b _ s none' w hw]
      simp [hidden]


end ChallengeStep

section Stable
open AdaptiveCtxDynamicKnownKeys (Spec)
open CtxRomAuth
variable (m0 m1 : Pqxdh.Bytes)

/-- A program is stable for a view when it is twin to itself with outputs related by equal views: for every pair of identified raw replies the viewed outputs agree. -/
def Stable {α γ : Type} (V : α → γ) (x : OracleComp Spec α) : Prop :=
  Twin m0 m1 (fun a b => V a = V b) (fun _ => False) (fun _ => False) x x

/-- Raw-free programs are stable for every view. -/
theorem stable_rawfree {α γ : Type} (V : α → γ) (x : OracleComp Spec α) (noRaw : x.IsQueryBoundP IsRaw 0) : Stable m0 m1 V x := by
  have twin := twin_map m0 m1 (twin_refl m0 m1 (Dead := fun _ => False) x noRaw) id id
    (Out' := fun a b => V a = V b) (Dead0' := fun _ => False) (Dead1' := fun _ => False)
    (fun a b same => by rw [same]) (fun _ h => h) (fun _ h => h)
  simp only [id_map] at twin
  exact twin

/-- Pure programs are stable. -/
theorem stable_pure {α γ : Type} (V : α → γ) (a : α) : Stable m0 m1 V (pure a) := Twin.pure rfl

/-- Stability through a map is stability for the composed view. -/
theorem stable_map {α β γ : Type} (V : β → γ) (f : α → β) (x : OracleComp Spec α) (stable : Stable m0 m1 (V ∘ f) x) :
    Stable m0 m1 V (f <$> x) :=
  twin_map m0 m1 stable f f (fun _ _ same => same) (fun _ h => h) (fun _ h => h)

/-- A raw-free prefix followed by stable continuations is stable. -/
theorem stable_bind {α β γ : Type} (V : β → γ) (x : OracleComp Spec α) (noRaw : x.IsQueryBoundP IsRaw 0)
    (f : α → OracleComp Spec β) (stable : ∀ a, Stable m0 m1 V (f a)) : Stable m0 m1 V (x >>= f) :=
  twin_bind m0 m1 (twin_refl m0 m1 (Dead := fun _ => False) x noRaw) (fun a _ same => same ▸ stable a)
    (fun _ h => h.elim) (fun _ h => h.elim)

/-- One raw opening whose viewed result identifies identified replies is stable. -/
theorem stable_raw {α γ : Type} (V : α → γ) (raw : Pqxdh.Bytes) (g : Option Pqxdh.Bytes → α)
    (invariant : ∀ r0 r1, Option.map (ident m0 m1) r0 = Option.map (ident m0 m1) r1 → V (g r0) = V (g r1)) :
    Stable m0 m1 V (g <$> (Spec.query (rawQuery raw) : OracleComp Spec _)) := by
  rw [map_eq_bind_pure_comp]
  exact Twin.raw raw fun r0 r1 related => Twin.pure (invariant r0 r1 related)

/-- One quiet request followed by a map is stable. -/
theorem stable_quiet {α γ : Type} (V : α → γ) (q : Spec.Domain) (quiet : Quiet q) (g : Spec.Range q → α) :
    Stable m0 m1 V (g <$> (Spec.query q : OracleComp Spec _)) := by
  rw [map_eq_bind_pure_comp]
  exact Twin.quiet q quiet fun r => Twin.pure rfl

/-- One raw opening is stable for every view that identifies identified replies. -/
theorem stable_query_raw {γ : Type} (V : Option Pqxdh.Bytes → γ) (raw : Pqxdh.Bytes)
    (invariant : ∀ r0 r1, Option.map (ident m0 m1) r0 = Option.map (ident m0 m1) r1 → V r0 = V r1) :
    Stable m0 m1 V (Spec.query (rawQuery raw) : OracleComp Spec _) := by
  have stable := stable_raw m0 m1 V raw id invariant
  simp only [id_map] at stable
  exact stable

/-- One quiet request is stable. -/
theorem stable_query_quiet {γ : Type} (q : Spec.Domain) (V : Spec.Range q → γ) (quiet : Quiet q) :
    Stable m0 m1 V (Spec.query q : OracleComp Spec _) := by
  have stable := stable_quiet m0 m1 V q quiet id
  simp only [id_map] at stable
  exact stable

end Stable

section RawFree
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxGenericRoleStorage
open AdaptiveCtxDynamicKnownKeys (Spec)
open AdaptiveCtxDynamicKnownBounds (TargetClass)
variable {M P I D K : Type} {S B : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)

/-- A selected raw-opening bound in the target classification is a raw-opening bound. -/
theorem raw_of_target {α : Type} (x : OracleComp Spec α)
    (bound : x.IsQueryBoundP (TargetClass AdaptiveCtxReceive.IsRawQuery) 0) : x.IsQueryBoundP IsRaw 0 :=
  IsQueryBoundP.of_imp (fun q holds => by
    rcases q with ((coin | (hash | input)) | raw) | known <;>
      simp_all [IsRaw, TargetClass, AdaptiveCtxReceive.IsRawQuery]) bound

/-- A compiled send makes no selected raw opening. -/
theorem send_raw (kernel : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :
    (RawCtxSelectedSendCompiler.send source writer prior parent target nonce next kernel context).IsQueryBoundP IsRaw 0 := by
  apply raw_of_target
  rw [RawCtxSelectedSendCompiler.send_cases]
  split
  · trivial
  · rw [isQueryBoundP_map_iff]
    exact (RawCtxSelectedSealConsumer.sealing_bills _ _ _).2.2.1

/-- A compiled owner send makes no selected raw opening. -/
theorem owner_send_raw {Metadata : Type} (senderId : Std.U64) (plaintext : Pqxdh.Bytes)
    (before : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) :
    (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read senderId (.inl plaintext) before).IsQueryBoundP
      IsRaw 0 := by
  rw [RawCtxSelectedOwnerCompiler.send_cases]
  split
  · trivial
  · rw [isQueryBoundP_map_iff]
    exact send_raw source writer prior parent target nonce next _ _

/-- A compiled Beacon send makes no selected raw opening. -/
theorem beacon_send_raw (plaintext : Pqxdh.Bytes) (before : BeaconState RawCtxSelectedMessageReveals.Kernel I D K) :
    (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read (.inl plaintext) before).IsQueryBoundP
      IsRaw 0 := by
  rw [RawCtxSelectedRoleCompiler.beacon_cases]
  split
  · rw [isQueryBoundP_map_iff]
    exact owner_send_raw source writer prior parent target nonce next read _ _ _
  · trivial

/-- A compiled Server send makes no selected raw opening. -/
theorem server_send_raw (plaintext : Pqxdh.Bytes) (kid : Std.U64) (before : ServerState RawCtxSelectedMessageReveals.Kernel M P) :
    (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inl (plaintext, kid))
      before).IsQueryBoundP IsRaw 0 := by
  rw [RawCtxSelectedRoleCompiler.server_send_cases]
  split
  · trivial
  · split
    · trivial
    · rw [isQueryBoundP_map_iff]
      exact owner_send_raw source writer prior parent target nonce next read _ _ _

/-- Public work makes no selected raw opening. -/
theorem public_raw (request : RawCtxServerServices.PublicSpec.Domain) :
    (RawCtxSelectedFamilyCompiler.publicWork source request).IsQueryBoundP IsRaw 0 := by
  rcases request with coin | bytes | request
  · simp [RawCtxSelectedFamilyCompiler.publicWork, IsRaw]
  · simp [RawCtxSelectedFamilyCompiler.publicWork, IsRaw]
  · trivial

/-- The raw receives of the role family. -/
def FamilyReceive : (RawCtxProtocolRoles.SourceSpec S B).Domain → Prop
  | .inl ⟨_, .inr _⟩ => True
  | .inr (.inl ⟨_, .inr _⟩) => True
  | _ => False

/-- A compiled role request other than a raw receive makes no selected raw opening. -/
theorem family_raw (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (notReceive : ¬ FamilyReceive query)
    (before : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B) :
    (RawCtxSelectedFamilyCompiler.family source writer prior parent target nonce next sender route read query before).IsQueryBoundP
      IsRaw 0 := by
  rw [RawCtxSelectedFamilyCompiler.family_cases]
  rcases query with ⟨index, (⟨plaintext, kid⟩ | raw)⟩ | (⟨index, (plaintext | raw)⟩ | request)
  · rw [isQueryBoundP_map_iff]
    exact server_send_raw source writer prior parent target nonce next sender route read _ _ _
  · exact absurd trivial notReceive
  · rw [isQueryBoundP_map_iff]
    exact beacon_send_raw source writer prior parent target nonce next read _ _
  · exact absurd trivial notReceive
  · rw [isQueryBoundP_map_iff]
    exact public_raw source request

end RawFree

section ReceiveStable
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxGenericRoleStorage
open AdaptiveCtxDynamicKnownKeys (Spec)
open ratchet.refined
variable (m0 m1 : Pqxdh.Bytes)

/-- Identified decrypted replies: equal, or two present replies with the same key identifier and sequence whose plaintexts are identified. -/
def DecRel (d0 d1 : core.option.Option RawCtxWholeOwner.Decrypted) : Prop :=
  d0 = d1 ∨ ∃ p0 p1 keyId sequence, d0 = .Some ⟨p0, keyId, sequence⟩ ∧ d1 = .Some ⟨p1, keyId, sequence⟩ ∧
    ident m0 m1 p0 = ident m0 m1 p1

/-- A finished opening's kernel depends only on whether a plaintext was returned. -/
theorem finish_kernel {Material Context Plaintext : Type}
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Material Context) (d0 d1 : Plaintext) :
    (RawCtxInterpretedReceive.normalFinish pending (core.option.Option.Some d0)).1 =
      (RawCtxInterpretedReceive.normalFinish pending (core.option.Option.Some d1)).1 := by
  have e0 := RawCtxInterpretedReceive.normalFinish_exact pending (core.option.Option.Some d0)
  have e1 := RawCtxInterpretedReceive.normalFinish_exact pending (core.option.Option.Some d1)
  simp only [RawCtxInterpretedOpening.finish] at e0 e1
  cases hprep : pending.prepared with
  | PreparedReceiveCachedCase prepared =>
    simp only [hprep] at e0 e1
    cases hpub : publish_cached_receive pending.entry prepared with
    | ok published =>
      simp only [hpub, bind_tc_ok] at e0 e1
      rw [← RustM.ok.inj e0, ← RustM.ok.inj e1]
    | fail error => simp [hpub] at e0
    | div => simp [hpub] at e0
  | PreparedReceiveFutureCase future =>
    simp only [hprep] at e0 e1
    cases hpub : publish_future_receive pending.entry future with
    | ok published =>
      simp only [hpub, bind_tc_ok] at e0 e1
      rw [← RustM.ok.inj e0, ← RustM.ok.inj e1]
    | fail error => simp [hpub] at e0
    | div => simp [hpub] at e0

/-- Identified raw replies give identified decrypted replies. -/
theorem apiReply_rel (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext) (r0 r1 : Option Pqxdh.Bytes)
    (related : Option.map (ident m0 m1) r0 = Option.map (ident m0 m1) r1) :
    DecRel m0 m1 (RawCtxSharedOpeningConsumer.apiReply sequence context r0) (RawCtxSharedOpeningConsumer.apiReply sequence context r1) := by
  cases r0 with
  | none =>
    cases r1 with
    | none => exact Or.inl rfl
    | some p1 => simp at related
  | some p0 =>
    cases r1 with
    | none => simp at related
    | some p1 =>
      right
      exact ⟨p0, p1, context.frame.sender, sequence, rfl, rfl, by simpa using related⟩

set_option backward.isDefEq.respectTransparency false in
/-- A compiled receive is stable for every view that identifies identified decrypted replies with the same kernel. -/
theorem receive_stable {γ : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput)
    (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (V : RawCtxSelectedMessageReveals.Kernel × core.option.Option RawCtxWholeOwner.Decrypted → γ)
    (invariant : ∀ k d0 d1, DecRel m0 m1 d0 d1 → V (k, d0) = V (k, d1)) :
    Stable m0 m1 V (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read expected kernel sequence context) := by
  simp only [RawCtxSelectedReceiveCompiler.receive, RawCtxSelectedMessageDriver.receive, ← QueryImpl.simulateQ_compose,
    RawCtxInterpretedReceive.receive]
  change Stable m0 m1 V (simulateQ (RawCtxSelectedReceiveCompiler.compiler prior parent target nonce next read expected)
    (RawCtxInterpretedReceive.program (RawCtxInterpretedReceive.normalBegin kernel sequence context)))
  rw [RawCtxSelectedReceiveReceipt.program_terminal]
  split
  · exact stable_pure m0 m1 V _
  · rename_i pending _
    apply stable_map
    unfold RawCtxSelectedOpenConsumer.service
    split
    · exact stable_pure m0 m1 _ _
    · rename_i input _
      apply stable_map
      unfold RawCtxUniversalOpening.call
      split
      · split
        · refine stable_query_raw m0 m1 _ _ fun r0 r1 related => ?_
          have decrypted := apiReply_rel m0 m1 input.sequence input.context r0 r1 related
          simp only [Function.comp_apply]
          rcases decrypted with same | ⟨p0, p1, keyId, seq, h0, h1, identified⟩
          · rw [same]
          · rw [h0, h1]
            change V ((RawCtxInterpretedReceive.normalFinish pending
                (core.option.Option.Some (⟨p0, keyId, seq⟩ : RawCtxWholeOwner.Decrypted))).1,
                core.option.Option.Some (⟨p0, keyId, seq⟩ : RawCtxWholeOwner.Decrypted)) =
              V ((RawCtxInterpretedReceive.normalFinish pending
                (core.option.Option.Some (⟨p1, keyId, seq⟩ : RawCtxWholeOwner.Decrypted))).1,
                core.option.Option.Some (⟨p1, keyId, seq⟩ : RawCtxWholeOwner.Decrypted))
            rw [finish_kernel pending (⟨p0, keyId, seq⟩ : RawCtxWholeOwner.Decrypted) ⟨p1, keyId, seq⟩]
            exact invariant _ _ _ (Or.inr ⟨p0, p1, keyId, seq, rfl, rfl, identified⟩)
        · exact stable_pure m0 m1 _ _
      · unfold RawCtxSelectedMessageOpening.call
        simp only
        exact stable_query_quiet m0 m1 (Sum.inr ⟨0, RawCtxSourceOpen.sourceKey ⟨_, input.sequence, input.context⟩,
          RawCtxKeyFreeDecoder.decoder (RawCtxSourceOpen.sourceNonce ⟨_, input.sequence, input.context⟩) expected
            input.context.associatedData read, Sum.inr input.context.raw⟩) _ trivial

/-- A compiled raw delivery to an owner is stable for every view that identifies identified decrypted replies with the same owner. -/
theorem raw_stable {γ Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput)
    (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata)
    (V : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata → γ)
    (invariant : ∀ st d0 d1, DecRel m0 m1 d0 d1 → V (d0, st) = V (d1, st)) :
    Stable m0 m1 V (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner) := by
  simp only [RawCtxSelectedReceiveCompiler.raw, RawCtxChainOwner.rawReceive, StateT.run]
  split
  · exact stable_pure m0 m1 V _
  · split
    · exact stable_pure m0 m1 V _
    · split
      · rw [bind_pure_comp]
        apply stable_map
        exact receive_stable m0 m1 prior parent target nonce next read _ _ _ _ _
          fun k d0 d1 related => invariant _ d0 d1 related
      · exact stable_pure m0 m1 V _

/-- A compiled owner raw receive is stable for every view that identifies identified decrypted replies with the same owner. -/
theorem owner_raw_stable {γ Metadata : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput)
    (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (senderId : Std.U64) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata)
    (V : Option (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata) → γ)
    (invariant : ∀ st d0 d1, DecRel m0 m1 d0 d1 → V (some (d0, st)) = V (some (d1, st))) :
    Stable m0 m1 V (RawCtxSelectedOwnerCompiler.owner source writer prior parent target nonce next read senderId (.inr bytes) owner) := by
  rw [RawCtxSelectedOwnerCompiler.raw_cases]
  apply stable_map
  exact raw_stable m0 m1 prior parent target nonce next read bytes owner _ fun st d0 d1 related => invariant st d0 d1 related

/-- A compiled Server raw receive is stable for every view that identifies identified decrypted replies with the same Server state. -/
theorem server_raw_stable {γ M P : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (bytes : Pqxdh.Bytes) (before : ServerState RawCtxSelectedMessageReveals.Kernel M P)
    (V : Option (core.option.Option RawCtxWholeOwner.Decrypted × ServerState RawCtxSelectedMessageReveals.Kernel M P) → γ)
    (invariant : ∀ st d0 d1, DecRel m0 m1 d0 d1 → V (some (d0, st)) = V (some (d1, st))) :
    Stable m0 m1 V (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read (.inr bytes)
      before) := by
  rw [RawCtxSelectedRoleCompiler.server_raw_cases]
  split
  · exact stable_pure m0 m1 V _
  · split
    · exact stable_pure m0 m1 V _
    · split
      · exact stable_pure m0 m1 V _
      · apply stable_map
        exact owner_raw_stable m0 m1 source writer prior parent target nonce next read _ bytes _ _
          fun st d0 d1 related => invariant _ d0 d1 related

/-- A compiled Beacon raw receive is stable for every view that identifies identified decrypted replies with the same Beacon state. -/
theorem beacon_raw_stable {γ I D K : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes) (before : BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (V : Option (core.option.Option RawCtxWholeOwner.Decrypted × BeaconState RawCtxSelectedMessageReveals.Kernel I D K) → γ)
    (invariant : ∀ st d0 d1, DecRel m0 m1 d0 d1 → V (some (d0, st)) = V (some (d1, st))) :
    Stable m0 m1 V (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read (.inr bytes) before) := by
  rw [RawCtxSelectedRoleCompiler.beacon_cases]
  split
  · apply stable_map
    exact owner_raw_stable m0 m1 source writer prior parent target nonce next read _ bytes _ _
      fun st d0 d1 related => invariant _ d0 d1 related
  · exact stable_pure m0 m1 V _


end ReceiveStable

section StepTwin
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedFirstRecord RawCtxGenericRoleStorage
open AdaptiveCtxDynamicKnownKeys (Spec)
variable {ι I D K X Response Shared A N C M P : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (mark : PqxdhBeaconPhase2Shared.Secrets Shared → Bool) (b : Fin B)

set_option backward.isDefEq.respectTransparency false in
/-- One forwarded adversary request: the instrumented step with the wrapper's screening and bookkeeping. -/
theorem adv_run (β : Bool) (request : (ConfPostSpec extra S B).Domain) (c : ConfState) (s : InsState M P I D K A N C S B) :
    runStepper (confIns b β (insImpl pre application initial selector aux source writer prior none target nonce next sender route read
      mark b) (.inl request)) c s =
      (fun z => (z.1.map (fun reply => (screen c request reply, observe b c request reply)), z.2)) <$>
        ((insImpl pre application initial selector aux source writer prior none target nonce next sender route read mark b
          request).run).run s := by
  have conf : (confImpl (extra := extra) (S := S) b β (.inl request)).run c =
      ((liftM ((ConfPostSpec extra S B).query request) : OracleComp (ConfPostSpec extra S B) _) >>= fun reply =>
        pure (screen c request reply, observe b c request reply)) := rfl
  simp only [runStepper, confIns, StateT.run_mk, conf]
  rw [simulateQ_bind]
  simp only [simulateQ_query, simulateQ_pure, OptionT.run_bind, Option.elimM, StateT.run_bind, map_eq_bind_pure_comp]
  rw [bind_assoc]
  congr 1
  funext z
  rcases z with ⟨_ | reply, s'⟩ <;> rfl

/-- Distinct identified plaintexts are the two challenge plaintexts. -/
theorem ident_pair (m0 m1 p0 p1 : Pqxdh.Bytes) (same : ident m0 m1 p0 = ident m0 m1 p1) (distinct : p0 ≠ p1) :
    (p0 = m0 ∨ p0 = m1) ∧ (p1 = m0 ∨ p1 = m1) := by
  unfold ident at same
  split_ifs at same with h0 h1 h1
  · exact absurd (h0.trans h1.symm) distinct
  · exact ⟨Or.inr h0, Or.inl same.symm⟩
  · exact ⟨Or.inl same, Or.inr h1⟩
  · exact absurd same distinct

/-- Screening with the challenge pair identifies identified decrypted replies. -/
theorem suppress_rel (m0 m1 : Pqxdh.Bytes) (d0 d1 : core.option.Option RawCtxWholeOwner.Decrypted) (related : DecRel m0 m1 d0 d1) :
    suppress (some (m0, m1)) d0 = suppress (some (m0, m1)) d1 := by
  rcases related with same | ⟨p0, p1, keyId, sequence, rfl, rfl, identified⟩
  · rw [same]
  · by_cases equal : p0 = p1
    · rw [equal]
    · obtain ⟨left, right⟩ := ident_pair m0 m1 p0 p1 identified equal
      simp only [suppress, left, right, ite_true]

/-- Adversary requests keep the challenge pair. -/
theorem observe_pair (c : ConfState) (request : (ConfPostSpec extra S B).Domain) (reply : (ConfPostSpec extra S B).Range request) :
    (observe b c request reply).pair = c.pair := by
  unfold observe
  split
  · split_ifs <;> rfl
  · rfl

/-- A raw receive of a role leaves the transcript unchanged. -/
theorem traceRecord_server_receive (t : PqxdhInitialOriginPost.Trace Bool S B) (index : Fin S) (raw : Pqxdh.Bytes)
    (d : core.option.Option RawCtxWholeOwner.Decrypted) :
    traceRecord t (.inl (.inl ⟨index, .inr raw⟩)) (some d) = t := by
  simp [traceRecord, PqxdhInitialOriginPost.record, RawCtxPublishedRecords.record]

/-- A raw receive of a Beacon leaves the transcript unchanged. -/
theorem traceRecord_beacon_receive (t : PqxdhInitialOriginPost.Trace Bool S B) (index : Fin B) (raw : Pqxdh.Bytes)
    (d : core.option.Option RawCtxWholeOwner.Decrypted) :
    traceRecord t (.inl (.inr (.inl ⟨index, .inr raw⟩))) (some d) = t := by
  simp [traceRecord, PqxdhInitialOriginPost.record, RawCtxPublishedRecords.record]



/-- A Server raw receive reply is screened by the challenge pair. -/
theorem screen_server_receive (c : ConfState) (index : Fin S) (raw : Pqxdh.Bytes)
    (d : core.option.Option RawCtxWholeOwner.Decrypted) :
    screen (extra := extra) (B := B) c (.inl (.inl (.inl (.inl ⟨index, .inr raw⟩)))) d = suppress c.pair d := rfl

/-- A Beacon raw receive reply is screened by the challenge pair. -/
theorem screen_beacon_receive (c : ConfState) (index : Fin B) (raw : Pqxdh.Bytes)
    (d : core.option.Option RawCtxWholeOwner.Decrypted) :
    screen (extra := extra) (S := S) c (.inl (.inl (.inl (.inr (.inl ⟨index, .inr raw⟩))))) d = suppress c.pair d := rfl

/-- A Server raw receive leaves the wrapper record unchanged. -/
theorem observe_server_receive (c : ConfState) (index : Fin S) (raw : Pqxdh.Bytes)
    (d : core.option.Option RawCtxWholeOwner.Decrypted) :
    observe (extra := extra) (S := S) b c (.inl (.inl (.inl (.inl ⟨index, .inr raw⟩)))) d = c := rfl

/-- A Beacon raw receive leaves the wrapper record unchanged. -/
theorem observe_beacon_receive (c : ConfState) (index : Fin B) (raw : Pqxdh.Bytes)
    (d : core.option.Option RawCtxWholeOwner.Decrypted) :
    observe (extra := extra) (S := S) b c (.inl (.inl (.inl (.inr (.inl ⟨index, .inr raw⟩))))) d = c := rfl

/-- A stable forwarded step gives twin wrapper steps that keep the challenge pair. -/
theorem twin_of_stable (m0 m1 : Pqxdh.Bytes) (request : (ConfPostSpec extra S B).Domain) (c : ConfState)
    (paired : c.pair = some (m0, m1))
    (x : OracleComp Spec (Option ((ConfPostSpec extra S B).Range request) × InsState M P I D K A N C S B))
    (stable : Stable m0 m1 (fun z => (z.1.map (fun reply => (screen c request reply, observe b c request reply)), z.2)) x) :
    Twin m0 m1 (fun z0 z1 => z0 = z1 ∧ ∀ (reply : (AdvSpec extra S B).Range (.inl request)) c',
        z0.1 = some (reply, c') → c'.pair = some (m0, m1))
      (fun z => InsDead z.2) (fun z => InsDead z.2)
      ((fun z => (z.1.map (fun reply => (screen c request reply, observe b c request reply)), z.2)) <$> x)
      ((fun z => (z.1.map (fun reply => (screen c request reply, observe b c request reply)), z.2)) <$> x) := by
  refine twin_map m0 m1 stable _ _ (fun a₀ a₁ same => ⟨same, ?_⟩) (fun _ h => h.elim) (fun _ h => h.elim)
  intro reply c' holds
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at holds
  obtain ⟨answer, _, _, rfl⟩ := holds
  rw [observe_pair b c request answer, paired]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every step after an accepted challenge is twin: refused challenges and raw-free requests are identical, raw receives return identified plaintexts only as screened failures with identical states, and a Beacon finish that makes a selected raw opening raises the dead flag. -/
theorem step_twin (m0 m1 : Pqxdh.Bytes) (q : (AdvSpec extra S B).Domain) (c : ConfState) (s : InsState M P I D K A N C S B)
    (paired : c.pair = some (m0, m1)) (alive : ¬ InsDead s) :
    Twin m0 m1 (fun z0 z1 => z0 = z1 ∧ ∀ reply c', z0.1 = some (reply, c') → c'.pair = some (m0, m1))
      (fun z => InsDead z.2) (fun z => InsDead z.2)
      (runStepper (confIns b false (insImpl pre application initial selector aux source writer prior none target nonce next sender
        route read mark b) q) c s)
      (runStepper (confIns b true (insImpl pre application initial selector aux source writer prior none target nonce next sender
        route read mark b) q) c s) := by
  rcases q with request | ⟨x0, x1⟩
  · rw [adv_run pre application initial selector aux source writer prior target nonce next sender route read mark b false request c s,
      adv_run pre application initial selector aux source writer prior target nonce next sender route read mark b true request c s]
    rcases request with (record | ext) | ⟨index, raw⟩
    · refine twin_of_stable b m0 m1 _ c paired _ ?_
      simp only [insImpl, OptionT.run_mk, StateT.run]
      apply stable_map
      rcases record with family | reveal
      · simp only [RawCtxSelectedFamilyLiveCompiler.impl, OptionT.run_mk]
        apply stable_map
        by_cases receive : FamilyReceive family
        · rcases family with ⟨index, (⟨plaintext, kid⟩ | raw)⟩ | (⟨index, (plaintext | raw)⟩ | request)
          · exact absurd receive id
          · rw [RawCtxSelectedFamilyCompiler.family_cases]
            apply stable_map
            refine server_raw_stable m0 m1 source writer prior none target nonce next sender route read raw _ _ ?_
            intro st d0 d1 related
            simp only [Function.comp_apply, Option.map_some, RawCtxSelectedFamilyLiveCompiler.publish, traceRecord_server_receive,
              screen_server_receive, observe_server_receive, paired]
            rw [suppress_rel m0 m1 d0 d1 related]
          · exact absurd receive id
          · rw [RawCtxSelectedFamilyCompiler.family_cases]
            apply stable_map
            refine beacon_raw_stable m0 m1 source writer prior none target nonce next read raw _ _ ?_
            intro st d0 d1 related
            simp only [Function.comp_apply, Option.map_some, RawCtxSelectedFamilyLiveCompiler.publish, traceRecord_beacon_receive,
              screen_beacon_receive, observe_beacon_receive, paired]
            rw [suppress_rel m0 m1 d0 d1 related]
          · exact absurd receive id
        · exact stable_rawfree m0 m1 _ _
            (family_raw source writer prior none target nonce next sender route read family receive _)
      · exact stable_pure m0 m1 _ _
    · refine twin_of_stable b m0 m1 _ c paired _ ?_
      simp only [insImpl, OptionT.run_mk, StateT.run]
      refine stable_rawfree m0 m1 _ _ ?_
      rw [isQueryBoundP_map_iff]
      exact raw_of_target _ (PqxdhSelectedInitialOwnerCompiler.external_no_open pre application initial selector aux _ _)
    · have flag : s.2.2.2 = false := by
        cases h : s.2.2.2 with
        | false => rfl
        | true => exact absurd (Or.inr h) alive
      simp only [insImpl, OptionT.run_mk, StateT.run, Functor.map_map, flag]
      refine twin_map m0 m1 (twin_markRaw m0 m1 _ false) _ _ ?_ ?_ ?_
      · rintro a _ rfl
        refine ⟨rfl, ?_⟩
        intro reply c' holds
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at holds
        rw [← holds.2]
        exact paired
      · intro a flagged
        exact Or.inr flagged
      · intro a flagged
        exact Or.inr flagged
  · have refused : c.pair.isSome ∨ c.beaconSent ∨ x0.length ≠ x1.length := Or.inl (by simp [paired])
    have stop : ∀ β, runStepper (confIns b β (insImpl pre application initial selector aux source writer prior none target nonce next
        sender route read mark b) (.inr (x0, x1))) c s = pure (some (none, c), s) := by
      intro β
      have run : (confImpl (extra := extra) (S := S) b β (.inr (x0, x1))).run c =
          (pure ((none : Option RawCtxSourceSend.Encrypted), c) :
            OracleComp (ConfPostSpec extra S B) (Option RawCtxSourceSend.Encrypted × ConfState)) := by
        simp only [confImpl, StateT.run]
        rw [ite_eq_left_iff.mpr fun impossible => absurd refused impossible]
      simp only [runStepper, confIns, StateT.run_mk, run, simulateQ_pure]
      rfl
    rw [stop false, stop true]
    refine Twin.pure ⟨rfl, ?_⟩
    intro reply c' holds
    simp only [Option.some.injEq, Prod.mk.injEq] at holds
    rw [← holds.2]
    exact paired


/-- The monitor value after one instrumented request. -/
noncomputable def monitorAfter (request : (ConfPostSpec extra S B).Domain) (front : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (hidden : Option Bool) : Option Bool :=
  match request with
  | .inl (.inl record) => hiddenStep b target record front hidden
  | _ => hidden

/-- Every instrumented step records the monitor value `monitorAfter`. -/
theorem ins_monitor (request : (ConfPostSpec extra S B).Domain) (s : InsState M P I D K A N C S B)
    (w : Option ((ConfPostSpec extra S B).Range request) × InsState M P I D K A N C S B)
    (supported : w ∈ support (((insImpl pre application initial selector aux source writer prior none target nonce next sender route
      read mark b request).run).run s)) :
    w.2.2.2.1 = monitorAfter target b request s.1.1 s.2.2.1 := by
  rcases request with (record | ext) | ⟨index, raw⟩
  all_goals
    simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, _, rfl⟩ := supported
    rfl

/-- A raised finish flag stays raised through every instrumented step. -/
theorem ins_flag (request : (ConfPostSpec extra S B).Domain) (s : InsState M P I D K A N C S B) (raised : s.2.2.2 = true)
    (w : Option ((ConfPostSpec extra S B).Range request) × InsState M P I D K A N C S B)
    (supported : w ∈ support (((insImpl pre application initial selector aux source writer prior none target nonce next sender route
      read mark b request).run).run s)) :
    w.2.2.2.2 = true := by
  rcases request with (record | ext) | ⟨index, raw⟩
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, _, rfl⟩ := supported
    exact raised
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, _, rfl⟩ := supported
    exact raised
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image, raised] at supported
    obtain ⟨result, inner, rfl⟩ := supported
    exact markRaw_sticky _ result inner

/-- A recorded monitor value stays recorded. -/
theorem monitorAfter_some (request : (ConfPostSpec extra S B).Domain) (front : PqxdhSelectedPostCompiler.Front M P I D K S B)
    (value : Bool) : monitorAfter target b request front (some value) = some value := by
  rcases request with (record | ext) | fin
  · simp only [monitorAfter, hiddenStep]
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Dead instrumented states stay dead through every wrapper step. -/
theorem ins_sticky (β : Bool) (q : (AdvSpec extra S B).Domain) (c : ConfState) (s : InsState M P I D K A N C S B)
    (dead : InsDead s) (z : Option ((AdvSpec extra S B).Range q × ConfState) × InsState M P I D K A N C S B)
    (supported : z ∈ support (runStepper (confIns b β (insImpl pre application initial selector aux source writer prior none target
      nonce next sender route read mark b) q) c s)) :
    InsDead z.2 := by
  have step : ∀ (request : (ConfPostSpec extra S B).Domain) (w : Option ((ConfPostSpec extra S B).Range request) × InsState M P I D K A N C S B),
      w ∈ support (((insImpl pre application initial selector aux source writer prior none target nonce next sender route read mark b
        request).run).run s) → InsDead w.2 := by
    intro request w hw
    rcases dead with hidden | raised
    · left
      rw [ins_monitor pre application initial selector aux source writer prior target nonce next sender route read mark b request s w hw,
        hidden, monitorAfter_some]
    · right
      exact ins_flag pre application initial selector aux source writer prior target nonce next sender route read mark b request s raised
        w hw
  rcases q with request | ⟨x0, x1⟩
  · rw [adv_run pre application initial selector aux source writer prior target nonce next sender route read mark b β request c s,
      support_map] at supported
    obtain ⟨w, hw, rfl⟩ := supported
    exact step request w hw
  · by_cases refused : c.pair.isSome ∨ c.beaconSent ∨ x0.length ≠ x1.length
    · have run : (confImpl (extra := extra) (S := S) b β (.inr (x0, x1))).run c =
          (pure ((none : Option RawCtxSourceSend.Encrypted), c) :
            OracleComp (ConfPostSpec extra S B) (Option RawCtxSourceSend.Encrypted × ConfState)) := by
        simp only [confImpl, StateT.run]
        rw [ite_eq_left_iff.mpr fun impossible => absurd refused impossible]
      have stop : runStepper (confIns b β (insImpl pre application initial selector aux source writer prior none target nonce next
          sender route read mark b) (.inr (x0, x1))) c s = pure (some (none, c), s) := by
        simp only [runStepper, confIns, StateT.run_mk, run, simulateQ_pure]
        rfl
      rw [stop, support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
      exact dead
    · simp only [not_or, Bool.not_eq_true, not_not] at refused
      obtain ⟨unpaired, sent, equal⟩ := refused
      have none' : c.pair = none := by
        cases hc : c.pair with
        | none => rfl
        | some v => simp [hc] at unpaired
      rw [challenge_run pre application initial selector aux source writer prior target nonce next sender route read mark b β x0 x1 c s
        none' sent equal, support_map] at supported
      obtain ⟨w, hw, rfl⟩ := supported
      exact step _ w hw


/-- While the wrapper has seen no send of Beacon `b`, the monitor records nothing. -/
theorem observe_monitor (c : ConfState) (request : (ConfPostSpec extra S B).Domain) (r : (ConfPostSpec extra S B).Range request)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (hidden : Option Bool)
    (sent' : (observe b c request r).beaconSent = false) (link : c.beaconSent = false → hidden = none) :
    monitorAfter target b request front hidden = none := by
  rcases request with (((⟨i, (⟨p, kid⟩ | raw)⟩ | (⟨i, (p | raw)⟩ | pub)) | reveal) | ext) | fin
  all_goals first
    | (have none' := link sent'
       subst none'
       simp [monitorAfter, hiddenStep])
    | skip
  by_cases same : i = b
  · simp [observe, same] at sent'
  · have none' := link (by simpa [observe, same] using sent')
    subst none'
    simp [monitorAfter, hiddenStep, same]

set_option backward.isDefEq.respectTransparency false in
/-- Adversary requests keep the challenge pair and the link between the wrapper record and the monitor. -/
theorem ins_keep (request : (ConfPostSpec extra S B).Domain) (c : ConfState) (s : InsState M P I D K A N C S B) (link : InsLink c s)
    (z : Option ((AdvSpec extra S B).Range (.inl request) × ConfState) × InsState M P I D K A N C S B)
    (supported : z ∈ support (runStepper (confIns b false (insImpl pre application initial selector aux source writer prior none target
      nonce next sender route read mark b) (.inl request)) c s))
    (reply : (AdvSpec extra S B).Range (.inl request)) (c' : ConfState) (reached : z.1 = some (reply, c')) :
    c'.pair = c.pair ∧ InsLink c' z.2 := by
  rw [adv_run pre application initial selector aux source writer prior target nonce next sender route read mark b false request c s,
    support_map] at supported
  obtain ⟨w, hw, rfl⟩ := supported
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at reached
  obtain ⟨r, _, _, rfl⟩ := reached
  refine ⟨observe_pair b c request r, ?_⟩
  intro sent'
  rw [ins_monitor pre application initial selector aux source writer prior target nonce next sender route read mark b request s w hw]
  exact observe_monitor target b c request r s.1.1 s.2.2.1 sent' link


/-- The two instrumented wrapper runs from a linked state without a challenge are adaptive twins. -/
theorem ins_post_pre {α : Type} (X : OracleComp (AdvSpec extra S B) α) (c : ConfState) (s : InsState M P I D K A N C S B)
    (link : InsLink c s) (fresh : c.pair = none) :
    Pre (fun a b => a = b) (fun z => InsDead z.2) (fun z => InsDead z.2)
      (runStepper (simulateQ (confIns b false (insImpl pre application initial selector aux source writer prior none target nonce next
        sender route read mark b)) X) c s)
      (runStepper (simulateQ (confIns b true (insImpl pre application initial selector aux source writer prior none target nonce next
        sender route read mark b)) X) c s) :=
  pre_run b (insImpl pre application initial selector aux source writer prior none target nonce next sender route read mark b)
    InsDead InsLink
    (fun request c s link z supported reply c' reached =>
      ins_keep pre application initial selector aux source writer prior target nonce next sender route read mark b request c s link z
        supported reply c' reached)
    (fun m0 m1 c s link fresh sent equal _ =>
      challenge_twin pre application initial selector aux source writer prior target nonce next sender route read mark b m0 m1 c s
        link fresh sent equal)
    (fun m0 m1 q c s paired alive =>
      step_twin pre application initial selector aux source writer prior target nonce next sender route read mark b m0 m1 q c s
        paired alive)
    (fun β q c s dead z supported =>
      ins_sticky pre application initial selector aux source writer prior target nonce next sender route read mark b β q c s dead z
        supported)
    X c s link fresh


end StepTwin

section FirstPre
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhFirstBeaconRecordCtx
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : PqxdhCorrelatedExtractFamily.Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

/-- The instrumented first runs of the two wrapper posts are adaptive twins: the builder is shared, and the wrapper runs are adaptive twins from the linked initial state. -/
theorem insFirstRun_pre {Selection : Type}
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (selection : Selection) :
    Pre (fun a b => a = b) (fun r => InsDead r.2) (fun r => InsDead r.2)
      (insFirstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
        metadata ready (confPost adversary b false selection) before selected shared privateState cache store nonce next b)
      (insFirstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode index
        metadata ready (confPost adversary b true selection) before selected shared privateState cache store nonce next b) := by
  unfold insFirstRun
  refine pre_bind_refl _ fun built _ => ?_
  rw [conf_post_run b false _ adversary selection built.1.1, conf_post_run b true _ adversary selection built.1.1]
  exact pre_map (ins_post_pre pre application initial selector aux source writer (productionStream source.crypto)
      (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode
      (PqxdhInitialSelectedOrigin.mark source selectedMessage) b (adversary selection built.1.1) confInitial _ (fun _ => rfl) rfl)
    _ _ (fun a₀ a₁ same => by rw [same]) (fun _ dead => dead) (fun _ dead => dead)

end FirstPre

section PreludeSame
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

/-- A completed preparation mode. -/
def CompletedMode (mode : PqxdhCommonSharedDispatch.Mode (PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K)
    (A := A) setup program)) : Prop :=
  ∃ decision, mode = .completed decision

/-- The forwarded dispatch of two posts is identical until it completes: posts run only in completed branches. -/
theorem dispatch_same (post0 post1 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (secret : KemSK) (output : PqxdhBorrowedSharedPrefix.LocalOutput (M := M) (P := P) (I := I) (K := K) (A := A) setup program) :
    Same (fun a b => a = b) (CompletedMode setup program) (CompletedMode setup program)
      (simulateQ RawCtxSourceSharedRom.forward (PqxdhCommonSharedDispatch.dispatch setup env callbacks program post0 attachedVerify
        primitives baseImpl kem secret output))
      (simulateQ RawCtxSourceSharedRom.forward (PqxdhCommonSharedDispatch.dispatch setup env callbacks program post1 attachedVerify
        primitives baseImpl kem secret output)) := by
  unfold PqxdhCommonSharedDispatch.dispatch
  dsimp only
  split_ifs with changed eligible
  · simp only [simulateQ_pure]
    exact Same.pure rfl
  · rw [simulateQ_bind, simulateQ_bind]
    refine same_bind (same_refl (Dead := fun _ => False) _) (fun a₀ a₁ same => ?_) (fun _ h => h.elim) (fun _ h => h.elim)
    subst same
    split
    · simp only [simulateQ_pure]
      exact Same.pure rfl
    · refine Same.dead ?_ ?_
      · intro mode supported
        simp only [simulateQ_bind, simulateQ_map, mem_support_bind_iff, support_map, Set.mem_image] at supported
        obtain ⟨_, _, decision, _, rfl⟩ := supported
        exact ⟨decision, rfl⟩
      · intro mode supported
        simp only [simulateQ_bind, simulateQ_map, mem_support_bind_iff, support_map, Set.mem_image] at supported
        obtain ⟨_, _, decision, _, rfl⟩ := supported
        exact ⟨decision, rfl⟩
  · refine Same.dead ?_ ?_
    · intro mode supported
      simp only [simulateQ_map, support_map, Set.mem_image] at supported
      obtain ⟨decision, _, rfl⟩ := supported
      exact ⟨decision, rfl⟩
    · intro mode supported
      simp only [simulateQ_map, support_map, Set.mem_image] at supported
      obtain ⟨decision, _, rfl⟩ := supported
      exact ⟨decision, rfl⟩

/-- The forwarded preludes of two posts are identical until the preparation completes. -/
theorem prelude_same (post0 post1 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) :
    Same (fun a b => a = b) (fun sample => CompletedMode setup program sample.1.state)
      (fun sample => CompletedMode setup program sample.1.state)
      (simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post0))
      (simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post1)) := by
  unfold prelude PqxdhSourceSharedPreparation.prepare PqxdhSourceSharedPreparation.run
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  refine same_bind (same_refl (Dead := fun _ => False) _) ?_ (fun _ h => h.elim) (fun _ h => h.elim)
  rintro pair _ rfl
  refine same_bind (same_refl (Dead := fun _ => False) _) ?_ (fun _ h => h.elim) (fun _ h => h.elim)
  rintro generated _ rfl
  refine same_bind (dispatch_same setup env callbacks baseImpl kem attachedVerify primitives program post0 post1 pair.2 generated)
    ?_ ?_ ?_
  · rintro state _ rfl
    exact same_refl _
  · intro state completed sample supported
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := supported
    exact completed
  · intro state completed sample supported
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := supported
    exact completed


end PreludeSame

section ClientPre
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

/-- The prepared inputs of two posts agree except for their post: completed packets give the same decision, pending packets the same input with the post of the same selection. -/
theorem input_relate (post0 post1 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (packet : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program) :
    (∃ decision, PqxdhSourceSharedInput.input setup env callbacks program post0 attachedVerify primitives baseImpl kem
        owner number ancestors disclosed packet = .inl decision ∧
      PqxdhSourceSharedInput.input setup env callbacks program post1 attachedVerify primitives baseImpl kem
        owner number ancestors disclosed packet = .inl decision ∧ CompletedMode setup program packet.state) ∨
    (∃ input selection, PqxdhSourceSharedInput.input setup env callbacks program post0 attachedVerify primitives baseImpl kem
        owner number ancestors disclosed packet = .inr input ∧
      PqxdhSourceSharedInput.input setup env callbacks program post1 attachedVerify primitives baseImpl kem
        owner number ancestors disclosed packet = .inr { input with post := post1 selection } ∧ input.post = post0 selection) := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  cases state with
  | completed decision => exact Or.inl ⟨decision, rfl, rfl, decision, rfl⟩
  | pending output ephemeral => exact Or.inr ⟨_, _, rfl, rfl, rfl⟩

/-- Completed packets give a completed input decision. -/
theorem input_completed (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (owner : RawCtxProtocolReveals.Owner S (B + 1)) (number : Std.U64) (ancestors disclosed : List RatchetChain)
    (packet : Packet (M := M) (P := P) (I := I) (K := K) (A := A) (KemSK := KemSK) setup program)
    (completed : CompletedMode setup program packet.state) :
    ∃ decision, PqxdhSourceSharedInput.input setup env callbacks program post attachedVerify primitives baseImpl kem
      owner number ancestors disclosed packet = .inl decision := by
  rcases packet with ⟨publicKey, secretKey, state, ciphertext⟩
  obtain ⟨decision, rfl⟩ := completed
  exact ⟨decision, rfl⟩

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The confidentiality output of the instrumented client: the client event, the first send of Beacon `b` used the selected hidden material, and no Beacon finish made a selected raw opening. -/
noncomputable def twinOut (target : Target S (B + 1)) (owner : RawCtxProtocolReveals.Owner S (B + 1))
    (response64 : PqxdhInitialRootLabelService.Response)
    (result : Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
      (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)) : Bool :=
  clientOut setup env callbacks target owner response64 result && decide (result.2.2.2.1 = some true) && !result.2.2.2.2

/-- Dead instrumented results give the confidentiality output `false`. -/
theorem twinOut_dead (target : Target S (B + 1)) (owner : RawCtxProtocolReveals.Owner S (B + 1))
    (response64 : PqxdhInitialRootLabelService.Response)
    (result : Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
      (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1))
    (dead : InsDead result.2) : twinOut setup env callbacks target owner response64 result = false := by
  unfold twinOut
  rcases dead with hidden | raised
  · simp [hidden]
  · simp [raised]

/-- The two instrumented confidentiality clients of the left-or-right wrapper are adaptive twins. -/
theorem client_pre (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (target : Target S (B + 1)) :
    Pre (fun a b => a = b) (fun a => a = false) (fun a => a = false)
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b target
        (twinOut setup env callbacks target))
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b target
        (twinOut setup env callbacks target)) := by
  unfold insFullClient
  refine same_pre (prelude_same setup env callbacks baseImpl kem attachedVerify primitives program _ _) ?_ ?_ ?_
  · rintro sample _ rfl
    unfold insSuffix insSuffixRun
    rcases input_relate setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
        (confPost adversary b true) target.owner target.number target.ancestors target.disclosed sample.1 with
      ⟨decision, h0, h1, _⟩ | ⟨input, selection, h0, h1, hpost⟩
    · simp only [h0, h1, map_pure]
      exact Pre.pure rfl
    · simp only [h0, h1, hpost, Functor.map_map]
      exact pre_map (insFirstRun_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ adversary selection) _ _
        (fun a₀ a₁ same => by rw [same])
        (fun r dead => twinOut_dead setup env callbacks target _ _ r dead)
        (fun r dead => twinOut_dead setup env callbacks target _ _ r dead)
  · intro sample completed c supported
    obtain ⟨decision, h⟩ := input_completed setup env callbacks baseImpl kem attachedVerify primitives program
      (confPost adversary b false) target.owner target.number target.ancestors target.disclosed sample.1 completed
    simp only [insSuffix, insSuffixRun, h, map_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
    rfl
  · intro sample completed c supported
    obtain ⟨decision, h⟩ := input_completed setup env callbacks baseImpl kem attachedVerify primitives program
      (confPost adversary b true) target.owner target.number target.ancestors target.disclosed sample.1 completed
    simp only [insSuffix, insSuffixRun, h, map_pure, support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
    rfl


end ClientPre

/-- One event dominated pointwise by another has at most its mass. -/
theorem map_le_map {α : Type} (mx : ProbComp α) (f g : α → Bool) (le : ∀ a, f a = true → g a = true) :
    𝒟[f <$> mx] {true} ≤ 𝒟[g <$> mx] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun a holds => le a holds

section OutputSwitch
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The raw instrumented client: the forwarded prelude and the raw suffix. -/
noncomputable def insFullRun (target : Target S (B + 1)) :
    OracleComp AdaptiveCtxDynamicKnownKeys.Spec (PrepResult M P I (DhPair setup) K A S (B + 1)) :=
  simulateQ RawCtxSourceSharedRom.forward (prelude setup env callbacks baseImpl kem attachedVerify primitives program post) >>=
    insSuffixRun setup env callbacks baseImpl kem attachedVerify primitives program post b target

/-- Every instrumented client reads its output from the raw instrumented client. -/
theorem insFullClient_run (target : Target S (B + 1))
    (out : RawCtxProtocolReveals.Owner S (B + 1) → PqxdhInitialRootLabelService.Response →
      Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
        (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1) → Bool) :
    insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target out =
      readOut out <$> insFullRun setup env callbacks baseImpl kem attachedVerify primitives program post b target := by
  simp only [insFullClient, insFullRun, map_bind]
  rfl

/-- The ordinary CTX source game of a mapped client is the mapped source game. -/
theorem source_map {α β : Type} (real : Bool) (decode : AdaptiveCtxReceive.RawDecoder) (c : Pqxdh.Crypto) (f : α → β)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec α) :
    Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame real decode c (f <$> client) =
      f <$> (Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame real decode c client) := by
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, simulateQ_map, StateT.run_map, map_bind, Functor.map_map]

/-- The finish-flag output: the client event holds and some Beacon finish of the instrumented run made a selected raw opening. -/
noncomputable def flagOut (target : Target S (B + 1)) (owner : RawCtxProtocolReveals.Owner S (B + 1))
    (response64 : PqxdhInitialRootLabelService.Response)
    (result : Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
      (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)) : Bool :=
  clientOut setup env callbacks target owner response64 result && result.2.2.2.2

/-- The hidden-gap output: the client event holds although the first send of Beacon `b` was not recorded as using the selected hidden material. -/
noncomputable def gapOut (target : Target S (B + 1)) (owner : RawCtxProtocolReveals.Owner S (B + 1))
    (response64 : PqxdhInitialRootLabelService.Response)
    (result : Option Bool × InsState M P (PqxdhGeneratedBeaconState.IdentityHandle I) (DhPair setup)
      (PqxdhGeneratedBeaconState.KemHandle K) A (BareState 1) RootOracle.QueryCache S (B + 1)) : Bool :=
  clientOut setup env callbacks target owner response64 result && !decide (result.2.2.2.1 = some true)

/-- The explicit finish-collision game `collGame`: in the ordinary selected-key CTX source game, the instrumented client event holds and a Beacon finish of the run made a selected raw opening. -/
noncomputable def collGame (target : Target S (B + 1)) : ProbComp Bool :=
  Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target
      (flagOut setup env callbacks target))

/-- The explicit hidden-gap game `gapGame`: in the ordinary selected-key CTX source game, the instrumented client event holds while the first send of Beacon `b` was not recorded as hidden. -/
noncomputable def hiddenGapGame (target : Target S (B + 1)) : ProbComp Bool :=
  Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target (gapOut setup env callbacks target))

/-- The confidentiality client is dominated by the client-event client. -/
theorem twin_le_client (target : Target S (B + 1)) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target
        (twinOut setup env callbacks target))] {true} ≤
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target
        (clientOut setup env callbacks target))] {true} := by
  rw [insFullClient_run, insFullClient_run, source_map, source_map]
  refine map_le_map _ _ _ fun result holds => ?_
  rcases result with _ | ⟨_, _, value⟩
  · exact absurd holds (by simp [readOut])
  · simp only [readOut, twinOut, Bool.and_eq_true] at holds ⊢
    exact holds.1.1

/-- The client-event client is dominated by the confidentiality client plus the hidden-gap game and the finish-collision game. -/
theorem client_le_twin (target : Target S (B + 1)) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target
        (clientOut setup env callbacks target))] {true} ≤
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b target
        (twinOut setup env callbacks target))] {true} +
      𝒟[hiddenGapGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} +
      𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program post b target] {true} := by
  unfold hiddenGapGame collGame
  rw [insFullClient_run, insFullClient_run, insFullClient_run, insFullClient_run, source_map, source_map, source_map, source_map]
  refine (map_le_add _ _ (fun result => readOut (twinOut setup env callbacks target) result ||
      readOut (gapOut setup env callbacks target) result) (readOut (flagOut setup env callbacks target)) fun result holds => ?_).trans
    (add_le_add (map_le_add _ _ _ _ fun result holds => by simpa only [Bool.or_eq_true] using holds) le_rfl)
  rcases result with _ | ⟨_, _, value⟩
  · exact absurd holds (by simp [readOut])
  · simp only [readOut, Bool.or_eq_true] at holds ⊢
    by_cases raised : value.2.2.2.2 = true
    · exact Or.inr (by simp [flagOut, holds, raised])
    · by_cases hidden : value.2.2.2.1 = some true
      · left
        left
        simp [twinOut, holds, hidden, raised]
      · left
        right
        simp [gapOut, holds, hidden]

end OutputSwitch

section Privacy
open AdaptiveCtxDynamicKnownKeys (Spec)
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The ordinary CTX privacy loss of a constructed key-free client: the IND$ advantage of the constructed validation reduction, the hash-guessing term, twice the INT-CTXT advantages of the constructed attempt-indexed reductions, the raw-guessing term and the IND$ advantage of the constructed view reduction. -/
noncomputable def privacyLoss (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp Spec Bool)
    (fallback : ModifiedNonceAeadForgery) (qHash qRaw : Nat) : ℝ≥0∞ :=
  ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
    (AdaptiveCtxPrefixValidation.validationReduction decode c (AdaptiveCtxDynamicKnownKeys.decisionClient c client) qHash)) +
  (qHash : ℝ≥0∞) * (((2 ^ 128 : Nat) : ℝ≥0∞))⁻¹ +
  2 * ∑ index ∈ Finset.range qRaw, modifiedNonceAeadINTCTXTAdvantage c
    (AdaptiveRawNonceAead.indexedReduction (baseDecoder decode) fallback
      (AdaptiveCtxReceive.wrapped decode (AdaptiveCtxDynamicKnownKeys.decisionClient c client)) index) +
  (qRaw : ℝ≥0∞) / (2 ^ 512 : Nat) +
  ENNReal.ofReal (modifiedNonceAeadINDDollarAdvantage c
    (AdaptiveCtxPrivacyGuard.viewReduction decode (AdaptiveCtxDynamicKnownKeys.decisionClient c client)))

/-- The privacy loss is finite. -/
theorem privacyLoss_ne_top (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp Spec Bool)
    (fallback : ModifiedNonceAeadForgery) (qHash qRaw : Nat) : privacyLoss decode c client fallback qHash qRaw ≠ ⊤ := by
  unfold privacyLoss
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
    ⟨ENNReal.ofReal_ne_top, ?_⟩, ?_⟩, ?_⟩, ENNReal.ofReal_ne_top⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr (by positivity))
  · refine ENNReal.mul_ne_top (by norm_num) (ENNReal.sum_ne_top.mpr fun index _ => ?_)
    exact prEvent_ne_top _
  · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)

/-- Two-sided ordinary CTX privacy of a constructed key-free client: its selected-key source game and its ordinary random view differ by at most the privacy loss. -/
theorem source_random (decode : RawDecoder) (c : Pqxdh.Crypto) (client : OracleComp Spec Bool)
    (fallback : ModifiedNonceAeadForgery) (qHash qSeal qRaw : Nat)
    (hashBound : client.IsQueryBoundP HashRoute qHash)
    (sealBound : client.IsQueryBoundP (TargetClass SourceSeal) qSeal)
    (rawBound : client.IsQueryBoundP (TargetClass IsRawQuery) qRaw)
    (small : qSeal < 2 ^ 96) :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode c client] {true} ≤
        𝒟[AdaptiveCtxPrivacyGuard.randomView decode (AdaptiveCtxDynamicKnownKeys.decisionClient c client)] {true} +
          privacyLoss decode c client fallback qHash qRaw ∧
      𝒟[AdaptiveCtxPrivacyGuard.randomView decode (AdaptiveCtxDynamicKnownKeys.decisionClient c client)] {true} ≤
        𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true decode c client] {true} +
          privacyLoss decode c client fallback qHash qRaw := by
  have bound := AdaptiveCtxDynamicKnownBounds.selected_privacy decode c fallback client qHash qSeal qRaw hashBound sealBound
    rawBound small
  constructor
  · exact (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage _ _).trans (add_le_add le_rfl bound)
  · refine (ProbComp.evalDist_apply_true_le_add_ofReal_boolDistAdvantage _ _).trans (add_le_add le_rfl ?_)
    rw [ProbComp.boolDistAdvantage_comm]
    exact bound

end Privacy

section Chain
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)) (b : Fin (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- Upper half of the chain: the pending source-observer mass is dominated by the confidentiality client in the selected-key CTX source game, the hidden-gap and finish-collision games, the restricted stop game and the initial half-alias term. -/
theorem ideal_le_twin :
    𝒟[PqxdhFirstRecordTarget.pendingIdeal env0 baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} ≤
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
        (twinOut setup env callbacks (firstBeacon b)))] {true} +
      𝒟[hiddenGapGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true} +
      𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true} +
      𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} +
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  refine (pending_ideal_upper setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) rfl).trans ?_
  have compiled := (insCompiled_le_separated setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)).trans
    (add_le_add le_rfl (insSeparated_le_client setup env callbacks baseImpl kem attachedVerify primitives program post b))
  have switched := client_le_twin setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
  calc _ ≤ ((1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) + _) + _ := add_le_add compiled le_rfl
    _ ≤ ((1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) + (_ + _ + _)) + _ := add_le_add (add_le_add le_rfl switched) le_rfl
    _ = _ := by ring

/-- Lower half of the chain: the confidentiality client in the selected-key CTX source game is dominated by the pending source-observer mass, the key-disclosure game and the initial half-alias term. -/
theorem twin_le_ideal :
    𝒟[Prod.fst <$> AdaptiveCtxDynamicKnownKeys.sourceGame true (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
      (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
        (twinOut setup env callbacks (firstBeacon b)))] {true} ≤
    𝒟[PqxdhFirstRecordTarget.pendingIdeal env0 baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} +
      𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true} +
      (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  refine (twin_le_client setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)).trans ?_
  refine (insClient_le_separated setup env callbacks baseImpl kem attachedVerify primitives program post b).trans ?_
  refine add_le_add ?_ le_rfl
  exact (insSeparated_le_compiled setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)).trans
    (pending_ideal_lower setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b) rfl)

open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation

/-- The confidentiality client's privacy loss with the certificate budgets: `qPrelude + 1 + qPost` hash requests and `1 + qPost` raw openings. -/
noncomputable def twinLoss (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat) : ℝ≥0∞ :=
  privacyLoss (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
      (twinOut setup env callbacks (firstBeacon b)))
    ctxFallback (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c)) (1 + postTotal setup env callbacks baseImpl kem program c)

/-- Both halves of the per-bit chain in reals: the accepted pending mass of the HB-112 actual game is within the root losses, the privacy loss, the explicit game terms and `2^-256` of the ordinary random view of the confidentiality client, in each direction. -/
theorem bit_bounds (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude : Nat)
    (prepareHash : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program post qPrelude)
    (small : 1 + postTotal setup env callbacks baseImpl kem program c < 2 ^ 96) :
    (𝒟[PqxdhFirstRecordTarget.pendingActual env0 baseImpl kem attachedVerify primitives program post
        (PqxdhInitialRootEventSecrecy.accepted env0 attachedVerify primitives program post (.beacon b) 1#u64 [] [])] {true}).toReal ≤
      (𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder (env0).decode)
        (AdaptiveCtxDynamicKnownKeys.decisionClient (env0).source.crypto
          (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
            (twinOut setup env callbacks (firstBeacon b))))] {true}).toReal +
      (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude).toReal +
      (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
        (PqxdhFirstRecordTarget.unitPost program post) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
        (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program post c) hmac fallback ordinaryFallback () +
      PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback) +
      (𝒟[hiddenGapGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true}).toReal +
      (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)] {true}).toReal +
      (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true}).toReal +
      1 / 2 ^ 256 ∧
    (𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder (env0).decode)
        (AdaptiveCtxDynamicKnownKeys.decisionClient (env0).source.crypto
          (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
            (twinOut setup env callbacks (firstBeacon b))))] {true}).toReal ≤
      (𝒟[PqxdhFirstRecordTarget.pendingActual env0 baseImpl kem attachedVerify primitives program post
        (PqxdhInitialRootEventSecrecy.accepted env0 attachedVerify primitives program post (.beacon b) 1#u64 [] [])] {true}).toReal +
      (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program post b c ctxFallback qPrelude).toReal +
      (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
        (PqxdhFirstRecordTarget.unitPost program post) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
        (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program post c) hmac fallback ordinaryFallback () +
      PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback) +
      (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true}).toReal +
      1 / 2 ^ 256 := by
  have postBound : ∀ selection reply, (post selection reply).IsTotalQueryBound (postTotal setup env callbacks baseImpl kem program c) :=
    fun selection reply => total_of_kinds PqxdhPhase2SourceSchedulerBounds.classify (post selection reply) c.postBudget
      (c.postBound selection reply)
  have hashBound := insFullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
    (twinOut setup env callbacks (firstBeacon b)) HashRoute (fun _ _ _ _ query state => external_no_hash _ _ _ _ _ query state) qPrelude
    (prelude_hash setup env callbacks baseImpl kem attachedVerify primitives program post qPrelude prepareHash) _ postBound
  have sealBound := insFullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
    (twinOut setup env callbacks (firstBeacon b)) (TargetClass SourceSeal)
    (fun _ _ _ _ query state => external_no_seal _ _ _ _ _ query state) 0 (forward_no_seal _) _ postBound
  have rawBound := insFullClient_uses setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
    (twinOut setup env callbacks (firstBeacon b)) (TargetClass AdaptiveCtxReceive.IsRawQuery)
    (fun _ _ _ _ query state => PqxdhSelectedInitialOwnerCompiler.external_no_open _ _ _ _ _ query state) 0 (forward_no_open _) _
      postBound
  rw [Nat.zero_add] at sealBound rawBound
  have privacy := source_random (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
      (twinOut setup env callbacks (firstBeacon b))) ctxFallback _ _ _ hashBound sealBound rawBound small
  have pending : |(𝒟[PqxdhFirstRecordTarget.pendingActual env0 baseImpl kem attachedVerify primitives program post
        (PqxdhInitialRootEventSecrecy.accepted env0 attachedVerify primitives program post (.beacon b) 1#u64 [] [])] {true}).toReal -
      (𝒟[PqxdhFirstRecordTarget.pendingIdeal env0 baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true}).toReal| ≤
      PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
        (PqxdhFirstRecordTarget.unitPost program post) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
        (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program post c) hmac fallback ordinaryFallback () +
      PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program post hmac fallback ordinaryFallback :=
    PqxdhFirstRecordTarget.pending_bound env0 baseImpl kem attachedVerify primitives program post (firstBeacon b) rfl c
      compatible adapter functional hmac correct fallback ordinaryFallback
  have halfFinite : (1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
  have lossFinite := privacyLoss_ne_top (RawCtxUniversalDecoder.decoder (env0).decode) (env0).source.crypto
    (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program post b (firstBeacon b)
      (twinOut setup env callbacks (firstBeacon b))) ctxFallback
    (qPrelude + (1 + postTotal setup env callbacks baseImpl kem program c)) (1 + postTotal setup env callbacks baseImpl kem program c)
  have up := (ideal_le_twin setup env callbacks baseImpl kem attachedVerify primitives program post b).trans
    (add_le_add (add_le_add (add_le_add (add_le_add privacy.1 le_rfl) le_rfl) le_rfl) le_rfl)
  have lo := privacy.2.trans (add_le_add (twin_le_ideal setup env callbacks baseImpl kem attachedVerify primitives program post b) le_rfl)
  have half : ((1 : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞)).toReal = 1 / 2 ^ 256 := by
    rw [ENNReal.toReal_div, ENNReal.toReal_pow]
    norm_num
  have upReal := ENNReal.toReal_mono (by simp [lossFinite, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]) up
  have loReal := ENNReal.toReal_mono (by simp [lossFinite, -evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ]) lo
  simp only [ENNReal.toReal_add, ne_eq, ENNReal.add_eq_top, PqxdhFirstRecordTarget.true_ne_top, halfFinite, lossFinite,
    not_false_eq_true, or_self, half] at upReal loReal
  unfold twinLoss
  rw [abs_le] at pending
  constructor <;> linarith [pending.1, pending.2]

end Chain

section Headline
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The left-or-right first-record game for challenge bit `β`: the accepted pending leaf of the HB-112 actual game (secrets sampled inside) with the wrapper post `confPost adversary b β`. It is `PqxdhInitialRootEventSecrecy.actual` minus its constant-`false` continuation (`PqxdhFirstRecordTarget.target_split`), and counts the runs in which the selected root is accepted, Beacon `b`'s first record is published from the selected root, the selected chain and its record key stay undisclosed, the challenge is fresh and the adversary outputs `true`. -/
noncomputable def confGame (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (β : Bool) : ProbComp Bool :=
  PqxdhFirstRecordTarget.pendingActual env0 baseImpl kem attachedVerify primitives program (confPost adversary b β)
    (PqxdhInitialRootEventSecrecy.accepted env0 attachedVerify primitives program (confPost adversary b β) (.beacon b) 1#u64 [] [])

/-- The ordinary random views of the two confidentiality clients have the same `true` mass. -/
theorem random_views_equal (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) :
    𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder (env0).decode)
        (AdaptiveCtxDynamicKnownKeys.decisionClient (env0).source.crypto
          (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b (firstBeacon b)
            (twinOut setup env callbacks (firstBeacon b))))] {true} =
      𝒟[AdaptiveCtxPrivacyGuard.randomView (RawCtxUniversalDecoder.decoder (env0).decode)
        (AdaptiveCtxDynamicKnownKeys.decisionClient (env0).source.crypto
          (insFullClient setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b (firstBeacon b)
            (twinOut setup env callbacks (firstBeacon b))))] {true} :=
  randomView_pre _ _ (client_pre setup env callbacks baseImpl kem attachedVerify primitives program b adversary (firstBeacon b))

/-- The real value of the nonce-repeat stop bound. -/
theorem stop_real (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post) (b : Fin (B + 1)) :
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post (firstBeacon b)] {true}).toReal ≤
      ((1 + c.postBudget (.inl .send) + 51 * (c.postBudget (.inl .raw) + c.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 := by
  have bound := PqxdhFirstRecordStopTagged.stop_bound setup env callbacks baseImpl kem attachedVerify primitives program post
    c.postBudget c.postBound b
  have real := ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)) bound
  rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast] at real
  simpa [-evalDist_apply_singleton, -evalDist_apply_setOf, -evalDist_apply_univ] using real

end Headline

section ReceiveChain
open ratchet.refined ratchet.control

/-- Cached publication keeps the send chain. -/
theorem cached_chain {Material : Type} (entry : RefinedRatchet RatchetChain RatchetChain Material)
    (prepared : PreparedCachedReceive) (result : RefinedRatchet RatchetChain RatchetChain Material)
    (published : publish_cached_receive entry prepared = ok result) : result.send_chain = entry.send_chain := by
  by_cases targetBound : prepared.target_slot.val < 50
  · by_cases lastBound : prepared.last_slot.val < 50
    · obtain ⟨actual, actualEq, _, chainEq, _⟩ := publish_cached_receive_exact entry prepared targetBound lastBound
      cases RustM.ok.inj (actualEq.symm.trans published)
      exact chainEq
    · have first : ¬UScalar.cast UScalarTy.Usize prepared.target_slot ≥ UScalar.cast UScalarTy.Usize 50#u64 := by scalar_tac
      have second : UScalar.cast UScalarTy.Usize prepared.last_slot ≥ UScalar.cast UScalarTy.Usize 50#u64 := by scalar_tac
      simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok, first, second, ↓reduceIte] at published
      cases RustM.ok.inj published
      rfl
  · have first : UScalar.cast UScalarTy.Usize prepared.target_slot ≥ UScalar.cast UScalarTy.Usize 50#u64 := by scalar_tac
    simp only [publish_cached_receive, lift, capacity_eq_ok, bind_tc_ok, first, ↓reduceIte] at published
    cases RustM.ok.inj published
    rfl

/-- Future publication keeps the send chain. -/
theorem future_chain {Material : Type} (entry : RefinedRatchet RatchetChain RatchetChain Material)
    (prepared : PendingReceive RatchetChain Material) (result : RefinedRatchet RatchetChain RatchetChain Material)
    (published : publish_future_receive entry prepared = ok result) : result.send_chain = entry.send_chain := by
  by_cases bound : prepared.first_slot.val + prepared.skipped.val ≤ 50
  · obtain ⟨actual, actualEq, _, chainEq, _⟩ := publish_future_receive_exact entry prepared bound
    cases RustM.ok.inj (actualEq.symm.trans published)
    exact chainEq
  · simp only [publish_future_receive, lift, capacity_eq_ok, bind_tc_ok] at published
    by_cases firstBound : 50 < prepared.first_slot.val
    · rw [ite_eq_left (by scalar_tac)] at published
      cases RustM.ok.inj published
      rfl
    · rw [ite_eq_right (by scalar_tac)] at published
      obtain ⟨available, availableEq, availableVal⟩ := uscalar_sub_eq_ok
        (UScalar.cast UScalarTy.Usize 50#u64) (UScalar.cast UScalarTy.Usize prepared.first_slot) (by scalar_tac)
      simp only [availableEq, bind_tc_ok,
        ite_eq_left (by scalar_tac : UScalar.cast UScalarTy.Usize prepared.skipped > available)] at published
      cases RustM.ok.inj published
      rfl

/-- A finished opening keeps the send chain of its entry. -/
theorem finish_chain {Material Context Plaintext : Type}
    (pending : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain Material Context) (reply : core.option.Option Plaintext) :
    (RawCtxInterpretedReceive.normalFinish pending reply).1.send_chain = pending.entry.send_chain := by
  have exact := RawCtxInterpretedReceive.normalFinish_exact pending reply
  cases reply with
  | none =>
    simp only [RawCtxInterpretedOpening.finish] at exact
    rw [← congrArg Prod.fst (RustM.ok.inj exact)]
  | some value =>
    simp only [RawCtxInterpretedOpening.finish] at exact
    cases hprep : pending.prepared with
    | PreparedReceiveCachedCase prepared =>
      simp only [hprep] at exact
      cases hpub : publish_cached_receive pending.entry prepared with
      | ok published =>
        simp only [hpub, bind_tc_ok] at exact
        rw [← congrArg Prod.fst (RustM.ok.inj exact)]
        exact cached_chain pending.entry prepared published hpub
      | fail error => simp [hpub] at exact
      | div => simp [hpub] at exact
    | PreparedReceiveFutureCase future =>
      simp only [hprep] at exact
      cases hpub : publish_future_receive pending.entry future with
      | ok published =>
        simp only [hpub, bind_tc_ok] at exact
        rw [← congrArg Prod.fst (RustM.ok.inj exact)]
        exact future_chain pending.entry future published hpub
      | fail error => simp [hpub] at exact
      | div => simp [hpub] at exact

end ReceiveChain

section CompiledReceiveChain
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxInterpretedReceive

/-- The terminal of a receive effect keeps the effect's entry. -/
theorem terminal_entry (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (effect : RawCtxSelectedReceiveReceipt.SourceEffect) :
    (∀ kernel, RawCtxSelectedReceiveReceipt.terminal prior parent target nonce next effect = .rejected kernel →
      kernel = effectEntry effect) ∧
    (∀ pending, RawCtxSelectedReceiveReceipt.terminal prior parent target nonce next effect = .opening pending →
      pending.entry = effectEntry effect) := by
  generalize depth : effectRank effect = rank
  induction rank using Nat.strong_induction_on generalizing effect with
  | h rank ih =>
    cases effect with
    | rejected entry actual =>
      constructor
      · intro kernel reached
        simp only [RawCtxSelectedReceiveReceipt.terminal, RawCtxSelectedReceiveReceipt.Terminal.rejected.injEq] at reached
        rw [← reached]
        rfl
      · intro pending reached
        simp only [RawCtxSelectedReceiveReceipt.terminal, reduceCtorEq] at reached
    | openRequested actual =>
      constructor
      · intro kernel reached
        simp only [RawCtxSelectedReceiveReceipt.terminal, reduceCtorEq] at reached
      · intro pending reached
        simp only [RawCtxSelectedReceiveReceipt.terminal, RawCtxSelectedReceiveReceipt.Terminal.opening.injEq] at reached
        rw [← reached]
        rfl
    | kdfRequested request =>
      have step := ih _ (depth ▸ normalResume_rank request
        (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next request.request)) _ rfl
      have kept : effectEntry (normalResume request
          (RawCtxSelectedSendCompiler.deriveValue prior parent target nonce next request.request)) = request.entry :=
        (resume_progress request _).choose_spec.2.1
      constructor
      · intro kernel reached
        simp only [RawCtxSelectedReceiveReceipt.terminal] at reached
        rw [step.1 kernel reached, kept]
        rfl
      · intro pending reached
        simp only [RawCtxSelectedReceiveReceipt.terminal] at reached
        rw [step.2 pending reached, kept]
        rfl

/-- Every compiled receive keeps the kernel's send chain. -/
theorem receive_chain (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (expected : Std.U64) (kernel : RawCtxSelectedMessageReveals.Kernel)
    (sequence : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (result : RawCtxSelectedMessageReveals.Kernel × core.option.Option RawCtxWholeOwner.Decrypted)
    (supported : result ∈ support (RawCtxSelectedReceiveCompiler.receive prior parent target nonce next read expected kernel
      sequence context)) :
    result.1.send_chain = kernel.send_chain := by
  have begun : effectEntry (normalBegin kernel sequence context) = kernel := (begin_total kernel sequence context).choose_spec.2
  simp only [RawCtxSelectedReceiveCompiler.receive, RawCtxSelectedMessageDriver.receive, ← QueryImpl.simulateQ_compose,
    RawCtxInterpretedReceive.receive] at supported
  change result ∈ support (simulateQ (RawCtxSelectedReceiveCompiler.compiler prior parent target nonce next read expected)
    (RawCtxInterpretedReceive.program (normalBegin kernel sequence context))) at supported
  rw [RawCtxSelectedReceiveReceipt.program_terminal] at supported
  have entries := terminal_entry prior parent target nonce next (normalBegin kernel sequence context)
  split at supported
  · rename_i rejected reached
    simp only [support_pure, Set.mem_singleton_iff] at supported
    rw [supported, entries.1 rejected reached, begun]
  · rename_i pending reached
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    rw [finish_chain, entries.2 pending reached, begun]

/-- A compiled raw delivery keeps the owner's send chain. -/
theorem raw_chain {Metadata : Type} (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput)
    (next : RootOutput) (read : RawCtxReceive.FrameDecoder) (bytes : Pqxdh.Bytes)
    (owner : RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State RawCtxSelectedMessageReveals.Kernel Metadata)
    (supported : result ∈ support (RawCtxSelectedReceiveCompiler.raw prior parent target nonce next read bytes owner)) :
    result.2.kernel.send_chain = owner.kernel.send_chain := by
  simp only [RawCtxSelectedReceiveCompiler.raw, RawCtxChainOwner.rawReceive, StateT.run] at supported
  split at supported
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    rw [supported]
    rfl
  · split at supported
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      rw [supported]
      rfl
    · split at supported
      · simp only [bind_pure_comp, support_map, Set.mem_image] at supported
        obtain ⟨inner, innerSupported, rfl⟩ := supported
        exact receive_chain prior parent target nonce next read _ _ _ _ inner innerSupported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        rw [supported]
        rfl

end CompiledReceiveChain

section BeaconFrame
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf RawCtxSelectedParentTable RawCtxSelectedParentEntry
open RawCtxGenericRoleStorage
variable {I D K M P : Type} {S B : Nat}

/-- An established Beacon stays established with the same send chain. -/
def ChainKept (before after : BeaconState RawCtxSelectedMessageReveals.Kernel I D K) : Prop :=
  ∀ control ad kernel, before.beacon.phase = .established control ad kernel →
    ∃ control' ad' kernel', after.beacon.phase = .established control' ad' kernel' ∧ kernel'.send_chain = kernel.send_chain

/-- An established Beacon stays established. -/
def EstKept (before after : BeaconState RawCtxSelectedMessageReveals.Kernel I D K) : Prop :=
  ∀ control ad kernel, before.beacon.phase = .established control ad kernel →
    ∃ control' ad' kernel', after.beacon.phase = .established control' ad' kernel'

/-- Keeping the send chain keeps the phase established. -/
theorem ChainKept.est {before after : BeaconState RawCtxSelectedMessageReveals.Kernel I D K} (kept : ChainKept before after) :
    EstKept before after := by
  intro control ad kernel phase
  obtain ⟨control', ad', kernel', phase', _⟩ := kept control ad kernel phase
  exact ⟨control', ad', kernel', phase'⟩

/-- An unchanged Beacon keeps its send chain. -/
theorem ChainKept.refl (beacon : BeaconState RawCtxSelectedMessageReveals.Kernel I D K) : ChainKept beacon beacon :=
  fun control ad kernel phase => ⟨control, ad, kernel, phase, rfl⟩

/-- Keeping the send chain transfers hiddenness. -/
theorem ChainKept.hidden {before after : BeaconState RawCtxSelectedMessageReveals.Kernel I D K} (kept : ChainKept before after)
    (target : RootOutput) (hidden : HiddenBeacon target before) : HiddenBeacon target after := by
  unfold HiddenBeacon at hidden ⊢
  split at hidden
  · rename_i control ad kernel phase
    obtain ⟨control', ad', kernel', phase', chain⟩ := kept control ad kernel phase
    rw [phase']
    simpa only [chain] using hidden
  · exact hidden.elim

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)

/-- A compiled Beacon step keeps an established phase, and keeps its send chain unless it is a send. -/
theorem beacon_frame (query : RawCtxMixedOwner.SourceSpec.Domain) (before : BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (result : Option (RawCtxMixedOwner.SourceSpec.Range query × BeaconState RawCtxSelectedMessageReveals.Kernel I D K))
    (supported : result ∈ support (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read query before)) :
    ∀ value after, result = some (value, after) →
      EstKept before after ∧ ((∀ plaintext, query ≠ .inl plaintext) → ChainKept before after) := by
  intro value after reached
  rw [RawCtxSelectedRoleCompiler.beacon_cases] at supported
  split at supported
  · rename_i control ad kernel phase
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨inner, innerSupported, rfl⟩ := supported
    rcases inner with _ | ⟨reply, owner⟩
    · simp at reached
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at reached
      obtain ⟨_, rfl⟩ := reached
      have established : ∀ c a k, before.beacon.phase = .established c a k →
          ∃ c' a' k', (RawCtxGenericBeacon.reinstall before control ad owner).beacon.phase = .established c' a' k' :=
        fun _ _ _ _ => ⟨control, ad, owner.kernel, rfl⟩
      refine ⟨established, fun notSend => ?_⟩
      rcases query with plaintext | raw
      · exact absurd rfl (notSend plaintext)
      · rw [RawCtxSelectedOwnerCompiler.raw_cases, support_map] at innerSupported
        obtain ⟨owned, ownedSupported, same⟩ := innerSupported
        simp only [Option.some.injEq] at same
        intro c a k phase'
        rw [phase] at phase'
        simp only [RawCtxBeaconLifecycle.Phase.established.injEq] at phase'
        obtain ⟨rfl, rfl, rfl⟩ := phase'
        refine ⟨control, ad, owner.kernel, rfl, ?_⟩
        have chain := raw_chain prior parent target nonce next read raw _ owned ownedSupported
        rw [same] at chain
        exact chain
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp only [Option.some.injEq] at reached
    rcases query with plaintext | raw
    · simp only [RawCtxGenericBeacon.rejected, Prod.mk.injEq] at reached
      obtain ⟨_, rfl⟩ := reached
      exact ⟨fun c a k phase => ⟨c, a, k, phase⟩, fun _ => ChainKept.refl _⟩
    · simp only [RawCtxGenericBeacon.rejected, Prod.mk.injEq] at reached
      obtain ⟨_, rfl⟩ := reached
      exact ⟨fun c a k phase => ⟨c, a, k, phase⟩, fun _ c a k phase => ⟨c, a, k, phase, rfl⟩⟩

/-- A send request of Beacon `b` at the live interface. -/
def IsBeaconSend (b : Fin B) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain) : Prop :=
  ∃ plaintext, request = .inl (.inr (.inl ⟨b, .inl plaintext⟩))

/-- A live compiled request keeps Beacon `b` established, and keeps its send chain unless it is a send of Beacon `b`. -/
theorem live_frame (b : Fin B) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (front : RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (z : Option ((RawCtxProtocolReveals.SourceSpec S B).Range request) × RawCtxSelectedFamilyLiveCompiler.Front M P I D K S B)
    (supported : z ∈ support (((RawCtxSelectedFamilyLiveCompiler.impl source writer prior parent target nonce next sender route read
      request).run).run front)) :
    EstKept (front.1.2 b) (z.2.1.2 b) ∧ (¬ IsBeaconSend b request → ChainKept (front.1.2 b) (z.2.1.2 b)) := by
  rcases request with family | reveal
  · change z ∈ support (RawCtxSelectedFamilyLiveCompiler.publish front <$> RawCtxSelectedFamilyCompiler.family source writer prior
      parent target nonce next sender route read family front.1) at supported
    simp only [support_map, Set.mem_image] at supported
    obtain ⟨r, rSupported, rfl⟩ := supported
    rw [RawCtxSelectedFamilyCompiler.family_cases] at rSupported
    have unchanged : ∀ roles : RawCtxGenericRoleFamily.Roles RawCtxSelectedMessageReveals.Kernel M P I D K S B,
        roles.2 b = front.1.2 b → EstKept (front.1.2 b) (roles.2 b) ∧
          (¬ IsBeaconSend b (.inl family) → ChainKept (front.1.2 b) (roles.2 b)) := by
      intro roles same
      rw [same]
      exact ⟨(ChainKept.refl _).est, fun _ => ChainKept.refl _⟩
    rcases family with ⟨index, q⟩ | (⟨index, q⟩ | request)
    · simp only [support_map, Set.mem_image] at rSupported
      obtain ⟨inner, _, rfl⟩ := rSupported
      rcases inner with _ | ⟨value, after⟩
      · exact unchanged front.1 rfl
      · exact unchanged _ rfl
    · simp only [support_map, Set.mem_image] at rSupported
      obtain ⟨inner, innerSupported, rfl⟩ := rSupported
      rcases inner with _ | ⟨value, after⟩
      · exact unchanged front.1 rfl
      · by_cases same : index = b
        · subst same
          have frame := beacon_frame source writer prior parent target nonce next read q (front.1.2 index) _ innerSupported
            value after rfl
          simp only [Option.map_some, RawCtxSelectedFamilyLiveCompiler.publish, Function.update_self]
          refine ⟨frame.1, fun notSend => frame.2 fun plaintext holds => notSend ⟨plaintext, ?_⟩⟩
          rw [holds]
        · exact unchanged _ (Function.update_of_ne (Ne.symm same) _ _)
    · simp only [support_map, Set.mem_image] at rSupported
      obtain ⟨reply, _, rfl⟩ := rSupported
      exact unchanged front.1 rfl
  · change z ∈ support (pure (RawCtxSelectedMessageReveals.emit reveal (RawCtxSelectedMessageReveals.step reveal front).1,
      (RawCtxSelectedMessageReveals.step reveal front).2) : OracleComp AdaptiveCtxDynamicKnownKeys.Spec _) at supported
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨(ChainKept.refl _).est, fun _ => ChainKept.refl _⟩

end BeaconFrame

section MarkedOrigin
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix PqxdhInitialGenericBeacon
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedInitialOwnerCompiler PqxdhInitialFinishOrigin
open PqxdhCorrelatedExtractFamily PqxdhCorrelatedExpand PqxdhInitialBeaconAmbient
variable {ι I D K X Response A N : Type} {extra : OracleSpec ι}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : Message) (previousRoot : RootOutput)
    (response : PqxdhInitialRootLabelService.Response)

/-- On the selected message the compiled initializer callback returns the kernel of the supplied response. -/
theorem lower_initial_marked (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared)
    (marked : PqxdhInitialSelectedOrigin.mark fixed selectedMessage secrets = true)
    (state : Local A N RootOracle.QueryCache)
    (result : Option (PqxdhInitialPendingPost.KernelOf RatchetChain) × Local A N RootOracle.QueryCache)
    (supported : result ∈ support ((PqxdhSelectedCallbackCompiler.lower (extra := extra) (X := X) pre application
      (initialLocal fixed selectedMessage previousRoot response) selector aux (.inl (.inr (.inr (.inl secrets))))).run state)) :
    result.1 = some (PqxdhInitialRootAudit.kernel (previousRoot, response)).refined := by
  have request := (PqxdhInitialSelectedOrigin.selectedRequest_iff selectedMessage _).mp marked
  simp only [PqxdhSelectedCallbackCompiler.lower, PqxdhSelectedCallbackCompiler.callback, initialCall, initialLocal, request,
    PqxdhInitialRootAudit.retained, ite_true, StateT.run] at supported
  simp only [simulateQ_map] at supported
  rw [supported]

/-- A published finish establishes the staged kernel. -/
theorem finish_some {Kernel : Type} (control : pqxdh.BeaconInitSent) (state : RawCtxGenericRoleStorage.BeaconState Kernel I D K)
    (staged : Option (Staged Kernel)) (bytes : Pqxdh.Bytes)
    (published : (PqxdhInitialGenericBeacon.finish control state staged).1 = some bytes) :
    ∃ value established ad, staged = some value ∧
      (PqxdhInitialGenericBeacon.finish control state staged).2.beacon.phase = .established established ad value.kernel := by
  unfold PqxdhInitialGenericBeacon.finish at published ⊢
  rcases staged with _ | value
  · simp at published
  · simp only at published ⊢
    split_ifs at published ⊢
    exact ⟨value, _, _, rfl, rfl⟩

variable (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (read : RawCtxReceive.FrameDecoder)

/-- A compiled finish application that publishes establishes a kernel with the send chain of the initialized kernel. -/
theorem finishApplication_chain (control : pqxdh.BeaconInitSent)
    (before : RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : RawCtxSelectedMessageReveals.Kernel) (app : Option Pqxdh.Bytes)
    (reply : Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState RawCtxSelectedMessageReveals.Kernel I D K)
    (supported : reply ∈ support (PqxdhSelectedBeaconCompiler.finishApplication prior parent target nonce next read control before
      candidate kernel app))
    (bytes : Pqxdh.Bytes) (published : reply.1 = some bytes) :
    ∃ established ad kernel', reply.2.beacon.phase = .established established ad kernel' ∧ kernel'.send_chain = kernel.send_chain := by
  simp only [PqxdhSelectedBeaconCompiler.finishApplication, support_map, Set.mem_image] at supported
  obtain ⟨staged, stagedSupported, rfl⟩ := supported
  obtain ⟨value, established, ad, rfl, phase⟩ := finish_some control before staged bytes published
  refine ⟨established, ad, value.kernel, phase, ?_⟩
  simp only [PqxdhSelectedBeaconCompiler.afterApplication] at stagedSupported
  rcases app with _ | raw
  · simp at stagedSupported
  · simp only [support_map, Set.mem_image] at stagedSupported
    obtain ⟨owned, ownedSupported, found⟩ := stagedSupported
    rw [PqxdhFirstRecordStopTagged.opening_kernel candidate _ _ value found]
    exact raw_chain prior parent target nonce next read raw _ owned ownedSupported

/-- A compiled marked finish that records origin `true` establishes a Beacon whose send chain is the send chain of the supplied-response kernel; a finish of an established Beacon changes nothing and records no origin. -/
theorem owner_marked_origin (raw : Pqxdh.Bytes) (before : PqxdhSelectedInitialOwnerCompiler.Beacon I D K)
    (state : Local A N RootOracle.QueryCache)
    (w : PqxdhInitialFinishOrigin.Result PqxdhSelectedInitialOwnerCompiler.Kernel Bool I D K × Local A N RootOracle.QueryCache)
    (supported : w ∈ support ((simulateQ (PqxdhSelectedInitialOwnerCompiler.lower (extra := extra) (X := X) pre application
      (initialLocal fixed selectedMessage previousRoot response) selector aux prior parent target nonce next read)
      (ownerMarked (PqxdhInitialSelectedOrigin.mark fixed selectedMessage) raw before)).run state)) :
    (w.1.2 = some true → ∃ established ad kernel, w.1.1.2.beacon.phase = .established established ad kernel ∧
      kernel.send_chain = (PqxdhInitialRootAudit.kernel (previousRoot, response)).refined.send_chain) ∧
    (∀ control ad kernel, before.beacon.phase = .established control ad kernel → w.1.1.2 = before ∧ w.1.2 = none) := by
  revert supported
  unfold ownerMarked
  cases phase : before.beacon.phase with
  | initSent control prekey oneTime kem =>
    intro supported
    refine ⟨fun origin => ?_, fun c a k established => by cases established⟩
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨prepared, state1⟩, _, rest⟩ := supported
    rcases prepared with _ | pending
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
      rw [rest] at origin
      simp at origin
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨⟨kernelReply, state2⟩, kernelSupported, rest⟩ := rest
      change (kernelReply, state2) ∈ support ((PqxdhSelectedCallbackCompiler.lower pre application
        (initialLocal fixed selectedMessage previousRoot response) selector aux (.inl (.inr (.inr (.inl pending.root))))).run
          state1) at kernelSupported
      rcases kernelReply with _ | kernel
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at rest
        rw [rest] at origin
        simp [tag, PqxdhInitialGenericBeacon.finish] at origin
      · simp only [simulateQ_bind, simulateQ_map, simulateQ_spec_query, StateT.run_bind, StateT.run_map, mem_support_bind_iff,
          support_map, Set.mem_image] at rest
        obtain ⟨⟨app, state3⟩, _, final, finalSupported, rfl⟩ := rest
        change final ∈ support ((fun reply => (reply, state3)) <$> PqxdhSelectedBeaconCompiler.finishApplication prior parent target
          nonce next read control before (PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata)
            (PqxdhSelectedMessageBeacon.knownKernel kernel) app) at finalSupported
        simp only [support_map, Set.mem_image] at finalSupported
        obtain ⟨reply, replySupported, rfl⟩ := finalSupported
        simp only [tag, Option.map_eq_some_iff] at origin
        obtain ⟨bytes, published, marked⟩ := origin
        have initialKernel := lower_initial_marked pre application selector aux fixed selectedMessage previousRoot response
          pending.root marked state1 (some kernel, state2) kernelSupported
        simp only [Option.some.injEq] at initialKernel
        obtain ⟨established, ad, kernel', phase', chain⟩ := finishApplication_chain prior parent target nonce next read control
          before _ _ _ reply replySupported bytes published
        refine ⟨established, ad, kernel', phase', ?_⟩
        rw [chain, initialKernel]
        rfl
  | established control ad kernel =>
    intro supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨fun impossible => by simp at impossible, fun _ _ _ _ => ⟨rfl, rfl⟩⟩
  | aborted control =>
    intro supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨fun impossible => by simp at impossible, fun c a k established => by cases established⟩
  | fresh control prekey kem =>
    intro supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨fun impossible => by simp at impossible, fun c a k established => by cases established⟩
  | freshWithCoins control prekey oneTime kem =>
    intro supported
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact ⟨fun impossible => by simp at impossible, fun c a k established => by cases established⟩

end MarkedOrigin

section OriginStep
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedFirstRecord PqxdhCorrelatedExtractFamily
open PqxdhCorrelatedExpand PqxdhInitialBeaconAmbient
open AdaptiveCtxDynamicKnownKeys (Spec)
variable {ι I D K X Response A N M P : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Beacon `b`'s origin invariant: an origin-`true` installation of Beacon `b` is established, and while the monitor is empty its send chain is the selected hidden chain. -/
def OriginInv (target : RootOutput) (b : Fin B) (s : InsState M P I D K A N RootOracle.QueryCache S B) : Prop :=
  s.2.1.installed (.beacon b) = some true →
    (∃ control ad kernel, (s.1.1.roles.1.2 b).beacon.phase = .established control ad kernel) ∧
      (s.2.2.1 = none → HiddenBeacon target (s.1.1.roles.1.2 b))

/-- A `markRaw`-wrapped result is a result of the wrapped program. -/
theorem markRaw_support {α : Type} (x : OracleComp Spec α) (flag : Bool) (result : α × Bool)
    (supported : result ∈ support ((simulateQ markRaw x).run flag)) : result.1 ∈ support x := by
  rw [← markRaw_erase x flag, support_map]
  exact ⟨result, supported, rfl⟩

/-- The monitor keeps its value on every request other than a send of Beacon `b`. -/
theorem hiddenStep_other (target : RootOutput) (b : Fin B) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (hidden : Option Bool) (other : ¬ IsBeaconSend b request) :
    hiddenStep b target request front hidden = hidden := by
  unfold hiddenStep
  split
  · rfl
  · rename_i index p
    split_ifs with same
    · exact absurd ⟨p, by rw [same]⟩ other
    · rfl
  · rfl

/-- The monitor is set after a send of Beacon `b`. -/
theorem hiddenStep_send (target : RootOutput) (b : Fin B) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (hidden : Option Bool) (send : IsBeaconSend b request) :
    hiddenStep b target request front hidden ≠ none := by
  obtain ⟨p, rfl⟩ := send
  unfold hiddenStep
  split
  · simp
  · simp_all
  · rename_i hne
    exact absurd rfl (hne b p)

/-- Recording a reply keeps the installations. -/
theorem traceRecord_installed (t : PqxdhInitialOriginPost.Trace Bool S B) (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (reply : Option ((RawCtxProtocolReveals.SourceSpec S B).Range request)) :
    (traceRecord t request reply).installed = t.installed := by
  cases reply <;> rfl

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (selectedMessage : Message)
    (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (prior : Prior) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (b : Fin B)

local notation "sendTarget" => PqxdhInitialOriginFinishPath.sendRoot previousRoot response

/-- Every instrumented request keeps Beacon `b`'s origin invariant. -/
theorem ins_origin_step (q : (PqxdhInitialGenericPost.Spec extra S B).Domain) (s : InsState M P I D K A N RootOracle.QueryCache S B)
    (inv : OriginInv sendTarget b s)
    (w : Option ((PqxdhInitialGenericPost.Spec extra S B).Range q) × InsState M P I D K A N RootOracle.QueryCache S B)
    (supported : w ∈ support (((insImpl pre application (initialLocal source selectedMessage previousRoot response) selector aux
      source writer prior none sendTarget nonce next sender route read (PqxdhInitialSelectedOrigin.mark source selectedMessage) b
        q).run).run s)) :
    OriginInv sendTarget b w.2 := by
  rcases q with (request | ext) | ⟨index, raw⟩
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, resultSupported, rfl⟩ := supported
    have frame := live_frame source writer prior none sendTarget nonce next sender route read b request s.1.1.roles result
      resultSupported
    intro installed
    simp only [traceRecord_installed] at installed
    obtain ⟨established, hidden⟩ := inv installed
    by_cases send : IsBeaconSend b request
    · obtain ⟨control, ad, kernel, phase⟩ := established
      obtain ⟨control', ad', kernel', phase'⟩ := frame.1 control ad kernel phase
      exact ⟨⟨control', ad', kernel', phase'⟩, fun empty => absurd empty (hiddenStep_send _ b request _ _ send)⟩
    · have kept := frame.2 send
      obtain ⟨control, ad, kernel, phase⟩ := established
      obtain ⟨control', ad', kernel', phase', _⟩ := kept control ad kernel phase
      refine ⟨⟨control', ad', kernel', phase'⟩, fun empty => ?_⟩
      simp only [hiddenStep_other _ b request _ _ send] at empty
      exact kept.hidden _ (hidden empty)
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, _, rfl⟩ := supported
    exact inv
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, resultSupported, rfl⟩ := supported
    have inner := markRaw_support _ _ result resultSupported
    have origin := owner_marked_origin pre application selector aux source selectedMessage previousRoot response prior none sendTarget
      nonce next read raw (s.1.1.roles.1.2 index) s.1.2 result.1 inner
    intro installed
    by_cases same : index = b
    · subst same
      by_cases before : s.2.1.installed (.beacon index) = some true
      · obtain ⟨⟨control, ad, kernel, phase⟩, hidden⟩ := inv before
        obtain ⟨unchanged, none'⟩ := origin.2 control ad kernel phase
        simp only [PqxdhSelectedPostCompiler.install, Function.update_self, unchanged]
        exact ⟨⟨control, ad, kernel, phase⟩, hidden⟩
      · have marked : result.1.1.2 = some true := by
          cases hOrigin : result.1.1.2 with
          | none =>
            simp only [hOrigin, PqxdhInitialOriginPost.finish] at installed
            exact absurd installed before
          | some value =>
            simp only [hOrigin, PqxdhInitialOriginPost.finish, Function.update_self] at installed
            rw [installed]
        obtain ⟨control, ad, kernel, phase, chain⟩ := origin.1 marked
        simp only [PqxdhSelectedPostCompiler.install, Function.update_self]
        refine ⟨⟨control, ad, kernel, phase⟩, fun _ => ?_⟩
        unfold HiddenBeacon
        rw [phase]
        exact (RawCtxSelectedParentPrivatePatch.address_eq _ _).mpr (by rw [chain]; rfl)
    · have kept : (PqxdhSelectedPostCompiler.install index s.1.1 result.1.1.1.2).roles.1.2 b = s.1.1.roles.1.2 b := by
        simp only [PqxdhSelectedPostCompiler.install]
        exact Function.update_of_ne (Ne.symm same) _ _
      have installedSame : (PqxdhInitialOriginPost.finish s.2.1 index result.1.1.2).installed (.beacon b) =
          s.2.1.installed (.beacon b) := by
        cases result.1.1.2 with
        | none => rfl
        | some value =>
          simp only [PqxdhInitialOriginPost.finish]
          exact Function.update_of_ne (fun h => same (RawCtxProtocolReveals.Owner.beacon.inj h).symm) _ _
      simp only [kept]
      rw [installedSame] at installed
      exact inv installed

end OriginStep

section PublishStep
variable {S B : Nat}

/-- A reply to a send of Beacon `b` that returned a record of the given sequence. -/
def BeaconFirst (b : Fin B) : (request : (RawCtxProtocolReveals.SourceSpec S B).Domain) →
    Option ((RawCtxProtocolReveals.SourceSpec S B).Range request) → Std.U64 → Prop
  | .inl (.inr (.inl ⟨index, .inl _⟩)), some (some sent), number => index = b ∧ sent.sequence = number
  | _, _, _ => False

/-- A Beacon `b` entry of a recorded transcript is old or comes from a send of Beacon `b` returning that record, with the current installation as origin. -/
theorem traceRecord_entry (b : Fin B) (t : PqxdhInitialOriginPost.Trace Bool S B)
    (request : (RawCtxProtocolReveals.SourceSpec S B).Domain) (reply : Option ((RawCtxProtocolReveals.SourceSpec S B).Range request))
    (number : Std.U64) (origin : Bool)
    (mem : ((.beacon b, number), origin) ∈ (traceRecord t request reply).published) :
    ((.beacon b, number), origin) ∈ t.published ∨
      (BeaconFirst b request reply number ∧ t.installed (.beacon b) = some origin) := by
  rcases reply with _ | value
  · exact Or.inl mem
  · simp only [traceRecord, PqxdhInitialOriginPost.record, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff] at mem
    rcases mem with old | ⟨publication, recorded, found, installedEq, pairEq⟩
    · exact Or.inl old
    · right
      rcases request with ((⟨i, (⟨p, kid⟩ | raw)⟩ | (⟨i, (p | raw)⟩ | pub)) | reveal)
      all_goals simp only [RawCtxPublishedRecords.record, List.not_mem_nil] at recorded
      · rcases value with _ | sent
        · simp at recorded
        · simp only [List.mem_singleton] at recorded
          rw [recorded] at pairEq
          simp only [Prod.mk.injEq, reduceCtorEq, false_and] at pairEq
      · rcases value with _ | sent
        · simp at recorded
        · simp only [List.mem_singleton] at recorded
          rw [recorded] at pairEq installedEq
          simp only [Prod.mk.injEq, RawCtxProtocolReveals.Owner.beacon.injEq] at pairEq
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := pairEq
          exact ⟨⟨rfl, rfl⟩, installedEq⟩

end PublishStep

section ConfInvariant
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhFullSecretInputKdf PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry PqxdhSelectedFirstRecord PqxdhCorrelatedExtractFamily
open PqxdhCorrelatedExpand PqxdhInitialBeaconAmbient
open AdaptiveCtxDynamicKnownKeys (Spec)
variable {ι I D K X Response A N M P : Type} {extra : OracleSpec ι} {S B : Nat}

/-- A sequence-one reply to an adversary send of Beacon `b` is noted by the wrapper. -/
theorem observe_first (b : Fin B) (c : ConfState) (record : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (r : (RawCtxProtocolReveals.SourceSpec S B).Range record) (first : BeaconFirst b record (some r) 1#u64) :
    (observe (extra := extra) b c (.inl (.inl record)) r).otherFirst = true := by
  rcases record with ((⟨i, (⟨p, kid⟩ | raw)⟩ | (⟨i, (p | raw)⟩ | pub)) | reveal)
  all_goals simp only [BeaconFirst] at first
  rcases r with _ | sent
  · simp at first
  · obtain ⟨rfl, sequence⟩ := first
    simp [observe, firstRecord, sequence]

/-- The wrapper never forgets a noted sequence-one reply. -/
theorem observe_mono (b : Fin B) (c : ConfState) (request : (ConfPostSpec extra S B).Domain) (r : (ConfPostSpec extra S B).Range request)
    (noted : c.otherFirst = true) : (observe b c request r).otherFirst = true := by
  unfold observe
  split
  · split_ifs
    · simp [noted]
    · exact noted
  · exact noted

/-- The first-record publication invariant: a published origin-`true` first record of Beacon `b` was noted by the wrapper or used the selected hidden material. -/
def PublishInv (b : Fin B) (c : ConfState) (s : InsState M P I D K A N RootOracle.QueryCache S B) : Prop :=
  (((RawCtxProtocolReveals.Owner.beacon b), 1#u64), true) ∈ s.2.1.published → c.otherFirst = true ∨ s.2.2.1 = some true

/-- The combined invariant of the wrapper and the instrumented state. -/
def AllInv (target : RootOutput) (b : Fin B) (c : ConfState) (s : InsState M P I D K A N RootOracle.QueryCache S B) : Prop :=
  InsLink c s ∧ OriginInv target b s ∧ PublishInv b c s

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (selectedMessage : Message)
    (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
    (prior : Prior) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (b : Fin B)

local notation "sendTarget" => PqxdhInitialOriginFinishPath.sendRoot previousRoot response
local notation "impl" => insImpl pre application (initialLocal source selectedMessage previousRoot response) selector aux source writer
  prior none sendTarget nonce next sender route read (PqxdhInitialSelectedOrigin.mark source selectedMessage) b

/-- A published Beacon `b` entry after an instrumented record request was published before or comes from this request's Beacon `b` send, with the current installation. -/
theorem ins_publish_record (record : (RawCtxProtocolReveals.SourceSpec S B).Domain) (s : InsState M P I D K A N RootOracle.QueryCache S B)
    (w : Option ((RawCtxProtocolReveals.SourceSpec S B).Range record) × InsState M P I D K A N RootOracle.QueryCache S B)
    (supported : w ∈ support (((impl (.inl (.inl record))).run).run s))
    (mem : (((RawCtxProtocolReveals.Owner.beacon b), 1#u64), true) ∈ w.2.2.1.published) :
    (((RawCtxProtocolReveals.Owner.beacon b), 1#u64), true) ∈ s.2.1.published ∨
      (BeaconFirst b record w.1 1#u64 ∧ s.2.1.installed (.beacon b) = some true) := by
  simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨result, _, rfl⟩ := supported
  exact traceRecord_entry b s.2.1 record result.1 1#u64 true mem

/-- Instrumented requests other than record requests keep the transcript's publications. -/
theorem ins_publish_other (q : (PqxdhInitialGenericPost.Spec extra S B).Domain) (notRecord : ∀ record, q ≠ .inl (.inl record))
    (s : InsState M P I D K A N RootOracle.QueryCache S B)
    (w : Option ((PqxdhInitialGenericPost.Spec extra S B).Range q) × InsState M P I D K A N RootOracle.QueryCache S B)
    (supported : w ∈ support (((impl q).run).run s)) : w.2.2.1.published = s.2.1.published := by
  rcases q with (record | ext) | ⟨index, raw⟩
  · exact absurd rfl (notRecord record)
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, _, rfl⟩ := supported
    rfl
  · simp only [insImpl, OptionT.run_mk, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨result, _, rfl⟩ := supported
    cases result.1.1.2 <;> rfl

/-- A kept monitor value stays `some true`. -/
theorem monitor_true (q : (PqxdhInitialGenericPost.Spec extra S B).Domain) (s : InsState M P I D K A N RootOracle.QueryCache S B)
    (w : Option ((PqxdhInitialGenericPost.Spec extra S B).Range q) × InsState M P I D K A N RootOracle.QueryCache S B)
    (supported : w ∈ support (((impl q).run).run s)) (hidden : s.2.2.1 = some true) : w.2.2.2.1 = some true := by
  rw [ins_monitor pre application (initialLocal source selectedMessage previousRoot response) selector aux source writer prior sendTarget
    nonce next sender route read (PqxdhInitialSelectedOrigin.mark source selectedMessage) b q s w supported, hidden, monitorAfter_some]

set_option backward.isDefEq.respectTransparency false in
/-- Every wrapper step keeps the combined invariant. -/
theorem all_step (β : Bool) (q : (AdvSpec extra S B).Domain) (c : ConfState) (s : InsState M P I D K A N RootOracle.QueryCache S B)
    (inv : AllInv sendTarget b c s)
    (z : Option ((AdvSpec extra S B).Range q × ConfState) × InsState M P I D K A N RootOracle.QueryCache S B)
    (supported : z ∈ support (runStepper (confIns b β impl q) c s))
    (reply : (AdvSpec extra S B).Range q) (c' : ConfState) (reached : z.1 = some (reply, c')) :
    AllInv sendTarget b c' z.2 := by
  obtain ⟨link, origin, publish⟩ := inv
  rcases q with request | ⟨m0, m1⟩
  · rw [adv_run pre application (initialLocal source selectedMessage previousRoot response) selector aux source writer prior sendTarget
      nonce next sender route read (PqxdhInitialSelectedOrigin.mark source selectedMessage) b β request c s, support_map] at supported
    obtain ⟨w, hw, rfl⟩ := supported
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at reached
    obtain ⟨r, hr, _, rfl⟩ := reached
    refine ⟨?_, ins_origin_step pre application selector aux source writer selectedMessage previousRoot response prior nonce next
      sender route read b request s origin w hw, ?_⟩
    · intro sent'
      rw [ins_monitor pre application (initialLocal source selectedMessage previousRoot response) selector aux source writer prior
        sendTarget nonce next sender route read (PqxdhInitialSelectedOrigin.mark source selectedMessage) b request s w hw]
      exact observe_monitor sendTarget b c request r s.1.1 s.2.2.1 sent' link
    · intro mem
      have fromOld : (((RawCtxProtocolReveals.Owner.beacon b), 1#u64), true) ∈ s.2.1.published →
          (observe b c request r).otherFirst = true ∨ w.2.2.2.1 = some true := by
        intro old
        rcases publish old with noted | hidden
        · exact Or.inl (observe_mono b c request r noted)
        · exact Or.inr (monitor_true pre application selector aux source writer selectedMessage previousRoot response prior nonce next
            sender route read b request s w hw hidden)
      rcases request with (record | ext) | fin
      · rcases ins_publish_record pre application selector aux source writer selectedMessage previousRoot response prior nonce next
            sender route read b record s w hw mem with old | ⟨first, _⟩
        · exact fromOld old
        · rw [hr] at first
          exact Or.inl (observe_first b c record r first)
      · rw [ins_publish_other pre application selector aux source writer selectedMessage previousRoot response prior nonce next
          sender route read b _ (fun record h => by cases h) s w hw] at mem
        exact fromOld mem
      · rw [ins_publish_other pre application selector aux source writer selectedMessage previousRoot response prior nonce next
          sender route read b _ (fun record h => by cases h) s w hw] at mem
        exact fromOld mem
  · by_cases refused : c.pair.isSome ∨ c.beaconSent ∨ m0.length ≠ m1.length
    · have run : (confImpl (extra := extra) (S := S) b β (.inr (m0, m1))).run c =
          (pure ((none : Option RawCtxSourceSend.Encrypted), c) :
            OracleComp (ConfPostSpec extra S B) (Option RawCtxSourceSend.Encrypted × ConfState)) := by
        simp only [confImpl, StateT.run]
        rw [ite_eq_left_iff.mpr fun impossible => absurd refused impossible]
      have stop : runStepper (confIns b β impl (.inr (m0, m1))) c s = pure (some (none, c), s) := by
        simp only [runStepper, confIns, StateT.run_mk, run, simulateQ_pure]
        rfl
      rw [stop, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      simp only [Option.some.injEq, Prod.mk.injEq] at reached
      rw [← reached.2]
      exact ⟨link, origin, publish⟩
    · simp only [not_or, Bool.not_eq_true, not_not] at refused
      obtain ⟨unpaired, sent, equal⟩ := refused
      have none' : c.pair = none := by
        cases hc : c.pair with
        | none => rfl
        | some v => simp [hc] at unpaired
      rw [challenge_run pre application (initialLocal source selectedMessage previousRoot response) selector aux source writer prior
        sendTarget nonce next sender route read (PqxdhInitialSelectedOrigin.mark source selectedMessage) b β m0 m1 c s none' sent equal,
        support_map] at supported
      obtain ⟨w, hw, rfl⟩ := supported
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at reached
      obtain ⟨r, _, _, rfl⟩ := reached
      have empty : s.2.2.1 = none := link sent
      refine ⟨fun sent' => by simp at sent', ins_origin_step pre application selector aux source writer selectedMessage previousRoot
        response prior nonce next sender route read b _ s origin w hw, ?_⟩
      intro mem
      change (((RawCtxProtocolReveals.Owner.beacon b), 1#u64), true) ∈ w.2.2.1.published at mem
      rcases ins_publish_record pre application selector aux source writer selectedMessage previousRoot response prior nonce next
          sender route read b (.inl (.inr (.inl ⟨b, .inl (if β then m1 else m0)⟩))) s w hw mem with old | ⟨_, installed⟩
      · rcases publish old with noted | hidden
        · exact Or.inl noted
        · rw [empty] at hidden
          cases hidden
      · right
        rw [ins_send_monitor pre application (initialLocal source selectedMessage previousRoot response) selector aux source writer prior
          sendTarget nonce next sender route read (PqxdhInitialSelectedOrigin.mark source selectedMessage) b _ s empty w hw]
        have hidden := (origin installed).2 empty
        simp [hidden]

/-- Every wrapper run keeps the combined invariant at every continued result. -/
theorem all_run (β : Bool) {α : Type} (X : OracleComp (AdvSpec extra S B) α) (c : ConfState)
    (s : InsState M P I D K A N RootOracle.QueryCache S B) (inv : AllInv sendTarget b c s)
    (z : Option (α × ConfState) × InsState M P I D K A N RootOracle.QueryCache S B)
    (supported : z ∈ support (runStepper (simulateQ (confIns b β impl) X) c s))
    (value : α) (c' : ConfState) (reached : z.1 = some (value, c')) : AllInv sendTarget b c' z.2 := by
  induction X using OracleComp.inductionOn generalizing c s z with
  | pure v =>
    simp only [runStepper, simulateQ_pure, StateT.run_pure, OptionT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp only [Option.some.injEq, Prod.mk.injEq] at reached
    rw [← reached.2]
    exact inv
  | query_bind query cont ih =>
    rw [simulateQ_bind, simulateQ_spec_query, runStepper_bind, mem_support_bind_iff] at supported
    obtain ⟨w, hw, rest⟩ := supported
    rcases w with ⟨_ | ⟨reply, c1⟩, s1⟩
    · simp only [support_pure, Set.mem_singleton_iff] at rest
      subst rest
      simp at reached
    · exact ih reply c1 s1 (all_step pre application selector aux source writer selectedMessage previousRoot response prior nonce
        next sender route read b β query c s inv _ hw reply c1 rfl) z rest reached

end ConfInvariant

section GapFree
open PqxdhNativeSharedPrefix PqxdhSelectedStateInterpreter PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open RawCtxSelectedParentTable PqxdhSelectedFirstRecord PqxdhFirstBeaconRecordIntegrity PqxdhCorrelatedExpand
open PqxdhInitialBeaconAmbient PqxdhFirstBeaconRecordCtx PqxdhCorrelatedExtractFamily
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The initial transcript installs and publishes nothing for any Beacon. -/
theorem selectedAfter_beacon (front : PqxdhSelectedPostCompiler.Front M P I D K S B) (index : Fin S) (origin : Bool)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (b : Fin B) :
    (selectedAfter PqxdhInitialSourcePublication.empty front index origin reply).installed (.beacon b) = none ∧
      ∀ number value, ((RawCtxProtocolReveals.Owner.beacon b, number), value) ∉
        (selectedAfter PqxdhInitialSourcePublication.empty front index origin reply).published := by
  unfold selectedAfter
  split
  · split
    · exact ⟨rfl, fun _ _ h => by simp [PqxdhInitialSourcePublication.empty] at h⟩
    · refine ⟨?_, fun _ _ h => ?_⟩
      · simp only
        rw [Function.update_of_ne (by simp)]
        rfl
      · simp [PqxdhInitialSourcePublication.empty] at h
  · exact ⟨rfl, fun _ _ h => by simp [PqxdhInitialSourcePublication.empty] at h⟩

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (selectedMessage : Message) (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (nonce : NonceOutput) (next : RootOutput) (b : Fin B)

/-- Beacon `b`'s first record: whenever the instrumented first run of the wrapper post reaches the client event for Beacon `b`'s first record, the monitor recorded that the challenge used the selected hidden material. -/
theorem gap_free {Selection : Type}
    (adversary : Selection → RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (AdvSpec extra S B) Bool)
    (selection : Selection) (β : Bool) (ancestors disclosed : List RatchetChain)
    (result : Option Bool × InsState M P I D K A N RootOracle.QueryCache S B)
    (supported : result ∈ support (insFirstRun pre application (initialLocal source selectedMessage previousRoot response64) selector
      aux source writer selectedMessage previousRoot response64 sender route decode index metadata ready
      (confPost adversary b β selection) before (.beacon b) shared privateState cache store nonce next b))
    (event : ClientEvent source previousRoot response64 (.beacon b) 1#u64 ancestors disclosed result) :
    result.2.2.2.1 = some true := by
  unfold insFirstRun at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨built, _, hres⟩ := supported
  rw [conf_post_run, support_map] at hres
  obtain ⟨z, hz, rfl⟩ := hres
  obtain ⟨accepted, published, _, _⟩ := event
  cases hz1 : z.1 with
  | none =>
    simp [hz1] at accepted
  | some value =>
    rcases value with ⟨bit, final⟩
    simp only [hz1, Option.map_some, Option.some.injEq, confOutput, Bool.and_eq_true, decide_eq_true_eq] at accepted
    have initial := selectedAfter_beacon built.1.2 index true built.1.1 b
    have inv := all_run pre application selector aux source writer selectedMessage previousRoot response64
      (productionStream source.crypto) nonce next sender route decode b β (adversary selection built.1.1) confInitial
      ((built.1.2, built.2), (selectedAfter PqxdhInitialSourcePublication.empty built.1.2 index true built.1.1, none, false))
      ⟨fun _ => rfl, fun installed => by simp [initial.1] at installed, fun mem => absurd mem (initial.2 _ _)⟩ z hz bit final hz1
    rcases inv.2.2 published with noted | hidden
    · rw [accepted.2.2.2] at noted
      cases noted
    · exact hidden

end GapFree

section Final
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- The hidden-gap game of the wrapper post has mass zero: the client event for Beacon `b`'s first record forces the challenge to use the selected hidden material (`gap_free`). -/
theorem hiddenGap_zero (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool) (β : Bool) :
    𝒟[hiddenGapGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b β) b (firstBeacon b)]
      {true} = 0 := by
  unfold hiddenGapGame
  rw [insFullClient_run, source_map, ← prEvent_eq_evalDist_singleton _ true]
  refine prEvent_eq_zero_of_not_mem_support _ ?_
  rw [support_map]
  rintro ⟨r, hr, reached⟩
  simp only [AdaptiveCtxDynamicKnownKeys.sourceGame, support_map] at hr
  obtain ⟨full, hfullKey, rfl⟩ := hr
  rw [mem_support_bind_iff] at hfullKey
  obtain ⟨key, _, hfull⟩ := hfullKey
  have inRun : full.1 ∈ support (insFullRun setup env callbacks baseImpl kem attachedVerify primitives program
      (confPost adversary b β) b (firstBeacon b)) := by
    refine support_simulateQ_run'_subset (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder (env0).decode)
      (env0).source.crypto key) _ AdaptiveCtxDynamicKnownKeys.initialSource ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨full, hfull, rfl⟩
  unfold insFullRun at inRun
  rw [mem_support_bind_iff] at inRun
  obtain ⟨sample, _, inSuffix⟩ := inRun
  unfold insSuffixRun at inSuffix
  split at inSuffix
  · simp only [support_pure, Set.mem_singleton_iff] at inSuffix
    rw [inSuffix] at reached
    simp [readOut] at reached
  · rename_i input pending
    simp only [support_map, Set.mem_image] at inSuffix
    obtain ⟨result, resultSupported, same⟩ := inSuffix
    rw [← same] at reached
    have owner := input_selected setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b β)
      _ _ _ _ sample.1 input pending
    obtain ⟨selection, hpost⟩ := input_post setup env callbacks baseImpl kem attachedVerify primitives program
      (confPost adversary b β) _ _ _ _ sample.1 input pending
    simp only [readOut, gapOut, clientOut, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      at reached
    obtain ⟨event, notHidden⟩ := reached
    rw [owner] at event
    rw [owner, hpost] at resultSupported
    exact notHidden (gap_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ adversary selection β _ _ result resultSupported event)

/-- First-record left-or-right confidentiality (S7). For any adversary against the full post-registration protocol (secrets sampled inside, HB-112 actual game) choosing two equal-length plaintexts for the first send of Beacon `b`, the difference between the accepted pending masses of the two challenge bits is at most, for each bit: the confidentiality client's ordinary CTX privacy loss `twinLoss` (IND$ advantages of the constructed validation and view reductions, `qHash/2^128`, twice the INT-CTXT advantages of the constructed attempt-indexed reductions, `qRaw/2^512`), the HB-112 first-record target loss and completed-branch root loss of the challenge-fixed post (advantages of C1's constructed reductions), the explicit games `collGame` (the client event holds and a Beacon finish made a selected raw opening) and `keyGame` (in the key-last run, the first-record event and no hidden disclosure hold while the uniform record key equals a revealed value), which are not yet bounded by assumption terms, and the nonce-repeat stop bound of `PqxdhFirstRecordStopTagged.stop_bound`; plus `2 * 2^-256` for the initial half alias. The stop and CTX budgets are those of the certificates `c0` and `c1` of the two wrapper posts (`first_record_confidentiality_budget` states them with the adversary's own budget). The hidden-gap game of the output switch has mass zero (`hiddenGap_zero`). The restrictions are enforced by the wrapper `confPost` and by HB-112's event: equal lengths, the challenge is the first acceptable challenge and Beacon `b`'s unique sequence-one record, raw-receive replies whose plaintext is a challenge plaintext are reported as failures (finish replies are covered by `collGame`), and the selected chain and record key stay undisclosed. The two plaintext-independent random views are equal (`random_views_equal`). -/
theorem first_record_confidentiality (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (c0 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b false))
    (c1 : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program (confPost adversary b true))
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small0 : 1 + postTotal setup env callbacks baseImpl kem program c0 < 2 ^ 96)
    (small1 : 1 + postTotal setup env callbacks baseImpl kem program c1 < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0 ctxFallback
      qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1 ctxFallback
      qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false) c0) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true) c1) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b (firstBeacon b)]
      {true}).toReal +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b (firstBeacon b)]
      {true}).toReal +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) (firstBeacon b)]
      {true}).toReal +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) (firstBeacon b)]
      {true}).toReal +
    ((1 + c0.postBudget (.inl .send) + 51 * (c0.postBudget (.inl .raw) + c0.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    ((1 + c1.postBudget (.inl .send) + 51 * (c1.postBudget (.inl .raw) + c1.postBudget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256 +
    2 / 2 ^ 256 := by
  have left := bit_bounds setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b c0
    compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 prepareHash0 small0
  have right := bit_bounds setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b c1
    compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude1 prepareHash1 small1
  have gap0 := congrArg ENNReal.toReal (hiddenGap_zero setup env callbacks baseImpl kem attachedVerify primitives program b adversary false)
  have gap1 := congrArg ENNReal.toReal (hiddenGap_zero setup env callbacks baseImpl kem attachedVerify primitives program b adversary true)
  rw [ENNReal.toReal_zero] at gap0 gap1
  have views := congrArg ENNReal.toReal
    (random_views_equal setup env callbacks baseImpl kem attachedVerify primitives program b adversary)
  have stop0 := stop_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) c0 b
  have stop1 := stop_real setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) c1 b
  have n1 := ENNReal.toReal_nonneg (a := twinLoss setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b false) b c0 ctxFallback qPrelude0)
  have n2 := ENNReal.toReal_nonneg (a := twinLoss setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b true) b c1 ctxFallback qPrelude1)
  have n5 := ENNReal.toReal_nonneg (a := 𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b false) b (firstBeacon b)] {true})
  have n6 := ENNReal.toReal_nonneg (a := 𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b true) b (firstBeacon b)] {true})
  have n7 := ENNReal.toReal_nonneg (a := 𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b false) (firstBeacon b)] {true})
  have n8 := ENNReal.toReal_nonneg (a := 𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b true) (firstBeacon b)] {true})
  have n9 := ENNReal.toReal_nonneg (a := 𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b false) (firstBeacon b)] {true})
  have n10 := ENNReal.toReal_nonneg (a := 𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program
    (confPost adversary b true) (firstBeacon b)] {true})
  unfold confGame
  rw [abs_le]
  constructor <;> linarith [left.1, left.2, right.1, right.2]


end Final

section AdversaryBudget
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : Program baseSpec setup.Context S (B + 1))

/-- The adversary's per-kind request budget: every adversary run makes at most `budget kind` requests of each kind of the post interface, where each challenge query counts as the Beacon `b` send it may become. -/
def AdvBounded (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) : Prop :=
  ∀ selection reply kind, (adversary selection reply).IsQueryBoundP
    (liftPred b (fun query => PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec) query = kind)) (budget kind)

/-- The wrapper post keeps the adversary's per-kind budget. -/
theorem confPost_bounded (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program b adversary budget) (β : Bool)
    (selection : program.Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) :
    PqxdhPhase2SourceSchedulerBounds.Bounded (confPost adversary b β selection reply) budget := by
  intro kind
  unfold confPost
  rw [isQueryBoundP_map_iff]
  exact conf_query_bound b β _ (adversary selection reply) (budget kind) (bounded selection reply kind) confInitial

/-- A resource certificate for the wrapper post, built from a certificate of any post (only its program and environment fields are used) and the adversary's per-kind budget. -/
def confCertificate {post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post0) (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program b adversary budget) (β : Bool) :
    PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (confPost adversary b β) :=
  { c with
    postBudget := budget
    postBound := confPost_bounded program b adversary budget bounded β }

end AdversaryBudget

section BudgetHeadline
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity PqxdhFirstBeaconRecordCtx CtxRomAuth AdaptiveCtxSharedHash
open RawCtxSelectedAuthenticationObserver AdaptiveCtxDynamicKnownBounds AdaptiveCtxQueryBounds AdaptiveCtxReceive
open CtxNonceAeadIntCtxt CtxNonceAeadIndDollarValidation
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅

/-- First-record left-or-right confidentiality with the adversary's own budget: `first_record_confidentiality` for the certificates `confCertificate` built from a certificate of any post and the adversary's per-kind budget `budget` (each challenge counted as one Beacon `b` send). The CTX budgets inside `twinLoss` are those of these certificates, and both stop bounds become `(1 + budget send + 51 * (budget raw + budget finish)) / 2^256`. The explicit games `collGame` and `keyGame` are not yet bounded by assumption terms. -/
theorem first_record_confidentiality_budget (b : Fin (B + 1))
    (adversary : program.Selection → RustM (Option PqxdhServerRegistrationPublication.Response) →
      OracleComp (AdvSpec (SelectorSpec baseSpec) S (B + 1)) Bool)
    {post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1)}
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget) (bounded : AdvBounded program b adversary budget)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery)
    (ctxFallback : ModifiedNonceAeadForgery) (qPrelude0 qPrelude1 : Nat)
    (prepareHash0 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false)
      qPrelude0)
    (prepareHash1 : PrepareHashBudget setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true)
      qPrelude1)
    (small : 1 + ∑ kind, budget kind < 2 ^ 96) :
    |(𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary false] {true}).toReal -
      (𝒟[confGame setup env callbacks baseImpl kem attachedVerify primitives program b adversary true] {true}).toReal| ≤
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded false) ctxFallback qPrelude0).toReal +
    (twinLoss setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b
      (confCertificate env0 baseImpl kem program c b adversary budget bounded true) ctxFallback qPrelude1).toReal +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b false)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b false)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded false)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b false) hmac fallback
      ordinaryFallback) +
    (PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (confPost adversary b true)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (confPost adversary b true)
        (confCertificate env0 baseImpl kem program c b adversary budget bounded true)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (confPost adversary b true) hmac fallback
      ordinaryFallback) +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) b (firstBeacon b)]
      {true}).toReal +
    (𝒟[collGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) b (firstBeacon b)]
      {true}).toReal +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b false) (firstBeacon b)]
      {true}).toReal +
    (𝒟[keyGame setup env callbacks baseImpl kem attachedVerify primitives program (confPost adversary b true) (firstBeacon b)]
      {true}).toReal +
    2 * (((1 + budget (.inl .send) + 51 * (budget (.inl .raw) + budget (.inr 5)) : ℕ) : ℝ) / 2 ^ 256) +
    2 / 2 ^ 256 := by
  have bound := first_record_confidentiality setup env callbacks baseImpl kem attachedVerify primitives program b adversary
    (confCertificate env0 baseImpl kem program c b adversary budget bounded false)
    (confCertificate env0 baseImpl kem program c b adversary budget bounded true)
    compatible adapter functional hmac correct fallback ordinaryFallback ctxFallback qPrelude0 qPrelude1 prepareHash0 prepareHash1
    small small
  refine bound.trans (le_of_eq ?_)
  simp only [confCertificate]
  ring

end BudgetHeadline
end BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.tsum_map_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.tsum_map_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.tsum_fiber_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.tsum_fiber_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_event

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.runLogged_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.runLogged_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomView_collapse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomView_collapse

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_state_map_apply' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_state_map_apply

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ident_ident' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ident_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ident_length' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ident_length

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomSeal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomSeal_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomSeal_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomSeal_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_seal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_seal

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.loggedPlaintext_ident' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.loggedPlaintext_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.simulatedOpen_ident' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.simulatedOpen_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_coin_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_coin_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_seal_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_seal_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_raw_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_raw_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_liftComp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower4_liftComp

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.privateStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.privateStep_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_coin_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_coin_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.publicOracle_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.publicOracle_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_hash_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_hash_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.sealStep_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.sealStep_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_seal_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_seal_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_raw_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower3_raw_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.publicReply_ident' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.publicReply_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.guard_forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.guard_forward

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_coin_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_coin_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_hash_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_hash_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_seal_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_seal_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_raw_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower2_raw_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.confRandomImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.confRandomImpl_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.reduction_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.reduction_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.forward_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.forward_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_quiet_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_quiet_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_seal_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_seal_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_raw_ident' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_raw_ident

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_compatible

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomView_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomView_twin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_erase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_sticky' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_markRaw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_markRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.runStepper_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.runStepper_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.runStepper_dead' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.runStepper_dead

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.same_refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.same_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.same_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.same_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.same_pre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.same_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_event

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomView_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.randomView_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_run_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_run_inv

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.single_output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.single_output

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.single_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.single_true

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.suppress_challenge' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.suppress_challenge

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.suppress_other' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.suppress_other

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.unscreened_reveals' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.unscreened_reveals

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.run_good_back' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.run_good_back

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.good_output_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.good_output_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.good_event_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.good_event_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.trOriginal_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.trOriginal_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traced_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traced_agree

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traced_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traced_read

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.trOriginal_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.trOriginal_read

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traced_event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traced_event_good

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ownerMarked_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ownerMarked_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ownerMarked_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ownerMarked_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.marked_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.marked_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.optionalClient_bind' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.optionalClient_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.marked_flag_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.marked_flag_none

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_evaluate' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_evaluate

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insAugmented_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insAugmented_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insAugmented_nonstop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insAugmented_nonstop

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvaluated_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvaluated_program

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvaluated_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvaluated_stop

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insImpl_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insImpl_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvaluated_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvaluated_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insAugmented_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insAugmented_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insPost_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insPost_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insPost_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insPost_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.post_source_augmented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.post_source_augmented

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.augmented_le_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.augmented_le_evaluated

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.evaluated_le_augmented' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.evaluated_le_augmented

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.flagged_le_stop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.flagged_le_stop

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.true_mass_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.true_mass_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.map_le_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.map_le_add

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.built_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.built_upper

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.built_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.built_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.firstRun_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.firstRun_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_upper

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pending_ideal_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pending_ideal_upper

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pending_ideal_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pending_ideal_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvent_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insEvent_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFirstClient_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFirstClient_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insPostBit_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insPostBit_ghost

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insCompiledRun_postBit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insCompiledRun_postBit

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insRun_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insRun_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFirstRun_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFirstRun_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insObserve_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insObserve_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.prepared_reorder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.prepared_reorder

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insCompiled_le_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insCompiled_le_separated

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insSeparated_le_compiled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insSeparated_le_compiled

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insClient_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insClient_source

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insSeparated_le_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insSeparated_le_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insClient_le_separated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insClient_le_separated

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFullClient_uses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFullClient_uses

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_bind_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_bind_refl

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_post_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.conf_post_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.pre_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beginSend_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beginSend_context

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.normalBegin_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.normalBegin_context

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.send_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.send_twin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.challenge_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.challenge_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenStep_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenStep_first

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_send_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_send_monitor

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_beacon

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.challenge_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.challenge_twin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_rawfree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_rawfree

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_pure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_raw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_quiet' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_query_raw' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_query_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_query_quiet' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stable_query_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.raw_of_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.raw_of_target

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.send_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.send_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.owner_send_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.owner_send_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beacon_send_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beacon_send_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.server_send_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.server_send_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.public_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.public_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.family_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.family_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finish_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finish_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.apiReply_rel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.apiReply_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.receive_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.receive_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.raw_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.raw_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.owner_raw_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.owner_raw_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.server_raw_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.server_raw_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beacon_raw_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beacon_raw_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.adv_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.adv_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ident_pair' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ident_pair

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.suppress_rel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.suppress_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_pair

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_server_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_server_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_beacon_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_beacon_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.screen_server_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.screen_server_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.screen_beacon_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.screen_beacon_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_server_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_server_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_beacon_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_beacon_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_of_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_of_stable

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.step_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.step_twin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_monitor

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.monitorAfter_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.monitorAfter_some

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_monitor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_monitor

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_keep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_keep

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_post_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_post_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFirstRun_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFirstRun_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.dispatch_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.dispatch_same

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.prelude_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.prelude_same

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.input_relate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.input_relate

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.input_completed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.input_completed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twinOut_dead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twinOut_dead

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.client_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.client_pre

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.map_le_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.map_le_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFullClient_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.insFullClient_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.source_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.source_map

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_le_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_le_client

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.client_le_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.client_le_twin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.privacyLoss_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.privacyLoss_ne_top

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.source_random' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.source_random

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ideal_le_twin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ideal_le_twin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_le_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.twin_le_ideal

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.bit_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.bit_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_views_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.random_views_equal

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stop_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.stop_real

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.cached_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.cached_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.future_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.future_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finish_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finish_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.terminal_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.terminal_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.receive_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.receive_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.raw_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.raw_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ChainKept.est' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ChainKept.est

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ChainKept.refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ChainKept.refl

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ChainKept.hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ChainKept.hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beacon_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.beacon_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.live_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.live_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower_initial_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.lower_initial_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finish_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finish_some

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finishApplication_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.finishApplication_chain

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.owner_marked_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.owner_marked_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_support' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.markRaw_support

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenStep_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenStep_other

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenStep_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenStep_send

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_installed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_installed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_origin_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_origin_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.traceRecord_entry

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_first

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.observe_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_publish_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_publish_record

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_publish_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.ins_publish_other

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.monitor_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.monitor_true

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.all_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.all_step

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.all_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.all_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.selectedAfter_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.selectedAfter_beacon

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.gap_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.gap_free

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenGap_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.hiddenGap_zero

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_record_confidentiality' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_record_confidentiality

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.confPost_bounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.confPost_bounded

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_record_confidentiality_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordConfidentiality.first_record_confidentiality_budget

import BeaconcryptCore.Computational.PqxdhFirstRecordTarget
import BeaconcryptCore.Computational.PqxdhSelectedFirstRecord
/-!
First Beacon record integrity for a protocol-derived key, reduced to one compiled CTX game and one explicit restricted stop game. The adversary's post program `post0` is wrapped by the public proxy `forgeryPost`, which logs every post request with its reply and outputs `post0`'s bit together with `Forged`: some Server raw receive at the registered peer (Server `env.index`, key identifier of the registration reply) accepted a sequence-one record whose decoded frame differs from the decoded frame of every sequence-one record returned by an earlier send of any Server or Beacon. Logging adds no request, so the original query certificate transfers unchanged. Comparing with the sends of every role, not only Beacon `b`, means that a genuine first record of another sender whose chain reaches the selected root (for example a second Beacon holding the same Diffie-Hellman handles) is not counted as a forgery; comparing decoded frames means that a re-encoding of a sent frame is not counted either. `forged_single` shows that the event is not vacuous.

For the fixed target Beacon `b`, record one, no ancestors and no disclosures, the HB-112 actual game with this proxy post, minus its constant-`false` continuation, is bounded by the first-record target loss and the completed-branch root loss of `PqxdhFirstRecordTarget`, each the advantage of a constructed reduction, plus the `true` mass of `compiledGame` (the selected first Server builder followed by the executable key-free CTX post client, evaluated by the real selected-key challenger; the event is that the client did not stop and returned `true`, i.e. `post0` and `Forged`), plus `stopMass`, the `true` mass of `stopGame` (the same augmented post run reached an exact selected-nonce stop and, at its end, the selected chain was still undisclosed). The counted mass is the pending mass of the HB-112 target decision, so it covers only runs in which Beacon `b` published its first record from the selected root and the selected chain was never disclosed. The pending source-observer mass is rewritten exactly into the selected first-record run of `PqxdhSelectedFirstRecord` on the key-last side, before the KEM secret is forgotten, so no callback premise remains; the publication and selected-key conjuncts of the source decision are dropped, which is sound for an upper bound, while the undisclosure of the selected chain is kept; hidden-disclosure stopping is removed exactly by `PqxdhSelectedPostDisclosure.event_good`; and the executable client is reached by an identical-until-stop coupling restricted to the kept event (`restricted_le`), so a stop that happens only after the selected chain was disclosed is not charged.

Limits: the builder in `compiledGame` is still the selected-material source builder (it uses the selected material only where one of its derivations reaches the selected root), and the post starts from the CTX challenger state `initialSource` carrying the builder's hash cache. Sampling the key first (in `compiledGame` it is sampled last and independently, so this is an exchange of independent samples), compiling the builder, proving that a non-stopped `true` run of the combined client is a win of `RawCtxSelectedAuthenticationObserver`, and applying its `authentication_bound` remain to be done; that win step also needs explicit codec facts, namely that bytes produced by the record writer decode back to the written frame and that every selected seal before the acceptance is returned by its send (a seal whose writer fails is recorded by the CTX challenger but never reaches the transcript). `stopMass` is left for a separate bound: the restriction removes the case in which the adversary learns the selected chain and then searches for a public HKDF preimage, but two Beacons of the prepared front with identical Diffie-Hellman handles still make it large, so it needs a front hypothesis or a charged preparation-phase event. The replay corollary shows that an exact replay of an accepted record is rejected by the extracted receive driver and that rejected receives never change `Forged`.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity

section Transcript
variable {ι : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- The adversary's post interface. -/
abbrev PostSpec (baseSpec : OracleSpec ι) (S B : Nat) := PqxdhPhase2SourceScheduler.Spec baseSpec S B

/-- One post request together with the reply it actually received. -/
abbrev Entry (baseSpec : OracleSpec ι) (S B : Nat) :=
  (query : (PostSpec baseSpec S B).Domain) × (PostSpec baseSpec S B).Range query

/-- Forward every request unchanged and append it with its actual reply to the transcript. -/
def recorder : QueryImpl (PostSpec baseSpec S B) (StateT (List (Entry baseSpec S B)) (OracleComp (PostSpec baseSpec S B))) :=
  fun query log => do
    let reply ← (PostSpec baseSpec S B).query query
    pure (reply, log ++ [⟨query, reply⟩])

/-- Run a post program while recording its complete transcript. -/
noncomputable def logged {Result : Type} (client : OracleComp (PostSpec baseSpec S B) Result) (log : List (Entry baseSpec S B)) :
    OracleComp (PostSpec baseSpec S B) (Result × List (Entry baseSpec S B)) :=
  (simulateQ recorder client).run log

/-- A Server raw receive request with its index, raw bytes and optional decrypted reply. -/
def serverOpen : Entry baseSpec S B → Option (Fin S × Pqxdh.Bytes × core.option.Option RawCtxWholeOwner.Decrypted)
  | ⟨.inl (.inl (.inl (.inl ⟨index, .inr raw⟩))), reply⟩ => some (index, raw, reply)
  | _ => none

/-- The encrypted record returned by a successful Server or Beacon send request. -/
def sent : Entry baseSpec S B → Option RawCtxSourceSend.Encrypted
  | ⟨.inl (.inl (.inl (.inl ⟨_, .inl _⟩))), reply⟩ => reply
  | ⟨.inl (.inl (.inl (.inr (.inl ⟨_, .inl _⟩)))), reply⟩ => reply
  | _ => none

/-- A successful send in the transcript returned a sequence-one record whose wire bytes decode to `frame`. -/
def FirstSent (decode : RawCtxReceive.FrameDecoder) (log : List (Entry baseSpec S B))
    (frame : Option RawCtxReceive.DecodedFrame) : Prop :=
  ∃ entry ∈ log, ∃ encrypted, sent entry = some encrypted ∧ encrypted.sequence.val = 1 ∧ decode encrypted.ciphertext = frame

/-- Some Server raw receive at `index`, routed to `kid`, accepted a sequence-one record whose decoded frame differs from every sequence-one record returned by an earlier send. -/
def Forged (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (log : List (Entry baseSpec S B)) : Prop :=
  ∃ before entry after raw decrypted, log = before ++ entry :: after ∧
    serverOpen entry = some (index, raw, .Some decrypted) ∧ route raw = some kid ∧ decrypted.sequence.val = 1 ∧
    ¬FirstSent decode before (decode raw)

/-- The forgery event for the registration reply: its key identifier names the Server peer; an unsuccessful registration has no forgery. -/
def ReplyForged (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (log : List (Entry baseSpec S B)) : Prop :=
  match reply with
  | .ok (some response) => Forged index route decode response.keyId log
  | _ => False

/-- The logged post bit: the adversary's own bit and the public forgery event. -/
noncomputable def forgeryBit (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (reply : RustM (Option PqxdhServerRegistrationPublication.Response)) (result : Bool × List (Entry baseSpec S B)) : Bool :=
  result.1 && @decide (ReplyForged index route decode reply result.2) (Classical.propDecidable _)

/-- Recording the transcript leaves every forwarded request unchanged, so each query predicate keeps its bound. -/
theorem logged_queries {Result : Type} (predicate : (PostSpec baseSpec S B).Domain → Prop) [DecidablePred predicate]
    (client : OracleComp (PostSpec baseSpec S B) Result) (log : List (Entry baseSpec S B)) (bound : Nat) :
    (logged client log).IsQueryBoundP predicate bound ↔ client.IsQueryBoundP predicate bound := by
  induction client using OracleComp.inductionOn generalizing log bound with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [logged, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    simp only [recorder, StateT.run, bind_assoc, pure_bind]
    simp only [isQueryBoundP_query_bind_iff]
    exact and_congr_right fun _ => forall_congr' fun reply => ih reply _ _

/-- A transcript entry for a Server raw receive request with its optional reply. -/
def serverRawEntry (index : Fin S) (raw : Pqxdh.Bytes) (reply : core.option.Option RawCtxWholeOwner.Decrypted) :
    Entry baseSpec S B :=
  ⟨.inl (.inl (.inl (.inl ⟨index, .inr raw⟩))), reply⟩

/-- A send witness in a transcript remains a witness after inserting any entry. -/
theorem firstSent_insert (decode : RawCtxReceive.FrameDecoder) (pre post : List (Entry baseSpec S B)) (inserted : Entry baseSpec S B)
    (frame : Option RawCtxReceive.DecodedFrame) (witness : FirstSent decode (pre ++ post) frame) :
    FirstSent decode (pre ++ inserted :: post) frame := by
  obtain ⟨entry, present, encrypted, sentEntry, sequence, decoded⟩ := witness
  refine ⟨entry, ?_, encrypted, sentEntry, sequence, decoded⟩
  simp only [List.mem_append, List.mem_cons] at present ⊢
  tauto

/-- Inserting an entry that is not a successful send adds no send witness. -/
theorem firstSent_erase (decode : RawCtxReceive.FrameDecoder) (pre post : List (Entry baseSpec S B)) (inserted : Entry baseSpec S B)
    (unsent : sent inserted = none) (frame : Option RawCtxReceive.DecodedFrame)
    (witness : FirstSent decode (pre ++ inserted :: post) frame) : FirstSent decode (pre ++ post) frame := by
  obtain ⟨entry, present, encrypted, sentEntry, sequence, decoded⟩ := witness
  refine ⟨entry, ?_, encrypted, sentEntry, sequence, decoded⟩
  simp only [List.mem_append, List.mem_cons] at present ⊢
  rcases present with inPre | same | inPost
  · exact Or.inl inPre
  · subst same
    rw [unsent] at sentEntry
    cases sentEntry
  · exact Or.inr inPost

/-- A position in a list with one inserted element is the inserted element, a position before it, or a position after it. -/
theorem split_insert {α : Type} (pre post before after : List α) (inserted entry : α)
    (split : pre ++ inserted :: post = before ++ entry :: after) :
    (entry = inserted ∧ before = pre ∧ after = post) ∨
      (∃ middle, pre = before ++ entry :: middle ∧ after = middle ++ inserted :: post) ∨
      (∃ middle, post = middle ++ entry :: after ∧ before = pre ++ inserted :: middle) := by
  induction pre generalizing before with
  | nil =>
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at split
      exact Or.inl ⟨split.1.symm, rfl, split.2.symm⟩
    | cons head tail =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at split
      exact Or.inr (Or.inr ⟨tail, split.2, by simp [split.1]⟩)
  | cons head tail ih =>
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at split
      exact Or.inr (Or.inl ⟨tail, by simp [split.1], split.2.symm⟩)
    | cons first rest =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, split⟩ := split
      rcases ih rest split with ⟨same, rfl, rfl⟩ | ⟨middle, preEq, afterEq⟩ | ⟨middle, postEq, beforeEq⟩
      · exact Or.inl ⟨same, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨middle, by simp [preEq], afterEq⟩)
      · exact Or.inr (Or.inr ⟨middle, postEq, by simp [beforeEq]⟩)

/-- A position in a concatenation lies in its first or its second part. -/
theorem split_append {α : Type} (pre post before after : List α) (entry : α)
    (split : pre ++ post = before ++ entry :: after) :
    (∃ middle, pre = before ++ entry :: middle ∧ after = middle ++ post) ∨
      (∃ middle, post = middle ++ entry :: after ∧ before = pre ++ middle) := by
  induction pre generalizing before with
  | nil => exact Or.inr ⟨before, split, by simp⟩
  | cons head tail ih =>
    cases before with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at split
      exact Or.inl ⟨tail, by simp [split.1], split.2.symm⟩
    | cons first rest =>
      simp only [List.cons_append, List.cons.injEq] at split
      obtain ⟨rfl, split⟩ := split
      rcases ih rest split with ⟨middle, preEq, afterEq⟩ | ⟨middle, postEq, beforeEq⟩
      · exact Or.inl ⟨middle, by simp [preEq], afterEq⟩
      · exact Or.inr ⟨middle, postEq, by simp [beforeEq]⟩

/-- A transcript entry that is neither a successful send nor an accepted Server raw receive at the Server index can be inserted anywhere without changing the forgery event: only accepted receives are counted, and only sends are compared. -/
theorem forged_insert (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (pre post : List (Entry baseSpec S B)) (inserted : Entry baseSpec S B)
    (unsent : sent inserted = none)
    (unaccepted : ∀ raw decrypted, serverOpen inserted ≠ some (index, raw, .Some decrypted)) :
    Forged index route decode kid (pre ++ inserted :: post) ↔ Forged index route decode kid (pre ++ post) := by
  constructor
  · rintro ⟨before, entry, after, raw, decrypted, split, opened, routed, sequence, fresh⟩
    rcases split_insert pre post before after inserted entry split with
      ⟨rfl, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
    · exact False.elim (unaccepted raw decrypted opened)
    · exact ⟨before, entry, middle ++ post, raw, decrypted, by simp, opened, routed, sequence, fresh⟩
    · refine ⟨pre ++ middle, entry, after, raw, decrypted, by simp, opened, routed, sequence, ?_⟩
      exact fun witness => fresh (firstSent_insert decode pre middle inserted _ witness)
  · rintro ⟨before, entry, after, raw, decrypted, split, opened, routed, sequence, fresh⟩
    rcases split_append pre post before after entry split with ⟨middle, rfl, rfl⟩ | ⟨middle, rfl, rfl⟩
    · exact ⟨before, entry, middle ++ inserted :: post, raw, decrypted, by simp, opened, routed, sequence, fresh⟩
    · refine ⟨pre ++ inserted :: middle, entry, after, raw, decrypted, by simp, opened, routed, sequence, ?_⟩
      exact fun witness => fresh (firstSent_erase decode pre middle inserted unsent _ witness)

/-- Non-vacuity: a transcript whose only entry is an accepted sequence-one Server raw receive at `index` routed to `kid` is a forgery. -/
theorem forged_single (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (raw : Pqxdh.Bytes) (decrypted : RawCtxWholeOwner.Decrypted)
    (routed : route raw = some kid) (sequence : decrypted.sequence.val = 1) :
    Forged index route decode kid [serverRawEntry (baseSpec := baseSpec) (B := B) index raw (.Some decrypted)] :=
  ⟨[], _, [], raw, decrypted, rfl, rfl, routed, sequence, fun ⟨_, present, _⟩ => by simp at present⟩

/-- Replay (audit F7): once the extracted receive driver accepted `raw` on `entry` and moved to `result`, an exact replay of `raw` on `result` is rejected with the unchanged kernel; and a rejected Server raw receive entry, wherever it is inserted in the transcript, neither creates nor removes a forgery. The theorem does not prove that the Server receive wrapper's transcript reply to the replay is the driver's `.None`; that link is the wrapper's own behaviour. Independently of rejection, a replay of a record returned by an earlier send is never counted, because `Forged` compares with every earlier send. -/
theorem replay_not_counted (index : Fin S) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (kid : Std.U64) (c : Pqxdh.Crypto) (execute : KdfInterpreter) (expected : Std.U64) (ad raw plaintext : Pqxdh.Bytes)
    (entry result : ConcreteRatchetKernel) (valid : ratchet.refined.ValidRefined entry.refined)
    (accepted : RawCtxReceive.rawReceive decode c execute expected ad raw entry = ok (result, .Some plaintext))
    (pre post : List (Entry baseSpec S B)) :
    RawCtxReceive.rawReceive decode c execute expected ad raw result = ok (result, .None) ∧
      (Forged index route decode kid (pre ++ serverRawEntry index raw .None :: post) ↔ Forged index route decode kid (pre ++ post)) :=
  ⟨RawCtxReceive.rawReceive_success_replay decode c execute expected ad raw plaintext entry result valid accepted,
    forged_insert index route decode kid pre post _ rfl (fun _ _ same => by cases same)⟩

end Transcript

section Post
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

/-- The public forgery proxy: run `post0` while logging its transcript and output its bit together with the Server-peer first-record forgery event. -/
noncomputable def forgeryPost : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1) :=
  fun selection reply => forgeryBit env.index env.route env.decode reply <$> logged (post0 selection reply) []

/-- The forgery proxy makes exactly the requests of `post0`, so it keeps every post query budget. -/
theorem forgery_query_bound (selection : program.Selection) (reply : RustM (Option PqxdhServerRegistrationPublication.Response))
    (predicate : (PostSpec baseSpec S (B + 1)).Domain → Prop) [DecidablePred predicate] (bound : Nat) :
    (forgeryPost env program post0 selection reply).IsQueryBoundP predicate bound ↔
      (post0 selection reply).IsQueryBoundP predicate bound := by
  simp only [forgeryPost, isQueryBoundP_map_iff]
  exact logged_queries predicate (post0 selection reply) [] bound

/-- The original certificate transported to the forgery proxy: only the post budget refers to the post, and it is unchanged. -/
def certificate (c : PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program post0) :
    PqxdhAuthenticatedRootBudgets.Certificate env baseImpl kem program (forgeryPost env program post0) :=
  { c with
    postBound := by
      intro selection reply kind
      exact (forgery_query_bound env program post0 selection reply _ _).mpr (c.postBound selection reply kind) }

end Post

/-- A Boolean game whose pointwise continuation is dominated by the sum of two continuations is dominated by the two games. -/
theorem true_bind_le {α : Type} (mx : ProbComp α) (f g h : α → ProbComp Bool)
    (le : ∀ a, 𝒟[f a] {true} ≤ 𝒟[g a] {true} + 𝒟[h a] {true}) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} + 𝒟[mx >>= h] {true} := by
  have pointwise : ∀ a, Pr{let x ← f a}[x = true] ≤ Pr{let x ← g a}[x = true] + Pr{let x ← h a}[x = true] :=
    fun a => by
      rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
      exact le a
  rw [← prEvent_eq_evalDist_singleton (mx >>= f), ← prEvent_eq_evalDist_singleton (mx >>= g),
    ← prEvent_eq_evalDist_singleton (mx >>= h)]
  simp only [OracleComp.prEvent_bind_eq_tsum, ← ENNReal.tsum_add, ← mul_add]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (pointwise a) zero_le

/-- A Boolean projection of one game exceeds the same projection of another game by at most their total-variation distance. -/
theorem map_le_tvDist {α : Type} (mx my : ProbComp α) (f : α → Bool) :
    𝒟[f <$> mx] {true} ≤ 𝒟[f <$> my] {true} + ENNReal.ofReal (tvDist mx my) := by
  have distance : |(𝒟[f <$> mx] {true}).toReal - (𝒟[f <$> my] {true}).toReal| ≤ tvDist mx my := by
    rw [VCVioLegacy.evalDist_singleton_eq_probOutput, VCVioLegacy.evalDist_singleton_eq_probOutput]
    exact (abs_probOutput_toReal_sub_le_tvDist _ _).trans (tvDist_map_le _ mx my)
  have upper := (abs_le.mp distance).2
  have finite : ∀ mz : ProbComp α, 𝒟[f <$> mz] {true} ≠ ⊤ := fun mz => by
    rw [← prEvent_eq_evalDist_singleton _ true]; exact prEvent_ne_top _
  rw [← ENNReal.ofReal_toReal (finite mx), ← ENNReal.ofReal_toReal (finite my),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (tvDist_nonneg mx my)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The mass of an event equals the `true` mass of its decided indicator. -/
theorem setOf_bool {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : ProbComp α) (p : α → Prop) [DecidablePred p] :
    𝒟[mx] {x | p x} = 𝒟[(fun x => decide (p x)) <$> mx] {true} := by
  rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_singleton _ true, prEvent_map]
  simp only [decide_eq_true_eq]


/-- Weakening a Boolean projection pointwise weakens its `true` mass. -/
theorem map_mono {α : Type} (mx : ProbComp α) (f g : α → Bool) (weaker : ∀ a, f a = true → g a = true) :
    𝒟[f <$> mx] {true} ≤ 𝒟[g <$> mx] {true} := by
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  exact prEvent_mono _ _ _ fun a => weaker a

/-- From a flagged state, every output of a marked run stays flagged. -/
theorem flagged_run {ι σ X : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (client : OracleComp spec X) (state : σ × Bool) (flagged : state.2 = true) (result : X × σ × Bool)
    (supported : result ∈ support ((simulateQ (RawCtxSelectedFamilyNonceCoupling.marked handler bad) client).run state)) :
    result.2.2 = true := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact flagged
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨step, stepSupported, rest⟩ := supported
    exact ih step.1 step.2 (RawCtxSelectedFamilyNonceCoupling.marked_sticky handler bad query state flagged step stepSupported) rest

/-- A marked run started from a flagged state has no unflagged output. -/
theorem flagged_absent {ι σ X : Type} {spec : OracleSpec ι}
    (handler : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (client : OracleComp spec X) (state : σ) (value : X) (final : σ) :
    (value, (final, false)) ∉ support ((simulateQ (RawCtxSelectedFamilyNonceCoupling.marked handler bad) client).run (state, true)) :=
  fun supported => Bool.false_ne_true (flagged_run handler bad client (state, true) rfl _ supported)

/-- Two marked runs whose callbacks agree whenever the bad predicate fails put the same mass on every unflagged output. -/
theorem unflagged_eq {ι σ X : Type} {spec : OracleSpec ι} [MeasurableSpace (X × σ × Bool)]
    [MeasurableSingletonClass (X × σ × Bool)]
    (left right : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (agree : ∀ query state, ¬ bad query state → (left query).run state = (right query).run state)
    (client : OracleComp spec X) (state : σ) (value : X) (final : σ) :
    𝒟[(simulateQ (RawCtxSelectedFamilyNonceCoupling.marked left bad) client).run (state, false)] {(value, (final, false))} =
      𝒟[(simulateQ (RawCtxSelectedFamilyNonceCoupling.marked right bad) client).run (state, false)] {(value, (final, false))} := by
  rw [← prEvent_eq_evalDist_singleton _ (value, (final, false)),
    ← prEvent_eq_evalDist_singleton _ (value, (final, false))]
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr ?_
    rintro ⟨reply, next, flag⟩
    cases flag with
    | true =>
      rw [prEvent_eq_zero_of_not_mem_support _ (flagged_absent left bad (continuation reply) next value final),
        prEvent_eq_zero_of_not_mem_support _ (flagged_absent right bad (continuation reply) next value final), mul_zero,
        mul_zero]
    | false =>
      -- Event form of `RawCtxSelectedFamilyNonceCoupling.marked_agree` (stated with a local σ-algebra), by the same two cases.
      have step : Pr{let y ← (RawCtxSelectedFamilyNonceCoupling.marked left bad query).run (state, false)}[
            y = (reply, (next, false))] =
          Pr{let y ← (RawCtxSelectedFamilyNonceCoupling.marked right bad query).run (state, false)}[
            y = (reply, (next, false))] := by
        by_cases hit : bad query state
        · rw [prEvent_eq_zero_of_not_mem_support _ fun supported => Bool.false_ne_true
              (RawCtxSelectedFamilyNonceCoupling.marked_hit left bad query (state, false) hit _ supported),
            prEvent_eq_zero_of_not_mem_support _ fun supported => Bool.false_ne_true
              (RawCtxSelectedFamilyNonceCoupling.marked_hit right bad query (state, false) hit _ supported)]
        · have equal := agree query state hit
          change left query state = right query state at equal
          simp only [RawCtxSelectedFamilyNonceCoupling.marked, StateT.run, equal]
      rw [step, ih reply next]

/-- Identical until the flag, restricted to an event: the `true` mass of an event of one marked run is at most the same event in the other marked run plus the mass of the flag together with the event in the first run. -/
theorem restricted_le {ι σ X : Type} {spec : OracleSpec ι}
    (left right : QueryImpl spec (StateT σ ProbComp)) (bad : spec.Domain → σ → Prop)
    (agree : ∀ query state, ¬ bad query state → (left query).run state = (right query).run state)
    (client : OracleComp spec X) (state : σ) (event : X × σ → Bool) :
    𝒟[(fun result => event (result.1, result.2.1)) <$>
        (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked left bad) client).run (state, false)] {true} ≤
      𝒟[(fun result => event (result.1, result.2.1)) <$>
        (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked right bad) client).run (state, false)] {true} +
      𝒟[(fun result => result.2.2 && event (result.1, result.2.1)) <$>
        (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked left bad) client).run (state, false)] {true} := by
  classical
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true]
  simp only [prEvent_map]
  rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun result => ?_
  rcases result with ⟨value, final, flag⟩
  cases flag with
  | false =>
    let _ : MeasurableSpace (X × σ × Bool) := ⊤
    have _ : DiscreteMeasurableSpace (X × σ × Bool) := ⟨fun _ => trivial⟩
    have same := unflagged_eq left right bad agree client state value final
    rw [← prEvent_eq_evalDist_singleton _ (value, (final, false)),
      ← prEvent_eq_evalDist_singleton _ (value, (final, false))] at same
    simp only [Bool.false_and, Bool.false_eq_true, ite_false, add_zero, same, le_refl]
  | true =>
    simp only [Bool.true_and]
    exact le_add_self

section Generic
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
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
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The result of the selected first Server builder: registration reply, selected front and selected local state. -/
abbrev Built (M P I D K A N : Type) (S B : Nat) :=
  (RustM (Option PqxdhServerRegistrationPublication.Response) × PqxdhSelectedPostCompiler.Front M P I D K S B) ×
    RawCtxSharedPrimitive.SharedState (Local A N RootOracle.QueryCache)

/-- The compiled post start after the builder: its front and local state, and the CTX challenger state carrying the builder's shared hash cache. -/
def startOf (built : Built M P I D K A N S B) : PqxdhSelectedPostCompiler.Full M P I D K A N RootOracle.QueryCache S B :=
  ((built.1.2, built.2.1), { AdaptiveCtxDynamicKnownKeys.initialSource with cache := built.2.2 })

/-- The selected first Server builder of the first-record run. -/
noncomputable def firstBuild : ProbComp (Built M P I D K A N S B) :=
  (selectedBuild pre application initial selector aux source writer (productionStream source.crypto) none key
    (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender
    (initialKernel response64) index metadata ready (initialFront before)).run (initialShared shared privateState cache store)

/-- The executable CTX post client evaluated by the real selected-key challenger after the builder. -/
noncomputable def compiledPost (built : Built M P I D K A N S B) :=
  (PqxdhSelectedStateInterpreter.evaluate
    (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key)
    (simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer (productionStream source.crypto) none
      (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode)
      (post built.1.1)).run).run (startOf built)

/-- The compiled first-record game: the post client did not stop and returned `true`. -/
noncomputable def compiledRun : ProbComp Bool := do
  let built ← firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
    before selected shared privateState cache store key nonce next
  (fun result => decide (result.1 = some true)) <$>
    compiledPost pre application initial selector aux source writer previousRoot response64 sender route decode post selected key nonce next built

/-- The selected chain and the listed ancestors are not among the chains known from `disclosed` and from the reveal history of the source state. -/
def Undisclosed (target : RootOutput) (ancestors disclosed : List RatchetChain)
    (state : PqxdhSelectedPostCompiler.SourceState M P I D K A N RootOracle.QueryCache S B) : Prop :=
  RawCtxLiveLineage.FreshValues (RawCtxFreshChainCut.concreteChain target :: ancestors)
    (RawCtxSelectedMessageFreshness.known disclosed state.1.roles.2)

/-- Undisclosure is decided classically. -/
noncomputable instance undisclosedDecidable (target : RootOutput) (ancestors disclosed : List RatchetChain) :
    DecidablePred (Undisclosed (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (N := N) (S := S) (B := B)
      target ancestors disclosed) :=
  fun _ => Classical.propDecidable _

/-- The restricted stop game: the augmented post run reached an exact selected-nonce stop, and at the end of that run the selected chain and the listed ancestors were still undisclosed. -/
noncomputable def stopRun (ancestors disclosed : List RatchetChain) : ProbComp Bool := do
  let built ← firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
    before selected shared privateState cache store key nonce next
  (fun result => result.2.2 && decide (Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected)
      ancestors disclosed (PqxdhSelectedPostCompiler.project result.2.1))) <$>
    (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
      (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer (productionStream source.crypto) none key
        (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode)
      (PqxdhSelectedPostCompiler.Stops (extra := extra) (productionStream source.crypto) none
        (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender))
      (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (startOf built, false)


local instance : MeasurableSpace (Option Bool × PqxdhSelectedPostCompiler.SourceState M P I D K A N RootOracle.QueryCache S B) := ⊤
local instance : DiscreteMeasurableSpace (Option Bool × PqxdhSelectedPostCompiler.SourceState M P I D K A N RootOracle.QueryCache S B) :=
  ⟨fun _ => by simp⟩

/-- From any full compiled state, the stopped-source post event `bit ∧ no hidden disclosure` on the projected source state is dominated by the evaluated executable post bit plus the exact stop probability of the same augmented run. -/
theorem post_le_full (prior : Prior) (parent : Option RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (start : PqxdhSelectedPostCompiler.Full M P I D K A N RootOracle.QueryCache S B) :
    𝒟[(fun result => decide (result.1 = some true ∧ RawCtxSelectedMessageFreshness.hidden result.2.1.roles.2 = false)) <$>
      (simulateQ (PqxdhSelectedPostDisclosure.normal pre application initial selector aux source writer prior parent key
        target nonce next sender route decode)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (PqxdhSelectedPostCompiler.project start)] {true} ≤
    𝒟[(fun result => decide (result.1 = some true)) <$>
      (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key)
        (simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent
          target nonce next sender route decode) work).run).run start] {true} +
    𝒟[(fun result => result.2.2) <$>
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key
          target nonce next sender route decode)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (start, false)] {true} := by
  have good := PqxdhSelectedPostDisclosure.event_good pre application initial selector aux source writer prior parent key
    target nonce next sender route decode (RawCtxSelectedFamilyNonceCoupling.optionalClient work) (PqxdhSelectedPostCompiler.project start)
    (fun result => result.1 = some true)
  simp only [PqxdhSelectedPostDisclosure.Good] at good
  rw [setOf_bool, setOf_bool] at good
  rw [good]
  refine (map_mono _ _ (fun result => decide (result.1 = some true)) (fun result holds => by simp_all)).trans ?_
  have distance := PqxdhSelectedPostCompiler.source_distance pre application initial selector aux source writer
    prior parent key target nonce next sender route decode work start
  refine ((map_le_tvDist _ (Prod.map id PqxdhSelectedPostCompiler.project <$> (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key)
        (simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent
          target nonce next sender route decode) work).run).run start)
    (fun result : Option Bool × PqxdhSelectedPostCompiler.SourceState M P I D K A N RootOracle.QueryCache S B =>
      decide (result.1 = some true))).trans ?_)
  rw [Functor.map_map]
  refine add_le_add (le_of_eq rfl) ?_
  refine (ENNReal.ofReal_le_ofReal distance).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_toReal]
  rw [← prEvent_eq_evalDist_singleton _ true]
  exact prEvent_ne_top _

/-- From any full compiled state, the stopped-source post event `bit ∧ no hidden disclosure ∧ undisclosed` on the projected source state is dominated by the evaluated executable post bit plus the probability that the same augmented run reached an exact selected-nonce stop and satisfies `undisclosed` on its final projected state. -/
theorem post_le_undisclosed (prior : Prior) (parent : Option RawCtxSelectedParentEntry.Entry) (target : RootOutput)
    (work : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (start : PqxdhSelectedPostCompiler.Full M P I D K A N RootOracle.QueryCache S B)
    (undisclosed : PqxdhSelectedPostCompiler.SourceState M P I D K A N RootOracle.QueryCache S B → Prop)
    [DecidablePred undisclosed] :
    𝒟[(fun result => decide (result.1 = some true ∧ RawCtxSelectedMessageFreshness.hidden result.2.1.roles.2 = false ∧
        undisclosed result.2)) <$>
      (simulateQ (PqxdhSelectedPostDisclosure.normal pre application initial selector aux source writer prior parent key
        target nonce next sender route decode)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (PqxdhSelectedPostCompiler.project start)] {true} ≤
    𝒟[(fun result => decide (result.1 = some true)) <$>
      (PqxdhSelectedStateInterpreter.evaluate
        (AdaptiveCtxDynamicKnownKeys.sourceImpl true (RawCtxUniversalDecoder.decoder decode) source.crypto key)
        (simulateQ (PqxdhSelectedPostCompiler.impl pre application initial selector aux source writer prior parent
          target nonce next sender route decode) work).run).run start] {true} +
    𝒟[(fun result => result.2.2 && decide (undisclosed (PqxdhSelectedPostCompiler.project result.2.1))) <$>
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key
          target nonce next sender route decode)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient work)).run (start, false)] {true} := by
  have good := PqxdhSelectedPostDisclosure.event_good pre application initial selector aux source writer prior parent key
    target nonce next sender route decode (RawCtxSelectedFamilyNonceCoupling.optionalClient work) (PqxdhSelectedPostCompiler.project start)
    (fun result => result.1 = some true ∧ undisclosed result.2)
  simp only [PqxdhSelectedPostDisclosure.Good] at good
  rw [setOf_bool, setOf_bool] at good
  refine (map_mono _ _ (fun result => decide ((result.1 = some true ∧ undisclosed result.2) ∧
    RawCtxSelectedMessageFreshness.hidden result.2.1.roles.2 = false)) (fun result holds => by simp_all)).trans ?_
  rw [good]
  refine (map_mono _ _ (fun result => decide (result.1 = some true ∧ undisclosed result.2))
    (fun result holds => by simp_all)).trans ?_
  rw [← PqxdhSelectedPostCompiler.augmented_program pre application initial selector aux source writer prior parent key target
      nonce next sender route decode work start,
    ← RawCtxSelectedFamilyNonceCoupling.marked_client
      (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key
        target nonce next sender route decode)
      (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work) (start, false),
    Functor.map_map, Functor.map_map,
    PqxdhSelectedPostCompiler.evaluated_program,
    ← RawCtxSelectedFamilyNonceCoupling.marked_client
      (PqxdhSelectedPostCompiler.evaluated pre application initial selector aux source writer prior parent key
        target nonce next sender route decode)
      (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient work) (start, false),
    Functor.map_map]
  refine (restricted_le _ _ _ (PqxdhSelectedPostCompiler.augmented_nonstop pre application initial selector aux source writer
    prior parent key target nonce next sender route decode) (RawCtxSelectedFamilyNonceCoupling.optionalClient work) start
    (fun result => decide (result.1 = some true ∧ undisclosed (PqxdhSelectedPostCompiler.project result.2)))).trans ?_
  refine add_le_add (map_mono _ _ _ fun result holds => by simp_all) (map_mono _ _ _ fun result holds => by simp_all)

/-- After the selected builder, the stopped-source post event `bit ∧ no hidden disclosure ∧ undisclosed selected chain and ancestors` is dominated by the compiled post bit plus the restricted stop probability. -/
theorem post_le (ancestors disclosed : List RatchetChain) (built : Built M P I D K A N S B) :
    𝒟[(fun result => decide (result.1 = some true ∧ RawCtxSelectedMessageFreshness.hidden result.2.1.roles.2 = false ∧
        Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) ancestors disclosed result.2)) <$>
      (simulateQ (PqxdhSelectedPostDisclosure.normal pre application initial selector aux source writer (productionStream source.crypto) none key
        (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode)
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (built.1.2, built.2)] {true} ≤
    𝒟[(fun result => decide (result.1 = some true)) <$>
      compiledPost pre application initial selector aux source writer previousRoot response64 sender route decode post selected key nonce next built] {true} +
    𝒟[(fun result => result.2.2 && decide (Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected)
        ancestors disclosed (PqxdhSelectedPostCompiler.project result.2.1))) <$>
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer (productionStream source.crypto) none key
          (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) (productionStream source.crypto) none
          (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender))
        (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run (startOf built, false)] {true} :=
  post_le_undisclosed pre application initial selector aux source writer sender route decode key nonce next
    (productionStream source.crypto) none (PqxdhInitialSourceExperiment.root source previousRoot response64 selected)
    (post built.1.1) (startOf built)
    (Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) ancestors disclosed)

/-- The first randomized source decision on the selected first-record run is dominated by the compiled post bit plus the restricted stop probability. The publication conjunct and the selected-key conjunct of the decision are dropped, which is sound for an upper bound; the undisclosure of the selected chain and the ancestors is kept and restricts the stop event. -/
theorem first_le (number : Std.U64) (position : number.val = 1) (ancestors disclosed : List RatchetChain) :
    𝒟[(fun result => PqxdhInitialSourceRandom.decision source previousRoot response64 selected
        (RawCtxSelectedMessageKdf.response key nonce next) number ancestors disclosed (nativeView key result)) <$>
      firstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
        index metadata ready post before selected shared privateState cache store key nonce next] {true} ≤
    𝒟[compiledRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store key nonce next] {true} +
    𝒟[stopRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store key nonce next ancestors disclosed] {true} := by
  refine (map_mono _ _ (fun result => decide (result.1 = some true ∧
    RawCtxSelectedMessageFreshness.hidden result.2.1.1.roles.2 = false ∧
    Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) ancestors disclosed result.2.1)) ?_).trans ?_
  · intro result holds
    have characterized := (first_selected_decision source previousRoot response64 selected key nonce next number position
      ancestors disclosed result).mp holds
    rw [decide_eq_true_eq]
    exact ⟨characterized.1.1, characterized.2.1, characterized.2.2.1⟩
  · have erase := selectedRun_erase pre application initial selector aux source writer (productionStream source.crypto) none key
      (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode
      (PqxdhInitialSelectedOrigin.mark source selectedMessage) (initialKernel response64) index metadata ready post
      (initialFront before) (initialShared shared privateState cache store)
    have projected : (fun result : Option Bool × Traced M P I D K A N RootOracle.QueryCache S B => decide (result.1 = some true ∧
        RawCtxSelectedMessageFreshness.hidden result.2.1.1.roles.2 = false ∧
        Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) ancestors disclosed result.2.1)) <$>
        firstRun pre application initial selector aux source writer selectedMessage previousRoot response64 sender route decode
          index metadata ready post before selected shared privateState cache store key nonce next =
        (fun result => decide (result.1 = some true ∧ RawCtxSelectedMessageFreshness.hidden result.2.1.roles.2 = false ∧
          Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) ancestors disclosed result.2)) <$>
          (Prod.map id Prod.fst <$> selectedRun pre application initial selector aux source writer (productionStream source.crypto) none key
            (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode
            (PqxdhInitialSelectedOrigin.mark source selectedMessage) (initialKernel response64) index metadata ready post
            (initialFront before) (initialShared shared privateState cache store)) := by
      rw [Functor.map_map]
      rfl
    rw [projected, erase, map_bind]
    exact true_bind_le _ _ _ _ fun built => post_le pre application initial selector aux source writer previousRoot response64
      sender route decode post selected key nonce next ancestors disclosed built

end Generic


section Prepared
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The unused selective-chain store carried by the selected local state. -/
def emptyStore : RawCtxSelectiveChainGame.Store := (∅, ⟨List.Vector.replicate 32 0, 0⟩)

/-- The compiled continuation of one prepared context: completed preparations give `false`; a pending preparation runs the selected first Server builder and the executable CTX post client with the prepared callbacks of its own KEM secret and challenge. -/
noncomputable def compiledObserve (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input => compiledRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore key nonce chain

/-- The stop continuation of one prepared context: completed preparations give `false`; a pending preparation runs the selected first Server builder and reports whether the augmented post run reached an exact selected-nonce stop while, at its end, the selected chain and the target's ancestors were still undisclosed. -/
noncomputable def stopObserve (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input => stopRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore key nonce chain
      target.ancestors target.disclosed


/-- The compiled first-record game: the actual preparation, the shared64 block, the selected nonce and next chain, then the selected key, then the compiled continuation. -/
noncomputable def compiledGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  compiledObserve setup env callbacks baseImpl kem attachedVerify primitives program post target context initialBlock nonce chain key

/-- The explicit restricted stop game `stopMass`: the same samples, then the event that the augmented post run reached an exact selected-nonce stop and, at its end, the selected chain and the target's ancestors were still undisclosed. -/
noncomputable def stopGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  stopObserve setup env callbacks baseImpl kem attachedVerify primitives program post target context initialBlock nonce chain key

/-- The pending source-observer mass of the first-record key-last endpoint is dominated by the compiled first-record game plus the explicit restricted stop game. -/
theorem pending_ideal_le (target : Target S (B + 1)) (position : target.number.val = 1) :
    𝒟[PqxdhFirstRecordTarget.pendingIdeal env0 baseImpl kem attachedVerify primitives program post target] {true} ≤
    𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} +
    𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} := by
  unfold PqxdhFirstRecordTarget.pendingIdeal PqxdhAdaptiveMessageKeySource.firstPrepare compiledGame stopGame
  rw [PqxdhFirstRecordTarget.mapPost_choose]
  simp only [bind_assoc, pure_bind, PqxdhFirstRecordTarget.unitTargets, PqxdhInitialPreparedSourceInput.prior, bind_map_left]
  refine true_bind_le _ _ _ _ fun context => ?_
  refine true_bind_le _ _ _ _ fun initialBlock => ?_
  refine true_bind_le _ _ _ _ fun nonce => ?_
  refine true_bind_le _ _ _ _ fun chain => ?_
  refine true_bind_le _ _ _ _ fun key => ?_
  unfold compiledObserve stopObserve
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
    exact first_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ position _ _


/-- The pending forgery mass of the fixed first-record source experiment with the forgery proxy post (eligible, accepted, published and fresh, `post0` true and the Server-peer first-record forgery) is at most the compiled first-record game, plus the explicit restricted stop game, plus the first-record target loss and the completed-branch root loss of C1, each the advantage of its constructed reduction. -/
theorem pending_forgery_le (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (target : Target S (B + 1)) (position : target.number.val = 1)
    (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (𝒟[PqxdhFirstRecordTarget.pendingActual env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (PqxdhInitialRootEventSecrecy.accepted env0 attachedVerify primitives program (forgeryPost env0 program post0)
          target.owner target.number target.ancestors target.disclosed)] {true}).toReal ≤
    (𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) target] {true}).toReal +
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) target] {true}).toReal +
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (forgeryPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets target)
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (forgeryPost env0 program post0)
        (certificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      hmac fallback ordinaryFallback := by
  have pending := PqxdhFirstRecordTarget.pending_le env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
    target position (certificate env0 baseImpl kem program post0 c) compatible adapter functional hmac correct fallback ordinaryFallback
  have ideal := pending_ideal_le setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
    target position
  have ideal_real := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PqxdhFirstRecordTarget.true_ne_top _,
    PqxdhFirstRecordTarget.true_ne_top _⟩) ideal
  rw [ENNReal.toReal_add (PqxdhFirstRecordTarget.true_ne_top _) (PqxdhFirstRecordTarget.true_ne_top _)] at ideal_real
  linarith


/-- The fixed first Beacon record target: Beacon `b`, record number one, no ancestors and no disclosed chains. -/
def firstBeacon (b : Fin (B + 1)) : Target S (B + 1) := ⟨.beacon b, 1#u64, [], []⟩

/-- First Beacon record integrity, reduced to the compiled CTX game: in the HB-112 actual game with the forgery proxy post, the mass above the constant-`false` continuation (the pending forgery mass: eligible, accepted, Beacon `b`'s first record published from the selected root, selected chain undisclosed, `post0` true and a Server-peer first-record forgery) is at most the `true` mass of the explicit game `compiledGame`, plus `stopMass` (the `true` mass of the explicit restricted stop game `stopGame`), plus the first-record target loss and the completed-branch root loss, each the advantage of a constructed reduction. This is an intermediate reduction: `compiledGame` and `stopMass` are not yet bounded by assumption terms. -/
theorem first_beacon_forgery_le (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    (𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      (firstBeacon b)] {true}).toReal +
    (𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      (firstBeacon b)] {true}).toReal +
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (forgeryPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (forgeryPost env0 program post0)
        (certificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      hmac fallback ordinaryFallback := by
  have split := PqxdhFirstRecordTarget.target_split env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
    (.beacon b) 1#u64 [] []
  rw [split, ENNReal.toReal_add (PqxdhFirstRecordTarget.true_ne_top _) (PqxdhFirstRecordTarget.true_ne_top _), add_sub_cancel_left]
  exact pending_forgery_le setup env callbacks baseImpl kem attachedVerify primitives program post0 (firstBeacon b) rfl c
    compatible adapter functional hmac correct fallback ordinaryFallback

end Prepared

end BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.logged_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.logged_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.firstSent_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.firstSent_insert

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.firstSent_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.firstSent_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.split_insert' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.split_insert

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.split_append' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.split_append

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.forged_insert' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.forged_insert

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.forged_single' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.forged_single

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.replay_not_counted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.replay_not_counted

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.forgery_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.forgery_query_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.true_bind_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.true_bind_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.map_le_tvDist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.map_le_tvDist

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.setOf_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.setOf_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.map_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.map_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.flagged_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.flagged_run

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.flagged_absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.flagged_absent

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.unflagged_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.unflagged_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.restricted_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.restricted_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.post_le_full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.post_le_full

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.post_le_undisclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.post_le_undisclosed

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.post_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.post_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.first_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.first_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.pending_ideal_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.pending_ideal_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.pending_forgery_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.pending_forgery_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.first_beacon_forgery_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity.first_beacon_forgery_le

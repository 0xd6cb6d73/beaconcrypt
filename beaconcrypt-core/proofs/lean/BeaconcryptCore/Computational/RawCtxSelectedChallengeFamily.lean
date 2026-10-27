import BeaconcryptCore.Computational.RawCtxSelectedMessageStopBounds
import BeaconcryptCore.Computational.RawCtxSelectedSealConsumer
import BeaconcryptCore.Computational.RawCtxSelectedOpenConsumer

/-!
The original finite family client is compiled to the one selected-key CTX interface and dynamic locally known-key calls. Actual private derivation routing retains its complete address and predecessor priority, while public HKDF is evaluated by the real source function. The original role frontend performs parsing, sender/AD selection, peer lookup and publication. The compiler never receives the selected message key. Hidden read stopping retains its observation; selected-nonce stopping retains the entry role state and the accumulated component effects and remains a separately charged event.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf RawCtxFreshChainCut
open RawCtxSelectedMessageKey RawCtxSelectedMessageFreshness RawCtxSelectedMessageReveals RawCtxSelectedMessageFamily RawCtxSelectedMessageStopping
open RawCtxSelectedMessageDriver RawCtxSelectedParentTable RawCtxSelectedParentEntry
variable {M P I D K A Result : Type} {S B : Nat}

abbrev Base := OracleComp AdaptiveCtxDynamicKnownKeys.Spec
abbrev Private (A : Type) := OptionT (StateT A Base)

def liftWork {X : Type} (work : Base X) : Private A X :=
  OptionT.mk fun state => (fun value => (some value, state)) <$> work

def liftOptional {X : Type} (work : Base (Option X)) : Private A X :=
  OptionT.mk fun state => (fun value => (value, state)) <$> work

noncomputable def receiveService (prior : Prior) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) (Private A)
  | .inl address => pure (prior address)
  | .inr pending => liftWork (RawCtxSelectedOpenConsumer.service 0 read pending.context.frame.sender pending)

noncomputable def sendService (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) (Private A)
  | .inl address => pure (prior address)
  | .inr pending => liftOptional (RawCtxSelectedSealConsumer.sealing c writer pending)

noncomputable def publicService (source : FixedHkdfSha512NoSaltSource) :
    QueryImpl RawCtxServerServices.PublicSpec (Private A)
  | .inl coin => liftWork (AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inl coin))))
  | .inr (.inl bytes) => liftWork ((fun digest : CtxRomAuth.CtxDigest => some digest.toList) <$> (AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inl ((), bytes)))))))
  | .inr (.inr request) => pure (request.project (PqxdhJointKdf.productionStream source.crypto request.address))

noncomputable def record (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolRoles.SourceSpec S B) (OptionT (StateT (Roles M P I D K S B × A) Base)) :=
  fun query => OptionT.mk fun state =>
    (fun result => match result.1 with
      | none => (none, (state.1, result.2))
      | some (value, roles) => (some value, (roles, result.2))) <$>
      (((frontend (receiveService prior read) (sendService source.crypto writer prior) (publicService source)
        parent target nonce next sender route read query).run state.1).run).run state.2

noncomputable def impl (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (OptionT (StateT (FullState M P I D K A S B) Base)) :=
  fun query => OptionT.mk fun state => match query with
  | .inl request =>
    (fun result => (result.1, ((result.2.1, tick state.1.2), result.2.2))) <$>
      ((record source writer prior parent target nonce next sender route read request).run).run (state.1.1, state.2)
  | .inr request =>
    let observed := RawCtxSelectedMessageReveals.step request state.1
    pure (emit request observed.1, (observed.2, state.2))

noncomputable def client (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : FullState M P I D K A S B) :
    Base (Option Result × FullState M P I D K A S B) :=
  ((simulateQ (impl source writer prior parent target nonce next sender route read) original).run).run state

noncomputable def candidates (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : FullState M P I D K A S B) :
    Base ((Option Result × FullState M P I D K A S B) × List CtxRomAuth.CtxKey) :=
  (fun result => (result, keys disclosed result.2.1.2)) <$>
    client source writer prior parent target nonce next sender route read original state

/-- A prior-table miss response is the complete original local full76 value and preserves unrelated private state. -/
theorem receive_prior (prior : Prior) (read : RawCtxReceive.FrameDecoder) (address : JointKdfAddress) (state : A) :
    ((receiveService prior read (.inl address)).run).run state = pure (some (prior address), state) := rfl

/-- Public HKDF always evaluates the unchanged production source function; the selected material table is private. -/
theorem public_hkdf (source : FixedHkdfSha512NoSaltSource) (request : JointKdfViewQuery) (state : A) :
    ((publicService source (.inr (.inr request))).run).run state =
      pure (some (request.project (PqxdhJointKdf.productionStream source.crypto request.address)), state) := rfl

/-- The actual optional native read is installed in history before its hidden-slot stop; it makes no CTX component request. -/
theorem read_step (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (request : RawCtxProtocolReveals.Request S B) (state : FullState M P I D K A S B) :
    ((impl source writer prior parent target nonce next sender route read (.inr request)).run).run state =
      pure (emit request (RawCtxSelectedMessageReveals.step request state.1).1,
        ((RawCtxSelectedMessageReveals.step request state.1).2, state.2)) := rfl

/-- A hidden read stops only after the exact source disclosure that falsifies the selected-record freshness gate. -/
theorem read_not_fresh (key : RootOutput) (remaining disclosed : List RatchetChain)
    (request : RawCtxProtocolReveals.Request S B) (state : FullState M P I D K A S B)
    (stopped : emit request (RawCtxSelectedMessageReveals.step request state.1).1 = none) :
    ¬ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) disclosed
      (interpretHistory key (RawCtxSelectedMessageReveals.step request state.1).2.2) :=
  source_stopped key request state.1 remaining disclosed stopped

/-- Attaching the internal known-candidate list preserves the entire stopped result distribution. -/
theorem candidates_result (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (state : FullState M P I D K A S B) :
    Prod.fst <$> candidates source writer prior parent target nonce next disclosed sender route read original state =
      client source writer prior parent target nonce next sender route read original state := by
  simp only [candidates, Functor.map_map]
  exact id_map _

/-- All concrete CTX callback branches preserve prior observations; a read adds at most one known candidate, including either stopping path. -/
theorem step_candidates (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : FullState M P I D K A S B)
    (result : Option ((RawCtxProtocolReveals.SourceSpec S B).Range query) × FullState M P I D K A S B)
    (supported : result ∈ support (((impl source writer prior parent target nonce next sender route read query).run).run state)) :
    (keys disclosed result.2.1.2).length ≤ (keys disclosed state.1.2).length + (if query.isRight then 1 else 0) := by
  cases query with
  | inl request =>
    simp only [impl, OptionT.run_mk, StateT.run] at supported
    rcases mem_support_map_peel _ _ supported with ⟨child, _, rfl⟩
    exact Nat.le_refl _
  | inr request =>
    simp only [read_step] at supported
    subst result
    exact step_probe_bound disclosed request state.1

/-- Every possible challenger reply continuation obeys the actual source reveal budget before any component game is chosen. -/
theorem client_candidates (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (original : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result) (qReveal : Nat)
    (bounded : original.IsQueryBoundP (fun query => query.isRight = true) qReveal)
    (state : FullState M P I D K A S B) (result : Option Result × FullState M P I D K A S B)
    (supported : result ∈ support (client source writer prior parent target nonce next sender route read original state)) :
    (keys disclosed result.2.1.2).length ≤ (keys disclosed state.1.2).length + qReveal := by
  induction original using OracleComp.inductionOn generalizing qReveal state with
  | pure value =>
    simp only [client, simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | query_bind query continuation ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded
    simp only [client, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, head, tail⟩
    have step := step_candidates source writer prior parent target nonce next disclosed sender route read query state reply head
    rcases reply with ⟨none | value, nextState⟩
    · simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at tail
      subst result
      dsimp only at step ⊢
      by_cases selected : query.isRight = true <;> simp_all only [Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega
    · simp only [Option.elim_some] at tail
      have rest := ih value _ (bounded.2 value) nextState tail
      dsimp only at step
      by_cases selected : query.isRight = true <;> simp_all only [Bool.false_eq_true, not_true_eq_false, not_false_eq_true, false_or, ↓reduceIte]
      all_goals omega

end BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.receive_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.receive_prior

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.public_hkdf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.public_hkdf

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.read_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.read_step

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.read_not_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.read_not_fresh

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.candidates_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.candidates_result

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.step_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.step_candidates

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.client_candidates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedChallengeFamily.client_candidates

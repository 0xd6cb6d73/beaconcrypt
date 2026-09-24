import BeaconcryptCore.Computational.RawCtxSelectedMessageFamily

/-!
A successful hidden skipped-key reveal stops before returning unavailable bytes. The stopped interpreter retains the actual full role state, ambient primitive state and newly appended observation. The original source may continue, but its retained hidden disclosure makes the final selected-record freshness false. The proof compares complete fresh output probabilities; it does not assume an arbitrary client decision is false after compromise.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedMessageStopping
open PqxdhSecretInputKdf PqxdhJointKdfGame RawCtxFreshChainCut
open RawCtxSelectedMessageKey RawCtxSelectedMessageFreshness RawCtxSelectedMessageReveals RawCtxSelectedMessageFamily
variable {M P I D K σ Result : Type} {S B : Nat}

abbrev FullState (M P I D K σ : Type) (S B : Nat) := State M P I D K S B × σ
abbrev Record (M P I D K σ : Type) (S B : Nat) :=
  QueryImpl (RawCtxProtocolRoles.SourceSpec S B) (StateT (Roles M P I D K S B × σ) ProbComp)

noncomputable def normal (record : Record M P I D K σ S B) (key : RootOutput) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (StateT (FullState M P I D K σ S B) ProbComp) :=
  fun query state => match query with
  | .inl request =>
    (fun result => (result.1, ((result.2.1, tick state.1.2), result.2.2))) <$>
      (record request).run (state.1.1, state.2)
  | .inr request =>
    let observed := RawCtxSelectedMessageReveals.step request state.1
    pure (interpretReply key request observed.1, (observed.2, state.2))

noncomputable def stopping (record : Record M P I D K σ S B) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B) (OptionT (StateT (FullState M P I D K σ S B) ProbComp)) :=
  fun query => OptionT.mk fun state => match query with
  | .inl request =>
    (fun result => (some result.1, ((result.2.1, tick state.1.2), result.2.2))) <$>
      (record request).run (state.1.1, state.2)
  | .inr request =>
    let observed := RawCtxSelectedMessageReveals.step request state.1
    pure (emit request observed.1, (observed.2, state.2))

def Good (state : FullState M P I D K σ S B) : Prop := hidden state.1.2 = false

/-- The actual appended observation and full state survive an unavailable-key stop. -/
theorem stopping_read (record : Record M P I D K σ S B) (request : RawCtxProtocolReveals.Request S B)
    (state : FullState M P I D K σ S B) :
    ((stopping record (.inr request)).run).run state =
      pure (emit request (RawCtxSelectedMessageReveals.step request state.1).1,
        ((RawCtxSelectedMessageReveals.step request state.1).2, state.2)) := rfl

/-- No source operation can remove a retained hidden-key disclosure. -/
theorem normal_good (record : Record M P I D K σ S B) (key : RootOutput)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : FullState M P I D K σ S B)
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query × FullState M P I D K σ S B)
    (supported : result ∈ support ((normal record key query).run state)) (good : Good result.2) : Good state := by
  cases query with
  | inl request =>
    simp only [normal, StateT.run] at supported
    rcases mem_support_map_peel _ _ supported with ⟨child, _, rfl⟩
    exact good
  | inr request =>
    simp only [normal, StateT.run, mem_support_pure_iff] at supported
    subst result
    simp only [Good, RawCtxSelectedMessageReveals.step, hidden_note, Bool.or_eq_false_iff] at good
    exact good.1

/-- An arbitrary actual adaptive suffix cannot restore freshness after a hidden disclosure. -/
theorem schedule_good (record : Record M P I D K σ S B) (key : RootOutput)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K σ S B) (result : Result × FullState M P I D K σ S B)
    (supported : result ∈ support ((simulateQ (normal record key) client).run state))
    (good : Good result.2) : Good state := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
    simpa only [supported] using good
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    rcases supported with ⟨reply, head, tail⟩
    exact normal_good record key query state reply head (ih reply.1 reply.2 result tail good)

/-- An original continuation after a hidden disclosure gives probability zero to every complete still-fresh output. -/
theorem output_bad_zero (record : Record M P I D K σ S B) (key : RootOutput)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K σ S B) (result : Result × FullState M P I D K σ S B)
    (bad : ¬ Good state) (good : Good result.2) :
    Pr[= result | (simulateQ (normal record key) client).run state] = 0 :=
  probOutput_eq_zero_of_not_mem_support fun supported =>
    bad (schedule_good record key client state result supported good)

set_option backward.isDefEq.respectTransparency false in
/-- Early stopping preserves the exact probability of every complete original output with no hidden disclosure. -/
theorem output_good (record : Record M P I D K σ S B) (key : RootOutput)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K σ S B) (result : Result × FullState M P I D K σ S B)
    (good : Good result.2) :
    Pr[= result | (simulateQ (normal record key) client).run state] =
      Pr[= (some result.1, result.2) | ((simulateQ (stopping record) client).run).run state] := by
  classical
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    have injective : Function.Injective (fun p : Result × FullState M P I D K σ S B => (some p.1, p.2)) := by
      intro a b equal
      exact Prod.ext (Option.some.inj (congrArg Prod.fst equal)) (congrArg (fun p : Option Result × FullState M P I D K σ S B => p.2) equal)
    simpa only [simulateQ_pure, StateT.run_pure, OptionT.run_pure, map_pure] using
      (probOutput_map_injective (pure (value, state) : ProbComp _) injective result).symm
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
    cases query with
    | inl request =>
      change Pr[= result | do
        let child ← (fun child : (RawCtxProtocolRoles.SourceSpec S B).Range request × (Roles M P I D K S B × σ) => (child.1, ((child.2.1, tick state.1.2), child.2.2))) <$> (record request).run (state.1.1, state.2)
        (simulateQ (normal record key) (next child.1)).run child.2] =
        Pr[= (some result.1, result.2) | do
          let child ← (fun child : (RawCtxProtocolRoles.SourceSpec S B).Range request × (Roles M P I D K S B × σ) => (some child.1, ((child.2.1, tick state.1.2), child.2.2))) <$> (record request).run (state.1.1, state.2)
          (child.1.elim (pure none) (fun value => (simulateQ (stopping record) (next value)).run)).run child.2]
      simp only [bind_map_left, Option.elim_some]
      rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
      exact tsum_congr fun child => congrArg (fun probability => Pr[= child | (record request).run (state.1.1, state.2)] * probability) (ih child.1 ((child.2.1, tick state.1.2), child.2.2))
    | inr request =>
      change Pr[= result | do
        let child ← pure (interpretReply key request (RawCtxSelectedMessageReveals.step request state.1).1, ((RawCtxSelectedMessageReveals.step request state.1).2, state.2))
        (simulateQ (normal record key) (next child.1)).run child.2] =
        Pr[= (some result.1, result.2) | do
          let child ← pure (emit request (RawCtxSelectedMessageReveals.step request state.1).1, ((RawCtxSelectedMessageReveals.step request state.1).2, state.2))
          (child.1.elim (pure none) (fun value => (simulateQ (stopping record) (next value)).run)).run child.2]
      simp only [pure_bind]
      cases emitted : emit request (RawCtxSelectedMessageReveals.step request state.1).1 with
      | none =>
        have bad : ¬ Good ((RawCtxSelectedMessageReveals.step request state.1).2, state.2) := by
          have returned := (stopped_iff request (RawCtxSelectedMessageReveals.step request state.1).1).mp emitted
          change hiddenObservation ⟨request, selectedReply request state.1.1⟩ = true at returned
          simp only [Good, RawCtxSelectedMessageReveals.step, hidden_note, returned, Bool.or_true, Bool.true_eq_false, not_false_eq_true]
        rw [output_bad_zero record key _ _ result bad good]
        symm
        apply probOutput_eq_zero_of_not_mem_support
        intro supported
        simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff] at supported
        have impossible : some result.1 = (none : Option Result) := congrArg (fun p : Option Result × FullState M P I D K σ S B => p.1) supported
        cases impossible
      | some value =>
        rw [emit_exact key request _ value emitted]
        exact ih value _

def completed (event : Result × FullState M P I D K σ S B → Prop) :
    Option Result × FullState M P I D K σ S B → Prop
  | (none, _) => False
  | (some value, state) => event (value, state)

/-- A final event gated by absence of hidden disclosure has identical unconditioned probability after stopping. -/
theorem event_good (record : Record M P I D K σ S B) (key : RootOutput)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K σ S B)
    (event : Result × FullState M P I D K σ S B → Prop) :
    Pr[fun result => event result ∧ Good result.2 | (simulateQ (normal record key) client).run state] =
      Pr[completed (fun result => event result ∧ Good result.2) | ((simulateQ (stopping record) client).run).run state] := by
  classical
  let embed := fun p : Result × FullState M P I D K σ S B => (some p.1, p.2)
  have injective : Function.Injective embed := by
    intro a b equal
    exact Prod.ext (Option.some.inj (congrArg Prod.fst equal)) (congrArg (fun p : Option Result × FullState M P I D K σ S B => p.2) equal)
  change Pr[(completed (fun result => event result ∧ Good result.2)) ∘ embed | _] = _
  rw [← probEvent_map, probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  refine tsum_congr ?_
  rintro ⟨value, finalState⟩
  cases value with
  | none => simp only [completed, ↓reduceIte]
  | some value =>
    by_cases good : Good finalState
    · simp only [completed, good, and_true]
      rw [probOutput_map_injective _ injective (value, finalState), output_good record key client state (value, finalState) good]
    · simp only [completed, good, and_false, ↓reduceIte]

/-- The original byte-based freshness gate already excludes every withheld hidden disclosure; stopping adds no error term and assumes no decision on compromised executions. -/
theorem event_fresh (record : Record M P I D K σ S B) (key : RootOutput)
    (remaining prior : List RatchetChain)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K σ S B)
    (event : Result × FullState M P I D K σ S B → Prop) :
    Pr[fun result => event result ∧ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key result.2.1.2) |
      (simulateQ (normal record key) client).run state] =
      Pr[completed (fun result => event result ∧ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key result.2.1.2)) |
        ((simulateQ (stopping record) client).run).run state] := by
  have factor : (fun result : Result × FullState M P I D K σ S B =>
      (event result ∧ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key result.2.1.2)) ∧ Good result.2) =
      (fun result => event result ∧ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key result.2.1.2)) := by
    funext result
    apply propext
    exact ⟨And.left, fun h => ⟨h, ((fresh_keys key remaining prior result.2.1.2).mp h.2).1.1⟩⟩
  simpa only [factor] using event_good record key client state
    (fun result => event result ∧ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) prior (interpretHistory key result.2.1.2))

set_option backward.isDefEq.respectTransparency false in
/-- The record service consumed by the stopping proof is the concrete original owner frontend, retaining every ambient primitive field. -/
theorem normal_family
    (receiveService : QueryImpl (RawCtxSelectedMessageDriver.ReceiveServices RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted) (StateT σ ProbComp))
    (sendService : QueryImpl (RawCtxSelectedMessageDriver.SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) (StateT σ ProbComp))
    (publicService : QueryImpl RawCtxServerServices.PublicSpec (StateT σ ProbComp))
    (parent : Option RawCtxSelectedParentEntry.Entry) (key target : RootOutput)
    (nonce : PqxdhFullSecretInputKdf.NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    normal ((frontend receiveService sendService publicService parent target nonce next sender route decode
      (P := P) (I := I) (D := D) (K := K) (S := S) (B := B)).flattenStateT) key =
      (live receiveService sendService publicService (sourceReader key) parent target nonce next sender route decode).flattenStateT := by
  funext query state
  cases query with
  | inl request =>
    let owner := frontend receiveService sendService publicService parent target nonce next sender route decode
      (P := P) (I := I) (D := D) (K := K) (S := S) (B := B)
    change (fun result : (RawCtxProtocolRoles.SourceSpec S B).Range request × (Roles M P I D K S B × σ) =>
        (result.1, ((result.2.1, tick state.1.2), result.2.2))) <$>
        (owner.flattenStateT request).run (state.1.1, state.2) =
      (fun result : ((RawCtxProtocolRoles.SourceSpec S B).Range request × State M P I D K S B) × σ =>
        (result.1.1, (result.1.2, result.2))) <$>
        ((do let result ← (owner request).run state.1.1
             pure (result.1, (result.2, tick state.1.2))) : StateT σ ProbComp _).run state.2
    simp only [QueryImpl.flattenStateT, StateT.run_mk, bind_pure_comp, StateT.run_map, Functor.map_map]
  | inr request =>
    simp only [normal, QueryImpl.flattenStateT, live, StateT.run, StateT.mk, sourceReader, pure_bind]
    rfl

noncomputable def sourceRecord {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (parent : Option RawCtxSelectedParentEntry.Entry)
    (key target : RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder) :
    Record M P I D K (RawCtxSharedPrimitive.SharedState A) S B :=
  (frontend (RawCtxSelectedMessageDriver.receiveServices source writer prior parent key target nonce next)
    (RawCtxSelectedMessageDriver.sendServices source writer prior parent key target nonce next)
    (RawCtxFunctionalFamily.backend source writer (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)) ∘ₛ RawCtxServerServices.publicLift)
    parent target nonce next sender route decode).flattenStateT

def nativeOutput (key : RootOutput) (result : Result × FullState M P I D K σ S B) :=
  ((result.1, nativeState key result.2.1), result.2.2)

/-- The normal interpreter used by stopping is the full original source execution, including all private role, history and shared primitive fields. -/
theorem native_schedule {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (parent : Option RawCtxSelectedParentEntry.Entry)
    (key target : RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K (RawCtxSharedPrimitive.SharedState A) S B) :
    (simulateQ (RawCtxFunctionalFamily.backend source writer (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
      ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run (nativeState key state.1))).run state.2 =
      nativeOutput key <$> (simulateQ (normal (sourceRecord source writer prior parent key target nonce next sender route decode) key) client).run state := by
  rcases state with ⟨state, ambient⟩
  rw [sourceRecord, normal_family, simulateQ_flattenStateT_run]
  have mapped := congrArg (fun computation => computation.run ambient)
    (live_source_schedule source writer prior parent key target nonce next sender route decode client state)
  simpa only [StateT.run_map, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, nativeOutput] using mapped

/-- Every actual original source event gated by selected-record freshness is unchanged by stopping before hidden material disclosure, with full native state and actual public replies retained. -/
theorem native_event {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : RawCtxSelectedParentTable.Prior) (parent : Option RawCtxSelectedParentEntry.Entry)
    (key target : RootOutput) (nonce : PqxdhFullSecretInputKdf.NonceOutput) (next : RootOutput)
    (remaining disclosed : List RatchetChain)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (state : FullState M P I D K (RawCtxSharedPrimitive.SharedState A) S B)
    (event : (Result × RawCtxProtocolReveals.State M P I D K S B) × RawCtxSharedPrimitive.SharedState A → Prop) :
    Pr[fun result => event result ∧ RawCtxLiveLineage.Fresh (concreteChain key :: remaining) disclosed result.1.2.2 |
      (simulateQ (RawCtxFunctionalFamily.backend source writer (RawCtxSelectedMessageDriver.privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
        ((simulateQ (RawCtxProtocolReveals.protocolImpl S B sender route decode) client).run (nativeState key state.1))).run state.2] =
      Pr[completed (fun result => event (nativeOutput key result) ∧
          RawCtxLiveLineage.Fresh (concreteChain key :: remaining) disclosed (interpretHistory key result.2.1.2)) |
        ((simulateQ (stopping (sourceRecord source writer prior parent key target nonce next sender route decode)) client).run).run state] := by
  rw [native_schedule, probEvent_map]
  exact event_fresh (sourceRecord source writer prior parent key target nonce next sender route decode)
    key remaining disclosed client state (fun result => event (nativeOutput key result))

end BeaconcryptCore.Computational.RawCtxSelectedMessageStopping

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.stopping_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.stopping_read
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.normal_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.normal_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.schedule_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.output_bad_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.output_bad_zero
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.output_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.output_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.event_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.event_good
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.event_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.event_fresh
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.normal_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.normal_family
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.native_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.native_schedule
/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.native_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedMessageStopping.native_event

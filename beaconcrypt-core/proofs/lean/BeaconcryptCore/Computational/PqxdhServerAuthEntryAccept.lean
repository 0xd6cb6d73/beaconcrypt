import BeaconcryptCore.Computational.PqxdhServerAuthEntryPublic
import BeaconcryptCore.Computational.PqxdhServerAuthEntryState

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The exact source accept prefix always advances its attempt counter and retains the complete returned consumed-registration state. -/
def acceptedPrefix (game : GameState KemSK) (consumed : List Pqxdh.Bytes) : GameState KemSK :=
  { game with sessions := game.sessions + 1, server := { game.server with consumed := consumed } }

/-- Rejected preparation preserves every relation clause after the real source prefix, including the operation latch. -/
theorem EntryRel.acceptPrefix (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (consumed : List Pqxdh.Bytes) (chosen : Bool)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context
      (acceptedPrefix left.1.1 consumed, left.1.2)) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      ((acceptedPrefix left.1.1 consumed, left.1.2), left.2 || chosen)
      ((acceptedPrefix right.1.1 consumed, right.1.2), right.2 || chosen) := by
  refine ⟨invariant, ProtocolRel.prefix _ _ _ _ related.protocol consumed, related.cache,
    congrArg (· || chosen) related.flag, ?_, related.selected, ?_, related.marked, related.good, related.clean⟩
  · intro flag
    exact related.unselected (Bool.or_eq_false_iff.mp flag).1
  · intro index marked
    exact Nat.lt_succ_of_lt (related.below index marked)

/-- Exact marked-token update made by the source accept continuation. -/
def acceptedMarks (marks : Marks) (index : Nat) (reply : Reply) : Marks :=
  if reply.isHidden then Function.update marks index true else marks

/-- Before the actual allocation counter, the selected mark is necessarily absent. -/
theorem EntryRel.freshMark (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    right.1.2.1 left.1.1.sessions = false := by
  cases marked : right.1.2.1 left.1.1.sessions with
  | false => rfl
  | true => exact (Nat.lt_irrefl _ (related.below _ marked)).elim

/-- The full source root-consumer update preserves the relation when its actual table transition supplies the literal hidden-input provenance. These are operational transition facts, discharged by the two concrete table interpreters. -/
theorem EntryRel.acceptDerived (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (consumed : List Pqxdh.Bytes) (chosen : Bool)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhJointIdentity.PeerEncoding)
    (reply : Reply) (next : HiddenTable)
    (unselected : (right.2 || chosen) = false → next.hidden = none)
    (retained : ∀ bytes, right.1.2.2.hidden = some bytes → next.hidden = some bytes)
    (selected : ∀ bytes, next.hidden = some bytes → SelectedAt setup context.seed context.scalar Q j
      (afterDerive setup (context.publicValue setup) left.1.1.sessions input
        (Reply.materialize setup.hmac prk reply) (acceptedPrefix left.1.1 consumed)).2.ghost bytes)
    (hiddenReply : reply.isHidden = true → ∃ bytes, next.hidden = some bytes ∧
      rootInput setup context.seed context.scalar (PqxdhServerRelatedRootInput.message input) = some bytes)
    (good : next.bad = false) (clean : next.Clean)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context
      ((afterDerive setup (context.publicValue setup) left.1.1.sessions input
        (Reply.materialize setup.hmac prk reply) (acceptedPrefix left.1.1 consumed)).2,
        left.1.2.1, next.fill prk)) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      (((afterDerive setup (context.publicValue setup) left.1.1.sessions input
        (Reply.materialize setup.hmac prk reply) (acceptedPrefix left.1.1 consumed)).2,
        left.1.2.1, next.fill prk), left.2 || chosen)
      (((afterDerive setup (context.publicValue setup) left.1.1.sessions input reply
        (acceptedPrefix right.1.1 consumed)).2,
        acceptedMarks right.1.2.1 left.1.1.sessions reply, next), right.2 || chosen) := by
  refine ⟨invariant, (ProtocolRel.derive setup (context.publicValue setup) prk right.1.2.1 _ _
    (ProtocolRel.prefix _ _ _ _ related.protocol consumed) left.1.1.sessions
    (EntryRel.freshMark setup context Q j prk left right related) input reply).2, rfl,
    congrArg (· || chosen) related.flag, unselected, selected, ?_, ?_, good, clean⟩
  · intro index marked
    cases reply <;>
      simp only [acceptedMarks, Reply.isHidden, Reply.materialize, afterDerive, Reply.value,
        Bool.false_eq_true, ↓reduceIte, acceptedPrefix] at marked ⊢
    · exact Nat.lt_succ_of_lt (related.below index marked)
    · exact Nat.lt_succ_of_lt (related.below index marked)
    · by_cases same : index = left.1.1.sessions
      · subst index
        exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (related.below index (by simpa only [Function.update_of_ne same] using marked))
  · intro index marked
    dsimp only at marked ⊢
    rw [afterDerive_touches]
    by_cases newMark : reply.isHidden = true ∧ index = left.1.1.sessions
    · obtain ⟨bytes, selectedInput, rooted⟩ := hiddenReply newMark.1
      rw [newMark.2]
      exact ⟨PqxdhServerRelatedRootInput.message input, reply.value, bytes,
        List.mem_append_right _ (List.mem_singleton_self _), selectedInput, rooted⟩
    · have oldMark : right.1.2.1 index = true := by
        unfold acceptedMarks at marked
        split at marked
        · rename_i hidden
          simpa only [Function.update_of_ne (fun same => newMark ⟨hidden, same⟩)] using marked
        · exact marked
      obtain ⟨message, value, bytes, touched, selectedInput, rooted⟩ := related.marked index oldMark
      exact ⟨message, value, bytes, List.mem_append_left _ touched, retained bytes selectedInput, rooted⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- An ordinary accept query runs the same source generator prefix and the retained real table, with exact marked-token reconstruction. -/
theorem accept_ordinary_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (raw : Pqxdh.Bytes) (chosen : Bool) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple
      ((fun result => (result.1, result.2, left.2 || chosen)) <$>
        (acceptStep setup codec checks (context.publicValue setup)
          (realServices context.seed context.scalar setup codec checks) raw).run left.1)
      ((fun result => (result.1, result.2, right.2 || chosen)) <$>
        (acceptStep setup codec checks (context.publicValue setup)
          (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk)) raw).run right.1)
      (QueryPost (Reader := Reader) (Response := Response) setup context Q j prk) := by
  simp only [acceptStep, StateT.run, map_bind]
  rw [show left.1.1.server.consumed = right.1.1.server.consumed from
    congrArg (·.consumed) related.protocol.server]
  refine relTriple_bind (relTriple_refl _) fun collected other same => ?_
  subst other
  cases prepared : collected.1 with
  | none =>
      simp only [map_pure]
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, fun invariant => EntryRel.acceptPrefix setup context Q j prk left right related
        collected.2 chosen invariant⟩
  | some input =>
      dsimp only
      split
      · simp only [realServices, sourceHiddenServices, related.cache]
        have reconstructed := hiddenDerive_source setup.hmac setup.joint setup.dh context.seed context.scalar prk
          (PqxdhServerRelatedRootInput.message input) right.1.2.2
        simp only [StateT.run] at reconstructed
        rw [← reconstructed]
        simp only [bind_pure_comp, Functor.map_map]
        apply relTriple_map_same
        intro read supported
        have materialized : (Reply.materialize setup.hmac prk read.1).isHidden = false := by
          cases read.1 <;> rfl
        simp only [materialized, Bool.false_eq_true, ↓reduceIte]
        refine Or.inl ⟨?_, fun invariant => ?_⟩
        · simpa only [acceptedPrefix, related.protocol.sessions] using
            (ProtocolRel.derive setup (context.publicValue setup) prk right.1.2.1 _ _
              (ProtocolRel.prefix _ _ _ _ related.protocol collected.2) left.1.1.sessions
              (EntryRel.freshMark setup context Q j prk left right related) input read.1).1
        · have kept := hiddenDerive_keeps setup context.seed context.scalar
            (PqxdhServerRelatedRootInput.message input) right.1.2.2 related.clean read supported
          have selected : ∀ bytes, read.2.hidden = some bytes → SelectedAt setup context.seed context.scalar Q j
              (afterDerive setup (context.publicValue setup) left.1.1.sessions input
                (Reply.materialize setup.hmac prk read.1) (acceptedPrefix left.1.1 collected.2)).2.ghost bytes := by
            intro bytes found
            apply selectedAt_prefix setup context.seed context.scalar Q j left.1.1.ghost _ bytes
              ⟨_, (afterDerive_touches setup (context.publicValue setup) left.1.1.sessions input
                (Reply.materialize setup.hmac prk read.1) (acceptedPrefix left.1.1 collected.2)).symm⟩
            exact related.selected bytes (kept.1 ▸ found)
          simpa only [acceptedMarks, acceptedPrefix, related.protocol.sessions] using
            (EntryRel.acceptDerived setup context Q j prk left right related collected.2 chosen input read.1 read.2
              (fun flag => kept.1.trans (related.unselected (Bool.or_eq_false_iff.mp flag).1))
              (fun bytes found => kept.1.trans found) selected
              (hiddenDerive_hidden setup context.seed context.scalar _ _ read supported)
              (kept.2.1.trans related.good) kept.2.2 invariant)
      · simp only [map_pure]
        apply relTriple_pure_pure
        exact Or.inl ⟨rfl, fun invariant => EntryRel.acceptPrefix setup context Q j prk left right related
          collected.2 chosen invariant⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The designated accept query uses the prefetched block on a missing actual input; an existing entry is charged to the original wrong-owner event. -/
theorem accept_selected_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (raw : Pqxdh.Bytes) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (before : left.2 = false) (session : j.val < Q) (index : left.1.1.sessions = j.val) :
    RelTriple
      ((fun result => (result.1, result.2, left.2 || true)) <$>
        (acceptStep setup codec checks (context.publicValue setup)
          (programmedServices context.seed context.scalar setup codec checks prk) raw).run left.1)
      ((fun result => (result.1, result.2, right.2 || true)) <$>
        (acceptStep setup codec checks (context.publicValue setup)
          (selectingServices setup context
            (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))) raw).run right.1)
      (QueryPost (Reader := Reader) (Response := Response) setup context Q j prk) := by
  have unselected := related.unselected (related.flag ▸ before)
  have cache : left.1.2.2 = right.1.2.2.cache := by
    simpa only [HiddenTable.fill, unselected] using related.cache
  simp only [acceptStep, StateT.run, map_bind]
  rw [show left.1.1.server.consumed = right.1.1.server.consumed from
    congrArg (·.consumed) related.protocol.server]
  refine relTriple_bind (relTriple_refl _) fun collected other same => ?_
  subst other
  cases prepared : collected.1 with
  | none =>
      simp only [map_pure]
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, fun invariant => EntryRel.acceptPrefix setup context Q j prk left right related
        collected.2 true invariant⟩
  | some input =>
      dsimp only
      split
      · simp only [programmedServices, realServices, selectingServices, StateT.run,
          programmedDerive, selectHidden, cache]
        cases rooted : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar
            (PqxdhServerRelatedRootInput.message input) with
        | none =>
            simp only [pure_bind, map_pure, Reply.isHidden, Bool.false_eq_true, ↓reduceIte]
            apply relTriple_pure_pure
            refine Or.inl ⟨rfl, fun invariant => ?_⟩
            have kept := EntryRel.acceptDerived setup context Q j prk left right related collected.2 true
              input .rejected right.1.2.2
              (fun _ => unselected) (fun _ found => found)
              (fun other found => by rw [unselected] at found; cases found)
              (fun hidden => by cases hidden) related.good related.clean
              (by simpa only [HiddenTable.fill, unselected, Reply.materialize, acceptedPrefix] using invariant)
            simpa only [acceptedMarks, acceptedPrefix, related.protocol.sessions, Reply.materialize,
              Reply.isHidden, Bool.false_eq_true, ↓reduceIte, HiddenTable.fill, unselected] using kept
        | some bytes =>
            cases hit : right.1.2.2.cache bytes with
            | none =>
                simp only [programmedRead, hit, map_pure, pure_bind, Reply.isHidden,
                  Bool.false_eq_true, ↓reduceIte]
                apply relTriple_pure_pure
                refine Or.inl ⟨?_, fun invariant => ?_⟩
                · simpa only [acceptedPrefix, related.protocol.sessions, Reply.materialize] using
                    (ProtocolRel.derive setup (context.publicValue setup) prk right.1.2.1 _ _
                      (ProtocolRel.prefix _ _ _ _ related.protocol collected.2) left.1.1.sessions
                      (EntryRel.freshMark setup context Q j prk left right related) input .hidden).1
                · have kept := EntryRel.acceptDerived setup context Q j prk left right related collected.2 true
                    input .hidden { right.1.2.2 with hidden := some bytes }
                    (fun flag => by simp only [Bool.or_true, Bool.true_eq_false] at flag)
                    (fun other found => by rw [unselected] at found; cases found)
                    ?_ (fun _ => ⟨bytes, rfl, rooted⟩) related.good ?_ invariant
                  simpa only [acceptedMarks, acceptedPrefix, related.protocol.sessions, Reply.materialize,
                    Reply.isHidden, ↓reduceIte, HiddenTable.fill] using kept
                  · intro other found
                    cases Option.some.inj found
                    simp only [SelectedAt, session, ↓reduceIte]
                    refine ⟨PqxdhServerRelatedRootInput.message input, some (expandRoot setup.hmac prk), ?_, rooted⟩
                    rw [afterDerive_touches, index]
                    exact List.mem_append_right _ (List.mem_singleton_self _)
                  · intro other found
                    cases Option.some.inj found
                    exact hit
            | some value =>
                simp only [programmedRead, hit, map_pure, pure_bind, Reply.isHidden,
                  Bool.false_eq_true, ↓reduceIte]
                apply relTriple_pure_pure
                refine Or.inr ⟨?_, rfl⟩
                apply session_cache_refusal setup context.seed context.scalar (context.publicValue setup) Q j
                  left.1.1 left.1.2.2 _ bytes related.source.1 related.source.2.2 session index
                · simp only [cache, hit, ne_eq, reduceCtorEq, not_false_eq_true]
                · exact ⟨_, (afterDerive_touches setup (context.publicValue setup) left.1.1.sessions input
                    (.root (expandRoot setup.hmac value)) (acceptedPrefix left.1.1 collected.2)).symm⟩
                · simp only [SelectedAt, session, ↓reduceIte]
                  refine ⟨PqxdhServerRelatedRootInput.message input, some (expandRoot setup.hmac value), ?_, rooted⟩
                  rw [afterDerive_touches, index]
                  exact List.mem_append_right _ (List.mem_singleton_self _)
      · simp only [map_pure]
        apply relTriple_pure_pure
        exact Or.inl ⟨rfl, fun invariant => EntryRel.acceptPrefix setup context Q j prk left right related
          collected.2 true invariant⟩

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor
open PqxdhServerAuthExperiment PqxdhSecretInputKdf PqxdhJointKdfGame

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The actual adaptive accept handler preserves complete replies and states until the refusal already excluded by the original event. Both reused and first designated operations are covered. -/
theorem accept_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (raw : Pqxdh.Bytes) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.accept raw))).run left)
      ((hiddenHandler setup codec checks context Q j
        (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))
        (.inr (.accept raw))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  apply close_query_coupling setup codec checks context Q j prk _ (.inr (.accept raw)) left right related.source
  rw [hiddenHandler_good setup codec checks context Q j _ (.inr (.accept raw)) right related.good]
  have chosenSame := designated_related Q j (.inr (.accept raw)) _ left.1 right.1 related.protocol
  simp only [prefetchedHandler, once, StateT.run, ← chosenSame, ← related.flag]
  by_cases used : left.2 = true
  · simp only [used, ↓reduceIte, latch, StateT.run, skeleton, ← chosenSame]
    simpa only [used, StateT.run, ServerAuthSpec, PqxdhServerAuthExperiment.QuerySpec, OracleSpec.Range, OracleSpec.add_apply_inr] using accept_ordinary_coupling setup codec checks context Q j prk raw
      (designated Q j (.inr (.accept raw)) left.1) left right related
  · by_cases chosen : designated Q j (.inr (.accept raw)) left.1 = true
    · simp only [used, ↓reduceIte, latch, StateT.run, skeleton, ← chosenSame, chosen]
      have designatedFacts : j.val < Q ∧ left.1.1.sessions = j.val := by
        simpa only [designated, decide_eq_true_eq] using chosen
      simpa only [used, StateT.run, ServerAuthSpec, PqxdhServerAuthExperiment.QuerySpec, OracleSpec.Range, OracleSpec.add_apply_inr, Bool.false_eq_true, ↓reduceIte] using accept_selected_coupling setup codec checks context Q j prk raw left right related
        (Bool.eq_false_iff.mpr used) designatedFacts.1 designatedFacts.2
    · simp only [used, chosen, latch, StateT.run, skeleton, ← chosenSame]
      simpa only [used, chosen, StateT.run, ServerAuthSpec, PqxdhServerAuthExperiment.QuerySpec, OracleSpec.Range, OracleSpec.add_apply_inr, Bool.false_eq_true, ↓reduceIte] using accept_ordinary_coupling setup codec checks context Q j prk raw
        (designated Q j (.inr (.accept raw)) left.1) left right related

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.acceptPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.acceptPrefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.freshMark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.freshMark
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.acceptDerived' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.acceptDerived
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_ordinary_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_ordinary_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_selected_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_selected_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.accept_step_coupling

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

/-- A failed preparation still executes the exact finish and operation latch. -/
theorem EntryRel.finishPlain (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (control : pqxdh.BeaconInitSent) (staged : Option PqxdhBeaconPhase2Publication.Staged) (chosen : Bool)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context
      ((finishOutcome control left.1.1 staged).2, left.1.2)) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      (((finishOutcome control left.1.1 staged).2, left.1.2), left.2 || chosen)
      (((finishOutcome control right.1.1 staged).2, right.1.2), right.2 || chosen) := by
  refine ⟨invariant, (ProtocolRel.finish _ _ _ _ related.protocol control staged).2, related.cache,
    congrArg (· || chosen) related.flag, ?_, ?_, related.below, ?_, related.good, related.clean⟩
  · intro flag
    exact related.unselected (Bool.or_eq_false_iff.mp flag).1
  · intro bytes selected
    simpa only [SelectedAt, finishOutcome_touches] using related.selected bytes selected
  · intro index marked
    simpa only [finishOutcome_touches] using related.marked index marked

/-- The actual Beacon input touch is recorded before any table lookup. -/
def finishTouched (game : GameState KemSK) (message : PqxdhJointDhExtractFamily.Message) : GameState KemSK :=
  { game with ghost := { game.ghost with touches := game.ghost.touches ++ [Touch.beacon message] } }

/-- Final staging installs the reached primitive cache before the unchanged publication checks. -/
noncomputable def finishAfterInput (control : pqxdh.BeaconInitSent) (game : GameState KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (cache : CtxRomAuth.CtxRO.QueryCache)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) : Option Pqxdh.Bytes × GameState KemSK :=
  finishOutcome control { finishTouched game message with ctx := cache } staged

/-- The complete finish update preserves literal marked-input provenance after the actual table transition. -/
theorem EntryRel.finishDerived (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (control : pqxdh.BeaconInitSent) (message : PqxdhJointDhExtractFamily.Message)
    (cache : CtxRomAuth.CtxRO.QueryCache) (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (chosen : Bool) (next : HiddenTable)
    (unselected : (right.2 || chosen) = false → next.hidden = none)
    (retained : ∀ bytes, right.1.2.2.hidden = some bytes → next.hidden = some bytes)
    (selected : ∀ bytes, next.hidden = some bytes → SelectedAt setup context.seed context.scalar Q j
      (finishAfterInput control left.1.1 message cache staged).2.ghost bytes)
    (good : next.bad = false) (clean : next.Clean)
    (invariant : SourceInvariant (Reader := Reader) (Response := Response) setup context
      ((finishAfterInput control left.1.1 message cache staged).2, left.1.2.1, next.fill prk)) :
    EntryRel (Reader := Reader) (Response := Response) setup context Q j prk
      (((finishAfterInput control left.1.1 message cache staged).2, left.1.2.1, next.fill prk), left.2 || chosen)
      (((finishAfterInput control right.1.1 message cache staged).2, right.1.2.1, next), right.2 || chosen) := by
  refine ⟨invariant, ?_, rfl, congrArg (· || chosen) related.flag, unselected, selected,
    related.below, ?_, good, clean⟩
  · exact (ProtocolRel.finish _ _ _ _ (ProtocolRel.context _ _ _ _
      (ProtocolRel.touch _ _ _ _ related.protocol (.beacon message) (.beacon message) rfl) cache) control staged).2
  · intro index marked
    obtain ⟨messageS, replyS, bytes, touched, hidden, rooted⟩ := related.marked index marked
    refine ⟨messageS, replyS, bytes, ?_, retained bytes hidden, rooted⟩
    simp only [finishAfterInput, finishOutcome_touches, finishTouched]
    exact List.mem_append_left _ touched

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

/-- An ordinary finish preserves the complete source prefix, optional root reply and actual staged result. -/
theorem finish_ordinary_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (raw : Pqxdh.Bytes) (chosen : Bool) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple
      ((fun result => (result.1, result.2, left.2 || chosen)) <$>
        (finishStep setup codec (context.publicValue setup) context.beaconSeed
          (realServices context.seed context.scalar setup codec checks) raw).run left.1)
      ((fun result => (result.1, result.2, right.2 || chosen)) <$>
        (finishStep setup codec (context.publicValue setup) context.beaconSeed
          (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk)) raw).run right.1)
      (QueryPost (Reader := Reader) (Response := Response) setup context Q j prk) := by
  simp only [finishStep, StateT.run]
  rw [related.protocol.beacon]
  cases phase : right.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [map_bind]
      refine relTriple_bind (relTriple_refl _) fun prepared other same => ?_
      subst other
      cases prepared with
      | none =>
          simp only [map_pure]
          apply relTriple_pure_pure
          exact Or.inl ⟨(ProtocolRel.finish _ _ _ _ related.protocol control none).1,
            fun invariant => EntryRel.finishPlain setup context Q j prk left right related control none chosen invariant⟩
      | some pending =>
          simp only [realServices, sourceHiddenServices, related.cache]
          have reconstructed := hiddenDerive_source setup.hmac setup.joint setup.dh context.seed context.scalar prk
            (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) right.1.2.2
          simp only [StateT.run] at reconstructed
          rw [← reconstructed]
          simp only [bind_map_left, map_bind]
          refine relTriple_bind (relTriple_with_support _ _ Eq (relTriple_refl _)) fun read other paired => ?_
          rcases paired with ⟨same, supported, _⟩
          subst other
          have kept := hiddenDerive_keeps setup context.seed context.scalar
            (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
            right.1.2.2 related.clean read supported
          have post : ∀ cache staged, QueryPost (Reader := Reader) (Response := Response) setup context Q j prk
              ((finishAfterInput control left.1.1
                (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) cache staged).1,
                (((finishAfterInput control left.1.1
                  (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) cache staged).2,
                  left.1.2.1, read.2.fill prk), left.2 || chosen))
              ((finishAfterInput control right.1.1
                (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) cache staged).1,
                (((finishAfterInput control right.1.1
                  (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) cache staged).2,
                  right.1.2.1, read.2), right.2 || chosen)) := by
            intro cache staged
            refine Or.inl ⟨(ProtocolRel.finish _ _ _ _ (ProtocolRel.context _ _ _ _
              (ProtocolRel.touch _ _ _ _ related.protocol _ _ rfl) cache) control staged).1, fun invariant => ?_⟩
            apply EntryRel.finishDerived setup context Q j prk left right related control _ cache staged chosen read.2
              (fun flag => kept.1.trans (related.unselected (Bool.or_eq_false_iff.mp flag).1))
              (fun bytes found => kept.1.trans found) ?_ (kept.2.1.trans related.good) kept.2.2 invariant
            intro bytes found
            apply selectedAt_prefix setup context.seed context.scalar Q j left.1.1.ghost _ bytes
              ⟨[Touch.beacon (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)], ?_⟩
              (related.selected bytes (kept.1 ▸ found))
            simp only [finishAfterInput, finishOutcome_touches, finishTouched]
          cases reply : read.1 <;> simp only [Reply.materialize]
          · simp only [map_pure]
            apply relTriple_pure_pure
            simpa only [finishAfterInput, finishTouched, related.protocol.beacon, related.protocol.ctx] using
              post right.1.1.ctx none
          all_goals
            simp only [bind_pure_comp, Functor.map_map, related.protocol.ctx]
            apply relTriple_map_same
            intro staged _
            simpa only [finishAfterInput, finishTouched, related.protocol.beacon] using post staged.2.2 staged.1
  | _ =>
      simp only [map_pure]
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, fun _ => { related with
        flag := congrArg (· || chosen) related.flag
        unselected := fun flag => related.unselected (Bool.or_eq_false_iff.mp flag).1 }⟩

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

/-- The designated Beacon finish preserves all source opening and publication effects, selecting only its actual fresh root input or refusing an input already owned in the source log. -/
theorem finish_selected_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (raw : Pqxdh.Bytes) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right)
    (before : left.2 = false) (last : j.val = Q) :
    RelTriple
      ((fun result => (result.1, result.2, left.2 || true)) <$>
        (finishStep setup codec (context.publicValue setup) context.beaconSeed
          (programmedServices context.seed context.scalar setup codec checks prk) raw).run left.1)
      ((fun result => (result.1, result.2, right.2 || true)) <$>
        (finishStep setup codec (context.publicValue setup) context.beaconSeed
          (selectingServices setup context
            (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))) raw).run right.1)
      (QueryPost (Reader := Reader) (Response := Response) setup context Q j prk) := by
  have unselected := related.unselected (related.flag ▸ before)
  have cache : left.1.2.2 = right.1.2.2.cache := by
    simpa only [HiddenTable.fill, unselected] using related.cache
  simp only [finishStep, StateT.run]
  rw [related.protocol.beacon]
  cases phase : right.1.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      have active : InitSent left.1.1 := by
        refine ⟨control, prekey, oneTime, kem, ?_⟩
        rw [related.protocol.beacon]
        exact phase
      simp only [map_bind]
      refine relTriple_bind (relTriple_refl _) fun prepared other same => ?_
      subst other
      cases prepared with
      | none =>
          simp only [map_pure]
          apply relTriple_pure_pure
          exact Or.inl ⟨(ProtocolRel.finish _ _ _ _ related.protocol control none).1,
            fun invariant => EntryRel.finishPlain setup context Q j prk left right related control none true invariant⟩
      | some pending =>
          have selectedInput : ∀ bytes, rootInput setup context.seed context.scalar
              (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) = some bytes →
              ∀ cache staged, SelectedAt setup context.seed context.scalar Q j
                (finishAfterInput control left.1.1
                  (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) cache staged).2.ghost bytes := by
            intro bytes rooted nextCache staged
            simp only [SelectedAt, last, Nat.lt_irrefl, ↓reduceIte, finishAfterInput, finishOutcome_touches,
              finishTouched, beaconInput]
            rw [firstBeacon_after _ [] _ (related.source.1.clean active)]
            exact rooted
          simp only [programmedServices, realServices, selectingServices, programmedDerive, selectHidden,
            StateT.run, cache]
          cases rooted : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar
              (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) with
          | none =>
              simp only [pure_bind, map_pure]
              apply relTriple_pure_pure
              refine Or.inl ⟨?_, fun invariant => ?_⟩
              · simpa only [finishTouched, related.protocol.beacon, related.protocol.ctx] using
                  (ProtocolRel.finish _ _ _ _ (ProtocolRel.context _ _ _ _
                    (ProtocolRel.touch _ _ _ _ related.protocol _ _ rfl) right.1.1.ctx) control none).1
              · have kept := EntryRel.finishDerived setup context Q j prk left right related control
                  (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
                  right.1.1.ctx none true right.1.2.2
                  (fun _ => unselected) (fun _ found => found)
                  (fun other found => by rw [unselected] at found; cases found) related.good related.clean
                  (by simpa only [finishAfterInput, finishTouched, related.protocol.beacon, related.protocol.ctx,
                    HiddenTable.fill, unselected] using invariant)
                simpa only [finishAfterInput, finishTouched, related.protocol.beacon, related.protocol.ctx,
                  HiddenTable.fill, unselected] using kept
          | some bytes =>
              cases hit : right.1.2.2.cache bytes with
              | none =>
                  simp only [programmedRead, hit, map_pure, pure_bind, sourceHiddenServices, related.protocol.ctx,
                    bind_pure_comp, Functor.map_map]
                  apply relTriple_map_same
                  intro staged _
                  refine Or.inl ⟨?_, fun invariant => ?_⟩
                  · simpa only [finishTouched, related.protocol.beacon] using
                      (ProtocolRel.finish _ _ _ _ (ProtocolRel.context _ _ _ _
                        (ProtocolRel.touch _ _ _ _ related.protocol _ _ rfl) staged.2.2) control staged.1).1
                  · have kept := EntryRel.finishDerived setup context Q j prk left right related control
                      (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)
                      staged.2.2 staged.1 true { right.1.2.2 with hidden := some bytes }
                      (fun flag => by simp only [Bool.or_true, Bool.true_eq_false] at flag)
                      (fun other found => by rw [unselected] at found; cases found)
                      (fun other found => by cases Option.some.inj found; exact selectedInput bytes rooted _ _)
                      related.good (fun other found => by cases Option.some.inj found; exact hit)
                      (by simpa only [finishAfterInput, finishTouched, related.protocol.beacon, HiddenTable.fill] using invariant)
                    simpa only [finishAfterInput, finishTouched, related.protocol.beacon, HiddenTable.fill] using kept
              | some value =>
                  simp only [programmedRead, hit, map_pure, pure_bind, bind_pure_comp, Functor.map_map]
                  refine relTriple_post_mono (relTriple_support _ _
                    (fun result => SelectedBad setup context.seed context.scalar Q j result.2.1.1.ghost)
                    (fun result => result.2.1.2.2.bad = true) ?_ ?_)
                    (fun _ _ pair => Or.inr pair)
                  · intro result supported
                    simp only [support_map, Set.mem_image] at supported
                    obtain ⟨staged, _, rfl⟩ := supported
                    have lastIndex : j = Fin.last Q := Fin.ext last
                    rw [lastIndex]
                    apply beacon_cache_refusal setup context.seed context.scalar (context.publicValue setup) Q
                      left.1.1 left.1.2.2 _ bytes related.source.1 related.source.2.2 active
                    · simp only [cache, hit, ne_eq, reduceCtorEq, not_false_eq_true]
                    · refine ⟨[Touch.beacon (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected)], ?_⟩
                      simp only [finishOutcome_touches]
                    · simpa only [← lastIndex, SelectedAt, finishAfterInput, finishOutcome_touches, finishTouched] using
                        selectedInput bytes rooted staged.2.2 staged.1
                  · intro result supported
                    simp only [support_pure, Set.mem_singleton_iff] at supported
                    subst supported
                    rfl
  | _ =>
      simp only [map_pure]
      apply relTriple_pure_pure
      exact Or.inl ⟨rfl, fun _ => { related with
        flag := congrArg (· || true) related.flag
        unselected := fun flag => related.unselected (Bool.or_eq_false_iff.mp flag).1 }⟩

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

/-- The actual adaptive finish handler preserves complete replies and states until the refusal already excluded by the original event. Both reused and first designated operations are covered. -/
theorem finish_step_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (prk : HmacBlock)
    (raw : Pqxdh.Bytes) (left : EntryState KemSK) (right : HiddenState KemSK)
    (related : EntryRel (Reader := Reader) (Response := Response) setup context Q j prk left right) :
    RelTriple ((prefetchedHandler setup codec checks context Q j prk (.inr (.finish raw))).run left)
      ((hiddenHandler setup codec checks context Q j
        (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))
        (.inr (.finish raw))).run right)
      (UntilBad (EntryRel (Reader := Reader) (Response := Response) setup context Q j prk)
        (SourceBad (Reader := Reader) (Response := Response) setup context Q j)
        (fun state => state.1.2.2.bad = true)) := by
  apply close_query_coupling setup codec checks context Q j prk _ (.inr (.finish raw)) left right related.source
  rw [hiddenHandler_good setup codec checks context Q j _ (.inr (.finish raw)) right related.good]
  have chosenSame := designated_related Q j (.inr (.finish raw)) _ left.1 right.1 related.protocol
  simp only [prefetchedHandler, once, StateT.run, ← chosenSame, ← related.flag]
  by_cases used : left.2 = true
  · simp only [used, ↓reduceIte, latch, StateT.run, skeleton, ← chosenSame]
    simpa only [used, StateT.run, ServerAuthSpec, PqxdhServerAuthExperiment.QuerySpec, OracleSpec.Range, OracleSpec.add_apply_inr] using finish_ordinary_coupling setup codec checks context Q j prk raw
      (designated Q j (.inr (.finish raw)) left.1) left right related
  · by_cases chosen : designated Q j (.inr (.finish raw)) left.1 = true
    · simp only [used, ↓reduceIte, latch, StateT.run, skeleton, ← chosenSame, chosen]
      have designatedLast : j.val = Q := by
        by_contra other
        simp only [designated, other, ↓reduceIte, Bool.false_eq_true] at chosen
      simpa only [used, StateT.run, ServerAuthSpec, PqxdhServerAuthExperiment.QuerySpec, OracleSpec.Range, OracleSpec.add_apply_inr, Bool.false_eq_true, ↓reduceIte] using finish_selected_coupling setup codec checks context Q j prk raw left right related
        (Bool.eq_false_iff.mpr used) designatedLast
    · simp only [used, chosen, latch, StateT.run, skeleton, ← chosenSame]
      simpa only [used, chosen, StateT.run, ServerAuthSpec, PqxdhServerAuthExperiment.QuerySpec, OracleSpec.Range, OracleSpec.add_apply_inr, Bool.false_eq_true, ↓reduceIte] using finish_ordinary_coupling setup codec checks context Q j prk raw
        (designated Q j (.inr (.finish raw)) left.1) left right related

end BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.finishPlain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.finishPlain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.finishDerived' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.EntryRel.finishDerived
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_ordinary_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_ordinary_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_selected_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_selected_coupling
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_step_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthEntryFactor.finish_step_coupling

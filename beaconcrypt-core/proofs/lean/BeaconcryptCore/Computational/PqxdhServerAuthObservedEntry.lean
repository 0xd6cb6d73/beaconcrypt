import BeaconcryptCore.Computational.PqxdhServerAuthApiJournal

/-! Accepted root-erased observations with exact public API journals. The observer may test publication history, but has no selected PRK, root or pending secret slot in its argument. -/
open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthAcceptedEntry
open PqxdhSecretInputKdf PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Only the root-erased analysis trace and literal public API requests and replies are observed. -/
abbrev Observer := Ghost → QueryLog ServerAuthSpec → Bool

/-- The accepted-owner coordinate and the supplied concrete observation are tested together. -/
noncomputable def decision (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) (ghost : Ghost)
    (journal : QueryLog ServerAuthSpec) : Bool :=
  @decide (Gate setup context.seed context.scalar Q j ghost ∧ observer (eraseGhost ghost) journal = true)
    (Classical.propDecidable _)

/-- The actual protocol relation preserves every observation in this interface. This is a proved interface property, not an assumed event-preservation premise. -/
theorem decision_related (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (Q : Nat) (j : Fin (Q + 1)) (observer : Observer) (root : RootOutput) (marks : Marks)
    (left right : GameState KemSK) (journal : QueryLog ServerAuthSpec)
    (related : ProtocolRel root marks left right) :
    decision setup context Q j observer left.ghost journal =
      decision setup context Q j observer right.ghost journal := by
  unfold decision
  rw [gate_related setup context.seed context.scalar Q j root marks left right related, related.ghost]

/-- Complete prefetched source run, retaining the exact chronological API history. -/
noncomputable def prefetched (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) (prk : HmacBlock) : ProbComp Bool :=
  (fun result => decision setup context Q j observer result.2.1.1.ghost result.1.2) <$>
    (simulateQ (prefetchedHandler setup codec checks context Q j prk)
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))).run
        ((contextState setup context, fun _ => false, ∅), false)

/-- The omitted-entry interpreter retains the same history and rejects its private refusal flag. -/
noncomputable def hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) (services : Services Response HiddenTable) : ProbComp Bool :=
  (fun result => !result.2.1.2.2.bad &&
    decision setup context Q j observer result.2.1.1.ghost result.1.2) <$>
    (simulateQ (hiddenHandler setup codec checks context Q j services)
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))).run
        ((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false)

/-- Per-context real comparison before the five key-schedule replacements. The chosen root appears only in the two actual source services. -/
noncomputable def sourceHidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) (prk : HmacBlock) : ProbComp Bool :=
  hidden setup codec checks adversary revealSeed Q j observer context
    (sourceHiddenServices setup codec checks context (expandRoot setup.hmac prk))

/-- Ordinary key-schedule continuation; its selected-key argument is exactly the correlated 108-byte output. -/
noncomputable def distinguisher (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) : ProbComp Bool :=
  hidden setup codec checks adversary revealSeed Q j observer context
    (factorServices setup codec checks context value)

/-- The existing complete-state source coupling applies to the client returning its whole journal. No equality of final marginals is used to infer a joint execution law. -/
theorem source_hidden_coupling (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK)
    (supported : context ∈ support (contextSample setup codec)) (prk : HmacBlock) :
    RelTriple (prefetched setup codec checks adversary revealSeed Q j observer context prk)
      (sourceHidden setup codec checks adversary revealSeed Q j observer context prk)
      (fun left right => left = true → right = true) := by
  classical
  unfold prefetched sourceHidden hidden
  apply relTriple_map
  apply relTriple_post_mono (hidden_client_coupling setup codec checks context Q j prk _ _ _
    (EntryRel.initial setup codec context supported Q j prk))
  rintro left right (⟨same, related⟩ | ⟨bad, _⟩) won
  case inr => exact (no_refusal setup context.seed context.scalar (context.publicValue setup) Q j
    left.2.1.1 bad.1.1 (@of_decide_eq_true _ (Classical.propDecidable _) won).1 bad.2).elim
  case inl =>
    simpa only [decision_related setup context Q j observer _ _ _ _ _ related.protocol, same,
      related.good, Bool.not_false, Bool.true_and] using won

/-- Full service equality replaces only the designated schedule, retaining the journal and observer decision. -/
theorem source_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) (prk : HmacBlock) :
    sourceHidden setup codec checks adversary revealSeed Q j observer context prk =
      distinguisher setup codec checks adversary revealSeed Q j observer context
        (PqxdhServerAuthKeySchedule.keySchedule setup.source setup.hmac prk) := by
  simp only [sourceHidden, distinguisher, PqxdhServerAuthKeySchedule.keySchedule,
    source_factor_services]

/-- Real table services and complete original source handlers, observed through the API journal. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) : ProbComp Bool :=
  (fun result => decision setup context Q j observer result.2.1.ghost result.1.2) <$>
    (simulateQ (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (realServices context.seed context.scalar setup codec checks))
      (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))).run
        (contextState setup context, fun _ => false, ∅)

set_option linter.deprecated false in
/-- The single prefetched block preserves the joint law of the complete source state and chronological API journal, and therefore this observation. It is unused on hits or rejection. -/
theorem source_prefetched (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (adversary : Adversary) (revealSeed : Bool) (Q : Nat) (j : Fin (Q + 1))
    (observer : Observer) (context : Context KemSK) :
    𝒮[source setup codec checks adversary revealSeed Q j observer context] =
      𝒮[do
        let prk ← $ᵗ HmacBlock
        prefetched setup codec checks adversary revealSeed Q j observer context prk] := by
  have complete := eager_projected (designated Q j) ($ᵗ HmacBlock)
    (skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (realServices context.seed context.scalar setup codec checks))
    (fun value => skeleton setup codec checks (context.publicValue setup) context.beaconSeed
      (programmedServices context.seed context.scalar setup codec checks value))
    (programmedStep_sample setup codec checks (context.publicValue setup) context.beaconSeed
      context.seed context.scalar)
    (PqxdhServerAuthApiJournal.record (adversary (contextInput setup revealSeed context)))
    ((contextState setup context, fun _ => false, ∅), false)
  simpa only [source, prefetched, prefetchedHandler, ← map_bind, evalSPMF_map,
    Functor.map_map, Function.comp_def] using
    congrArg (fun distribution => (fun result =>
      decision setup context Q j observer result.2.1.ghost result.1.2) <$> distribution) complete

end BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.decision_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.decision_related

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.source_hidden_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.source_hidden_coupling

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.source_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.source_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.source_prefetched' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthObservedEntry.source_prefetched

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitness
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationWitnessEvents
import BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityCoupling

open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor
open PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhDeploymentPublicationSuppression (Selection Target)
open PqxdhDeploymentPublicationSuppressionTrace
open PqxdhDeploymentPublicationSelectionFacts (targetAt fromAudit occurrenceTarget)
open PqxdhDeploymentPublicationAuditBounds (Valid)
open PqxdhDeploymentPublicationAuditHistory (Held)
open PqxdhDeploymentPublicationSecuritySelection (GoodTarget SelectedEvent)
open PqxdhDeploymentPublicationDomination (monitoredRun)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result X : Type}

/-- A public captured target is backed by an actual prepared occurrence at its selected global ordinal. -/
theorem targetAt_some (occurrences : List Occurrence) (ordinal : Nat) (target : Target)
    (captured : targetAt occurrences ordinal = some target) :
    ∃ occurrence ∈ occurrences, occurrence.ordinal = ordinal ∧ occurrenceTarget occurrence = target := by
  induction occurrences with
  | nil => cases captured
  | cons head tail ih =>
    by_cases selected : head.ordinal = ordinal
    · simp only [targetAt, List.findSome?_cons, selected, ite_true] at captured
      exact ⟨head, by simp, selected, Option.some.inj captured⟩
    · simp only [targetAt, List.findSome?_cons, selected, ite_false] at captured
      obtain ⟨occurrence, member, same, targetSame⟩ := ih captured
      exact ⟨occurrence, by simp [member], same, targetSame⟩

/-- An actual valid audit has at most one prepared occurrence at a global call ordinal. -/
theorem ordinal_unique (audit : Audit) (valid : Valid audit) (first second : Occurrence)
    (firstIn : first ∈ audit.occurrences) (secondIn : second ∈ audit.occurrences)
    (same : first.ordinal = second.ordinal) : first = second := by
  have unique : ∀ (occurrences : List Occurrence), occurrences.Pairwise (fun left right => left.ordinal < right.ordinal) →
      ∀ first ∈ occurrences, ∀ second ∈ occurrences, first.ordinal = second.ordinal → first = second := by
    intro occurrences pairwise
    induction occurrences with
    | nil => intro first member; cases member
    | cons head tail ih =>
      obtain ⟨headBefore, rest⟩ := List.pairwise_cons.mp pairwise
      intro first firstIn second secondIn same
      rcases List.mem_cons.mp firstIn with rfl | firstTail
      · rcases List.mem_cons.mp secondIn with rfl | secondTail
        · rfl
        · have increasing := headBefore second secondTail
          omega
      · rcases List.mem_cons.mp secondIn with rfl | secondTail
        · have increasing := headBefore first firstTail
          omega
        · exact ih rest first firstTail second secondTail same
  exact unique audit.occurrences valid.2 first firstIn second secondIn same

private theorem bundle_record (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (address : Nat)
    (state : State KemSK) (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support ((bundle setup codec address).run state)) :
    ∃ index tuples, tuples.length ≤ 1 ∧ result.2.2 = state.2.record address index result.1 tuples := by
  cases found : state.1.owners[address]? with
  | none =>
    simp only [bundle, StateT.run, found, mem_support_pure_iff] at supported
    subst result
    exact ⟨0, [], by simp, rfl⟩
  | some entry =>
    simp only [bundle, StateT.run, found, support_map, Set.mem_image] at supported
    obtain ⟨returned, member, rfl⟩ := supported
    obtain ⟨tuples, bounded, recorded⟩ := PqxdhDeploymentPublicationAuditBounds.trace_record setup codec address
      entry.identityIndex entry.owner state.1.pool.1 state.2 returned member
    exact ⟨entry.identityIndex, tuples, bounded, recorded⟩

/-- Every actual source query retains all previous chronological occurrences. -/
theorem query_inclusion (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed index query).run state)) :
    ∀ occurrence ∈ state.2.occurrences, occurrence ∈ result.2.2.occurrences := by
  rcases query with (coin | command) | read
  case inl.inr =>
    cases command
    case bundle address =>
      obtain ⟨_, tuples, _, recorded⟩ := bundle_record setup codec address state result supported
      rw [recorded]
      intro occurrence member
      exact List.mem_append_left _ member
    all_goals
      simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact fun _ member => member
  all_goals
    simp only [handler, onSource, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact fun _ member => member

/-- Every adaptive real suffix retains all earlier prepared occurrences, including failed attempts. -/
theorem program_inclusion (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed index) program).run state)) :
    ∀ occurrence ∈ state.2.occurrences, occurrence ∈ result.2.2.occurrences := by
  exact run_rel (handler setup codec checks seed index)
    (fun before after => ∀ occurrence ∈ before.2.occurrences, occurrence ∈ after.2.occurrences)
    (fun _ _ member => member)
    (fun _ _ _ first second occurrence member => second occurrence (first occurrence member))
    (fun query before after member => query_inclusion setup codec checks seed index query before after member)
    program state result supported

private theorem next_record (audit : Audit) (valid : Valid audit) (ordinal address index : Nat)
    (reply : Option Pqxdh.Bytes) (tuples : List PqxdhEd25519EufCma.Phase1KeyTuple) (bounded : tuples.length ≤ 1) :
    (fromAudit ordinal audit).next
      (targetAt (audit.record address index reply tuples).occurrences audit.nextBundle) =
      fromAudit ordinal (audit.record address index reply tuples) := by
  cases tuples with
  | nil =>
    have prepared := PqxdhDeploymentPublicationSelectionFacts.targetAt_record audit audit.nextBundle address index reply none valid.1
    simp only [Option.toList_none, Option.map_none, ite_true] at prepared
    rw [prepared]
    simpa only [Option.toList_none, Option.map_none] using
      PqxdhDeploymentPublicationSelectionFacts.fromAudit_record audit ordinal address index reply none valid.1
  | cons head tail =>
    cases tail with
    | nil =>
      have prepared := PqxdhDeploymentPublicationSelectionFacts.targetAt_record audit audit.nextBundle address index reply (some head) valid.1
      simp only [Option.toList_some, Option.map_some, ite_true] at prepared
      rw [prepared]
      simpa only [Option.toList_some, Option.map_some] using
        PqxdhDeploymentPublicationSelectionFacts.fromAudit_record audit ordinal address index reply (some head) valid.1
    | cons other rest => simp only [List.length_cons] at bounded; omega

private theorem prepared_receipt (audit : Audit) (valid : Valid audit) (address index : Nat)
    (reply : Option Pqxdh.Bytes) (tuples : List PqxdhEd25519EufCma.Phase1KeyTuple) (target : Target)
    (prepared : targetAt (audit.record address index reply tuples).occurrences audit.nextBundle = some target) :
    ∃ occurrence ∈ (audit.record address index reply tuples).occurrences,
      occurrenceTarget occurrence = target ∧ occurrence.reply = reply := by
  obtain ⟨occurrence, member, ordinal, targetSame⟩ := targetAt_some _ _ target prepared
  rcases List.mem_append.mp member with old | added
  · have past := valid.1 occurrence old
    omega
  · obtain ⟨keys, keyIn, rfl⟩ := List.mem_map.mp added
    exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨keys, keyIn, rfl⟩), targetSame, rfl⟩

private theorem goodTarget_at (ordinal : Nat) (audit : Audit) (target : Target)
    (valid : Valid audit) (good : GoodTarget ordinal audit target) (occurrence : Occurrence)
    (member : occurrence ∈ audit.occurrences) (sameOrdinal : occurrence.ordinal = ordinal) :
    occurrenceTarget occurrence = target := by
  obtain ⟨selected, selectedIn, ordinalSame, targetSame, _, _⟩ := good
  have same := ordinal_unique audit valid occurrence selected member selectedIn (sameOrdinal.trans ordinalSame.symm)
  simpa only [same] using targetSame

private theorem targetAt_complete (occurrences : List Occurrence) (ordinal : Nat) (target : Target)
    (present : ∃ occurrence ∈ occurrences, occurrence.ordinal = ordinal)
    (same : ∀ occurrence ∈ occurrences, occurrence.ordinal = ordinal → occurrenceTarget occurrence = target) :
    targetAt occurrences ordinal = some target := by
  induction occurrences with
  | nil => obtain ⟨_, impossible, _⟩ := present; cases impossible
  | cons head tail ih =>
    by_cases selected : head.ordinal = ordinal
    · simp only [targetAt, List.findSome?_cons, selected, ite_true, same head (by simp) selected]
    · obtain ⟨occurrence, member, atOrdinal⟩ := present
      have inTail : occurrence ∈ tail := by
        rcases List.mem_cons.mp member with rfl | inTail
        · exact False.elim (selected atOrdinal)
        · exact inTail
      have rest := ih ⟨occurrence, inTail, atOrdinal⟩
        (fun occurrence member sameOrdinal => same occurrence (by simp [member]) sameOrdinal)
      simpa only [targetAt, List.findSome?_cons, selected, ite_false] using rest

/-- The final good selection is exactly the captured target reconstructed from the real global audit. -/
theorem goodTarget_captured (audit : Audit) (valid : Valid audit) (ordinal : Nat) (target : Target)
    (good : GoodTarget ordinal audit target) : (fromAudit ordinal audit).target = some target := by
  exact targetAt_complete audit.occurrences ordinal target
    ⟨good.choose, good.choose_spec.1, good.choose_spec.2.1⟩
    (fun occurrence member sameOrdinal => goodTarget_at ordinal audit target valid good occurrence member sameOrdinal)

/-- A real source step on a correctly selected final trajectory satisfies the actual one-sided coupling guard. Both publication failure and first-message freshness follow from the same final chronological source audit. -/
theorem step_allowed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : State KemSK) (valid : Valid state.2) (held : Held (fun _ => []) state)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support ((handler setup codec checks seed index query).run state))
    (final : Audit) (finalValid : Valid final) (target : Target) (good : GoodTarget ordinal final target)
    (retained : ∀ occurrence ∈ result.2.2.occurrences, occurrence ∈ final.occurrences) :
    PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal query state result = true := by
  rcases query with (coin | command) | read
  case inl.inr =>
    cases command
    case bundle address =>
      obtain ⟨slot, tuples, bounded, recorded⟩ := bundle_record setup codec address state result supported
      have allowedWrite : ((fromAudit ordinal state.2).next
          (targetAt result.2.2.occurrences state.2.nextBundle)).blocks
          (targetAt result.2.2.occurrences state.2.nextBundle) = true → result.1 = none := by
        intro blocked
        rw [recorded, next_record state.2 valid ordinal address slot result.1 tuples bounded] at blocked
        cases prepared : targetAt (state.2.record address slot result.1 tuples).occurrences state.2.nextBundle with
        | none => simp only [prepared, Selection.blocks, Bool.false_eq_true] at blocked
        | some captured =>
          have selected : targetAt (state.2.record address slot result.1 tuples).occurrences ordinal = some captured := by
            simpa only [Selection.blocks, fromAudit, prepared, beq_iff_eq] using blocked
          obtain ⟨chosen, chosenIn, chosenOrdinal, chosenTarget⟩ := targetAt_some _ ordinal captured selected
          have chosenGood := goodTarget_at ordinal final target finalValid good chosen
            (retained chosen (recorded ▸ chosenIn)) chosenOrdinal
          have capturedSame : captured = target := chosenTarget.symm.trans chosenGood
          obtain ⟨current, currentIn, currentTarget, currentReply⟩ := prepared_receipt state.2 valid address slot result.1
            tuples captured prepared
          have failed := good.choose_spec.2.2.2.2 current (retained current (recorded ▸ currentIn))
            (currentTarget.trans capturedSame)
          exact currentReply.symm.trans failed
      have allowedFresh : ∀ captured, state.2.nextBundle = ordinal →
          targetAt result.2.2.occurrences state.2.nextBundle = some captured →
          PqxdhDeploymentPublicationSuppressionFreshness.Fresh captured state.1.pool.1 := by
        intro captured selected prepared
        have preparedAt : targetAt result.2.2.occurrences ordinal = some captured := by rwa [← selected]
        obtain ⟨current, currentIn, currentOrdinal, currentTarget⟩ := targetAt_some _ ordinal captured preparedAt
        have capturedSame : captured = target := currentTarget.symm.trans
          (goodTarget_at ordinal final target finalValid good current (retained current currentIn) currentOrdinal)
        rw [capturedSame]
        have exactHistory := held target.identityIndex
        simp only [List.nil_append] at exactHistory
        apply PqxdhDeploymentPublicationWitness.earliest_source_fresh final state.2 target.identityIndex ordinal target.oneTime
          state.1.pool.1 exactHistory
        · intro previous previousIn before
          apply Bool.eq_false_iff.mpr
          intro matched
          exact good.choose_spec.2.2.2.1 previous previousIn before
            ((PqxdhDeploymentPublicationWitnessEvents.occurrenceTarget_eq _ _ _).mpr matched)
        · intro previous previousIn
          exact ⟨retained previous (query_inclusion setup codec checks seed index _ state result supported previous previousIn),
            selected ▸ valid.1 previous previousIn⟩
      simp only [PqxdhDeploymentPublicationSecurityCoupling.allowed, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨allowedWrite, allowedFresh⟩
    all_goals rfl
  all_goals rfl

private theorem program_valid (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index : Nat) (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (valid : Valid state.2) (result : Result × State KemSK)
    (supported : result ∈ support ((simulateQ (handler setup codec checks seed index) program).run state)) :
    Valid result.2.2 :=
  OracleComp.simulateQ_run_preserves_inv_of_query _ (fun current => Valid current.2)
    (fun query current previous reached member =>
      (PqxdhDeploymentPublicationAuditBounds.query_audit setup codec checks seed index query current reached member).2 previous)
    program state valid result supported

/-- A correctly selected final actual trajectory never trips the concrete sticky guard. The proof follows every adaptive source continuation and derives its pre-capture freshness from the literal chronological history. -/
theorem monitored_good (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (index ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : State KemSK) (valid : Valid state.2) (held : Held (fun _ => []) state) (clean : Bool)
    (observed : (Result × State KemSK) × Bool)
    (supported : observed ∈ support (monitoredRun (handler setup codec checks seed index)
      (PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal) program state clean))
    (target : Target) (good : GoodTarget ordinal observed.1.2.2 target) : observed.2 = clean := by
  induction program using OracleComp.inductionOn generalizing state clean with
  | pure value =>
    change observed ∈ support (pure ((value, state), clean)) at supported
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    rfl
  | query_bind query next ih =>
    change observed ∈ support ((handler setup codec checks seed index query).run state >>= fun middle =>
      monitoredRun (handler setup codec checks seed index) (PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal)
        (next middle.1) middle.2 (clean && PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal query state middle)) at supported
    obtain ⟨middle, first, rest⟩ := (mem_support_bind_iff _ _ _).mp supported
    have terminal : observed.1 ∈ support
        ((simulateQ (handler setup codec checks seed index) (next middle.1)).run middle.2) := by
      rw [← PqxdhDeploymentPublicationDomination.monitoredRun_erasure _ _ _ _
        (clean && PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal query state middle), support_map]
      exact ⟨observed, rest, rfl⟩
    have middleValid := (PqxdhDeploymentPublicationAuditBounds.query_audit setup codec checks seed index query state middle first).2 valid
    have finalValid := program_valid setup codec checks seed index (next middle.1) middle.2 middleValid observed.1 terminal
    have included := program_inclusion setup codec checks seed index (next middle.1) middle.2 observed.1 terminal
    have admitted := step_allowed setup codec checks seed index ordinal query state valid held middle first
      observed.1.2.2 finalValid target good included
    have middleHeld := PqxdhDeploymentPublicationAuditHistoryInvariant.query_held setup codec checks seed index query
      (fun _ => []) state held middle first
    have compared := ih middle.1 middle.2 middleValid middleHeld
      (clean && PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal query state middle) rest
    simpa only [admitted, Bool.and_true] using compared

/-- The actual generated/imported constructor followed by the complete real scheduler with only a sticky analysis bit added. -/
noncomputable def initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    ProbComp ((Option (PqxdhDeploymentPublicationSecurityAudit.SourceOutcome KemSK Result) ×
      PqxdhRegistrationJointServerPrefix.State KemSK A) × Bool) := do
  let born ← (PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId supplied).run state
  match born.1 with
  | none => pure ((none, born.2), true)
  | some created =>
    (fun observed => ((some (PqxdhRegistrationJointServerBirth.encode created, observed.1.1, observed.1.2),
      (observed.1.2.1.pool, born.2.2)), observed.2)) <$>
      monitoredRun (handler setup codec checks created.seed created.server.server.metadata.identityIndex)
        (PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal) program
        (PqxdhRegistrationJointSchedule.initial born.2.1 (PqxdhRegistrationSchedule.initial created).shared, Audit.empty) true

/-- Erasing only the sticky bit gives the exact complete original initialized audit distribution. -/
theorem initialized_erasure (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (ordinal : Nat)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (state : PqxdhRegistrationJointServerPrefix.State KemSK A) :
    Prod.fst <$> initialized setup codec checks ensureInit supplied ordinal program state =
      (PqxdhDeploymentPublicationSecurityAudit.initialized setup codec checks ensureInit supplied program).run state := by
  simp only [initialized, PqxdhDeploymentPublicationSecurityAudit.initialized, StateT.run, map_bind]
  apply bind_congr
  rintro ⟨(_ | created), born⟩
  · rfl
  · simpa only [Functor.map_map, StateT.run] using congrArg
      (fun work => (fun result : Result × State KemSK =>
        (some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2),
          (result.2.1.pool, born.2))) <$> work)
      (PqxdhDeploymentPublicationDomination.monitoredRun_erasure
        (handler setup codec checks created.seed created.server.server.metadata.identityIndex)
        (PqxdhDeploymentPublicationSecurityCoupling.allowed ordinal) program
        (PqxdhRegistrationJointSchedule.initial born.1 (PqxdhRegistrationSchedule.initial created).shared, Audit.empty) true)

/-- Every actually initialized final selected event is retained by the concrete monitor. Constructor history, chronological validity and initial freshness are all derived from the actual empty private service pools. -/
theorem selected_clean (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (ordinal : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (runtime : A)
    (observed : PqxdhDeploymentPublicationSecurityAudit.Outcome KemSK A X × Bool)
    (supported : observed ∈ support
      (initialized setup codec checks ensureInit none ordinal
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary)
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (event : SelectedEvent setup codec ordinal observed.1) : observed.2 = true := by
  simp only [initialized, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨(_ | created), born⟩, bornMember, continued⟩ := supported
  · obtain rfl := OracleComp.eq_of_mem_support_pure _ continued
    obtain ⟨_, _, _, impossible, _⟩ := event
    cases impossible
  · simp only [support_map, Set.mem_image] at continued
    obtain ⟨reached, member, equal⟩ := continued
    subst observed
    obtain ⟨_, _, _, same, target, good, _⟩ := event
    have sameAudit := congrArg (fun value => value.2.2.2) (Option.some.inj same)
    have goodAt : GoodTarget ordinal reached.1.2.2 target := by rw [sameAudit]; exact good
    have unsigned : ∀ index, PqxdhRegistrationJointSigningTranscript.messagesAt index born.1.1.transcript = [] := by
      intro index
      rw [(PqxdhRegistrationJointServerBirth.source_constructor setup.joint ensureInit setup.serverKeyId none
        ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) born created bornMember).1,
        PqxdhRegistrationJointAttemptInitialized.install_messages]
      rfl
    have initialHeld : Held (fun _ => [])
        (PqxdhRegistrationJointSchedule.initial born.1 (PqxdhRegistrationSchedule.initial created).shared, Audit.empty) := by
      intro index
      simpa only [PqxdhRegistrationJointSchedule.initial, unsigned, List.nil_append] using
        PqxdhDeploymentPublicationAuditHistoryInvariant.initial_held
          (PqxdhRegistrationJointSchedule.initial born.1 (PqxdhRegistrationSchedule.initial created).shared) index
    exact monitored_good setup codec checks created.seed created.server.server.metadata.identityIndex ordinal _ _
      PqxdhDeploymentPublicationAuditBounds.valid_empty initialHeld true reached member target goodAt

end BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.targetAt_some' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.targetAt_some

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.ordinal_unique' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.ordinal_unique

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.query_inclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.query_inclusion

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.program_inclusion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.program_inclusion

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.goodTarget_captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.goodTarget_captured

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.step_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.step_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.monitored_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.monitored_good

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.initialized_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.initialized_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.selected_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentPublicationSecurityMonitor.selected_clean

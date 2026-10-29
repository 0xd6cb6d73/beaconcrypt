-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawKemTrace

/-! Raw-CBOR eligibility uses the actual public wire transcript and produced frames. The source registration codec is the tagged proof representation, while event designation reads the native wire codec. Accepts and bundles retain their original bytes, so their credential and KEM-pool correspondence follows the actual compiled trace. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CborRawKemTransfer

open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle Budget Mode ModeSpec FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentRegistrationTrace (Logged traceFrom acceptsOf)
open CborAdmissionCompiler (Local)
open CborTaggedSimulation (boundaryWire)
open PqxdhDeploymentKemTransfer (Observed target happens observeGame designated selectedKem tag_support designateIn_some
  designate_keys acceptOf_mem registrations map_support_congr)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

def observeCompiled (result : (X × Ledger) × Local) : Observed X :=
  (result.1.1, result.1.2, result.2.copies.produced)

noncomputable def decision (crypto : Pqxdh.Crypto) (wire : Codec Reader Response) (serverId : Std.U64)
    (budget : Budget) (event : Observed X → Bool) (claim : Observed X → Option Handle)
    (g : Fin budget.accept × Fin budget.capacity) (result : (X × Ledger) × Local) : Bool :=
  event (observeCompiled result) && decide (target crypto wire serverId budget claim (observeCompiled result) = some g)

theorem candidate_same (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (raw : Pqxdh.Bytes) :
    PqxdhDeploymentTranscript.candidateOf (CborRawCompile.sourceCodec wire parse) raw =
      PqxdhDeploymentTranscript.candidateOf (boundaryWire wire parse) raw := rfl

theorem keymatch_point (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse)) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A)
    (outcome : PqxdhRegistrationJointInitializedSchedule.SourceOutcome KemSK
      ((((X × Ledger) × Local) × List Logged) × PqxdhRegistrationJointAcceptCutTag.Tag))
    (after : PqxdhRegistrationJointServerPrefix.State KemSK A)
    (reached : (some outcome, after) ∈ support ((PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks
      ensureInit none (PqxdhRegistrationJointAcceptCutTag.tag (traceFrom (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary)
        []) g.1.val)).run ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)))
    (decided : decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g outcome.2.1.1.1 = true) :
    ∃ raw value, outcome.2.1.2 = some (raw, some g.1.val) ∧
      PqxdhRegistrationJointRawSignatures.verified setup (CborRawCompile.sourceCodec wire parse) checks raw = some value ∧
      (after.1.2.keys[g.2.val]?).map Prod.fst = some value.keys.pqKey := by
  have tagged := PqxdhDeploymentRegistrationTrace.source_support setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none _ _ _ outcome
    reached
  have tagEq := PqxdhDeploymentRegistrationTrace.tag_traced _ g.1.val outcome.2.1 tagged
  have logEq := CborRawKemTrace.compiled_trace setup wire parse bounds mode adversary outcome.2.1.1
    (tag_support _ g.1.val outcome.2.1 tagged)
  have projected : (some (outcome.1, outcome.2.1.1, outcome.2.2), after) ∈ support
      ((PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
        (traceFrom (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) [])).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) := by
    rw [← PqxdhRegistrationJointAcceptCutTag.tag_erase (traceFrom (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) [])
      g.1.val, PqxdhDeploymentRegistrationTrace.source_map, support_map]
    exact ⟨_, reached, rfl⟩
  obtain ⟨traced, poolEq⟩ := PqxdhDeploymentRegistrationTrace.traced_source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none _ _ rfl
    after (outcome.1, outcome.2.1.1, outcome.2.2) projected
  simp only at traced poolEq
  simp only [decision, Bool.and_eq_true, decide_eq_true_eq] at decided
  obtain ⟨_, targeted⟩ := decided
  obtain ⟨handle, _, designatedIn⟩ := Option.bind_eq_some_iff.mp targeted
  obtain ⟨raw, accepted, keys, published, rawFound, candidateFound, keysFound, publishedFound, pqFound⟩ :=
    designate_keys _ (boundaryWire wire parse) setup.serverKeyId _ handle _ _ (designateIn_some _ (boundaryWire wire parse) setup.serverKeyId budget _ handle g
      designatedIn)
  rw [← candidate_same wire parse raw] at candidateFound
  have acceptLogged : (raw, some g.1.val) ∈ acceptsOf outcome.2.1.1.2 := by
    rw [logEq]
    simp only [acceptsOf, registrations, List.mem_filterMap]
    exact ⟨.accept raw (some g.1.val), ⟨_, acceptOf_mem _ _ raw rawFound, rfl⟩, rfl⟩
  obtain ⟨position, positionFound⟩ := List.mem_iff_getElem?.mp acceptLogged
  have samePosition := traced.positional position raw g.1.val positionFound
  rw [← samePosition] at positionFound
  obtain ⟨value, checked⟩ := traced.verified raw g.1.val acceptLogged
  obtain ⟨candidateEq, keysEq⟩ := PqxdhDeploymentKeyMatch.verified_keys setup (CborRawCompile.sourceCodec wire parse) checks raw value checked
  rw [candidateFound, Option.some.injEq] at candidateEq
  subst candidateEq
  rw [keysFound, Option.some.injEq] at keysEq
  subst keysEq
  obtain ⟨bytes, bytesFound, publishedRead⟩ := Option.bind_eq_some_iff.mp publishedFound
  have bundleLogged : Logged.bundle g.2.val (some bytes) ∈ outcome.2.1.1.2 := by
    rw [logEq]
    simp only [registrations, List.mem_filterMap]
    exact ⟨_, PqxdhDeploymentKeyMatch.bundleOf_mem _ _ bytes bytesFound, rfl⟩
  obtain ⟨identity, tuple, s1, s2, s3, written, pooled⟩ := traced.bundles g.2.val bytes bundleLogged
  rw [← candidate_same wire parse bytes] at publishedRead
  rw [PqxdhDeploymentKeyMatch.candidateOf_written (CborRawCompile.sourceCodec wire parse) phase1 _ bytes written, Option.some.injEq] at publishedRead
  subst publishedRead
  rw [PqxdhDeploymentKeyMatch.publishedPq_candidate, Option.some.injEq] at pqFound
  refine ⟨raw, value, by rw [tagEq, positionFound], checked, ?_⟩
  rw [poolEq, pooled, pqFound]



theorem approved_goodkem (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (index : Nat) (runtime : A) {count : Nat}
    (kemIndex : Fin count)
    (final : PqxdhRegistrationJointKemRawBridge.Final KemSK A ((X × Ledger) × Local))
    (supported : final ∈ support ((fun result =>
      (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
      (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks
        ensureInit none (PqxdhRegistrationJointAcceptCutTag.tag
          (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) index)).run
            ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))) :
    PqxdhRegistrationJointKemRawBridge.GoodKem kemIndex final := by
  rw [support_map] at supported
  obtain ⟨result, member, rfl⟩ := supported
  have noIdentity := PqxdhRegistrationJointAcceptCutTag.tag_bound _ index _ 0
    (CborRawCompileSecrecy.compile_full_unread setup wire parse bounds mode adversary 0 (by decide))
  have noKem := PqxdhRegistrationJointAcceptCutTag.tag_bound _ index _ 0
    (CborRawCompileSecrecy.compile_full_unread setup wire parse bounds mode adversary 1 (by decide))
  exact PqxdhDeploymentQuiet.goodKem_of_quiet kemIndex _
    (PqxdhDeploymentQuiet.quiet_initialized setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none _
      noIdentity noKem _ PqxdhDeploymentQuiet.quiet_empty result member)

theorem eligible_actual (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse)) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option Handle) (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    𝒟[(fun outcome => decide (happens event outcome = true ∧
        designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome = some g)) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} =
    (letI := Classical.propDecidable
    𝒟[(fun final => decide (PqxdhRegistrationJointKemRawBridge.Decided
          (decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g) final ∧
        PqxdhRegistrationJointKemRawBridge.GoodKem (selectedKem budget g) final ∧
        PqxdhRegistrationJointKemRawBridge.KeyMatchFinal setup (CborRawCompile.sourceCodec wire parse) checks (selectedKem budget g) final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
          (PqxdhRegistrationJointAcceptCutTag.tag (CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary) g.1.val)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true}) := by
  set work := CborRawCompileSecrecy.compileFull setup wire parse bounds mode adversary with workEq
  set tagged := PqxdhRegistrationJointAcceptCutTag.tag (traceFrom work []) g.1.val with taggedEq
  set start : PqxdhRegistrationJointServerPrefix.State KemSK A :=
    ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) with startEq
  have erased : work = (fun outcome => outcome.1.1) <$> tagged := by
    calc work = Prod.fst <$> traceFrom work [] := (PqxdhDeploymentRegistrationTrace.traceFrom_erase work []).symm
      _ = Prod.fst <$> (Prod.fst <$> tagged) := by rw [taggedEq, PqxdhRegistrationJointAcceptCutTag.tag_erase]
      _ = (fun outcome => outcome.1.1) <$> tagged := by rw [Functor.map_map]
  have retagged : PqxdhRegistrationJointAcceptCutTag.tag work g.1.val =
      (fun outcome => (outcome.1.1, outcome.2)) <$> tagged := by
    have mapped := PqxdhDeploymentRegistrationTrace.tag_map Prod.fst (traceFrom work []) g.1.val
    rw [PqxdhDeploymentRegistrationTrace.traceFrom_erase] at mapped
    exact mapped
  have leftRun : (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none work).run start =
      (fun result => (result.1.map fun outcome => (outcome.1, outcome.2.1.1.1, outcome.2.2), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none tagged).run start := by
    have mapped := PqxdhDeploymentRegistrationTrace.source_map setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (fun outcome : (((X × Ledger) × Local) × List Logged) × PqxdhRegistrationJointAcceptCutTag.Tag => outcome.1.1)
      tagged start
    rw [← erased] at mapped
    exact mapped
  have rightRun : (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none
      (PqxdhRegistrationJointAcceptCutTag.tag work g.1.val)).run start =
      (fun result => (result.1.map fun outcome => (outcome.1, (outcome.2.1.1.1, outcome.2.1.2), outcome.2.2),
        result.2)) <$> (PqxdhRegistrationJointInitializedSchedule.source setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none tagged).run
          start := by
    rw [retagged]
    exact PqxdhDeploymentRegistrationTrace.source_map setup (CborRawCompile.sourceCodec wire parse) checks ensureInit none _ tagged start
  have game := CborRawCompileSecrecy.compile_full_source setup wire parse checks lengths parser ensureInit phase1 phase2 bounds
    mode adversary start
  change _ = (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime at game
  rw [← game, leftRun, rightRun]
  simp only [Functor.map_map]
  congr 2
  apply map_support_congr
  rintro ⟨_ | outcome, after⟩ member
  · simp [happens, observeGame, CborRawCompileSecrecy.mergeFull, PqxdhRegistrationJointKemRawBridge.Decided]
  · have observed : observeGame (CborRawCompileSecrecy.mergeFull
        (some (PqxdhRegistrationJointInitializedSchedule.eraseOutcome (outcome.1, outcome.2.1.1.1, outcome.2.2)),
          after.2)).1 = some (observeCompiled outcome.2.1.1.1) := rfl
    have good : PqxdhRegistrationJointKemRawBridge.GoodKem (selectedKem budget g)
        ((some (outcome.1, (outcome.2.1.1.1, outcome.2.1.2), outcome.2.2)).map
          (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), after) := by
      apply approved_goodkem setup wire parse checks ensureInit bounds mode
        adversary g.1.val runtime
      rw [← workEq, ← startEq, rightRun, Functor.map_map, support_map]
      exact ⟨_, member, rfl⟩
    rw [decide_eq_decide]
    constructor
    · rintro ⟨happened, chosen⟩
      simp only [happens, Option.map_some] at happened
      rw [observed] at happened
      simp only [designated, Option.map_some] at chosen
      rw [observed] at chosen
      have decided : decision setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget event claim g outcome.2.1.1.1 = true := by
        simp only [decision, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by simpa using happened, by simpa using chosen⟩
      obtain ⟨raw, value, tagEq, checked, keys⟩ := keymatch_point setup wire parse checks ensureInit phase1 bounds mode
        adversary budget event claim g runtime outcome after member decided
      refine ⟨⟨_, rfl, decided, by simp only [tagEq]; rfl⟩, good, _, raw, some g.1.val, value, rfl, tagEq, checked, keys⟩
    · rintro ⟨⟨reached, found, decided, _⟩, _⟩
      simp only [Option.map_some, Option.some.injEq] at found
      subst found
      simp only [decision, Bool.and_eq_true, decide_eq_true_eq] at decided
      refine ⟨?_, ?_⟩
      · simp only [happens, Option.map_some]
        rw [observed]
        exact decided.1
      · simp only [designated, Option.map_some]
        rw [observed, Option.bind_some]
        exact decided.2



end BeaconcryptCore.Computational.CborRawKemTransfer

/-- info: 'BeaconcryptCore.Computational.CborRawKemTransfer.candidate_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTransfer.candidate_same

/-- info: 'BeaconcryptCore.Computational.CborRawKemTransfer.keymatch_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTransfer.keymatch_point

/-- info: 'BeaconcryptCore.Computational.CborRawKemTransfer.approved_goodkem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTransfer.approved_goodkem

/-- info: 'BeaconcryptCore.Computational.CborRawKemTransfer.eligible_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawKemTransfer.eligible_actual

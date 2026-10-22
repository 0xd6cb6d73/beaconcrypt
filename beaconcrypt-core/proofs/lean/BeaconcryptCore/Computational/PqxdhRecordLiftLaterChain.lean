-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainLift
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterTargets

/-!
# Record-lift later `chain_lift` (items 4 and 5, stage S6, R6, item 5)

**Statement.** `later_chain_lift` proves `PqxdhRecordLiftLaterTargets.LaterChainLiftTarget` as defined, for the explicit reduction family `laterChainReduction` and the explicit bills `laterChainBills`: for every environment with `Frame`, every run-phase adversary within its budget, every reveal function, every post adversary within its post budget and every decision on the later view and the final shared BLAKE2b cache (or every Boolean event of them), the later real world and the later chain-ideal world differ by at most the sum over the `hops n budget` ordered indices of the Extract-on-`uniform32` and HMAC-PRF advantages of the explicit full76 observers, each with coefficient one, with zero aliasing and refusal terms.

**Method: the chain hybrid of an arbitrary World client.** The chain track's hop and telescope (`PqxdhRecordLiftChainHop`, `PqxdhRecordLiftChainHybrid`) are stated for the frozen run-phase program, but their cores are schedule-level: the seed and parent cuts (`PqxdhRecordLiftGlobalSeedCut.observed_bound`, `PqxdhRecordLiftGlobalCut.observed_bound`), the supported-prefix lemmas (`PqxdhRecordLiftSeedScope.sampled_schedule`, `PqxdhRecordLiftSourcePrefix.sampled_schedule`, `PqxdhRecordLiftPrefixPolicy.sampled_schedule`) and the operational invariant (`PqxdhRecordLiftMixedWorld.schedule_kdf`, `schedule_good`) hold for every compiled World client. This module restates the program-level wrappers for an arbitrary World client of the frozen result shape: the KDF cap and depth bound of a client within the record budget (`chainsOf_bounds`), the terminal hybrid (`terminal_safe_of`, `chainsOf_terminal`), the seed cut (`scan_absent_of`, `seed_prefix_of`, `uniform_policy_of`), the parent cut (`childUniform_policy_of`), one hop (`hopObserverOf`, `hop_bound_of`) and the telescope (`observerOf`, `chain_loss_of`); the proofs are the chain track's, with the compiled client in place of the frozen program. The later target is `chain_loss_of` at the two-phase program, which is within the run budget's record part (`PqxdhRecordLiftLaterWorlds.later_recordBounded`).

**Bills.** The observer bills hold for every compiled client whose services draw at most `bill` uniform bytes (`parentObserver_total_of`, `seedObserver_total_of`, `observerOf_total`: `2 * bill + 44 + cost`). The two-phase World program stays within `laterProgramBill` in every component ledger (`later_interface_weighted`, from `PqxdhRecordLiftLater.program_effect_bound` and `program_record_bound`), so its compiled form within `laterProgramCoins` uniform bytes (`later_weighted`, `later_coins`); `laterProgramCoins_closed` is the run-phase `PqxdhRecordLiftChainBills.programCoins` plus one byte per post coin effect and 64 per post hash and per post administrative effect, and `laterObserverBill_closed` the run-phase observer bill plus twice that post work.

**Contracts.** `hop_bound_of`, `chain_loss_of`, `later_chain_lift_bool` and `later_chain_lift` use the contract `SourceFullCorrect` (an explicit hypothesis of the first two, a premise of the target for the last two) and the Extract-on-`uniform32` and HMAC-PRF games as advantage terms; no other theorem uses a contract. New Claude work; the proofs of the client-level wrappers follow the chain track's program-level proofs.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf PqxdhSecretInputKdf
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftChainOrder
open PqxdhRecordLiftLaterWorlds
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### Run facts of an arbitrary World client -/

/-- Every chain world of an arbitrary World client factors through the complete compiler run. -/
theorem chainsOf_factor (ideal : Coordinate (Slot n) → Bool) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) :
    chainsOf ideal setup codec route client = splitResult <$>
      (simulateQ (PqxdhRecordLiftWorldCompiler.handler (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec
        route) client).run PqxdhRecordLiftWorldCompiler.initial :=
  schedule_factor _ setup codec route client PqxdhRecordLiftWorldCompiler.initial

/-- Every supported result of a chain world of an arbitrary World client within the record budget has the executed KDF cap `S + 51 R` and a table of depth below it. -/
theorem chainsOf_bounds (ideal : Coordinate (Slot n) → Bool) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (budget : Budget)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (records : RecordBounded budget client)
    (result : RunResult n E X) (supported : result ∈ support (chainsOf ideal setup codec route client)) :
    result.2.primitive.1.native .kdf ≤ budget.sends + 51 * budget.receives ∧
      DepthBound result.2.chain (budget.sends + 51 * budget.receives) := by
  rw [chainsOf_factor, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have kdf : inner.2.primitive.1.native .kdf ≤ budget.sends + 51 * budget.receives := by
    simpa only [PqxdhRecordLiftWorldCompiler.initial, PqxdhRecordLiftWorld.Counts.empty, Nat.zero_add] using
      PqxdhRecordLiftMixedWorld.schedule_kdf setup codec ideal route client budget.sends budget.receives
        (records .send) (records .raw) PqxdhRecordLiftWorldCompiler.initial inner member
  have good := PqxdhRecordLiftMixedWorld.schedule_good setup codec ideal route client
    PqxdhRecordLiftWorldCompiler.initial (PqxdhRecordLiftMixedWorld.initial_good setup.source ideal) inner member
  exact ⟨kdf, depth_mono inner.2.chain good.2.2.2.2 kdf⟩

/-- Every supported result of a chain world of an arbitrary World client has the mixed operational invariant. -/
theorem chainsOf_good (ideal : Coordinate (Slot n) → Bool) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X))
    (result : RunResult n E X) (supported : result ∈ support (chainsOf ideal setup codec route client)) :
    PqxdhRecordLiftMixedWorld.Good setup.source ideal (join result.1.2 result.2) := by
  rw [chainsOf_factor, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact PqxdhRecordLiftMixedWorld.schedule_good setup codec ideal route client PqxdhRecordLiftWorldCompiler.initial
    (PqxdhRecordLiftMixedWorld.initial_good setup.source ideal) inner member

/-! ### The terminal hybrid -/

/-- Every lookup reached by the terminal hybrid's run of an arbitrary World client within the record budget is at a coordinate where the terminal selector is ideal. -/
theorem terminal_safe_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) :
    PqxdhRecordLiftAvailability.Safe
      (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source
        (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))) setup codec)
      (fun query _ => PqxdhRecordLiftPrefixPolicy.AgreesAt
        (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget)) (fun _ => true) query)
      (schedule codec.frameRead route client initialControl) initialPrivate := by
  apply PqxdhRecordLiftSeedPolicy.safe_of_reaches
  intro query next after reached
  cases query with
  | lookup coordinate =>
      change selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget) coordinate = true
      rw [PqxdhRecordLiftIdeal.hops, selected_last]
      obtain ⟨step, member⟩ := OracleComp.support_nonempty
        ((interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
          (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))) setup codec
          (.lookup coordinate)).run after)
      obtain ⟨final, finalMember⟩ := OracleComp.support_nonempty
        ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
          (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))) setup codec)
          (next step.1)).run step.2)
      have present := simulateQ_run_preservesInv _ _
        (PqxdhRecordLiftSeedPolicy.present_preserved setup.source _ setup codec coordinate) (next step.1) step.2
        (PqxdhRecordLiftSeedPolicy.lookup_present setup.source _ setup codec coordinate after step member)
        final finalMember
      have whole := PqxdhRecordLiftSeedPolicy.reaches_final
        (PqxdhRecordLiftSeedPolicy.reaches_step reached step member) final finalMember
      have depth := (chainsOf_bounds (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget))
        setup codec route budget client records final whole).2
      obtain ⟨value, found⟩ := Option.ne_none_iff_exists'.mp present
      exact depth coordinate value found
  | _ => trivial

/-- The terminal ordered hybrid of an arbitrary World client within the record budget is its chain-ideal world. -/
theorem chainsOf_terminal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) :
    chainsOf (selected (PqxdhRecordLiftIdeal.positions budget) (PqxdhRecordLiftIdeal.hops n budget)) setup codec route
        client =
      chainsOf (fun _ => true) setup codec route client :=
  PqxdhRecordLiftSeedPolicy.run_agrees setup codec _ (fun _ => true) _ initialPrivate
    (terminal_safe_of setup codec route budget client records)

/-! ### The seed cut at depth zero -/

/-- Every supported final state of the first-allocation scan of an arbitrary compiled World client has an empty table at every coordinate of the selected slot. -/
theorem scan_absent_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X))
    (target : Slot n) (coordinate : Coordinate (Slot n)) (same : coordinate.slot = target)
    (final : PqxdhRecordLiftGlobalSeedCut.Cut n (Outcome E X × Control n) × Private n)
    (supported : final ∈ support ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
      setup codec) (PqxdhRecordLiftGlobalSeedCut.scan target
        (schedule codec.frameRead route client initialControl))).run initialPrivate)) :
    final.2.chain coordinate = none := by
  rcases final with ⟨cut | next, after⟩
  · have missing := PqxdhRecordLiftGlobalSeedCut.scan_initial_missing setup.source ideal setup codec target
      (schedule codec.frameRead route client initialControl) _ supported
    have whole := PqxdhRecordLiftSeedPolicy.complete_whole setup.source ideal setup codec target _ cut after supported
    have good := chainsOf_good ideal setup codec route client (cut, after) whole
    cases found : after.chain coordinate with
    | none => rfl
    | some value =>
        obtain ⟨seed, present⟩ := good.2.2.1 coordinate value found
        change after.seeds.1 coordinate.slot = some seed at present
        rw [same, missing] at present
        contradiction
  · exact (PqxdhRecordLiftSeedScope.pending_schedule setup codec ideal route client target next after supported).2.2
      coordinate same

/-- The first-allocation prefix of an arbitrary compiled World client is the same under the adjacent policy that idealizes one initial coordinate of the selected slot. -/
theorem seed_prefix_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (target : Slot n) (direction : Bool) :
    PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source ideal setup codec target
        (schedule codec.frameRead route client initialControl) =
      PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source
        (Function.update ideal ⟨target, direction, start direction⟩ true) setup codec target
        (schedule codec.frameRead route client initialControl) := by
  apply (map_inj_right (f := Subtype.val) (fun h => Subtype.ext h)).mp
  rw [PqxdhRecordLiftGlobalSeedCut.prefix_forget, PqxdhRecordLiftGlobalSeedCut.prefix_forget]
  have absent := PqxdhRecordLiftSeedPolicy.lookup_absent setup.source ideal setup codec ⟨target, direction, start direction⟩
    _ initialPrivate
    (fun final member => scan_absent_of setup codec ideal route client target ⟨target, direction, start direction⟩ rfl
      final member)
  exact PqxdhRecordLiftSeedPolicy.run_agrees setup codec ideal _ _ initialPrivate
    (PqxdhRecordLiftSeedPolicy.safe_mono _ _ absent
      (fun query _ different => PqxdhRecordLiftSeedPolicy.agrees_update ideal _ true query different))

/-- The independent seed endpoint of `PqxdhRecordLiftGlobalSeedCut.observed_bound` for an arbitrary compiled World client is the adjacent mixed policy with the selected initial coordinate ideal, for every observer. -/
theorem uniform_policy_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X))
    (filling : PqxdhSecretInputKdf.RootOutput) (target : Slot n) (direction : Bool)
    (real : ideal ⟨target, direction, start direction⟩ = false)
    (finish : PqxdhRecordLiftGlobalCut.Observer (Outcome E X × Control n)) :
    LazyOracleDiscard.LawEq
      (PqxdhRecordLiftGlobalSeedCut.seedUniform setup.source ideal filling setup codec target direction
        (schedule codec.frameRead route client initialControl) finish)
      ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
        (Function.update ideal ⟨target, direction, start direction⟩ true)) setup codec)
        (schedule codec.frameRead route client initialControl)).run initialPrivate >>=
          PqxdhRecordLiftGlobalCut.observe finish) := by
  rw [← PqxdhRecordLiftGlobalSeedCut.resume_prefix setup.source _ setup codec target,
    ← seed_prefix_of setup codec ideal route client target direction]
  simp only [PqxdhRecordLiftGlobalSeedCut.seedUniform, PqxdhRecordLiftGlobalSeedCut.retainedContext, bind_assoc,
    pure_bind]
  apply PqxdhRecordLiftSeedPolicy.lawEq_bind_support
  intro reached supported
  cases stopped : reached.val.1 with
  | complete result =>
      simp only [PqxdhRecordLiftGlobalSeedCut.seedObserver, stopped, PqxdhRecordLiftGlobalSeedCut.finish,
        simulateQ_pure, StateT.run_pure, pure_bind]
      exact (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
        (fun _ => LazyOracleDiscard.lawEq_drop _ _)).trans (LazyOracleDiscard.lawEq_drop _ _)
  | pending next =>
      have facts := PqxdhRecordLiftSeedScope.sampled_schedule setup codec ideal route client target reached supported
        next stopped
      simp only [PqxdhRecordLiftGlobalSeedCut.seedObserver, stopped, PqxdhRecordLiftGlobalSeedCut.finish,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      refine LazyOracleDiscard.LawEq.trans ?_ (PqxdhRecordLiftGlobalSeedCut.miss_continuation
        (PqxdhRecordLiftChainOracle.lookup setup.source ·
          (Function.update ideal ⟨target, direction, start direction⟩ true)) setup codec target direction
        reached.val.2 reached.property _).symm
      apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
      intro other
      have good : PqxdhRecordLiftSeedPolicy.Good ⟨target, direction, start direction⟩ ideal
          (PqxdhRecordLiftGlobalSeedCut.prepare reached.val.2 target direction other, none) :=
        ⟨rfl, real, facts.2.2 _ rfl⟩
      exact (LazyOracleDiscard.lawEq_drop ($ᵗ PqxdhSecretInputKdf.RootOutput) _).symm.trans
        (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) (fun hidden =>
          PqxdhRecordLiftSeedPolicy.independent_observed ideal setup codec filling hidden _ (next ())
            (PqxdhRecordLiftGlobalSeedCut.prepare reached.val.2 target direction other) good finish))

/-! ### The parent cut at positive depth -/

/-- The independent-child endpoint of `PqxdhRecordLiftGlobalCut.observed_bound` at a selected parent, for an arbitrary compiled World client, is the adjacent mixed policy with the parent's successor ideal, for every observer. -/
theorem childUniform_policy_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X))
    (parent : Coordinate (Slot n)) (lower : start parent.direction ≤ parent.position)
    (parentIdeal : ideal parent = true) (childReal : ideal (advance parent 1) = false)
    (observer : PqxdhRecordLiftGlobalCut.Observer (Outcome E X × Control n)) :
    LazyOracleDiscard.LawEq
      (PqxdhRecordLiftProjectionCut.childUniform
        (PqxdhRecordLiftGlobalCut.parentSample setup.source ideal setup codec parent
          (schedule codec.frameRead route client initialControl))
        (PqxdhRecordLiftGlobalCut.parentObserver setup.source ideal setup codec observer))
      ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
        (Function.update ideal (advance parent 1) true)) setup codec)
        (schedule codec.frameRead route client initialControl)).run initialPrivate >>=
          PqxdhRecordLiftGlobalCut.observe observer) := by
  have different : advance parent 1 ≠ parent := by
    intro equal
    have positions := congrArg Coordinate.position equal
    simp only [advance] at positions
    omega
  have reads : PqxdhRecordLiftMaskedReads.Reads (advance parent 1) parent := by
    refine ⟨?_, previous_advance parent⟩
    simp only [advance]
    omega
  have agree : ∀ coordinate, coordinate ≠ advance parent 1 →
      ideal coordinate = Function.update ideal (advance parent 1) true coordinate :=
    fun coordinate unequal => (Function.update_of_ne unequal true ideal).symm
  have parentIdeal' : Function.update ideal (advance parent 1) true parent = true := by
    rw [Function.update_of_ne (Ne.symm different)]
    exact parentIdeal
  rw [← PqxdhRecordLiftFirstLookup.resume_prefix setup.source _ setup codec parent,
    ← PqxdhRecordLiftPrefixPolicy.sampled_schedule setup codec ideal _ parent (advance parent 1) reads agree
      route client]
  simp only [PqxdhRecordLiftProjectionCut.childUniform, PqxdhRecordLiftProjectionCut.retainedContext,
    PqxdhRecordLiftGlobalCut.parentSample, bind_assoc, pure_bind]
  apply PqxdhRecordLiftSeedPolicy.lawEq_bind_support
  intro reached supported
  cases stopped : reached.val.1 with
  | complete result =>
      simp only [PqxdhRecordLiftGlobalCut.parentObserver, stopped, PqxdhRecordLiftFirstLookup.finish,
        simulateQ_pure, StateT.run_pure, pure_bind]
      exact (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
        (fun _ => LazyOracleDiscard.lawEq_drop _ _)).trans (LazyOracleDiscard.lawEq_drop _ _)
  | pending next =>
      have facts := PqxdhRecordLiftSourcePrefix.sampled_schedule setup codec ideal route client parent reached supported
        next stopped
      simp only [PqxdhRecordLiftGlobalCut.parentObserver, stopped, PqxdhRecordLiftFirstLookup.finish,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      refine LazyOracleDiscard.LawEq.trans ?_ (PqxdhRecordLiftGlobalCut.miss_continuation setup.source
        (Function.update ideal (advance parent 1) true) setup codec parent reached.val.2 parentIdeal'
        reached.property _).symm
      apply LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _)
      intro value
      have good : PqxdhRecordLiftChildPolicy.Good parent ideal
          (PqxdhRecordLiftGlobalCut.prepare reached.val.2 parent value, none) :=
        ⟨rfl, ⟨lower, parentIdeal, childReal⟩, facts.2.2.2 _ reads⟩
      exact (LazyOracleDiscard.lawEq_drop ($ᵗ RootOutput) _).symm.trans
        (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) (fun hidden =>
          PqxdhRecordLiftChildPolicy.independent_observed ideal setup codec hidden parent (next ())
            (PqxdhRecordLiftGlobalCut.prepare reached.val.2 parent value) good observer))

/-! ### One hop and the telescope -/

/-- The explicit full76 observer of one ordered hybrid index for an arbitrary compiled World client and a chain decision: the seed-cut reduction observer at depth zero, the parent-cut reduction observer at positive depth. -/
noncomputable def hopObserverOf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool)
    (positions : Nat) (step : Fin (positions * (n * 2))) : FullObserver Unit :=
  if (entryAt step).position = start (entryAt step).direction then
    PqxdhRecordLiftGlobalSeedCut.reductionObserver setup.source (selected positions step.val)
      PqxdhRecordLiftMaskedOracle.filling setup codec (entryAt step).slot (entryAt step).direction
      (schedule codec.frameRead route client initialControl) (PqxdhRecordLiftChainHop.finish decision)
  else
    PqxdhRecordLiftGlobalCut.reductionObserver setup.source (selected positions step.val) setup codec
      (previous (entryAt step)) (schedule codec.frameRead route client initialControl)
      (PqxdhRecordLiftChainHop.finish decision)

/-- One ordered hop for an arbitrary compiled World client and every chain decision: the adjacent chain hybrids differ by at most the Extract-on-`uniform32` advantage plus the HMAC-PRF advantage of `hopObserverOf`, each with coefficient one. Contract: `SourceFullCorrect`. -/
theorem hop_bound_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (hmac : HmacSha512) (correct : SourceFullCorrect setup.source hmac)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool)
    (positions : Nat) (step : Fin (positions * (n * 2))) :
    (chainsOf (selected positions step.val) setup codec route client >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)).boolDistance
      (chainsOf (selected positions (step.val + 1)) setup codec route client >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) ≤
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet
        (hopObserverOf setup codec route client decision positions step))).boolDistance
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
        (fullExtractReduction hmac .ratchet (hopObserverOf setup codec route client decision positions step))) +
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (hopObserverOf setup codec route client decision positions step))).boolDistance
      (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
        (hopObserverOf setup codec route client decision positions step))) := by
  change ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · (selected positions step.val))
      setup codec) (schedule codec.frameRead route client initialControl)).run initialPrivate >>=
        PqxdhRecordLiftGlobalCut.observe (PqxdhRecordLiftChainHop.finish decision)).boolDistance
    ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · (selected positions (step.val + 1)))
      setup codec) (schedule codec.frameRead route client initialControl)).run initialPrivate >>=
        PqxdhRecordLiftGlobalCut.observe (PqxdhRecordLiftChainHop.finish decision)) ≤ _
  rw [PqxdhRecordLiftChainHop.selected_succ step]
  have real := (selected_step step).1
  by_cases initial : (entryAt step).position = start (entryAt step).direction
  · have shape : entryAt step = ⟨(entryAt step).slot, (entryAt step).direction,
        start (entryAt step).direction⟩ := by
      rw [← initial]
    have real' : selected positions step.val ⟨(entryAt step).slot, (entryAt step).direction,
        start (entryAt step).direction⟩ = false := by
      rw [← shape]
      exact real
    have uniform := uniform_policy_of setup codec (selected positions step.val) route client
      PqxdhRecordLiftMaskedOracle.filling (entryAt step).slot (entryAt step).direction real'
      (PqxdhRecordLiftChainHop.finish decision)
    rw [← shape] at uniform
    have bound := PqxdhRecordLiftGlobalSeedCut.observed_bound setup.source hmac correct
      (selected positions step.val) PqxdhRecordLiftMaskedOracle.filling setup codec (entryAt step).slot
      (entryAt step).direction (schedule codec.frameRead route client initialControl)
      (PqxdhRecordLiftChainHop.finish decision)
    rw [PqxdhRecordLiftChainHop.advantage_congr_right _ _ _ uniform.evalDist_eq] at bound
    simpa only [hopObserverOf, initial, ite_true] using bound
  · have bounded := at_bounded step
    have later : start (entryAt step).direction < (entryAt step).position := by
      have lower := bounded.1
      omega
    have parentIdeal := selected_predecessor step later
    have positive : 0 < (entryAt step).position := Nat.lt_of_le_of_lt (Nat.zero_le _) later
    have advancePrior : advance (previous (entryAt step)) 1 = entryAt step := by
      have offset : (entryAt step).position - 1 + 1 = (entryAt step).position := Nat.sub_add_cancel positive
      simp only [previous, advance, offset]
    have lower : start (previous (entryAt step)).direction ≤ (previous (entryAt step)).position := by
      simp only [previous]
      omega
    have childReal : selected positions step.val (advance (previous (entryAt step)) 1) = false := by
      rw [advancePrior]
      exact real
    have uniform := childUniform_policy_of setup codec (selected positions step.val) route client
      (previous (entryAt step)) lower parentIdeal childReal (PqxdhRecordLiftChainHop.finish decision)
    rw [advancePrior] at uniform
    have bound := PqxdhRecordLiftGlobalCut.observed_bound setup.source hmac correct
      (selected positions step.val) setup codec (previous (entryAt step))
      (schedule codec.frameRead route client initialControl) parentIdeal (PqxdhRecordLiftChainHop.finish decision)
    rw [PqxdhRecordLiftChainHop.advantage_congr_right _ _ _ uniform.evalDist_eq] at bound
    simpa only [hopObserverOf, initial, ite_false] using bound

/-- The explicit full76 observer of one ordered index of the hybrid over `hops n budget` indices for an arbitrary compiled World client. -/
noncomputable def observerOf (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X))
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool)
    (budget : Budget) (step : Fin (PqxdhRecordLiftIdeal.hops n budget)) : FullObserver Unit :=
  hopObserverOf setup codec route client decision (PqxdhRecordLiftIdeal.positions budget) step

/-- **The chain bound for an arbitrary World client.** For every World client within the record budget and every decision on the view and the final shared cache, the all-real and chain-ideal worlds differ by at most the sum over the `hops n budget` ordered indices of the Extract-on-`uniform32` and HMAC-PRF losses of the explicit observers, each with coefficient one. Contract: `SourceFullCorrect`. -/
theorem chain_loss_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (budget : Budget) (client : OracleComp (WorldSpec n) (Outcome E X))
    (records : RecordBounded budget client) (hmac : HmacSha512) (correct : SourceFullCorrect setup.source hmac)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) :
    ENNReal.ofReal
      ((chainsOf (fun _ => false) setup codec route client >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)).boolDistance
        (chainsOf (fun _ => true) setup codec route client >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result))) ≤
    ∑ step : Fin (PqxdhRecordLiftIdeal.hops n budget),
      PqxdhRecordLiftIdeal.hopLoss hmac (observerOf setup codec route client decision budget step) := by
  let games : Nat → ProbComp Bool := fun index =>
    chainsOf (selected (PqxdhRecordLiftIdeal.positions budget) index) setup codec route client >>= fun result =>
      decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)
  have firstGame : (chainsOf (fun _ => false) setup codec route client >>= fun result =>
      decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) = games 0 := by
    have same : (selected (PqxdhRecordLiftIdeal.positions budget) 0 : Coordinate (Slot n) → Bool) = fun _ => false :=
      funext selected_zero
    simp only [games, same]
  have lastGame : (chainsOf (fun _ => true) setup codec route client >>= fun result =>
      decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) =
      games (PqxdhRecordLiftIdeal.hops n budget) := by
    simp only [games, chainsOf_terminal setup codec route budget client records]
  rw [firstGame, lastGame]
  have bound : (games 0).boolDistance (games (PqxdhRecordLiftIdeal.hops n budget)) ≤
      ∑ step : Fin (PqxdhRecordLiftIdeal.hops n budget),
        (PqxdhRecordLiftChainHybrid.extractAdvantage hmac (observerOf setup codec route client decision budget step) +
          PqxdhRecordLiftChainHybrid.prfAdvantage hmac (observerOf setup codec route client decision budget step)) := by
    refine (PqxdhRecordLiftChainHybrid.telescope games _).trans ?_
    rw [← Fin.sum_univ_eq_sum_range (fun index => (games index).boolDistance (games (index + 1)))]
    apply Finset.sum_le_sum
    intro step _
    exact hop_bound_of setup codec route client hmac correct decision (PqxdhRecordLiftIdeal.positions budget) step
  refine (ENNReal.ofReal_le_ofReal bound).trans (le_of_eq ?_)
  refine (ENNReal.ofReal_sum_of_nonneg (fun step _ => add_nonneg (abs_nonneg _) (abs_nonneg _))).trans ?_
  apply Finset.sum_congr rfl
  intro step _
  rw [PqxdhRecordLiftChainHybrid.hopLoss_eq]
  exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)

/-! ### Observer bills for an arbitrary World client -/

open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted operationBill)
open PqxdhRecordLiftChainBills (coinCost)

/-- The parent-cut reduction observer for a compiled World client whose services draw at most `bill` uniform bytes draws at most the prefix bill, the retained 44 bytes, the suffix bill and the decision's coins. -/
theorem parentObserver_total_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (bill : Nat)
    (weighted : Weighted coinCost (schedule codec.frameRead route client initialControl) bill)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) (cost : Nat)
    (decisionBound : ∀ view cache, (decision view cache).IsTotalQueryBound cost)
    (target : Coordinate (Slot n)) (context : Unit) (output : FullOutput) :
    (PqxdhRecordLiftGlobalCut.reductionObserver setup.source ideal setup codec target
      (schedule codec.frameRead route client initialControl)
      (PqxdhRecordLiftChainHop.finish decision) context output).IsTotalQueryBound (bill + (44 + (bill + cost))) := by
  have prefixRun := PqxdhRecordLiftChainBills.weighted_total coinCost _ _ _
    (PqxdhRecordLiftChainBills.lookupScan_weighted coinCost target _ _ weighted)
    (PqxdhRecordLiftChainBills.protocol_total setup.source ideal setup codec) initialPrivate
  have prefixBound : (PqxdhRecordLiftFirstLookup.sampledPrefix setup.source ideal setup codec target
      (schedule codec.frameRead route client initialControl)).IsTotalQueryBound bill := by
    rw [← isQueryBoundP_true_iff]
    exact PqxdhRecordLiftFirstLookup.sampledPrefix_bound setup.source ideal setup codec target _ (fun _ => True) _
      ((isQueryBoundP_true_iff _ _).mpr prefixRun)
  apply PqxdhRecordLiftGlobalCut.reductionObserver_bound _ _ _ _ _ _ _ _ _ prefixBound
  intro reached supported value child
  have member := PqxdhRecordLiftFirstLookupPrefix.sampled_support setup.source ideal setup codec target _ reached
    supported
  rcases reached with ⟨⟨cut, after⟩, missing⟩
  cases cut with
  | complete result =>
      exact (decisionBound _ _).mono (Nat.le_add_left _ _)
  | pending next =>
      exact isTotalQueryBound_bind
        (PqxdhRecordLiftChainBills.weighted_total coinCost _ (next ()) _
          (PqxdhRecordLiftChainBills.lookupScan_pending coinCost target _ _ _ weighted _ next after member)
          (PqxdhRecordLiftChainBills.mask_total setup.source ideal child setup codec) _)
        (fun _ => decisionBound _ _)

/-- The seed-cut reduction observer for a compiled World client whose services draw at most `bill` uniform bytes draws at most the prefix bill, the retained 32 bytes, the suffix bill and the decision's coins. -/
theorem seedObserver_total_of (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) (bill : Nat)
    (weighted : Weighted coinCost (schedule codec.frameRead route client initialControl) bill)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) (cost : Nat)
    (decisionBound : ∀ view cache, (decision view cache).IsTotalQueryBound cost)
    (filling : PqxdhSecretInputKdf.RootOutput) (target : Slot n) (direction : Bool)
    (context : Unit) (output : FullOutput) :
    (PqxdhRecordLiftGlobalSeedCut.reductionObserver setup.source ideal filling setup codec target direction
      (schedule codec.frameRead route client initialControl)
      (PqxdhRecordLiftChainHop.finish decision) context output).IsTotalQueryBound (bill + (32 + (bill + cost))) := by
  have prefixRun := PqxdhRecordLiftChainBills.weighted_total coinCost _ _ _
    (PqxdhRecordLiftChainBills.seedScan_weighted coinCost target _ _ weighted)
    (PqxdhRecordLiftChainBills.protocol_total setup.source ideal setup codec) initialPrivate
  have prefixBound : (PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source ideal setup codec target
      (schedule codec.frameRead route client initialControl)).IsTotalQueryBound bill := by
    rw [← isQueryBoundP_true_iff]
    exact PqxdhRecordLiftGlobalSeedCut.sampledPrefix_bound setup.source ideal setup codec target _ (fun _ => True) _
      ((isQueryBoundP_true_iff _ _).mpr prefixRun)
  apply PqxdhRecordLiftGlobalSeedCut.reductionObserver_bound _ _ _ _ _ _ _ _ _ _ _ prefixBound
  intro reached supported other child
  have member : reached.val ∈ support ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
      ideal) setup codec) (PqxdhRecordLiftGlobalSeedCut.scan target
        (schedule codec.frameRead route client initialControl))).run initialPrivate) := by
    rw [← PqxdhRecordLiftGlobalSeedCut.prefix_forget, support_map]
    exact ⟨reached, supported, rfl⟩
  rcases reached with ⟨⟨cut, after⟩, missing⟩
  cases cut with
  | complete result =>
      exact (decisionBound _ _).mono (Nat.le_add_left _ _)
  | pending next =>
      exact isTotalQueryBound_bind
        (PqxdhRecordLiftChainBills.weighted_total coinCost _ (next ()) _
          (PqxdhRecordLiftChainBills.seedScan_pending coinCost target _ _ _ weighted _ next after member)
          (PqxdhRecordLiftChainBills.seedMask_total setup.source ideal filling child setup codec) _)
        (fun _ => decisionBound _ _)

/-- Every observer of the ordered chain hybrid of a compiled World client whose services draw at most `bill` uniform bytes draws at most `2 * bill + 44 + cost` uniform bytes. -/
theorem observerOf_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X)) (bill : Nat)
    (weighted : Weighted coinCost (schedule codec.frameRead route client initialControl) bill)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) (cost : Nat)
    (decisionBound : ∀ view cache, (decision view cache).IsTotalQueryBound cost)
    (budget : Budget) (step : Fin (PqxdhRecordLiftIdeal.hops n budget)) (context : Unit) (output : FullOutput) :
    (observerOf setup codec route client decision budget step context output).IsTotalQueryBound
      (2 * bill + 44 + cost) := by
  unfold observerOf hopObserverOf
  split_ifs
  · exact (seedObserver_total_of setup codec _ route client bill weighted decision cost decisionBound _ _ _ context
      output).mono (by omega)
  · exact (parentObserver_total_of setup codec _ route client bill weighted decision cost decisionBound _ context
      output).mono (by omega)

/-! ### The later program's bills -/

open PqxdhRecordLiftLaterTargets

/-- The later effect total of one class: the run-phase total of `PqxdhRecordLiftChainBills.effectTotal` plus the post phase's effects `PqxdhRecordLiftLater.postCost` (direct post coins and hashes, and the environment's class-six allowance per post HMAC request). -/
def laterEffectTotal (input : LaterBillInput) (kind : EffectKind) : Nat :=
  PqxdhRecordLiftChainBills.effectTotal input.base kind + PqxdhRecordLiftLater.postCost input.base.allowance input.post kind

/-- The bill of the whole compiled two-phase program in one component ledger. -/
def laterProgramBill (kind : BudgetKind) (input : LaterBillInput) : Nat :=
  (match kind with | .uniform => 1 | _ => 0) * laterEffectTotal input .coin +
    (match kind with | .hash => 1 | _ => 0) * laterEffectTotal input .hash +
    (match kind with | .uniform => 64 | _ => 0) * laterEffectTotal input .administrative +
    operationBill kind .send * input.base.budget.sends + operationBill kind .raw * input.base.budget.receives

/-- The two-phase World program stays within `laterProgramBill` in every component ledger, for every environment within its `Frame`, every run-phase adversary within its budget and every post adversary within its post budget. -/
theorem later_interface_weighted (kind : BudgetKind) (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (post : PqxdhDeploymentLater.PostBudget) {Out R : Type} (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PqxdhDeploymentLater.PostSpec Out)
    (respects : budget.Respects first) (postRespects : ∀ output disclosed, post.Respects (second output disclosed))
    (cost : Nat) :
    Weighted (PqxdhRecordLiftChainBills.worldBill kind)
      (PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second)
      (laterProgramBill kind ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩) := by
  have class_bound := fun effect : EffectKind =>
    PqxdhRecordLiftLater.program_effect_bound env startup allowance framed crypto codec serverKid bounds mode
      ⟨budget, 0⟩ post reveal first second respects postRespects effect
  have combined := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
    (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
      (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
        (PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
          (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (match kind with | .uniform => 1 | _ => 0) _ _
            (class_bound .coin))
          (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (match kind with | .hash => 1 | _ => 0) _ _
            (class_bound .hash)))
        (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (match kind with | .uniform => 64 | _ => 0) _ _
          (class_bound .administrative)))
      (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (operationBill kind .send)
        _ _ (PqxdhRecordLiftLater.program_record_bound env crypto codec serverKid bounds mode budget reveal first second
          respects .send)))
    (PqxdhRecordLiftCtxProgramBounds.weighted_indicator _ (operationBill kind .raw)
      _ _ (PqxdhRecordLiftLater.program_record_bound env crypto codec serverKid bounds mode budget reveal first second
        respects .raw))
  exact PqxdhRecordLiftChainBills.weighted_cost_mono _ _ _ _ combined (PqxdhRecordLiftChainBills.worldBill_classes kind)

/-- The compiled two-phase program stays within `laterProgramBill` in every component ledger. -/
theorem later_weighted (kind : BudgetKind) (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (post : PqxdhDeploymentLater.PostBudget) {Out R : Type}
    (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PqxdhDeploymentLater.PostSpec Out) (respects : budget.Respects first)
    (postRespects : ∀ output disclosed, post.Respects (second output disclosed)) (cost : Nat) :
    Weighted (categoryCost kind) (schedule codec.frameRead route
      (PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second) initialControl)
      (laterProgramBill kind ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩) :=
  PqxdhRecordLiftCtxProgramBounds.weighted_run _ _ _ _ _ initialControl
    (later_interface_weighted kind env startup allowance framed crypto codec serverKid bounds mode budget post reveal
      first second respects postRespects cost)
    (PqxdhRecordLiftChainBills.handler_weighted kind codec.frameRead route)

/-- The uniform-draw bill of the whole compiled two-phase program: its uniform ledger plus 64 per shared-hash request. -/
def laterProgramCoins (input : LaterBillInput) : Nat :=
  laterProgramBill .uniform input + 64 * laterProgramBill .hash input

/-- The closed form of the later uniform-draw bill: the run-phase bill `PqxdhRecordLiftChainBills.programCoins` plus one byte per post coin effect and 64 per post hash and per post administrative effect. -/
theorem laterProgramCoins_closed (input : LaterBillInput) :
    laterProgramCoins input = PqxdhRecordLiftChainBills.programCoins input.base +
      PqxdhRecordLiftLater.postCost input.base.allowance input.post .coin +
      64 * PqxdhRecordLiftLater.postCost input.base.allowance input.post .hash +
      64 * PqxdhRecordLiftLater.postCost input.base.allowance input.post .administrative := by
  simp only [laterProgramCoins, laterProgramBill, laterEffectTotal, PqxdhRecordLiftChainBills.programCoins,
    PqxdhRecordLiftChainBills.programBill]
  omega

/-- The compiled two-phase program's services draw at most `laterProgramCoins` uniform bytes on every path. -/
theorem later_coins (env : Environment n E) (startup : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance) (crypto : Pqxdh.Crypto)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (post : PqxdhDeploymentLater.PostBudget) {Out R : Type}
    (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PqxdhDeploymentLater.PostSpec Out) (respects : budget.Respects first)
    (postRespects : ∀ output disclosed, post.Respects (second output disclosed)) (cost : Nat) :
    Weighted coinCost (schedule codec.frameRead route
      (PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second) initialControl)
      (laterProgramCoins ⟨⟨budget, startup, allowance, bounds, n, cost⟩, post⟩) := by
  have combined := PqxdhRecordLiftCtxProgramBounds.weighted_add _ _ _ _ _
    (later_weighted .uniform env startup allowance framed crypto codec route serverKid bounds mode budget post reveal
      first second respects postRespects cost)
    (PqxdhRecordLiftChainBills.weighted_scale _ 64 _ _ (later_weighted .hash env startup allowance framed crypto codec
      route serverKid bounds mode budget post reveal first second respects postRespects cost))
  exact PqxdhRecordLiftChainBills.weighted_cost_mono _ _ _ _ combined
    (fun query => (PqxdhRecordLiftChainBills.coinCost_categories query).le)

/-! ### Later `chain_lift` -/

/-- The bill of one later chain observer: the two-phase program's uniform-draw bill for the sampled prefix and again for the suffix, the retained 44 bytes (32 for a seed cut), and the decision's own coins. -/
def laterObserverBill (input : LaterBillInput) : Nat :=
  2 * laterProgramCoins input + 44 + input.base.decision

/-- The later observer bill is the run-phase observer bill plus twice the post phase's uniform-draw work. -/
theorem laterObserverBill_closed (input : LaterBillInput) :
    laterObserverBill input = PqxdhRecordLiftChainBills.observerBill input.base +
      2 * (PqxdhRecordLiftLater.postCost input.base.allowance input.post .coin +
        64 * PqxdhRecordLiftLater.postCost input.base.allowance input.post .hash +
        64 * PqxdhRecordLiftLater.postCost input.base.allowance input.post .administrative) := by
  simp only [laterObserverBill, laterProgramCoins_closed, PqxdhRecordLiftChainBills.observerBill]
  omega

/-- The explicit later chain bills. -/
def laterChainBills : LaterChainBills := ⟨laterObserverBill⟩

/-- The explicit later chain reduction family: the full76 observers of the ordered chain hybrid of the compiled two-phase program, built from the actual program, the actual seed or parent cut and the decision. -/
noncomputable def laterChainReduction (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (n : Nat) :
    LaterChainReduction n :=
  fun env mode reveal first second decision budget _ step =>
    observerOf setup codec route
      (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second) decision
      budget step

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (serverKid : Aeneas.Std.U64) (bounds : FreshBounds)

/-- Later `chain_lift`, Boolean form, with zero aliasing and refusal terms, the explicit reductions and the explicit bills. Contract: `SourceFullCorrect`. -/
theorem later_chain_lift_bool (n : Nat) (hmac : HmacSha512) :
    LaterChainLiftBool setup codec route serverKid bounds n hmac (laterChainReduction setup codec route serverKid bounds n)
      laterChainBills laterNoTerm laterNoTerm := by
  intro correct E X Out R env startup allowance framed mode reveal first second budget post respects postRespects
    decision cost decisionBound
  refine ⟨?_, fun step context output => observerOf_total setup codec route _ _
    (later_coins env startup allowance framed setup.source.crypto codec route serverKid bounds mode budget post reveal
      first second respects postRespects cost) decision cost decisionBound budget step context output⟩
  simpa only [laterNoTerm, add_zero, laterChainReduction, laterRealChains, laterIdealChains, laterChains] using
    chain_loss_of setup codec route budget
    (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)
    (later_recordBounded env setup.source.crypto codec serverKid bounds mode budget reveal first second respects)
    hmac correct decision

/-- **Later `chain_lift` (R6, item 5), delivered.** `LaterChainLiftTarget` (Boolean and event forms, zero aliasing and refusal terms) for the explicit reductions `laterChainReduction` and bills `laterChainBills`, for every slot count, HMAC and setup. Contract: `SourceFullCorrect`. -/
theorem later_chain_lift (n : Nat) (hmac : HmacSha512) :
    LaterChainLiftTarget setup codec route serverKid bounds n hmac (laterChainReduction setup codec route serverKid bounds n)
      laterChainBills :=
  laterChainLiftStatement_of_bool setup codec route serverKid bounds n hmac _ _ _ _
    (later_chain_lift_bool setup codec route serverKid bounds n hmac)

end BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_bounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.terminal_safe_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.terminal_safe_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chainsOf_terminal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.scan_absent_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.scan_absent_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.seed_prefix_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.seed_prefix_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.uniform_policy_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.uniform_policy_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.childUniform_policy_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.childUniform_policy_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.hop_bound_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.hop_bound_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chain_loss_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.chain_loss_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.parentObserver_total_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.parentObserver_total_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.seedObserver_total_of' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.seedObserver_total_of

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.observerOf_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.observerOf_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_interface_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_interface_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.laterProgramCoins_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.laterProgramCoins_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_coins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.laterObserverBill_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.laterObserverBill_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_chain_lift_bool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_chain_lift_bool

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_chain_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterChain.later_chain_lift

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftSeedPolicy
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-! One hop of the ordered chain hybrid of `PqxdhRecordLiftChainOrder`, for every index `step : Fin (positions * (n * 2))` and every chain decision on the permitted view and the final shared cache: the hybrids `selected positions step` and `selected positions (step + 1)` differ by at most one Extract-on-`uniform32` advantage plus one HMAC-PRF advantage of an explicit full76 observer (`hopObserver`), each with coefficient one. The selected coordinate `entryAt step` is the only callback whose mode changes (`selected_succ`). At depth zero it is an initial coordinate and the hop is the seed cut of `PqxdhRecordLiftGlobalSeedCut`, identified with the adjacent policy by `PqxdhRecordLiftSeedPolicy.uniform_policy`. At positive depth its predecessor is already ideal (`ChainOrder.selected_predecessor`) and the hop is the parent cut of `PqxdhRecordLiftGlobalCut`, identified with the adjacent policy by `childUniform_policy` from `PqxdhRecordLiftChildPolicy`, `PqxdhRecordLiftPrefixPolicy` and `PqxdhRecordLiftSourcePrefix`. A coordinate that the run never looks up (or a slot that it never allocates) gives equal games inside the cut's completed branch. The only source contract is `SourceFullCorrect`. -/
open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainHop
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhFullSecretInputKdf PqxdhSecretInputKdf
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftChainOrder
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

/-! ### The adjacent hybrids -/

/-- Advancing one hybrid makes exactly its selected coordinate ideal. -/
theorem selected_succ {positions : Nat} (step : Fin (positions * (n * 2))) :
    (selected positions (step.val + 1) : Coordinate (Fin n) → Bool) =
      Function.update (selected positions step.val) (entryAt step) true := by
  funext entry
  by_cases same : entry = entryAt step
  · subst entry
    rw [Function.update_self]
    exact (selected_step step).2
  · rw [Function.update_of_ne same]
    exact selected_unchanged step entry same

/-- The observer of a chain decision on the permitted view and the final shared cache. -/
def finish (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) :
    PqxdhRecordLiftGlobalCut.Observer (PqxdhRecordLiftIdeal.Client n E X) :=
  fun result cache produced _ => decision (PqxdhRecordLiftIdeal.viewOf result produced) cache

/-- A chain hybrid followed by a chain decision is the private Protocol run followed by the cut observer of that decision. -/
theorem chains_observe (ideal : Coordinate (Slot n) → Bool) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool) :
    (PqxdhRecordLiftIdeal.chains ideal setup codec route env serverKid bounds mode adversary >>= fun result =>
        decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) =
      ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal) setup codec)
        (program env setup.source.crypto codec route serverKid bounds mode adversary)).run initialPrivate >>=
          PqxdhRecordLiftGlobalCut.observe (finish decision)) := rfl

/-- Equal laws on the right preserve the Boolean distinguishing advantage. -/
theorem advantage_congr_right (left middle right : ProbComp Bool) (same : 𝒟[middle] = 𝒟[right]) :
    left.boolDistance middle = left.boolDistance right := by
  simp only [ProbComp.boolDistance, same]

/-! ### The parent cut at positive depth -/

/-- The independent-child endpoint of `PqxdhRecordLiftGlobalCut.observed_bound` at a selected parent is the adjacent concrete mixed policy with the parent's successor ideal, under the complete client result, shared ROM cache and writer logs. A parent that is never looked up gives equal games. -/
theorem childUniform_policy (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (parent : Coordinate (Slot n)) (lower : start parent.direction ≤ parent.position)
    (parentIdeal : ideal parent = true) (childReal : ideal (advance parent 1) = false)
    (observer : PqxdhRecordLiftGlobalCut.Observer (PqxdhRecordLiftIdeal.Client n E X)) :
    LazyOracleDiscard.LawEq
      (PqxdhRecordLiftProjectionCut.childUniform
        (PqxdhRecordLiftGlobalCut.parentSample setup.source ideal setup codec parent
          (program env setup.source.crypto codec route serverKid bounds mode adversary))
        (PqxdhRecordLiftGlobalCut.parentObserver setup.source ideal setup codec observer))
      ((simulateQ (interpreter (PqxdhRecordLiftChainOracle.lookup setup.source ·
        (Function.update ideal (advance parent 1) true)) setup codec)
        (program env setup.source.crypto codec route serverKid bounds mode adversary)).run initialPrivate >>=
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
    ← PqxdhRecordLiftPrefixPolicy.sampled_program setup codec ideal _ parent (advance parent 1) reads agree
      route env serverKid bounds mode adversary]
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
      have facts := PqxdhRecordLiftSourcePrefix.sampled_program setup codec ideal route env serverKid bounds mode
        adversary parent reached supported next stopped
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

/-! ### One hybrid hop -/

/-- The explicit full76 observer of one ordered hybrid index: at depth zero the seed-cut reduction observer of `PqxdhRecordLiftGlobalSeedCut` for the selected slot and direction, at positive depth the parent-cut reduction observer of `PqxdhRecordLiftGlobalCut` for the selected coordinate's predecessor. Both sample the actual source prefix of the hybrid `selected positions step` themselves and run its complete continuation. -/
noncomputable def hopObserver (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool)
    (positions : Nat) (step : Fin (positions * (n * 2))) : FullObserver Unit :=
  if (entryAt step).position = start (entryAt step).direction then
    PqxdhRecordLiftGlobalSeedCut.reductionObserver setup.source (selected positions step.val)
      PqxdhRecordLiftMaskedOracle.filling setup codec (entryAt step).slot (entryAt step).direction
      (program env setup.source.crypto codec route serverKid bounds mode adversary) (finish decision)
  else
    PqxdhRecordLiftGlobalCut.reductionObserver setup.source (selected positions step.val) setup codec
      (previous (entryAt step)) (program env setup.source.crypto codec route serverKid bounds mode adversary)
      (finish decision)

/-- One ordered hop, for every chain decision: the adjacent chain hybrids differ by at most the Extract-on-`uniform32` advantage plus the HMAC-PRF advantage of the explicit observer `hopObserver`, each with coefficient one. Contract: `SourceFullCorrect`. -/
theorem hop_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Aeneas.Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (hmac : HmacSha512) (correct : SourceFullCorrect setup.source hmac)
    (decision : PqxdhRecordLiftIdeal.View n E X → CtxRomAuth.CtxRO.QueryCache → ProbComp Bool)
    (positions : Nat) (step : Fin (positions * (n * 2))) :
    (PqxdhRecordLiftIdeal.chains (selected positions step.val) setup codec route env serverKid bounds mode
        adversary >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)).boolDistance
      (PqxdhRecordLiftIdeal.chains (selected positions (step.val + 1)) setup codec route env serverKid bounds mode
        adversary >>= fun result =>
          decision (PqxdhRecordLiftIdeal.chainView result) (PqxdhRecordLiftIdeal.chainCache result)) ≤
    (extractRealGame hmac PqxdhServerAuthKeySchedule.uniform32
      (fullExtractReduction hmac .ratchet
        (hopObserver setup codec route env serverKid bounds mode adversary decision positions step))).boolDistance
      (extractUniformGame PqxdhServerAuthKeySchedule.uniform32
        (fullExtractReduction hmac .ratchet
          (hopObserver setup codec route env serverKid bounds mode adversary decision positions step))) +
    (hmacPrfRealGame hmac (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
      (hopObserver setup codec route env serverKid bounds mode adversary decision positions step))).boolDistance
      (hmacPrfRandomGame (fullExpandReduction .ratchet PqxdhServerAuthKeySchedule.uniform32
        (hopObserver setup codec route env serverKid bounds mode adversary decision positions step))) := by
  rw [chains_observe, chains_observe, selected_succ step]
  have real := (selected_step step).1
  by_cases initial : (entryAt step).position = start (entryAt step).direction
  · have shape : entryAt step = ⟨(entryAt step).slot, (entryAt step).direction,
        start (entryAt step).direction⟩ := by
      rw [← initial]
    have real' : selected positions step.val ⟨(entryAt step).slot, (entryAt step).direction,
        start (entryAt step).direction⟩ = false := by
      rw [← shape]
      exact real
    have uniform := PqxdhRecordLiftSeedPolicy.uniform_policy setup codec (selected positions step.val) route env
      serverKid bounds mode adversary PqxdhRecordLiftMaskedOracle.filling (entryAt step).slot
      (entryAt step).direction real' (finish decision)
    rw [← shape] at uniform
    have bound := PqxdhRecordLiftGlobalSeedCut.observed_bound setup.source hmac correct
      (selected positions step.val) PqxdhRecordLiftMaskedOracle.filling setup codec (entryAt step).slot
      (entryAt step).direction (program env setup.source.crypto codec route serverKid bounds mode adversary)
      (finish decision)
    rw [advantage_congr_right _ _ _ uniform.evalDist_eq] at bound
    simpa only [hopObserver, initial, ite_true] using bound
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
    have uniform := childUniform_policy setup codec (selected positions step.val) route env serverKid bounds mode
      adversary (previous (entryAt step)) lower parentIdeal childReal (finish decision)
    rw [advancePrior] at uniform
    have bound := PqxdhRecordLiftGlobalCut.observed_bound setup.source hmac correct
      (selected positions step.val) setup codec (previous (entryAt step))
      (program env setup.source.crypto codec route serverKid bounds mode adversary) parentIdeal (finish decision)
    rw [advantage_congr_right _ _ _ uniform.evalDist_eq] at bound
    simpa only [hopObserver, initial, ite_false] using bound

end BeaconcryptCore.Computational.PqxdhRecordLiftChainHop

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.selected_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.selected_succ

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.chains_observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.chains_observe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.advantage_congr_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.advantage_congr_right

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.childUniform_policy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.childUniform_policy

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.hop_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainHop.hop_bound

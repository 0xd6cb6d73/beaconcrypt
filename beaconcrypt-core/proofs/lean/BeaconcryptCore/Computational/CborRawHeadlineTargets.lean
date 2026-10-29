-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawTargetRange
import BeaconcryptCore.Computational.PqxdhDeploymentKemTwoSided

/-! Exact named-event decomposition for the actual raw game. The original accept-times-create target set is retained; the extra private pool-reservation column has zero probability by the concrete raw source trace. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawHeadlineTargets
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec Budget)
open PqxdhDeploymentKemTransfer (Observed happens designated observeGame target)
open CborTaggedSimulation (boundaryWire)
variable {ι KemSK Reader Response A X : Type} {baseSpec : OracleSpec ι}

/-- Any actual raw event that names a designated handle is exactly the sum of its per-target events on the tight original domain. -/
theorem split_named (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks)
    (lengths : RawCtxSourcePublication.BodyLength setup.source.crypto)
    (parser : CborRawCanonicalBuild.CanonicalReadBack (boundaryWire wire parse)) (ensureInit : StateT A ProbComp Bool)
    (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack (CborRawCompile.sourceCodec wire parse))
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack (CborRawCompile.sourceCodec wire parse))
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool) (claim : Observed X → Option Handle) (runtime : A)
    (named : ∀ observed, event observed = true →
      (target setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim observed).isSome) :
    𝒟[(fun outcome => happens event outcome) <$>
      (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} =
      ∑ g : Fin budget.accept × Fin budget.create,
        𝒟[(fun outcome => decide (happens event outcome = true ∧
          designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim outcome =
            some ((g.1, g.2.castSucc) : Fin budget.accept × Fin budget.capacity))) <$>
        (CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime] {true} := by
  classical
  have split := UniformTargetSelection.split_of_eligible
    ((CborRawCompileSecrecy.game setup wire parse checks ensureInit 0 bounds mode adversary).run runtime)
    (fun outcome => happens event outcome = true)
    (designated setup.source.crypto (boundaryWire wire parse) setup.serverKeyId budget claim) (by
      intro outcome held
      cases found : observeGame outcome.1 with
      | none => simp [happens, found] at held
      | some observed =>
          have eligible := Option.isSome_iff_ne_none.mp (named observed (by simpa only [happens, found, Option.any_some] using held))
          simpa only [designated, found, Option.bind_some] using eligible)
  simp only [Bool.decide_eq_true] at split
  rw [split, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun session _ => PqxdhDeploymentKemTwoSided.sum_last_eq budget.create _ ?_
  rw [UniformTargetSelection.chance_eq, OracleComp.prEvent_eq_zero_iff]
  rintro outcome reached ⟨_, chosen⟩
  exact lt_irrefl _ (CborRawTargetRange.designated_create setup wire parse checks lengths parser ensureInit phase1 phase2
    bounds mode adversary budget respects runtime claim outcome reached _ chosen)

end BeaconcryptCore.Computational.CborRawHeadlineTargets

/-- info: 'BeaconcryptCore.Computational.CborRawHeadlineTargets.split_named' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawHeadlineTargets.split_named

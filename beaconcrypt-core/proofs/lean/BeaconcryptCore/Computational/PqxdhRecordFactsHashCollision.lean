-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsHashPairBills
import BeaconcryptCore.Computational.PqxdhRecordFactsHashOrdinaryBills

/-! Actual adaptive source digest-cache collision bound with derived global query caps. -/
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode sharedHashTotal)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsPrivateCacheSourceDraw (HashInput Spec)
open PqxdhRecordFactsPrivateCacheSourceDrawMemo (plain packed)
open PqxdhRecordLiftInterface (Environment Frame EffectKind)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec Budget)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The target class is fixed by the private address constructor before its digest reply. -/
def privateInput : HashInput n → Bool
  | .inl _ => true
  | .inr _ => false

/-- The paired experiment's private classifier is exactly the source compiler's counted predicate. -/
theorem private_class : PqxdhRecordFactsHashPairBills.classQuery (privateInput (n := n)) true =
    PqxdhRecordFactsHashPrivateBills.privateQuery := by
  funext query
  rcases query with (address | bytes) | coin <;> rfl

/-- The paired experiment's ordinary classifier is exactly the source compiler's counted predicate. -/
theorem ordinary_class : PqxdhRecordFactsHashPairBills.classQuery (privateInput (n := n)) false =
    PqxdhRecordFactsHashOrdinaryBills.ordinaryQuery := by
  funext query
  rcases query with (address | bytes) | coin <;> rfl

/-- The actual complete source compiler obeys the memoized collision bound, with both caps derived from source command/effect budgets. -/
theorem source_collision (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decisionCost : Nat) :
    𝒟[(fun result => @decide (PqxdhRecordFactsCollisionCache.Collision privateInput result.2)
      (Classical.propDecidable _)) <$>
      (simulateQ plain ((simulateQ (PqxdhRecordFactsHashSource.compiler modes replace setup codec)
        (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
          (PqxdhRecordFactsCounter.zeroCtx CtxPrivate.initial))).run ∅] {true} ≤
      ((budget.sends * (budget.sends + sharedHashTotal ⟨budget, startup, allowance, bounds, n, decisionCost⟩) : Nat) : ENNReal) /
        (2 : ENNReal)^512 := by
  apply PqxdhRecordFactsHashPairBills.ctx_collision_bound privateInput
  · rw [private_class]
    exact PqxdhRecordFactsHashPrivateBills.source_private modes replace setup codec route env serverKid bounds mode budget adversary respects
  · rw [ordinary_class]
    exact PqxdhRecordFactsHashOrdinaryBills.source_ordinary modes replace setup codec route env startup allowance framed
      serverKid bounds mode budget adversary respects decisionCost

/-- In the actual cache-erased source run the collision bound uses the source's own final combined cache, with no assumed compiler simulation or query caps. -/
theorem erased_collision (modes : Label n → KeyMode) (supported : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (startup : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startup allowance)
    (serverKid : Aeneas.Std.U64) (bounds : FreshBounds) (mode : Mode)
    (budget : Budget) (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (decisionCost : Nat) :
    𝒟[(fun result => @decide (PqxdhRecordFactsCollisionCache.Collision privateInput
      (PqxdhRecordFactsDigestCache.cacheOf result.2)) (Classical.propDecidable _)) <$>
      PqxdhRecordFactsPrivateCacheWorld.erasedRun modes replace setup codec route env serverKid bounds mode adversary] {true} ≤
      ((budget.sends * (budget.sends + sharedHashTotal ⟨budget, startup, allowance, bounds, n, decisionCost⟩) : Nat) : ENNReal) /
        (2 : ENNReal)^512 := by
  have bounded := source_collision modes replace setup codec route env startup allowance framed
    serverKid bounds mode budget adversary respects decisionCost
  rw [PqxdhRecordFactsHashSource.source_exact modes replace setup codec supported, Functor.map_map] at bounded
  exact bounded

end BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.private_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.private_class
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.ordinary_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.ordinary_class
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.source_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.source_collision
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.erased_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsHashCollision.erased_collision

import BeaconcryptCore.Computational.RawCtxSelectedMessageFreshness
import BeaconcryptCore.Computational.PqxdhInitialSourceRandom
import BeaconcryptCore.Computational.PqxdhInitialPrivateCheckedFreshness

/-!
The source final first-record lineage contains the actual selected full76 response's first32 key and its original directional input. The final later-record checker has the same local form, with its exact earlier ancestors retained. These pointwise source-event equations consume the opaque material log by its ordinary interpretation. They do not assert a whole-execution simulation or discard a known candidate that equals the selected key.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids RawCtxFreshChainCut
open RawCtxSelectedMessageFreshness
variable {S B : Nat}

/-- The first source record's exact private patch contributes its input and selected first32 key; the public KDF is untouched. -/
theorem first_lineage (prior : RawCtxSelectedParentTable.Prior) (input : RootOutput) (output : FullOutput) :
    RawCtxPublishedLineage.lineage (RawCtxSelectedParentPrivatePatch.privatePatch prior input output)
      (concreteChain input) 0 = [concreteChain input, concreteChain (material output).1] := by
  simp only [RawCtxPublishedLineage.lineage, RawCtxFiniteLineageCheck.trace, RawCtxPublishedLineage.step,
    RawCtxFunctionalFamily.execute, RawCtxSelectedParentPrivatePatch.privatePatch]
  change [concreteChain input, RawCtxFiniteLineageCheck.nativeKey
    (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse
      (if RawCtxSelectedParentPrivatePatch.targetAddress input = RawCtxSelectedParentPrivatePatch.targetAddress input then output else _))).2] = _
  rw [if_pos rfl, decoded_parts]
  rfl

/-- The actual first-record source freshness factors into retained input/ancestor checks, hidden-reveal stopping and the explicit selected-key candidate event. -/
theorem first_fresh (prior : RawCtxSelectedParentTable.Prior) (input : RootOutput) (output : FullOutput)
    (ancestors disclosed : List RatchetChain) (history : History S B) :
    RawCtxLiveLineage.Fresh
      (RawCtxPublishedLineage.lineage (RawCtxSelectedParentPrivatePatch.privatePatch prior input output)
        (concreteChain input) 0 ++ ancestors) disclosed (interpretHistory (material output).1 history) ↔
      hidden history = false ∧ RawCtxLiveLineage.FreshValues (concreteChain input :: ancestors) (known disclosed history) ∧
        concreteChain (material output).1 ∉ known disclosed history := by
  rw [first_lineage]
  have order : RawCtxLiveLineage.Fresh ([concreteChain input, concreteChain (material output).1] ++ ancestors)
      disclosed (interpretHistory (material output).1 history) ↔
      RawCtxLiveLineage.Fresh (concreteChain (material output).1 :: concreteChain input :: ancestors)
      disclosed (interpretHistory (material output).1 history) := by
    simp only [RawCtxLiveLineage.Fresh, RawCtxLiveLineage.FreshValues, List.cons_append, List.nil_append,
      List.mem_cons, or_left_comm]
  exact order.trans (fresh_factor (material output).1 (concreteChain input :: ancestors) disclosed history)

/-- The first source endpoint keeps its original publication gate and full result. A material-log interpretation suffices to expose its exact stopping and candidate conditions; no final-event equality is assumed. -/
theorem first_decision {M P I D K : Type}
    (prior : RawCtxSelectedParentTable.Prior) (input : RootOutput) (output : FullOutput)
    (selected : RawCtxProtocolReveals.Owner S B) (number : Std.U64) (position : number.val = 1)
    (ancestors disclosed : List RatchetChain)
    (result : Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) (history : History S B)
    (historyEq : result.2.1.roles.2 = interpretHistory (material output).1 history) :
    PqxdhInitialNativeParentRandom.retainedDecision
      (RawCtxSelectedParentPrivatePatch.privatePatch prior input output) input selected number ancestors disclosed result = true ↔
      PqxdhInitialPublishedEvent.Gate selected number result ∧ hidden history = false ∧
        RawCtxLiveLineage.FreshValues (concreteChain input :: ancestors) (known disclosed history) ∧
        concreteChain (material output).1 ∉ known disclosed history := by
  simp only [PqxdhInitialNativeParentRandom.retainedDecision, decide_eq_true_eq, position, Nat.sub_self]
  rw [historyEq, first_fresh]

end BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness

/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness.first_lineage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness.first_lineage
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness.first_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness.first_fresh
/-- info: 'BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness.first_decision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhSelectedMessageSourceFreshness.first_decision

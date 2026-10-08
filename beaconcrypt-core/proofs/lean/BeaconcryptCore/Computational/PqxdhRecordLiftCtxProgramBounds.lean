-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocolBounds
import BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueBounds
import BeaconcryptCore.Computational.PqxdhRecordLiftBudget

/-! Actual Protocol record syntax supplies weighted caps in the four CTX component ledgers (uniform, hash, seal, raw) for every hidden or caller-known send and receive under every typed private reply. Transport of these per-operation bills to program-level `Budget` fields is a separate step. Source-native KDF accounting remains a separate ledger. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhRecordLiftCtxProtocolBounds
variable {ι : Type} {spec : OracleSpec ι} {A B : Type} {n : Nat}

/-- The existing service CostBound, generalized only over the query signature for transport through the actual world compiler. -/
def Weighted (cost : spec.Domain → Nat) (client : OracleComp spec A) (bound : Nat) : Prop :=
  client.IsQueryBound bound (fun query available => cost query ≤ available)
    (fun query available => available - cost query)

/-- Exact additive budget composition retains every possible reply continuation. -/
theorem weighted_bind (cost : spec.Domain → Nat) (first : OracleComp spec A)
    (next : A → OracleComp spec B) (qFirst qNext : Nat)
    (bounded : Weighted cost first qFirst) (continued : ∀ reply, Weighted cost (next reply) qNext) :
    Weighted cost (first >>= next) (qFirst + qNext) :=
  isQueryBound_bind (fun left right : Nat => left + right) (by intro query left right current allowed; exact ⟨by omega, by omega⟩)
    (by intro query left right current allowed; exact ⟨by omega, by omega⟩) bounded continued

/-- A selective syntactic count gives its exact constant-weight bill, including zero-cost queries outside the selected category. -/
theorem weighted_indicator (predicate : spec.Domain → Prop) [DecidablePred predicate]
    (coefficient : Nat) (client : OracleComp spec A) (bound : Nat)
    (bounded : client.IsQueryBoundP predicate bound) :
    Weighted (fun query => if predicate query then coefficient else 0) client (coefficient * bound) := by
  apply OracleComp.IsQueryBound.proj (fun current => coefficient * current) (h := bounded)
  · intro query current allowed
    by_cases selected : predicate query
    · simp only [selected, ite_true]
      have positive : 1 ≤ current := by
        simp only [selected, not_true_eq_false, false_or] at allowed
        omega
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left coefficient positive
    · simp only [selected, ite_false, Nat.zero_le]
  · intro query current allowed
    by_cases selected : predicate query <;>
      simp only [selected, ite_true, ite_false, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.sub_zero]

/-- Larger explicit allowances preserve a weighted syntactic bound. -/
theorem weighted_mono (cost : spec.Domain → Nat) (client : OracleComp spec A)
    (bound larger : Nat) (bounded : Weighted cost client bound) (enough : bound ≤ larger) :
    Weighted cost client larger := by
  induction client using OracleComp.inductionOn generalizing bound larger with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded ⊢
      exact ⟨by omega, fun reply => ih reply _ _ (bounded.2 reply) (by omega)⟩

/-- Independent source category ledgers combine pointwise without losing any adaptive continuation. -/
theorem weighted_add (left right : spec.Domain → Nat) (client : OracleComp spec A)
    (qLeft qRight : Nat) (leftBound : Weighted left client qLeft)
    (rightBound : Weighted right client qRight) :
    Weighted (fun query => left query + right query) client (qLeft + qRight) := by
  induction client using OracleComp.inductionOn generalizing qLeft qRight with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at leftBound rightBound ⊢
      refine ⟨by omega, fun reply => ?_⟩
      exact weighted_mono _ _ _ _ (ih reply _ _ (leftBound.2 reply) (rightBound.2 reply)) (by omega)

/-- Literal query replacement transports its proved weighted cost through every typed continuation. -/
theorem weighted_simulate {κ : Type} {target : OracleSpec κ}
    (sourceCost : spec.Domain → Nat) (targetCost : target.Domain → Nat)
    (impl : QueryImpl spec (OracleComp target)) (client : OracleComp spec A) (bound : Nat)
    (bounded : Weighted sourceCost client bound)
    (step : ∀ query, Weighted targetCost (impl query) (sourceCost query)) :
    Weighted targetCost (simulateQ impl client) bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure result => trivial
  | query_bind query next ih =>
      rw [Weighted, isQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact weighted_mono _ _ _ _ (weighted_bind targetCost (impl query) _ _ _ (step query)
        (fun reply => ih reply _ (bounded.2 reply))) (by omega)

/-- Stateful source simulation keeps the complete control state and all reply branches. -/
theorem weighted_run {κ : Type} {target : OracleSpec κ} {State : Type}
    (sourceCost : spec.Domain → Nat) (targetCost : target.Domain → Nat)
    (impl : QueryImpl spec (StateT State (OracleComp target)))
    (client : OracleComp spec A) (bound : Nat) (state : State)
    (bounded : Weighted sourceCost client bound)
    (step : ∀ query state, Weighted targetCost ((impl query).run state) (sourceCost query)) :
    Weighted targetCost ((simulateQ impl client).run state) bound := by
  exact bounded.simulateQ_run_of_step
    (combine := fun left right : Nat => left + right) (mapBudget := id)
    (stepBudget := fun query _ => sourceCost query)
    (fun first rest => weighted_bind targetCost _ _ _ _ first rest)
    (fun query _ current _ => step query current)
    (fun query budget allowed => by dsimp; omega) state

open Classical
open PqxdhRecordLiftBudget

def localCost (lookup opening sealing : Nat) : (LocalSpec n).Domain → Nat
  | .inl _ => lookup
  | .inr (.inl _) => opening
  | .inr (.inr _) => sealing

/-- All three opaque local categories are charged together; their arbitrary reply bounds need no source reachability premise. -/
theorem local_weighted (client : OracleComp (LocalSpec n) A)
    (lookup opening sealing qLookup qOpening qSealing : Nat)
    (lookupBound : client.IsQueryBoundP PqxdhRecordLiftOpaqueBounds.IsLookup qLookup)
    (openingBound : client.IsQueryBoundP PqxdhRecordLiftOpaqueBounds.IsOpening qOpening)
    (sealingBound : client.IsQueryBoundP PqxdhRecordLiftOpaqueBounds.IsSealing qSealing) :
    Weighted (localCost lookup opening sealing) client
      (lookup * qLookup + opening * qOpening + sealing * qSealing) := by
  have combined := weighted_add _ _ client _ _
    (weighted_add _ _ client _ _ (weighted_indicator _ lookup _ _ lookupBound)
      (weighted_indicator _ opening _ _ openingBound))
    (weighted_indicator _ sealing _ _ sealingBound)
  convert combined using 1
  funext query
  rcases query with coordinate | pending
  · simp [localCost, PqxdhRecordLiftOpaqueBounds.IsLookup,
      PqxdhRecordLiftOpaqueBounds.IsOpening, PqxdhRecordLiftOpaqueBounds.IsSealing]
  · rcases pending with pending | pending <;>
      simp [localCost, PqxdhRecordLiftOpaqueBounds.IsLookup,
        PqxdhRecordLiftOpaqueBounds.IsOpening, PqxdhRecordLiftOpaqueBounds.IsSealing]

def lookupCost : BudgetKind → Nat | .uniform => 76 | _ => 0
def openingCost : BudgetKind → Nat | .hash | .raw => 1 | _ => 0
def sealingCost : BudgetKind → Nat | .hash | .seal => 1 | _ => 0

/-- The bill of one record send or receive in one CTX component ledger. Named apart from the opened `PqxdhRecordLiftBudget.recordCost`, which counts records per full-interface command. -/
def operationBill (kind : BudgetKind) : RecordKind → Nat
  | .send => lookupCost kind + sealingCost kind
  | .raw => 51 * lookupCost kind + openingCost kind

/-- The literal local inclusion exposes precisely the existing service-category charges. -/
theorem local_lift (kind : BudgetKind) (query : (LocalSpec n).Domain) :
    Weighted (categoryCost kind) (localLift query)
      (localCost (lookupCost kind) (openingCost kind) (sealingCost kind) query) := by
  rcases query with coordinate | pending
  · cases kind <;> simp [Weighted, localLift, localCost, categoryCost, lookupCost]
  · rcases pending with pending | pending <;> cases kind <;>
      simp [Weighted, localLift, localCost, categoryCost, openingCost, sealingCost]

/-- Full local send syntax costs one derivation and at most one sealing attempt. -/
theorem opaque_send (kind : BudgetKind) (kernel : PqxdhRecordLiftWorldCompiler.LabeledKernel n)
    (context : RawCtxSourceSend.SealContext) :
    Weighted (categoryCost kind)
      (simulateQ localLift (PqxdhRecordLiftOpaqueDrivers.admittedSend kernel context))
      (operationBill kind .send) := by
  apply weighted_simulate _ _ _ _ _
  · simpa [operationBill] using local_weighted
      (PqxdhRecordLiftOpaqueDrivers.admittedSend kernel context)
      (lookupCost kind) (openingCost kind) (sealingCost kind) 1 0 1
      (PqxdhRecordLiftOpaqueBounds.admitted_send_lookup kernel context)
      (PqxdhRecordLiftOpaqueBounds.admitted_send_opening kernel context)
      (PqxdhRecordLiftOpaqueBounds.admitted_send_sealing kernel context)
  · exact local_lift kind

/-- Full local receive syntax costs at most 51 derivations and one opening attempt, including cached, future, rejected and failed-opening paths. -/
theorem opaque_receive (kind : BudgetKind) (kernel : PqxdhRecordLiftWorldCompiler.LabeledKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Weighted (categoryCost kind)
      (simulateQ localLift (PqxdhRecordLiftOpaqueDrivers.admittedReceive kernel target context))
      (operationBill kind .raw) := by
  apply weighted_simulate _ _ _ _ _
  · have bounded := local_weighted
      (PqxdhRecordLiftOpaqueDrivers.admittedReceive kernel target context)
      (lookupCost kind) (openingCost kind) (sealingCost kind) 51 1 0
      (PqxdhRecordLiftOpaqueBounds.admitted_receive_lookup kernel target context)
      (PqxdhRecordLiftOpaqueBounds.admitted_receive_opening kernel target context)
      (PqxdhRecordLiftOpaqueBounds.admitted_receive_sealing kernel target context)
    exact weighted_mono _ _ _ _ bounded (by simp only [operationBill]; omega)
  · exact local_lift kind

/-- Every hidden or caller-known send, including exhaustion and writer failure, stays within the per-send category bill. -/
theorem kernel_send (kind : BudgetKind) (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n)
    (context : RawCtxSourceSend.SealContext) :
    Weighted (categoryCost kind) (kernelSend stored context) (operationBill kind .send) := by
  cases stored with
  | known kernel =>
      cases kind <;> simp [Weighted, kernelSend, categoryCost, operationBill, lookupCost, sealingCost]
  | hidden slot kernel =>
      simpa only [kernelSend, Nat.add_zero] using weighted_bind (categoryCost kind) _
        (fun result => pure (PqxdhRecordLiftWorldCompiler.StoredKernel.hidden slot result.1, result.2))
        _ 0 (opaque_send kind kernel context) (fun _ => trivial)

/-- Every hidden or caller-known receive, including cached, future, rejected and failed-opening paths, stays within the per-receive category bill. -/
theorem kernel_receive (kind : BudgetKind) (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    Weighted (categoryCost kind) (kernelReceive stored target context) (operationBill kind .raw) := by
  cases stored with
  | known kernel =>
      cases kind <;> simp [Weighted, kernelReceive, categoryCost, operationBill, lookupCost, openingCost]
  | hidden slot kernel =>
      simpa only [kernelReceive, Nat.add_zero] using weighted_bind (categoryCost kind) _
        (fun result => pure (PqxdhRecordLiftWorldCompiler.StoredKernel.hidden slot result.1, result.2))
        _ 0 (opaque_receive kind kernel target context) (fun _ => trivial)

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_indicator' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_indicator

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_add

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_simulate' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_simulate

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.weighted_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.local_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.local_weighted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.local_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.local_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.opaque_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.opaque_send

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.opaque_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.opaque_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.kernel_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.kernel_send

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.kernel_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProgramBounds.kernel_receive

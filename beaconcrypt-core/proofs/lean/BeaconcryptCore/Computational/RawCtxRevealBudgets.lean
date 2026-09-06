import BeaconcryptCore.Computational.RawCtxProtocolReveals

/-!
Ten statements account for actual replicated record/public operations interleaved with arbitrary current-chain and skipped-material compromise reads. Six structural budgets count sends S, raw attempts R, caller coins U, public commitments H, real public HKDF projections K and all reveal attempts E. Every possible reply continuation spends the original coordinate, including repeated reveals, missing-owner rejection and failed records.

The same full-state source interpreter retains native KDF/seal/open/hash/writer caps S+51R, S, R, S+R+H and S, and complete uniform cap U+64(S+R+H). Each reveal adds zero cryptographic oracle requests, while all E reads and S+R+U+H+K+E total source operations remain explicitly bounded. Actual lookup, copying, byte processing, logging and deterministic primitive work are not zero computation. The supported history bound in RawCtxProtocolReveals can use that complete source cap.

These resource statements add no target freshness, record-key independence or security premise. They preserve the supplied initial role/primitive correlations and do not charge absent allocation, registration, identity/KEM/root reveals, snapshot restoration or network declassification as free work. Their costs and cryptographic simulations must be connected in the enclosing experiment.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxRevealBudgets
open RawCtxProtocolReveals RawCtxServerServiceBounds

abbrev Budget := RawCtxServerServiceBounds.Budget × Nat

def permitted {serverCount beaconCount : Nat} : (SourceSpec serverCount beaconCount).Domain → Budget → Prop
  | .inl request, budget => 0 < budget.1 (RawCtxProtocolBudgets.sourceKind request)
  | .inr _, budget => 0 < budget.2

def remaining {serverCount beaconCount : Nat} : (SourceSpec serverCount beaconCount).Domain → Budget → Budget
  | .inl request, budget => (RawCtxServerServiceBounds.remaining (RawCtxProtocolBudgets.sourceKind request) budget.1, budget.2)
  | .inr _, budget => (budget.1, budget.2 - 1)

def Bounded {serverCount beaconCount : Nat} {Result : Type}
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget) : Prop :=
  IsQueryBound client budget permitted remaining

def weight {serverCount beaconCount : Nat} (base : Kind → Nat) (revealCost : Nat) :
    (SourceSpec serverCount beaconCount).Domain → Nat
  | .inl request => base (RawCtxProtocolBudgets.sourceKind request)
  | .inr _ => revealCost

def bill (base : Kind → Nat) (revealCost : Nat) (budget : Budget) : Nat :=
  RawCtxServerServiceBounds.bill base budget.1 + revealCost * budget.2

/-- An admitted source request consumes exactly its own weighted budget coordinate. -/
theorem bill_step {serverCount beaconCount : Nat} (base : Kind → Nat) (revealCost : Nat)
    (query : (SourceSpec serverCount beaconCount).Domain) (budget : Budget)
    (positive : permitted query budget) :
    weight base revealCost query + bill base revealCost (remaining query budget) = bill base revealCost budget := by
  cases query with
  | inl request =>
      simpa only [weight, bill, remaining, Nat.add_assoc] using
        congrArg (fun value => value + revealCost * budget.2)
          (RawCtxServerServiceBounds.bill_step base budget.1 (RawCtxProtocolBudgets.sourceKind request) positive)
  | inr request =>
      have count : budget.2 - 1 + 1 = budget.2 := Nat.sub_add_cancel positive
      simpa only [weight, bill, remaining, Nat.mul_add, Nat.mul_one, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using
        congrArg (fun value => RawCtxServerServiceBounds.bill base budget.1 + revealCost * value) count

/-- Full-state adaptive interpretation composes the exact per-query costs. -/
theorem weighted_bound {serverCount beaconCount : Nat} {Result PrivateState ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT PrivateState (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (cost : Kind → Nat) (revealCost : Nat)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget)
    (step : ∀ query state, ((impl query).run state).IsQueryBoundP predicate (weight cost revealCost query))
    (state : PrivateState) :
    ((simulateQ impl client).run state).IsQueryBoundP predicate (bill cost revealCost budget) := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := bill cost revealCost)
    (stepBudget := fun query _ => weight cost revealCost query)
    (fun first rest => isQueryBoundP_bind first (fun value _ => rest value))
    (fun query _ state _ => step query state)
    (fun query budget positive => bill_step cost revealCost query budget positive) state

/-- Real record/public steps retain their native caps; compromise reads issue no native crypto requests. -/
theorem backend_step {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (selected : RawCtxMixedOwner.CallKind) :
    ((protocolImpl serverCount beaconCount senderId route decode query).run state).IsQueryBoundP
      (nativePredicate selected) (weight (callWeight selected) 0 query) := by
  cases query with
  | inl request =>
      simpa only [protocolImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, weight] using
        RawCtxProtocolBudgets.backend_step serverCount beaconCount senderId route decode request state.1 selected
  | inr request => trivial

/-- Real source steps preserve their uniform cap; compromise reads make no new uniform requests. -/
theorem source_uniform_step {Metadata PeerMetadata Identity DhPair KemPair Auxiliary : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((sourceImpl source writer serverCount beaconCount senderId route decode query).run state).IsTotalQueryBound
      (weight (uniformWeight 0) 0 query) := by
  cases query with
  | inl request =>
      simpa only [sourceImpl, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, weight] using
        RawCtxProtocolUniform.source_step source writer serverCount beaconCount senderId route decode request
          (state.1.1, state.2)
  | inr request => trivial

/-- Both role families, public services and all reveals retain the same complete uniform ledger. -/
theorem schedule_uniform {Metadata PeerMetadata Identity DhPair KemPair Auxiliary Result : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount ×
      RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (sourceImpl source writer serverCount beaconCount senderId route decode) client).run state).IsTotalQueryBound
      (budget.1 .coin + 64 * (budget.1 .send + budget.1 .raw + budget.1 .hash)) := by
  have bound := weighted_bound
    (sourceImpl source writer serverCount beaconCount senderId route decode)
    (fun _ => True) (uniformWeight 0) 0 client budget bounded
    (fun query state => (source_uniform_step source writer serverCount beaconCount senderId route decode query state).isQueryBoundP)
    state
  simpa only [bill, uniform_bill, Nat.zero_mul, Nat.add_zero, IsTotalQueryBound, IsQueryBoundP,
    not_true_eq_false, false_or, if_true] using bound

/-- All adaptive compromise continuations retain the five explicit native resource caps. -/
theorem backend_bound {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (selected : RawCtxMixedOwner.CallKind) :
    ((simulateQ (protocolImpl serverCount beaconCount senderId route decode) client).run state).IsQueryBoundP
      (nativePredicate selected) (RawCtxMixedOwner.sendCost selected * budget.1 .send +
        RawCtxMixedOwner.receiveCost selected * budget.1 .raw +
        (if selected = .hash then budget.1 .hash else 0)) := by
  simpa only [bill, native_bill, Nat.zero_mul, Nat.add_zero] using weighted_bound
    (protocolImpl serverCount beaconCount senderId route decode) (nativePredicate selected) (callWeight selected) 0
    client budget bounded
    (fun query state => backend_step serverCount beaconCount senderId route decode query state selected) state

/-- Every reveal attempt consumes the explicit reveal budget, including repetition and rejection. -/
theorem reveal_bound {serverCount beaconCount : Nat} {Result : Type}
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget) :
    client.IsQueryBoundP (fun query => query.isRight = true) budget.2 := by
  refine IsQueryBound.proj Prod.snd ?_ ?_ bounded
  all_goals intro query current positive
  all_goals cases query <;> simp_all [permitted, remaining]

def serviceKind {serverCount beaconCount : Nat} : (SourceSpec serverCount beaconCount).Domain → Option Kind
  | .inl request => some (RawCtxProtocolBudgets.sourceKind request)
  | .inr _ => none

/-- Each original service retains its selective source budget under adaptive reveals. -/
theorem source_bound {serverCount beaconCount : Nat} {Result : Type}
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget) (selected : Kind) :
    client.IsQueryBoundP (fun query => serviceKind query = some selected) (budget.1 selected) := by
  refine IsQueryBound.proj (fun current : Budget => current.1 selected) ?_ ?_ bounded
  all_goals intro query current positive
  all_goals cases query with
    | inr request => simp [serviceKind, remaining]
    | inl request =>
        by_cases equal : RawCtxProtocolBudgets.sourceKind request = selected <;>
          simp_all [serviceKind, permitted, remaining, RawCtxServerServiceBounds.remaining,
            Function.update_of_ne, Ne.symm]

/-- All source operations, including reads, are covered by the sum of the six budgets. -/
theorem total_bound {serverCount beaconCount : Nat} {Result : Type}
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget) :
    client.IsTotalQueryBound (bill (fun _ => 1) 1 budget) := by
  refine IsQueryBound.proj (bill (fun _ => 1) 1) ?_ ?_ bounded
  all_goals intro query current positive
  all_goals have exactBill := bill_step (fun _ => 1) 1 query current positive
  all_goals cases query <;> simp only [weight] at exactBill <;> omega

/-- The total operation ledger is exactly S+R+U+H+K+E. -/
theorem total_bill (budget : Budget) :
    bill (fun _ => 1) 1 budget = budget.1 .send + budget.1 .raw + budget.1 .coin +
      budget.1 .hash + budget.1 .hkdf + budget.2 := by
  have enumeration : (Finset.univ : Finset Kind) = {.send, .raw, .coin, .hash, .hkdf} := by decide
  simp [bill, RawCtxServerServiceBounds.bill, enumeration, Nat.add_assoc]

end BeaconcryptCore.Computational.RawCtxRevealBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.bill_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.bill_step

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.weighted_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.backend_step

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.source_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.source_uniform_step

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.schedule_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.backend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.backend_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.reveal_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.reveal_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.source_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.total_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.total_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxRevealBudgets.total_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxRevealBudgets.total_bill

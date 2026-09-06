import BeaconcryptCore.Computational.RawCtxProtocolRoles

/-!
Five aggregate source budgets count sends, raw receives, caller uniform requests, public commitment requests and real public HKDF evaluations across both indexed role families. Five checked statements project each source cap and compose the actual native per-step bounds through every possible reply continuation and the entire shared state. The resulting KDF/seal/open/hash/writer caps are S+51R, S, R, S+R+H and S.

These are source-operation bounds, with no operational instance-selection factor. They do not remove cryptographic target/session selection losses or pay for earlier role generation, registration, reveals or other absent interfaces. Rejected and repeated requests count; real public HKDF evaluations have their own K cap. Input lengths, fixed primitive evaluations, parsing, copies, map access and supplied local computation retain their actual work.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxProtocolBudgets
open RawCtxRoleFamily RawCtxProtocolRoles RawCtxServerServiceBounds

/-- Both role families contribute to the same five actual operation counts. -/
def sourceKind {serverCount beaconCount : Nat} : (SourceSpec serverCount beaconCount).Domain → Kind
  | .inl ⟨_, .inl _⟩ | .inr (.inl ⟨_, .inl _⟩) => .send
  | .inl ⟨_, .inr _⟩ | .inr (.inl ⟨_, .inr _⟩) => .raw
  | .inr (.inr (.inl _)) => .coin
  | .inr (.inr (.inr (.inl _))) => .hash
  | .inr (.inr (.inr (.inr _))) => .hkdf

def Bounded {serverCount beaconCount : Nat} {Result : Type}
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget) : Prop :=
  IsQueryBound client budget (fun query budget => 0 < budget (sourceKind query))
    (fun query budget => remaining (sourceKind query) budget)

/-- Shared native calls count every attempted operation across every selected Server and Beacon. -/
theorem backend_step {Metadata PeerMetadata Identity DhPair KemPair : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (SourceSpec serverCount beaconCount).Domain)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (selected : RawCtxMixedOwner.CallKind) :
    ((protocolImpl serverCount beaconCount senderId route decode query).run state).IsQueryBoundP
      (nativePredicate selected) (callWeight selected (sourceKind query)) := by
  rcases query with ⟨index, send | raw⟩ | (⟨index, send | raw⟩ | (coin | (bytes | hkdf)))
  all_goals simp only [protocolImpl, familyImpl, StateT.run, bind_pure_comp, simulateQ_map,
    isQueryBoundP_map_iff, sourceKind, callWeight]
  case inl.inl =>
    exact nativeLift_bound selected _ _ (RawCtxServerMixed.send_bound senderId send.1 send.2 (state.1 index) selected)
  case inl.inr =>
    exact nativeLift_bound selected _ _ (RawCtxServerMixed.raw_bound route decode raw (state.1 index) selected)
  case inr.inl.inl =>
    exact nativeLift_bound selected _ _ (RawCtxBeaconLifecycle.step_bound decode (.inl send) (state.2 index) selected)
  case inr.inl.inr =>
    exact nativeLift_bound selected _ _ (RawCtxBeaconLifecycle.step_bound decode (.inr raw) (state.2 index) selected)
  case inr.inr.inl =>
    exact (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
      (p := nativePredicate selected) (.inl coin) 0).2 (fun contradiction => contradiction.elim)
  case inr.inr.inr.inl =>
    apply (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
      (p := nativePredicate selected) (.inr (.inl (.inr (.inr (.inr (.inl bytes)))))) _).2
    simp only [nativePredicate, RawCtxMixedOwner.callKind, eq_comm]
    exact fun equal => by simp [equal]
  case inr.inr.inr.inr =>
    exact (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
      (p := nativePredicate selected) (.inr (.inr hkdf)) 0).2 (fun contradiction => contradiction.elim)

/-- Per-step resource bounds compose through every adaptive continuation and the entire private protocol state. -/
theorem weighted_bound {serverCount beaconCount : Nat} {Result PrivateState ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl (SourceSpec serverCount beaconCount) (StateT PrivateState (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (weight : Kind → Nat)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget)
    (step : ∀ query state, ((impl query).run state).IsQueryBoundP predicate (weight (sourceKind query)))
    (state : PrivateState) :
    ((simulateQ impl client).run state).IsQueryBoundP predicate (bill weight budget) := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := bill weight)
    (stepBudget := fun query _ => weight (sourceKind query))
    (fun first rest => isQueryBoundP_bind first (fun value _ => rest value))
    (fun query _ state _ => step query state)
    (fun query budget positive => bill_step weight budget (sourceKind query) positive) state

/-- The global native ledger counts selected-role work and all public commitment attempts, with no operational instance-selection factor. -/
theorem backend_bound {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount)
    (selected : RawCtxMixedOwner.CallKind) :
    ((simulateQ (protocolImpl serverCount beaconCount senderId route decode) client).run state).IsQueryBoundP
      (nativePredicate selected) (RawCtxMixedOwner.sendCost selected * budget .send +
        RawCtxMixedOwner.receiveCost selected * budget .raw +
        (if selected = .hash then budget .hash else 0)) := by
  simpa only [native_bill] using weighted_bound
    (protocolImpl serverCount beaconCount senderId route decode) (nativePredicate selected) (callWeight selected)
    client budget bounded
    (fun query state => backend_step serverCount beaconCount senderId route decode query state selected) state

/-- Five explicit native caps cover both protocol roles and every public commitment request. -/
theorem backend_bounds {Metadata PeerMetadata Identity DhPair KemPair Result : Type}
    (serverCount beaconCount : Nat) (senderId : Metadata → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget)
    (state : State Metadata PeerMetadata Identity DhPair KemPair serverCount beaconCount) :
    let program := (simulateQ (protocolImpl serverCount beaconCount senderId route decode) client).run state
    program.IsQueryBoundP (nativePredicate .kdf) (budget .send + 51 * budget .raw) ∧
      program.IsQueryBoundP (nativePredicate .sealing) (budget .send) ∧
      program.IsQueryBoundP (nativePredicate .opening) (budget .raw) ∧
      program.IsQueryBoundP (nativePredicate .hash) (budget .send + budget .raw + budget .hash) ∧
      program.IsQueryBoundP (nativePredicate .writer) (budget .send) := by
  simpa only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost, Nat.one_mul, Nat.zero_mul,
    Nat.add_zero, Nat.zero_add, reduceCtorEq, ↓reduceIte] using
    And.intro (backend_bound serverCount beaconCount senderId route decode client budget bounded state .kdf)
      (And.intro (backend_bound serverCount beaconCount senderId route decode client budget bounded state .sealing)
        (And.intro (backend_bound serverCount beaconCount senderId route decode client budget bounded state .opening)
          (And.intro (backend_bound serverCount beaconCount senderId route decode client budget bounded state .hash)
            (backend_bound serverCount beaconCount senderId route decode client budget bounded state .writer))))

/-- Each aggregate source coordinate is an ordinary selective query cap, including real public HKDF evaluations. -/
theorem source_bound {serverCount beaconCount : Nat} {Result : Type}
    (client : OracleComp (SourceSpec serverCount beaconCount) Result) (budget : Budget)
    (bounded : Bounded client budget) (selected : Kind) :
    client.IsQueryBoundP (fun query => sourceKind query = selected) (budget selected) := by
  refine IsQueryBound.proj (fun current : Budget => current selected) ?_ ?_ bounded
  all_goals intro query current positive
  all_goals by_cases equal : sourceKind query = selected <;> simp_all [remaining, Function.update_of_ne, Ne.symm]

end BeaconcryptCore.Computational.RawCtxProtocolBudgets

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBudgets.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBudgets.backend_step

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBudgets.weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBudgets.weighted_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBudgets.backend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBudgets.backend_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBudgets.backend_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBudgets.backend_bounds

/-- info: 'BeaconcryptCore.Computational.RawCtxProtocolBudgets.source_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxProtocolBudgets.source_bound

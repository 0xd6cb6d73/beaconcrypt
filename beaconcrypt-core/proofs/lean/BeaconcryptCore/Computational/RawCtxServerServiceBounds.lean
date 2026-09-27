import BeaconcryptCore.Computational.RawCtxServerServices
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Five structural source budgets count sends, raw receives, caller coins, public commitment queries and public fixed-HKDF projections under every possible reply continuation. Eleven checked statements project ordinary selective source caps, compose exact per-step weighted costs and derive the full native and uniform ledgers in the same adaptive Server/public experiment.

Zero uniform cost for deterministic public HKDF, functional AEAD or writing does not mean zero primitive/local work. Native KDF callbacks, public HKDF evaluations, seal/open, hash and writer calls remain separately counted, with byte processing, parsing, copying and map/runtime work outside these oracle-call bounds. These resource statements do not prove cryptographic independence, freshness or global security.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxServerServiceBounds

inductive Kind where
  | send | raw | coin | hash | hkdf
  deriving DecidableEq

instance : Fintype Kind :=
  Fintype.ofList [.send, .raw, .coin, .hash, .hkdf] (by intro kind; cases kind <;> simp)

abbrev Budget := Kind → Nat

def remaining (kind : Kind) (budget : Budget) : Budget :=
  Function.update budget kind (budget kind - 1)

def bill (weight : Kind → Nat) (budget : Budget) : Nat :=
  ∑ kind, weight kind * budget kind

/-- A counted operation consumes exactly its own weighted budget coordinate. -/
theorem bill_step (weight : Kind → Nat) (budget : Budget) (kind : Kind)
    (positive : 0 < budget kind) :
    weight kind + bill weight (remaining kind budget) = bill weight budget := by
  simp only [bill, remaining, Function.apply_update (fun k n => weight k * n) budget kind (budget kind - 1), Finset.sum_update_of_mem (Finset.mem_univ kind)]
  have split : (∑ k, weight k * budget k) = weight kind * budget kind +
      ∑ k ∈ Finset.univ \ {kind}, weight k * budget k := by
    simpa only [Function.update_eq_self] using Finset.sum_update_of_mem
      (Finset.mem_univ kind) (fun k => weight k * budget k) (weight kind * budget kind)
  rw [split, ← Nat.add_assoc, Nat.add_comm (weight kind), ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel positive]

def sourceKind : RawCtxServerServices.SourceSpec.Domain → Kind
  | .inl (.inl _) => .send
  | .inl (.inr _) => .raw
  | .inr (.inl _) => .coin
  | .inr (.inr (.inl _)) => .hash
  | .inr (.inr (.inr _)) => .hkdf

/-- Five structural caps count every original request, including rejected requests and deterministic public HKDF work. -/
def Bounded {Result : Type} (client : OracleComp RawCtxServerServices.SourceSpec Result)
    (budget : Budget) : Prop :=
  IsQueryBound client budget (fun query budget => 0 < budget (sourceKind query))
    (fun query budget => remaining (sourceKind query) budget)

/-- The resource composition retains every possible reply continuation and the full interpreted state. -/
theorem weighted_bound {Result State ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxServerServices.SourceSpec (StateT State (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (weight : Kind → Nat)
    (client : OracleComp RawCtxServerServices.SourceSpec Result) (budget : Budget)
    (bounded : Bounded client budget)
    (step : ∀ query state, ((impl query).run state).IsQueryBoundP predicate (weight (sourceKind query)))
    (state : State) :
    ((simulateQ impl client).run state).IsQueryBoundP predicate (bill weight budget) := by
  exact bounded.simulateQ_run_of_step (combine := Nat.add) (mapBudget := bill weight)
    (stepBudget := fun query _ => weight (sourceKind query))
    (fun first rest => isQueryBoundP_bind first (fun value _ => rest value))
    (fun query _ state _ => step query state)
    (fun query budget positive => bill_step weight budget (sourceKind query) positive) state

/-- Each coordinate is an ordinary selective source-query bound, including public HKDF calls. -/
theorem source_bound {Result : Type}
    (client : OracleComp RawCtxServerServices.SourceSpec Result) (budget : Budget)
    (bounded : Bounded client budget) (selected : Kind) :
    client.IsQueryBoundP (fun query => sourceKind query = selected) (budget selected) := by
  refine IsQueryBound.proj (fun current : Budget => current selected) ?_ ?_ bounded
  all_goals intro query current positive
  all_goals by_cases equal : sourceKind query = selected <;> simp_all [remaining, Function.update_of_ne, Ne.symm]

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RawCtxServerRouting PqxdhJointKdfGame

def uniformWeight (kdfCoins : Nat) : Kind → Nat
  | .send => kdfCoins + 64
  | .raw => kdfCoins * 51 + 64
  | .coin => 1
  | .hash => 64
  | .hkdf => 0

/-- Every source or public request pays its actual complete uniform-oracle cost, including failed receive work. -/
theorem source_uniform_step {Metadata PeerMetadata Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (kdfCoins : Nat)
    (bounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerServices.SourceSpec.Domain)
    (state : State Metadata PeerMetadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    (((RawCtxServerServices.sourceImpl source writer kdf senderId route decode) query).run state).IsTotalQueryBound
      (uniformWeight kdfCoins (sourceKind query)) := by
  rcases query with (⟨plaintext, kid⟩ | raw) | (coin | (bytes | query))
  all_goals simp only [RawCtxServerServices.sourceImpl, RawCtxServerMixed.sourceImpl, StateT.run, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, sourceKind, uniformWeight]
  case inl.inl =>
    dsimp only [RawCtxServerServices.SourceSpec, RawCtxServerMixed.SourceSpec, RawCtxServerSend.ApplicationSpec, RawCtxWholeOwner.RawSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim, OracleSpec.ofFn]
    have interpreted := RawCtxServerMixed.send_interpretation
      (RawCtxMixedShared.sharedImpl source.crypto writer kdf)
      senderId plaintext kid state.1 state.2
    have stepBound : ((simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer kdf)
        (RawCtxServerMixed.sendServer senderId plaintext kid state.1)).run state.2).IsTotalQueryBound
        (kdfCoins + 64) := by
      simpa only [Nat.mul_one] using RawCtxMixedShared.shared_uniform source.crypto writer kdf
        kdfCoins bounded (RawCtxServerMixed.sendServer senderId plaintext kid state.1) 1 1
        (RawCtxServerMixed.send_bound senderId plaintext kid state.1 .kdf)
        (RawCtxServerMixed.send_bound senderId plaintext kid state.1 .hash) state.2
    exact interpreted ▸ stepBound
  case inl.inr =>
    dsimp only [RawCtxServerServices.SourceSpec, RawCtxServerMixed.SourceSpec, RawCtxServerSend.ApplicationSpec, RawCtxWholeOwner.RawSpec, OracleSpec.Range, OracleSpec.add_def, Sum.elim, OracleSpec.ofFn]
    have interpreted := RawCtxServerMixed.raw_interpretation
      (RawCtxMixedShared.sharedImpl source.crypto writer kdf)
      route decode raw state.1 state.2
    have stepBound : ((simulateQ (RawCtxMixedShared.sharedImpl source.crypto writer kdf)
        (RawCtxServerMixed.rawServer route decode raw state.1)).run state.2).IsTotalQueryBound
        (kdfCoins * 51 + 64) := by
      simpa only [Nat.mul_one] using RawCtxMixedShared.shared_uniform source.crypto writer kdf
        kdfCoins bounded (RawCtxServerMixed.rawServer route decode raw state.1) 51 1
        (RawCtxServerMixed.raw_bound route decode raw state.1 .kdf)
        (RawCtxServerMixed.raw_bound route decode raw state.1 .hash) state.2
    exact interpreted ▸ stepBound
  case inr.inl =>
    simp [QueryImpl.compose, RawCtxServerServices.publicLift, RawCtxServerServices.backendImpl, OracleSpec.query]
    exact (isQueryBound_query_iff (spec := unifSpec) coin 1 _ _).2 (by decide)
  case inr.inr.inl =>
    change IsTotalQueryBound (((RawCtxServerServices.backendImpl source writer kdf ∘ₛ
      RawCtxServerServices.publicLift) (.inr (.inl bytes))).run state.2) 64
    rw [RawCtxServerServices.public_hash, bind_pure_comp]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.2.2
  case inr.inr.inr => simp [QueryImpl.compose, RawCtxServerServices.publicLift, RawCtxServerServices.backendImpl, OracleSpec.query]

/-- The five request classes expand to the complete public/source uniform ledger. -/
theorem uniform_bill (kdfCoins : Nat) (budget : Budget) :
    bill (uniformWeight kdfCoins) budget = budget .coin +
      kdfCoins * (budget .send + 51 * budget .raw) +
      64 * (budget .send + budget .raw + budget .hash) := by
  have enumeration : (Finset.univ : Finset Kind) = {.send, .raw, .coin, .hash, .hkdf} := by decide
  simp [bill, enumeration, uniformWeight]
  ring

/-- The whole adaptive source/public schedule counts caller coins, every source KDF and all private/public commitment misses. -/
theorem schedule_uniform {Metadata PeerMetadata Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (kdfCoins : Nat)
    (kdfBounded : ∀ request state, ((kdf request).run state).IsTotalQueryBound kdfCoins)
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerServices.SourceSpec Result) (budget : Budget)
    (bounded : Bounded client budget)
    (state : State Metadata PeerMetadata × RawCtxSharedPrimitive.SharedState Auxiliary) :
    ((simulateQ (RawCtxServerServices.sourceImpl source writer kdf senderId route decode) client).run state).IsTotalQueryBound
      (budget .coin + kdfCoins * (budget .send + 51 * budget .raw) +
        64 * (budget .send + budget .raw + budget .hash)) := by
  have bound := weighted_bound (RawCtxServerServices.sourceImpl source writer kdf senderId route decode)
    (fun _ => True) (uniformWeight kdfCoins) client budget bounded
    (fun query state => (source_uniform_step source writer kdf kdfCoins kdfBounded
      senderId route decode query state).isQueryBoundP) state
  simpa only [uniform_bill, IsTotalQueryBound, IsQueryBoundP, not_true_eq_false, false_or, if_true] using bound

def nativePredicate (selected : RawCtxMixedOwner.CallKind) : RawCtxServerServices.BackendSpec.Domain → Prop
  | .inl _ => False
  | .inr (.inl query) => RawCtxMixedOwner.callKind query = selected
  | .inr (.inr _) => False

instance (selected : RawCtxMixedOwner.CallKind) : DecidablePred (nativePredicate selected) :=
  fun query => match query with
  | .inl _ => isFalse id
  | .inr (.inl query) => inferInstanceAs (Decidable (RawCtxMixedOwner.callKind query = selected))
  | .inr (.inr _) => isFalse id

/-- Lifting native requests retains every counted class without a key/peer split or additional query. -/
theorem nativeLift_bound {Result : Type} (selected : RawCtxMixedOwner.CallKind)
    (program : OracleComp RawCtxMixedOwner.NativeSpec Result) (cap : Nat)
    (bounded : program.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = selected) cap) :
    (simulateQ RawCtxServerServices.nativeLift program).IsQueryBoundP (nativePredicate selected) cap := by
  apply RawCtxSourceOpen.simulate_bound RawCtxServerServices.nativeLift _ _ program cap bounded
  intro query
  apply (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec) (p := nativePredicate selected) _ _).2
  simp only [nativePredicate]
  intro equal
  simp only [equal, ↓reduceIte, Nat.zero_lt_succ]

def callWeight (selected : RawCtxMixedOwner.CallKind) : Kind → Nat
  | .send => RawCtxMixedOwner.sendCost selected
  | .raw => RawCtxMixedOwner.receiveCost selected
  | .hash => if selected = .hash then 1 else 0
  | .coin | .hkdf => 0

/-- The source/public step counts actual native calls; public hashes join the private hash count. -/
theorem backend_step {Metadata PeerMetadata : Type}
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxServerServices.SourceSpec.Domain) (state : State Metadata PeerMetadata)
    (selected : RawCtxMixedOwner.CallKind) :
    (((RawCtxServerServices.serverImpl senderId route decode) query).run state).IsQueryBoundP
      (nativePredicate selected) (callWeight selected (sourceKind query)) := by
  rcases query with (⟨plaintext, kid⟩ | raw) | (coin | (bytes | query))
  all_goals simp only [RawCtxServerServices.serverImpl, StateT.run, bind_pure_comp, isQueryBoundP_map_iff, sourceKind, callWeight]
  case inl.inl => exact nativeLift_bound selected _ _ (RawCtxServerMixed.send_bound senderId plaintext kid state selected)
  case inl.inr => exact nativeLift_bound selected _ _ (RawCtxServerMixed.raw_bound route decode raw state selected)
  case inr.inl =>
    exact (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
      (p := nativePredicate selected) (.inl coin) 0).2 (fun contradiction => contradiction.elim)
  case inr.inr.inl =>
    apply (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
      (p := nativePredicate selected) _ _).2
    cases selected <;> simp [nativePredicate, RawCtxMixedOwner.callKind]
  case inr.inr.inr =>
    exact (isQueryBoundP_query_iff (spec := RawCtxServerServices.BackendSpec)
      (p := nativePredicate selected) (.inr (.inr query)) 0).2 (fun contradiction => contradiction.elim)

/-- The native ledger includes public commitment requests in the hash coordinate only. -/
theorem native_bill (selected : RawCtxMixedOwner.CallKind) (budget : Budget) :
    bill (callWeight selected) budget = RawCtxMixedOwner.sendCost selected * budget .send +
      RawCtxMixedOwner.receiveCost selected * budget .raw +
      (if selected = .hash then budget .hash else 0) := by
  have enumeration : (Finset.univ : Finset Kind) = {.send, .raw, .coin, .hash, .hkdf} := by decide
  cases selected <;> simp [bill, enumeration, callWeight, RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost, Nat.add_assoc]

/-- All native source calls remain bounded in the same adaptive public-service experiment. -/
theorem backend_bound {Metadata PeerMetadata Result : Type}
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerServices.SourceSpec Result) (budget : Budget)
    (bounded : Bounded client budget) (state : State Metadata PeerMetadata)
    (selected : RawCtxMixedOwner.CallKind) :
    ((simulateQ (RawCtxServerServices.serverImpl senderId route decode) client).run state).IsQueryBoundP
      (nativePredicate selected) (RawCtxMixedOwner.sendCost selected * budget .send +
        RawCtxMixedOwner.receiveCost selected * budget .raw +
        (if selected = .hash then budget .hash else 0)) := by
  simpa only [native_bill] using weighted_bound
    (RawCtxServerServices.serverImpl senderId route decode) (nativePredicate selected) (callWeight selected)
    client budget bounded (fun query state => backend_step senderId route decode query state selected) state

/-- Five explicit native caps share one peer map and include every public commitment attempt. -/
theorem backend_bounds {Metadata PeerMetadata Result : Type}
    (senderId : Metadata → Std.U64) (route : SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxServerServices.SourceSpec Result) (budget : Budget)
    (bounded : Bounded client budget) (state : State Metadata PeerMetadata) :
    let program := (simulateQ (RawCtxServerServices.serverImpl senderId route decode) client).run state
    program.IsQueryBoundP (nativePredicate .kdf) (budget .send + 51 * budget .raw) ∧
      program.IsQueryBoundP (nativePredicate .sealing) (budget .send) ∧
      program.IsQueryBoundP (nativePredicate .opening) (budget .raw) ∧
      program.IsQueryBoundP (nativePredicate .hash) (budget .send + budget .raw + budget .hash) ∧
      program.IsQueryBoundP (nativePredicate .writer) (budget .send) := by
  simpa only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost, Nat.one_mul, Nat.zero_mul,
    Nat.add_zero, Nat.zero_add, reduceCtorEq, ↓reduceIte] using
    And.intro (backend_bound senderId route decode client budget bounded state .kdf)
      (And.intro (backend_bound senderId route decode client budget bounded state .sealing)
        (And.intro (backend_bound senderId route decode client budget bounded state .opening)
          (And.intro (backend_bound senderId route decode client budget bounded state .hash)
            (backend_bound senderId route decode client budget bounded state .writer))))

end BeaconcryptCore.Computational.RawCtxServerServiceBounds

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.bill_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.bill_step

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.weighted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.weighted_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.source_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.source_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.source_uniform_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.source_uniform_step

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.uniform_bill

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.schedule_uniform

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.nativeLift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.nativeLift_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.backend_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.backend_step

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.native_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.native_bill

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.backend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.backend_bound

/-- info: 'BeaconcryptCore.Computational.RawCtxServerServiceBounds.backend_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxServerServiceBounds.backend_bounds

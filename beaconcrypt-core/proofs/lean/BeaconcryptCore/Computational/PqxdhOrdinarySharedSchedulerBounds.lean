import BeaconcryptCore.Computational.PqxdhOrdinarySharedScheduler
import BeaconcryptCore.Computational.RawCtxSelectiveChainBudgets

/-!
The actual ordinary prefix pays every old record/public/reveal attempt, the whole interpreted identity/base/KEM callback, and every native finish callback. Uniform bounds below apply to complete concrete local computations; deterministic primitive and parser work remains in the original source-call ledger.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds
open PqxdhOrdinarySharedScheduler PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity
open PqxdhPhase1AcceptanceOracle PqxdhKemIndCca PqxdhJointKdfGame PqxdhPrivateKemSource
open PqxdhInitializerSecrecy CtxRomAuth AdaptiveCtxSharedHash
variable {ι M P I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)

set_option backward.isDefEq.respectTransparency false in
/-- Every attempted old operation has at most one shared hash and one caller coin; reveal rejection and failed records retain those source caps. -/
theorem record_bills (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : Local M P I D K A S B count) :
    ((record count source writer sender route decode query).run state).IsQueryBoundP (HashClass true) 1 ∧
      ((record count source writer sender route decode query).run state).IsQueryBoundP (HashClass false) 1 := by
  simp only [record, StateT.run_mk, isQueryBoundP_map_iff]
  constructor
  · apply RawCtxSourceSharedRom.backend_bound
    have original := RawCtxRevealBudgets.backend_step S B sender route decode query state.roles .hash
    have weight : RawCtxRevealBudgets.weight (RawCtxServerServiceBounds.callWeight .hash) 0 query ≤ 1 := by
      cases query with
      | inl query =>
        simp only [RawCtxRevealBudgets.weight]
        cases RawCtxProtocolBudgets.sourceKind query <;>
          simp [RawCtxServerServiceBounds.callWeight, RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost]
      | inr query => simp [RawCtxRevealBudgets.weight]
    have predicate : RawCtxSourceSharedRom.backendClass true = RawCtxServerServiceBounds.nativePredicate .hash := by
      funext request
      rcases request with coin | ((kdf | (sealing | (opening | (bytes | frame)))) | view) <;> simp [RawCtxSourceSharedRom.backendClass, RawCtxServerServiceBounds.nativePredicate, RawCtxMixedOwner.callKind]
    simpa only [predicate] using original.mono weight
  · apply RawCtxSourceSharedRom.backend_bound
    have original := RawCtxSelectiveChainBudgets.reveal_coins S B sender route decode query state.roles
    have weight : RawCtxRevealBudgets.weight (fun kind => if kind = .coin then 1 else 0) 0 query ≤ 1 := by
      cases query with
      | inl query => simp only [RawCtxRevealBudgets.weight]; split <;> omega
      | inr query => simp [RawCtxRevealBudgets.weight]
    have predicate : RawCtxSourceSharedRom.backendClass false = (fun request : RawCtxServerServices.BackendSpec.Domain => request.isLeft = true) := by
      funext request
      rcases request with coin | ((kdf | (sealing | (opening | (bytes | frame)))) | view) <;> simp [RawCtxSourceSharedRom.backendClass]
    simpa only [predicate] using original.mono weight

/-- The full original selector evaluation has no hash request, and every actual identity/base/KEM random call remains in its stated bill. -/
theorem selector_bills (query : (SelectorSpec baseSpec).Domain)
    (state : Local M P I D K A S B count) (qSelector : Nat)
    (bounded : (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives count query).run state.auxiliary.2)).IsTotalQueryBound qSelector) :
    ((selector attachedVerify primitives count baseImpl kem secret query).run state).IsQueryBoundP (HashClass true) 0 ∧
      ((selector attachedVerify primitives count baseImpl kem secret query).run state).IsQueryBoundP (HashClass false) qSelector := by
  simp only [selector, StateT.run_mk, isQueryBoundP_map_iff]
  exact ⟨RawCtxSelectiveSharedRom.coins_no_hash _, RawCtxSelectiveSharedRom.coins_bound _ qSelector bounded⟩

/-- Every attempted Beacon finish pays all 69 native callbacks, including rejected or malformed paths and complete local callback work. -/
theorem finish_bills (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : Local M P I D K A S B count) (qLocal : Nat)
    (localBound : ∀ query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives count source localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal) :
    ((finish attachedVerify primitives count source decode localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass true) 69 ∧
      ((finish attachedVerify primitives count source decode localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass false) (69 * qLocal) := by
  cases query with
  | finish index raw =>
    simp only [PqxdhOrdinarySharedScheduler.finish, StateT.run_mk, bind_pure_comp, isQueryBoundP_map_iff]
    exact PqxdhOrdinaryNativeSharedRom.program_bills attachedVerify primitives count source localImpl baseImpl kem secret
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw (state.roles.1.2 index)) state.auxiliary 69 qLocal
      (PqxdhBeaconPhase2Bounds.native_owner_bound decode raw _) localBound

variable (qSelector qLocal : Nat)
    (selectorBound : ∀ query state,
      (evalKem baseImpl kem secret ((borrowedSelector attachedVerify primitives count query).run state)).IsTotalQueryBound qSelector)
    (localBound : ∀ query state, PqxdhOrdinaryNativeCache.sourceSafe query →
      ((PqxdhOrdinaryNativeCache.cacheFree attachedVerify primitives count source localImpl baseImpl kem secret query).run state).IsTotalQueryBound qLocal)

include selectorBound localBound in
/-- A conservative complete scheduler-step bill counts each source attempt and charges every local primitive computation's actual random calls. -/
theorem step_bills (query : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Domain)
    (state : Local M P I D K A S B count) :
    ((compiler attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass true) 69 ∧
      ((compiler attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret query).run state).IsQueryBoundP (HashClass false) (1 + qSelector + 69 * qLocal) := by
  rcases query with ((query | query) | query)
  · have bills := record_bills count source writer sender route decode query state
    exact ⟨bills.1.mono (by omega), bills.2.mono (by omega)⟩
  · have bills := selector_bills attachedVerify primitives count baseImpl kem secret query state qSelector (selectorBound query state.auxiliary.2)
    exact ⟨bills.1.mono (by omega), bills.2.mono (by omega)⟩
  · have bills := finish_bills attachedVerify primitives count source decode localImpl baseImpl kem secret query state qLocal localBound
    exact ⟨bills.1, bills.2.mono (by omega)⟩

include selectorBound localBound in
/-- The original adaptive client bounds the full ordinary prefix, including all rejected requests and local callback work. -/
theorem program_bills (client : OracleComp (PqxdhPhase2SourceScheduler.Spec baseSpec S B) Result)
    (state : Local M P I D K A S B count) (qCalls : Nat) (bounded : client.IsTotalQueryBound qCalls) :
    ((simulateQ (compiler attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret) client).run state).IsQueryBoundP (HashClass true) (69 * qCalls) ∧
      ((simulateQ (compiler attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret) client).run state).IsQueryBoundP (HashClass false) (qCalls * (1 + qSelector + 69 * qLocal)) := by
  induction client using OracleComp.inductionOn generalizing qCalls state with
  | pure value => simp
  | query_bind query next ih =>
    cases qCalls with
    | zero => simp only [isTotalQueryBound_query_bind_iff, Nat.not_lt_zero, false_and] at bounded
    | succ qCalls =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have first := step_bills attachedVerify primitives count source writer sender route decode localImpl baseImpl kem secret
        qSelector qLocal selectorBound localBound query state
      have rest := fun result : (PqxdhPhase2SourceScheduler.Spec baseSpec S B).Range query × Local M P I D K A S B count =>
        ih result.1 result.2 qCalls (by simpa using bounded.2 result.1)
      constructor
      · simpa only [Nat.mul_succ, Nat.add_comm] using isQueryBoundP_bind first.1 (fun result _ => (rest result).1)
      · simpa only [Nat.succ_mul, Nat.add_comm] using isQueryBoundP_bind first.2 (fun result _ => (rest result).2)

end BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds


/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.record_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.record_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.selector_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.selector_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.finish_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.finish_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.step_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.step_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.program_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhOrdinarySharedSchedulerBounds.program_bills

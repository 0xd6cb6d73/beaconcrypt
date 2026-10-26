import BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds
import BeaconcryptCore.Computational.PqxdhPhase2RouteQueries

/-!
The complete Phase2 attempt has ordinary CCA budgets derived from its actual callback syntax and the full private-state routing laws. Auxiliary callbacks retain their stated uniform, base and decapsulation allowances. The selected decapsulation contributes at most one ordinary decapsulation, and the owner's private root contributes none. Every optional branch and the source receive work before the sequence-one gate are included.

Subsequent private programs keep their explicitly bounded ordinary interpretation, including any further root or decapsulation work. These query ledgers do not instantiate the source auxiliary services, prove primitive implementations or replace a reached live-state distribution.
-/

open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2CcaBounds
open PqxdhBeaconPhase2Routed PqxdhBeaconPhase2RoutedBounds
open PqxdhPhase2RouteQueries PqxdhPhase2DecapsulationRouting
open PqxdhChallengeSecretRouting PqxdhKemIndCca PqxdhJointKdfGame
variable {ι : Type} {baseSpec : OracleSpec ι} {I D K X Response Auxiliary : Type}

/-- The callback allowance uses exactly the already checked source owner partition. -/
theorem allowance_eq (qAux qDecapsulation : Nat)
    (query : (PqxdhBeaconPhase2Shared.FullSpec I D (Option K) X Response Shared).Domain) :
    callbackAllowance qAux qDecapsulation query = publicCost qAux qDecapsulation (kind query) := by
  unfold callbackAllowance kind
  split <;> simp [publicCost]

/-- The full ordinary attempt charges all auxiliary work and one selected decapsulation allowance. -/
theorem owner_bound
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    ((simulateQ (routedHandles source challenge supplied aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary).IsQueryBoundP
        predicate (69 * qAux + qDecapsulation) := by
  have step := routedHandles_allowance source challenge supplied aux predicate qAux qDecapsulation auxBound decapsulationBound
  simp only [allowance_eq] at step
  simpa [Fin.sum_univ_three, publicCost, allowance, Nat.mul_comm] using
    FinitePartitionQueryBounds.weighted_bound kind (publicCost qAux qDecapsulation) allowance
      (routedHandles source challenge supplied aux) predicate
      (PqxdhBeaconPhase2Shared.owner decode raw state) (owner_kind decode raw state) step auxiliary

/-- The same bound holds for the literal ordinary interpretation of the original complete callback execution. -/
theorem owner_route_bound
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    (simulateQ (route source challenge supplied) ((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary)).IsQueryBoundP
        predicate (69 * qAux + qDecapsulation) := by
  rw [routed_program]
  exact owner_bound source challenge supplied aux predicate qAux qDecapsulation auxBound decapsulationBound decode raw state auxiliary

/-- Uniform, base and decapsulation classes retain the exact ordinary owner bounds without a second decapsulation charge for its root. -/
theorem owner_classes
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (qUniform qBase qDecapsulation : Nat)
    (uniformBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemUniformQuery qUniform)
    (baseBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemBaseQuery qBase)
    (decapsulationBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary) :
    let run := simulateQ (route source challenge supplied) ((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary)
    run.IsQueryBoundP IsMlKemUniformQuery (69 * qUniform) ∧
      run.IsQueryBoundP IsMlKemBaseQuery (69 * qBase) ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (69 * qDecapsulation + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using owner_route_bound source challenge supplied aux IsMlKemUniformQuery qUniform 0 uniformBound
      (fun _ => by simp [IsMlKemUniformQuery]) decode raw state auxiliary
  · simpa only [Nat.add_zero] using owner_route_bound source challenge supplied aux IsMlKemBaseQuery qBase 0 baseBound
      (fun _ => by simp [IsMlKemBaseQuery]) decode raw state auxiliary
  · exact owner_route_bound source challenge supplied aux IsMlKemLogicalDecapsulationQuery qDecapsulation 1 decapsulationBound
      (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) decode raw state auxiliary

/-- Subsequent private programs are charged at their actual ordinary interpretation from every complete optional owner result. -/
theorem continuation_bound {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (predicate : (MlKemCCAOracleSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr ciphertext) then 1 else 0) ≤ qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary)
    (next : ((Option PqxdhBeaconPhase2Preparation.Bytes × PqxdhBeaconPhase2Preparation.State I D (Option K)) × Auxiliary) →
      OracleComp (LocalPostSpec baseSpec) Result)
    (qNext : Nat)
    (nextBound : ∀ result, (simulateQ (route source challenge supplied) (next result)).IsQueryBoundP predicate qNext) :
    (simulateQ (route source challenge supplied) (((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary) >>= next)).IsQueryBoundP
        predicate (69 * qAux + qDecapsulation + qNext) := by
  rw [simulateQ_bind]
  exact isQueryBoundP_bind (owner_route_bound source challenge supplied aux predicate qAux qDecapsulation
    auxBound decapsulationBound decode raw state auxiliary) (fun result _ => nextBound result)

/-- Complete ordinary class ledgers add the actual continuation costs at the unchanged owner and auxiliary poststate. -/
theorem continuation_classes {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (challenge : MlKem768Ciphertext)
    (supplied : MlKemSharedSecret)
    (aux : QueryImpl (AuxSpec I D K X Response)
      (StateT Auxiliary (OracleComp (MlKemCCAOracleSpec baseSpec))))
    (qUniform qBase qDecapsulation : Nat)
    (uniformBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemUniformQuery qUniform)
    (baseBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemBaseQuery qBase)
    (decapsulationBound : ∀ query auxiliary, ((aux query).run auxiliary).IsQueryBoundP IsMlKemLogicalDecapsulationQuery qDecapsulation)
    (decode : RawCtxReceive.FrameDecoder) (raw : PqxdhBeaconPhase2Preparation.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D (Option K)) (auxiliary : Auxiliary)
    (next : ((Option PqxdhBeaconPhase2Preparation.Bytes × PqxdhBeaconPhase2Preparation.State I D (Option K)) × Auxiliary) →
      OracleComp (LocalPostSpec baseSpec) Result)
    (uNext bNext dNext : Nat)
    (nextBound : ∀ result,
      (simulateQ (route source challenge supplied) (next result)).IsQueryBoundP IsMlKemUniformQuery uNext ∧
      (simulateQ (route source challenge supplied) (next result)).IsQueryBoundP IsMlKemBaseQuery bNext ∧
      (simulateQ (route source challenge supplied) (next result)).IsQueryBoundP IsMlKemLogicalDecapsulationQuery dNext) :
    let run := simulateQ (route source challenge supplied) (((simulateQ (handles source challenge aux)
      (PqxdhBeaconPhase2Shared.owner decode raw state)).run auxiliary) >>= next)
    run.IsQueryBoundP IsMlKemUniformQuery (69 * qUniform + uNext) ∧
      run.IsQueryBoundP IsMlKemBaseQuery (69 * qBase + bNext) ∧
      run.IsQueryBoundP IsMlKemLogicalDecapsulationQuery (69 * qDecapsulation + 1 + dNext) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using continuation_bound source challenge supplied aux IsMlKemUniformQuery qUniform 0 uniformBound
      (fun _ => by simp [IsMlKemUniformQuery]) decode raw state auxiliary next uNext (fun result => (nextBound result).1)
  · simpa only [Nat.add_zero] using continuation_bound source challenge supplied aux IsMlKemBaseQuery qBase 0 baseBound
      (fun _ => by simp [IsMlKemBaseQuery]) decode raw state auxiliary next bNext (fun result => (nextBound result).2.1)
  · exact continuation_bound source challenge supplied aux IsMlKemLogicalDecapsulationQuery qDecapsulation 1 decapsulationBound
      (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) decode raw state auxiliary next dNext (fun result => (nextBound result).2.2)

end BeaconcryptCore.Computational.PqxdhPhase2CcaBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.allowance_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.allowance_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.owner_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.owner_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.owner_route_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.owner_route_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.owner_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.owner_classes

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.continuation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.continuation_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.continuation_classes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2CcaBounds.continuation_classes

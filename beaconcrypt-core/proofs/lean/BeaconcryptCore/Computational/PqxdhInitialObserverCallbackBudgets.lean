import BeaconcryptCore.Computational.PqxdhInitialCurrentSecrecy
import BeaconcryptCore.Computational.PqxdhInitialFusedBudgets
import BeaconcryptCore.Computational.PqxdhAuthenticatedRootBudgets

/-!
The current response-only initializer observer is costed from its literal source program. Its private cache retains real nonselected initializers and samples32 bytes only on their fresh root-family requests. Ordinary native, base and decapsulation work remains separately charged. Every bound applies to arbitrary supplied64-byte responses rather than transporting costs through a distribution equality.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets
open PqxdhInitialRootLabelService PqxdhInitialLabelCompiler PqxdhInitialRootFreeCallbacks
open PqxdhJointKdfGame PqxdhKemIndCca PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhInitializerSecrecy PqxdhCorrelatedExpand PqxdhCorrelatedExpandHybrid
variable {ι Result KemSK : Type} {baseSpec : OracleSpec ι}

def IsCoin : PqxdhInitialLabelCompiler.Spec.Domain → Prop
  | .inl _ => True
  | _ => False
def IsService : PqxdhInitialLabelCompiler.Spec.Domain → Prop
  | .inr _ => True
  | _ => False
instance : DecidablePred IsCoin := fun query => by cases query <;> simp only [IsCoin] <;> infer_instance
instance : DecidablePred IsService := fun query => by cases query <;> simp only [IsService] <;> infer_instance

/-- Embedding an actual ordinary computation retains exactly its uniform-query cap. -/
theorem coins_uniform (work : ProbComp Result) (q : Nat) (bounded : work.IsTotalQueryBound q) :
    (coins work).IsQueryBoundP IsCoin q :=
  IsQueryBoundP.liftComp_subSpec (p := fun _ => True) (fun _ => Iff.rfl) bounded.isQueryBoundP

/-- Ordinary local computations cannot make a private initializer service request. -/
theorem coins_service (work : ProbComp Result) : (coins work).IsQueryBoundP IsService 0 :=
  IsQueryBoundP.liftComp_subSpec (fun _ => Iff.rfl) (isQueryBoundP_false work 0)

/-- The executable root-free interpreter pays every original public coin, base and permitted decapsulation query. Its unused private-root fallback is pure. -/
theorem public_step
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (qBase qDecap : Nat) (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (query : (LocalPostSpec baseSpec).Domain) :
    (publicOnly baseImpl kem secret challenge query).IsTotalQueryBound
      ((if PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery query then 1 else 0) +
       (if PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery query then qBase else 0) +
       (if PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery query then qDecap else 0)) := by
  rcases query with ((coin | query) | ciphertext) | privateRequest
  all_goals simp only [publicOnly, publicImpl, PublicClass, IsMlKemUniformQuery,
    IsMlKemBaseQuery, IsMlKemLogicalDecapsulationQuery, if_true, if_false, Nat.zero_add, Nat.add_zero]
  · change (simulateQ (kemAmbientImpl baseImpl) ((unifSpec + baseSpec).query (.inl coin))).IsTotalQueryBound 1
    rw [simulateQ_spec_query]
    exact ⟨Nat.zero_lt_succ 0, fun _ => True.intro⟩
  · change (simulateQ (kemAmbientImpl baseImpl) ((unifSpec + baseSpec).query (.inr query))).IsTotalQueryBound qBase
    rw [simulateQ_spec_query]
    exact baseBound query
  · change (simulateQ (kemAmbientImpl baseImpl)
      (if ciphertext = challenge then pure none else kem.decaps secret ciphertext)).IsTotalQueryBound qDecap
    split
    · simp only [simulateQ_pure]; trivial
    · exact decapBound ciphertext
  · trivial

/-- All adaptive public callbacks retain their actual weighted sampling bill and complete return value. -/
theorem public_uniform
    (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (qBase qDecap : Nat) (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (client : OracleComp (LocalPostSpec baseSpec) Result) (u b d : Nat)
    (uniforms : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) u)
    (bases : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery) b)
    (decaps : client.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery) d) :
    (simulateQ (publicOnly baseImpl kem secret challenge) client).IsTotalQueryBound (u + qBase * b + qDecap * d) := by
  induction client using OracleComp.inductionOn generalizing u b d with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at uniforms bases decaps
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply (isTotalQueryBound_bind (public_step baseImpl kem secret challenge qBase qDecap baseBound decapBound query)
        (fun answer => ih answer _ _ _ (uniforms.2 answer) (bases.2 answer) (decaps.2 answer))).mono
      have hu := uniforms.1
      have hb := bases.1
      have hd := decaps.1
      have mulStep : ∀ cost n, 0 < n → cost * (n - 1) + cost = cost * n := by
        intro cost n positive
        rw [← Nat.mul_succ]
        congr 1
        omega
      split_ifs at * <;> simp_all only [not_true_eq_false, false_or]
      all_goals try have := mulStep qBase b (by omega)
      all_goals try have := mulStep qDecap d (by omega)
      all_goals omega

section Callbacks
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhPhase1AcceptanceOracle
variable {I D K X Response A : Type}

def BaseDecapsulation : (ActualBaseSpec I D K X Response).Domain → Prop
  | .inl query => PqxdhPhase2SharedBounds.IsDecapsulation query
  | _ => False
instance : DecidablePred (BaseDecapsulation (I := I) (D := D) (K := K) (X := X) (Response := Response)) :=
  fun query => by cases query <;> simp only [BaseDecapsulation] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Each real root-free callback retains its actual uniform, base and selected-decapsulation classes. -/
theorem work_caps
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (query : (ActualBaseSpec I D K X Response).Domain)
    (state : SharedState A × BareState count) :
    let actual := work (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge query state
    actual.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) (max qLocal 64) ∧
    actual.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery) 0 ∧
    actual.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery)
      (if BaseDecapsulation query then 1 else 0) := by
  have caps (query : (PqxdhPhase2PostScheduler.SharedSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)).Domain) :
      let actual := (PqxdhPhase2PostScheduler.handles (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge query).run state
      actual.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemUniformQuery) (max qLocal 64) ∧
      actual.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemBaseQuery) 0 ∧
      actual.IsQueryBoundP (PublicClass (baseSpec := baseSpec) IsMlKemLogicalDecapsulationQuery)
        (if PqxdhPhase2SharedBounds.IsOwnerDecapsulation query then 1 else 0) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [PqxdhPhase2PostSchedulerBounds.selected, PqxdhPhase2PostSchedulerBounds.perCall,
        PqxdhPhase2PostSchedulerBounds.predicate, PqxdhPhase2PostSchedulerBounds.publicPredicate, if_true] using
        PqxdhPhase2PostSchedulerBounds.handles_step attachedVerify primitives count fixed localImpl qLocal localBound challenge .uniform query state
    · simpa only [PqxdhPhase2PostSchedulerBounds.selected, PqxdhPhase2PostSchedulerBounds.predicate,
        PqxdhPhase2PostSchedulerBounds.publicPredicate, if_false] using
        PqxdhPhase2PostSchedulerBounds.handles_step attachedVerify primitives count fixed localImpl qLocal localBound challenge .base query state
    · simpa only [PqxdhPhase2PostSchedulerBounds.selected, PqxdhPhase2PostSchedulerBounds.perCall,
        PqxdhPhase2PostSchedulerBounds.predicate, PqxdhPhase2PostSchedulerBounds.publicPredicate] using
        PqxdhPhase2PostSchedulerBounds.handles_step attachedVerify primitives count fixed localImpl qLocal localBound challenge .decapsulation query state
  cases query with
  | inl query =>
      simpa only [work, original, simulateQ_spec_query, BaseDecapsulation,
        PqxdhPhase2SharedBounds.IsOwnerDecapsulation] using caps (.inl query)
  | inr query =>
      cases query with
      | inl query =>
          simpa only [work, original, simulateQ_spec_query, BaseDecapsulation,
            PqxdhPhase2SharedBounds.IsOwnerDecapsulation] using caps (.inr (.inl query))
      | inr response =>
          simpa only [work, original, simulateQ_spec_query, BaseDecapsulation,
            PqxdhPhase2SharedBounds.IsOwnerDecapsulation] using caps (.inr (.inr (.application response)))

inductive CallbackKind where
  | ordinary | decapsulation | service
  deriving DecidableEq, Fintype

def callbackKind : (PqxdhInitialFusedCompiler.Spec I D K X Response).Domain → CallbackKind
  | .inl query => if PqxdhPhase2SharedBounds.IsDecapsulation query then .decapsulation else .ordinary
  | .inr (.inl _) => .ordinary
  | .inr (.inr _) => .service

def callbackCost (qLocal qDecap : Nat) : CallbackKind → Nat
  | .ordinary => max qLocal 64
  | .decapsulation => max qLocal 64 + qDecap
  | .service => 0
def callbackBudget : CallbackKind → Nat
  | .ordinary => 68
  | _ => 1

set_option backward.isDefEq.respectTransparency false in
/-- Each executable fused compiler callback charges its real primitive sampling; the private response service has no ordinary coin query. -/
theorem compiler_uniform
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qLocal qBase qDecap : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (query : (PqxdhInitialFusedCompiler.Spec I D K X Response).Domain)
    (state : SharedState A × BareState count) :
    ((PqxdhInitialFusedCompiler.compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state).IsQueryBoundP IsCoin
      (callbackCost qLocal qDecap (callbackKind query)) := by
  have bounded (request : (ActualBaseSpec I D K X Response).Domain) :=
    public_uniform baseImpl kem secret challenge qBase qDecap baseBound decapBound
      (work attachedVerify primitives count fixed localImpl challenge request state) (max qLocal 64) 0
      (if BaseDecapsulation request then 1 else 0)
      (work_caps attachedVerify primitives count fixed localImpl qLocal localBound challenge request state).1
      (work_caps attachedVerify primitives count fixed localImpl qLocal localBound challenge request state).2.1
      (work_caps attachedVerify primitives count fixed localImpl qLocal localBound challenge request state).2.2
  cases query with
  | inl query =>
      simp only [PqxdhInitialFusedCompiler.compiler, StateT.run]
      apply coins_uniform
      by_cases selected : PqxdhPhase2SharedBounds.IsDecapsulation query
      · simpa only [callbackKind, selected, if_true, callbackCost, BaseDecapsulation,
          Nat.mul_zero, Nat.add_zero, Nat.mul_one, interpreted, StateT.run] using bounded (.inl query)
      · simpa only [callbackKind, selected, if_false, callbackCost, BaseDecapsulation,
          Nat.mul_zero, Nat.add_zero, interpreted, StateT.run] using bounded (.inl query)
  | inr query =>
      cases query with
      | inl query =>
          simp only [PqxdhInitialFusedCompiler.compiler, StateT.run]
          apply coins_uniform
          simpa only [callbackKind, callbackCost, BaseDecapsulation, if_false,
            Nat.mul_zero, Nat.add_zero, interpreted, StateT.run] using bounded (.inr query)
      | inr secrets =>
          simp only [PqxdhInitialFusedCompiler.compiler, StateT.run, callbackKind, callbackCost,
            isQueryBoundP_query_bind_iff, IsCoin, not_false_eq_true, true_or, if_false, true_and]
          intro response
          trivial

set_option backward.isDefEq.respectTransparency false in
/-- Only the actual fused private callback can add an initializer-service request; all native/public work is service-free. -/
theorem compiler_service
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhInitialFusedCompiler.Spec I D K X Response).Domain)
    (state : SharedState A × BareState count) :
    ((PqxdhInitialFusedCompiler.compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state).IsQueryBoundP IsService
      (if PqxdhInitialFusedBudgets.IsService query then 1 else 0) := by
  cases query with
  | inl query => exact coins_service _
  | inr query =>
      cases query with
      | inl query => exact coins_service _
      | inr secrets =>
          simp only [PqxdhInitialFusedCompiler.compiler, StateT.run,
            PqxdhInitialFusedBudgets.IsService, PqxdhInitialFusedBudgets.IsTailService, if_true,
            isQueryBoundP_query_bind_iff, IsService, not_true_eq_false, false_or]
          exact ⟨by decide, fun _ => by trivial⟩

/-- The real response-only owner gives the finite source callback partition used by the weighted primitive interpreter. -/
theorem owner_partition (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K))
    (kind : CallbackKind) :
    (PqxdhInitialFusedOwner.owner (X := X ⊕ PqxdhPhase2JointIdentity.Converted)
      (Response := Response) (Shared := PqxdhPhase2DecapsulationRouting.Shared) decode raw state).IsQueryBoundP
        (fun query => callbackKind query = kind) (callbackBudget kind) := by
  cases kind with
  | ordinary =>
      exact IsQueryBoundP.of_imp (fun _ _ => True.intro)
        (PqxdhInitialFusedBudgets.owner_total decode raw state).isQueryBoundP
  | decapsulation =>
      apply IsQueryBoundP.of_imp (p' := PqxdhInitialFusedBudgets.IsDecapsulation) _
        (PqxdhInitialFusedBudgets.owner_decapsulation decode raw state)
      intro query chosen
      cases query with
      | inl query =>
          by_cases selected : PqxdhPhase2SharedBounds.IsDecapsulation query
          · exact selected
          · simp [callbackKind, selected] at chosen
      | inr query => cases query <;> simp [callbackKind] at chosen
  | service =>
      apply IsQueryBoundP.of_imp (p' := PqxdhInitialFusedBudgets.IsService) _
        (PqxdhInitialFusedBudgets.owner_service decode raw state)
      intro query chosen
      cases query with
      | inl query => simp [callbackKind] at chosen; split at chosen <;> contradiction
      | inr query => cases query <;> simp_all [callbackKind, PqxdhInitialFusedBudgets.IsService, PqxdhInitialFusedBudgets.IsTailService]

/-- Every complete attempted owner pays the source-derived primitive bill and at most one initializer request for all supplied responses. -/
theorem owner_bounds
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (qLocal qBase qDecap : Nat)
    (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (baseBound : ∀ query, (baseImpl query).IsTotalQueryBound qBase)
    (decapBound : ∀ ciphertext, (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State
      (PqxdhGeneratedBeaconState.IdentityHandle I) D (PqxdhGeneratedBeaconState.KemHandle K))
    (state : SharedState A × BareState count) :
    let actual := (simulateQ (PqxdhInitialFusedCompiler.compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
      (PqxdhInitialFusedOwner.owner decode raw owner)).run state
    actual.IsQueryBoundP IsCoin (69 * max qLocal 64 + qDecap) ∧ actual.IsQueryBoundP IsService 1 := by
  constructor
  · have weighted := FinitePartitionQueryBounds.weighted_bound callbackKind (callbackCost qLocal qDecap) callbackBudget
      (PqxdhInitialFusedCompiler.compiler attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
      IsCoin (PqxdhInitialFusedOwner.owner decode raw owner) (owner_partition decode raw owner)
      (compiler_uniform attachedVerify primitives count fixed localImpl baseImpl kem secret challenge qLocal qBase qDecap localBound baseBound decapBound) state
    have bill : (∑ kind, callbackCost qLocal qDecap kind * callbackBudget kind) = 69 * max qLocal 64 + qDecap := by
      rw [show (Finset.univ : Finset CallbackKind) = {.ordinary, .decapsulation, .service} by decide]
      simp [callbackCost, callbackBudget]
      omega
    simpa only [bill] using weighted
  · exact (PqxdhInitialFusedBudgets.owner_service decode raw owner).simulateQ_run_StateT_of_step
      (fun query before => compiler_service attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query before) state

end Callbacks
end BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.coins_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.coins_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.coins_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.coins_service
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.public_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.public_step
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.public_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.public_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.work_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.work_caps
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.compiler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.compiler_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.compiler_service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.compiler_service
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.owner_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.owner_partition
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.owner_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets.owner_bounds

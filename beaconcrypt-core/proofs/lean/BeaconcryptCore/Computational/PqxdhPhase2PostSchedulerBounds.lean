import BeaconcryptCore.Computational.PqxdhPhase2PostScheduler
import BeaconcryptCore.Computational.PqxdhPhase2SharedBounds
import BeaconcryptCore.Computational.PqxdhPhase2SourceSchedulerBounds

/-!
The actual postchallenge compiler accounts separately for public uniform/base/decapsulation work and private root attempts. Every attempted native finish contributes its source-derived bounds, including rejected inputs and failed publication. Local callback sampling has an explicit allowance; opaque computation is not declared free. Public fixed-HKDF work remains its actual source operation.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds
open PqxdhPhase2PostScheduler PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource
open PqxdhJointKdfGame PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhChallengeSecretRouting PqxdhChallengeSecretQueryBounds
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
variable {ι M P I D K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

set_option backward.isDefEq.respectTransparency false in
inductive Resource where
  | uniform | base | decapsulation | root
  deriving DecidableEq, Fintype

def publicPredicate : Resource → (MlKemCCAOracleSpec baseSpec).Domain → Prop
  | .uniform => IsMlKemUniformQuery
  | .base => IsMlKemBaseQuery
  | .decapsulation => IsMlKemLogicalDecapsulationQuery
  | .root => fun _ => False

def predicate : Resource → (LocalPostSpec baseSpec).Domain → Prop
  | .root => IsPrivateRoot
  | resource => PublicClass (publicPredicate resource)

noncomputable instance (resource : Resource) : DecidablePred (publicPredicate (baseSpec := baseSpec) resource) :=
  by cases resource <;> dsimp only [publicPredicate] <;> infer_instance

noncomputable instance (resource : Resource) : DecidablePred (predicate (baseSpec := baseSpec) resource) :=
  by cases resource <;> dsimp only [predicate] <;> infer_instance

/-- Public forwarding preserves its exact original resource count and has no private-root capability. -/
theorem publicWork_bound {Result : Type} (resource : Resource)
    (work : OracleComp (MlKemCCAOracleSpec baseSpec) Result) (budget : Nat)
    (bounded : work.IsQueryBoundP (publicPredicate (baseSpec := baseSpec) resource) budget) :
    (publicWork work).IsQueryBoundP (predicate (baseSpec := baseSpec) resource) budget := by
  apply RawCtxSourceOpen.simulate_bound PqxdhBeaconPhase2Routed.publicLift
    (publicPredicate (baseSpec := baseSpec) resource) (predicate (baseSpec := baseSpec) resource) work budget bounded
  intro query
  apply (isQueryBoundP_query_iff (spec := LocalPostSpec baseSpec) (p := predicate (baseSpec := baseSpec) resource) (.inl query) _).mpr
  cases resource <;> simp [predicate, publicPredicate, PublicClass, IsPrivateRoot]
  all_goals exact fun selected => by simpa only [selected, ite_true] using Nat.zero_lt_one

def auxiliaryCost (qLocal : Nat) : Resource → Nat
  | .uniform => max qLocal 64
  | _ => 0

/-- The original concrete auxiliary compiler forwards only its actual local uniform work. Existing-key decapsulation remains a costed local callback and does not call the selected-key oracle. -/
theorem auxiliary_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (resource : Resource) (query : (PqxdhPhase2SourceAux.Spec I D K X Response).Domain)
    (state : SharedState A × BareState count) :
    ((PqxdhBeaconPhase2Routed.sharedAux (borrowedAux (baseSpec := baseSpec)
      attachedVerify primitives count source localImpl) query).run state).IsQueryBoundP
        (predicate (baseSpec := baseSpec) resource) (auxiliaryCost qLocal resource) := by
  apply publicWork_bound
  have actual := borrowed_classes (baseSpec := baseSpec) attachedVerify primitives count source localImpl
    qLocal localBound query state
  cases resource with
  | uniform => exact actual.1
  | base => exact actual.2.1
  | decapsulation => exact actual.2.2
  | root => exact isQueryBoundP_false _ 0

def selected {Shared : Type} : Resource → (PqxdhBeaconPhase2Shared.FullSpec I D K X Response Shared).Domain → Prop
  | .uniform => fun _ => True
  | .base => fun _ => False
  | .decapsulation => PqxdhPhase2SharedBounds.IsOwnerDecapsulation
  | .root => PqxdhPhase2SharedBounds.IsOwnerRoot

instance {Shared : Type} (resource : Resource) : DecidablePred
    (selected (I := I) (D := D) (K := K) (X := X) (Response := Response) (Shared := Shared) resource) :=
  by cases resource <;> dsimp only [selected] <;> infer_instance

def perCall (qLocal : Nat) : Resource → Nat
  | .uniform => max qLocal 64
  | _ => 1

/-- Every concrete routed callback keeps its class: auxiliary coins, the original decapsulation position, or the private root position. No callback can issue a selected-key base request. -/
theorem routed_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (resource : Resource)
    (query : (PqxdhBeaconPhase2Shared.FullSpec (IdentityHandle I) D (Option K)
      (X ⊕ Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : SharedState A × BareState count) :
    ((PqxdhBeaconPhase2Routed.handles source challenge
      (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl) query).run state).IsQueryBoundP
        (predicate (baseSpec := baseSpec) resource) (if selected resource query then perCall qLocal resource else 0) := by
  rcases query with (query | (query | query)) <;> cases query
  case inl.decapsulate value key =>
    cases key with
    | none =>
      have handled :
          (PqxdhBeaconPhase2Routed.handles source challenge
            (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl)
              (.inl (.decapsulate value none))).run state =
            (fun reply => (reply, state)) <$>
              PqxdhPhase2InputBytes.decapCall (baseSpec := baseSpec) challenge value := by
        rw [show PqxdhBeaconPhase2Routed.handles source challenge
          (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl)
            (.inl (.decapsulate value none)) =
              liftM (PqxdhPhase2InputBytes.decapCall (baseSpec := baseSpec) challenge value) by rfl]
        simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
          StateT.run, bind_pure_comp]
      rw [handled]
      rw [isQueryBoundP_map_iff]
      apply (PqxdhPhase2InputBytes.decapCall_bound challenge value (predicate (baseSpec := baseSpec) resource)).mono
      cases resource <;> simp [selected, perCall, predicate, publicPredicate, PublicClass, IsPrivateRoot,
        IsMlKemUniformQuery, IsMlKemBaseQuery, IsMlKemLogicalDecapsulationQuery,
        PqxdhPhase2SharedBounds.IsOwnerDecapsulation, PqxdhPhase2SharedBounds.IsDecapsulation,
        PqxdhPhase2SharedBounds.IsOwnerRoot]
      split <;> omega
    | some prior =>
      simp only [PqxdhBeaconPhase2Routed.handles, StateT.run_map, isQueryBoundP_map_iff]
      apply (auxiliary_bound attachedVerify primitives count source localImpl qLocal localBound resource
        (.localDecapsulation value prior) state).mono
      cases resource <;> simp [auxiliaryCost, selected, perCall]
  case inr.inr.root secrets =>
    have handled :
        (PqxdhBeaconPhase2Routed.handles source challenge
          (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl)
            (.inr (.inr (.root secrets)))).run state =
          (fun reply => (reply, state)) <$> PqxdhPhase2InputBytes.rootCall (baseSpec := baseSpec)
            source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4 := by
      rw [show PqxdhBeaconPhase2Routed.handles source challenge
        (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count source localImpl)
          (.inr (.inr (.root secrets))) =
            liftM (PqxdhPhase2InputBytes.rootCall (baseSpec := baseSpec)
              source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4) by rfl]
      simp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift, StateT.lift,
        StateT.run, bind_pure_comp]
    rw [handled]
    rw [isQueryBoundP_map_iff]
    apply (PqxdhPhase2InputBytes.rootCall_bound source challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3
      secrets.dh4 (predicate (baseSpec := baseSpec) resource)).mono
    cases resource <;> cases secrets.shared <;>
      simp [selected, perCall, predicate, PublicClass, IsPrivateRoot,
        PqxdhPhase2SharedBounds.IsOwnerDecapsulation, PqxdhPhase2SharedBounds.IsOwnerRoot,
        PqxdhPhase2SharedBounds.IsTailRoot]
  all_goals simp only [PqxdhBeaconPhase2Routed.handles]
  all_goals try
    apply (auxiliary_bound attachedVerify primitives count source localImpl qLocal localBound resource _ state).mono
    cases resource <;> simp [auxiliaryCost, selected, perCall,
      PqxdhPhase2SharedBounds.IsOwnerDecapsulation, PqxdhPhase2SharedBounds.IsDecapsulation,
      PqxdhPhase2SharedBounds.IsOwnerRoot, PqxdhPhase2SharedBounds.IsTailRoot]
  all_goals simp

set_option backward.isDefEq.respectTransparency false in
/-- Translating a retained KEM handle leaves every charged callback class unchanged. -/
theorem handles_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (resource : Resource)
    (query : (SharedSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)).Domain)
    (state : SharedState A × BareState count) :
    ((handles (baseSpec := baseSpec) attachedVerify primitives count source localImpl challenge query).run state).IsQueryBoundP
      (predicate (baseSpec := baseSpec) resource) (if selected resource query then perCall qLocal resource else 0) := by
  rcases query with (query | query)
  · cases query <;> simp only [handles, QueryImpl.compose, PqxdhPhase2SharedKemHandles.full,
      PqxdhPhase2SharedKemHandles.preparation, simulateQ_spec_query, PqxdhBeaconPhase2Shared.preLift]
    all_goals apply (routed_step attachedVerify primitives count source localImpl qLocal localBound challenge resource _ state).mono
    all_goals cases resource <;> rfl
  · simp only [handles, QueryImpl.compose, PqxdhPhase2SharedKemHandles.full, simulateQ_spec_query]
    apply (routed_step attachedVerify primitives count source localImpl qLocal localBound challenge resource (.inr query) state).mono
    cases resource <;> rfl

def finishCost (qLocal : Nat) : Resource → Nat
  | .uniform => 69 * max qLocal 64
  | .base => 0
  | .decapsulation | .root => 1

set_option backward.isDefEq.respectTransparency false in
/-- Every attempted finish pays for its whole source-shaped execution, including work before rejection. The selected private root and logical decapsulation each occur at most once. -/
theorem targetFinish_bound
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (challenge : MlKem768Ciphertext) (decode : RawCtxReceive.FrameDecoder) (resource : Resource)
    (query : (PqxdhPhase2LiveFinish.FinishSpec B).Domain)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((targetFinish (baseSpec := baseSpec) attachedVerify primitives count source localImpl challenge decode query).run state).IsQueryBoundP (predicate (baseSpec := baseSpec) resource) (finishCost qLocal resource) := by
  cases query with
  | finish index raw =>
    simp only [targetFinish, StateT.run]
    rw [isQueryBoundP_map_iff]
    cases resource with
    | uniform =>
      exact PqxdhBeaconPhase2Bounds.interpreted_total_bound _ _ (max qLocal 64) 69
        (fun query before => handles_step attachedVerify primitives count source localImpl qLocal localBound challenge .uniform query before)
        _ (PqxdhPhase2SharedBounds.owner_total decode raw _) _
    | base =>
      exact (isQueryBoundP_false _ 0).simulateQ_run_StateT_of_step
        (fun query before => handles_step attachedVerify primitives count source localImpl qLocal localBound challenge .base query before) _
    | decapsulation =>
      exact (PqxdhPhase2SharedBounds.owner_decapsulation decode raw _).simulateQ_run_StateT_of_step
        (fun query before => handles_step attachedVerify primitives count source localImpl qLocal localBound challenge .decapsulation query before) _
    | root =>
      exact (PqxdhPhase2SharedBounds.owner_root decode raw _).simulateQ_run_StateT_of_step
        (fun query before => handles_step attachedVerify primitives count source localImpl qLocal localBound challenge .root query before) _

/-- The original scheduler partition is retained; the source coordinate conservatively permits creation and a source coin request. -/
def cost (qLocal : Nat) (resource : Resource) : PqxdhPhase2SourceSchedulerBounds.Kind → Nat
  | .inl kind => match resource with
      | .uniform => RawCtxServerServiceBounds.uniformWeight 0 kind
      | _ => 0
  | .inr index => if index = 5 then finishCost qLocal resource else
      match resource with
      | .uniform => if index = 1 then 33 else if index = 2 then 1 else 0
      | .base => if index = 3 then 1 else 0
      | .decapsulation => if index = 4 then 1 else 0
      | .root => 0

/-- Each exact source request has its own selected-resource cost; public work cannot issue a private root request. -/
theorem target_step
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) (resource : Resource)
    (query : (Spec (baseSpec := baseSpec) (S := S) (B := B)).Domain)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((target (baseSpec := baseSpec) attachedVerify primitives count source localImpl writer senderId route decode challenge query).run state).IsQueryBoundP (predicate (baseSpec := baseSpec) resource)
        (cost qLocal resource (PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec) query)) := by
  rcases query with ((query | query) | query)
  · change (publicWork (ccaCoins ((fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decode query).run state.1))).IsQueryBoundP (predicate (baseSpec := baseSpec) resource) _
    apply publicWork_bound
    cases resource with
    | uniform =>
      apply PqxdhPrivateRootQueryBounds.ccaCoins_uniform
      simp only [IsTotalQueryBound, isQueryBound_map_iff]
      have bound := PqxdhProtocolQueryBounds.source_uniform_step source writer senderId route decode query state.1
      cases query <;> simpa [PqxdhPhase2SourceSchedulerBounds.classify, cost, RawCtxRevealBudgets.weight, IsTotalQueryBound] using bound
    | base =>
      apply (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ IsMlKemBaseQuery (fun _ => by simp [IsMlKemBaseQuery])).mono
      exact Nat.zero_le _
    | decapsulation =>
      apply (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ IsMlKemLogicalDecapsulationQuery
        (fun _ => by simp [IsMlKemLogicalDecapsulationQuery])).mono
      exact Nat.zero_le _
    | root => exact isQueryBoundP_false _ _
  · change (publicWork ((fun result => (result.1, (state.1, result.2))) <$>
      (borrowedSelector attachedVerify primitives count query).run state.2)).IsQueryBoundP
        (predicate (baseSpec := baseSpec) resource) _
    apply publicWork_bound
    rw [isQueryBoundP_map_iff]
    cases resource with
    | uniform =>
      apply (PqxdhPrivateRootQueryBounds.borrowed_uniform_step attachedVerify primitives count query state.2).mono
      rcases query with (request | ((coin | base) | decap)) <;>
        simp [PqxdhPhase2SourceSchedulerBounds.classify, cost, PqxdhPrivateKemQueryBounds.SelectorSource,
          PqxdhPrivateRootQueryBounds.SelectorCCA, IsMlKemUniformQuery]
      by_cases creating : PqxdhPrivatePhase1Prefix.Creating request <;>
        by_cases uniform : PqxdhPrivateRootQueryBounds.SourceUniform request <;>
          simp [creating, uniform]
    | base =>
      apply (PqxdhPrivateRootQueryBounds.borrowed_class_step attachedVerify primitives count IsMlKemBaseQuery
        (fun _ => by simp [IsMlKemBaseQuery]) query state.2).mono
      rcases query with (request | ((coin | base) | decap)) <;>
        simp [PqxdhPhase2SourceSchedulerBounds.classify, cost, PqxdhPrivateRootQueryBounds.SelectorCCA,
          IsMlKemBaseQuery]
    | decapsulation =>
      apply (PqxdhPrivateRootQueryBounds.borrowed_class_step attachedVerify primitives count IsMlKemLogicalDecapsulationQuery
        (fun _ => by simp [IsMlKemLogicalDecapsulationQuery]) query state.2).mono
      rcases query with (request | ((coin | base) | decap)) <;>
        simp [PqxdhPhase2SourceSchedulerBounds.classify, cost, PqxdhPrivateRootQueryBounds.SelectorCCA,
          IsMlKemLogicalDecapsulationQuery]
    | root => exact isQueryBoundP_false _ _
  · exact targetFinish_bound attachedVerify primitives count source localImpl qLocal localBound challenge decode resource query state

def bill (qLocal : Nat) (resource : Resource) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) : Nat :=
  ∑ kind, cost qLocal resource kind * budget kind

/-- The adaptive source budget charges every possible reply continuation and retains the entire result and private live state. -/
theorem target_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) (resource : Resource)
    (client : OracleComp (Spec (baseSpec := baseSpec) (S := S) (B := B)) Result)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhPhase2SourceSchedulerBounds.Bounded client budget)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    ((simulateQ (target attachedVerify primitives count source localImpl writer senderId route decode challenge) client).run state).IsQueryBoundP (predicate (baseSpec := baseSpec) resource) (bill qLocal resource budget) := by
  exact FinitePartitionQueryBounds.weighted_bound (PqxdhPhase2SourceSchedulerBounds.classify (baseSpec := baseSpec))
    (cost qLocal resource) budget _ _ client bounded
    (fun query before => target_step attachedVerify primitives count source localImpl qLocal localBound
      writer senderId route decode challenge resource query before) state

/-- The coin bill includes source identity generation, every public coin request and every finish attempt. -/
theorem uniform_bill (qLocal : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) :
    bill qLocal .uniform budget = budget (.inl .coin) +
      64 * (budget (.inl .send) + budget (.inl .raw) + budget (.inl .hash)) +
      33 * budget (.inr 1) + budget (.inr 2) +
      69 * max qLocal 64 * budget (.inr 5) := by
  simp only [bill, Fintype.sum_sum_type]
  have old := RawCtxServerServiceBounds.uniform_bill 0 (fun kind => budget (.inl kind))
  simp only [RawCtxServerServiceBounds.bill, Nat.zero_mul, Nat.add_zero] at old
  change (∑ kind, RawCtxServerServiceBounds.uniformWeight 0 kind * budget (.inl kind)) +
    (∑ kind : Fin 6, cost qLocal .uniform (.inr kind) * budget (.inr kind)) = _
  rw [old]
  simp [Fin.sum_univ_succ, cost, finishCost, Nat.add_assoc]

/-- Ordinary base requests come only from the caller's explicit public base coordinate. -/
theorem base_bill (qLocal : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) :
    bill qLocal .base budget = budget (.inr 3) := by
  simp [bill, Fintype.sum_sum_type, Fin.sum_univ_succ, cost, finishCost]

/-- Every explicit public decapsulation and every attempted finish is charged. -/
theorem decapsulation_bill (qLocal : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) :
    bill qLocal .decapsulation budget = budget (.inr 4) + budget (.inr 5) := by
  simp [bill, Fintype.sum_sum_type, Fin.sum_univ_succ, cost, finishCost]

/-- Public traffic cannot request a private root; each attempted finish contributes at most one. -/
theorem root_bill (qLocal : Nat) (budget : PqxdhPhase2SourceSchedulerBounds.Budget) :
    bill qLocal .root budget = budget (.inr 5) := by
  simp [bill, Fintype.sum_sum_type, cost, finishCost]

/-- The concrete adaptive target scheduler supplies the existing component PostBounds contract, with no ambient private-root allowance. -/
theorem fullPostBounds {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (writer : RawCtxMixedShared.Writer) (senderId : M → Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext)
    (client : OracleComp (Spec (baseSpec := baseSpec) (S := S) (B := B)) Result)
    (budget : PqxdhPhase2SourceSchedulerBounds.Budget)
    (bounded : PqxdhPhase2SourceSchedulerBounds.Bounded client budget)
    (state : State (M := M) (P := P) (I := I) (D := D) (K := K) (A := A) (S := S) (B := B) count) :
    PostBounds ((simulateQ (target attachedVerify primitives count source localImpl writer senderId route decode challenge) client).run state)
      (bill qLocal .uniform budget) (budget (.inr 3))
      (budget (.inr 4) + budget (.inr 5)) (budget (.inr 5)) := by
  have bound := fun resource => target_bound attachedVerify primitives count source localImpl qLocal localBound
    writer senderId route decode challenge resource client budget bounded state
  exact ⟨bound .uniform, by simpa only [base_bill, predicate, publicPredicate] using bound .base,
    by simpa only [decapsulation_bill, predicate, publicPredicate] using bound .decapsulation,
    by simpa only [root_bill, predicate] using bound .root⟩

end BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds


/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.publicWork_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.publicWork_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.auxiliary_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.auxiliary_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.routed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.routed_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.handles_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.handles_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.targetFinish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.targetFinish_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.target_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.target_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.target_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.target_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.uniform_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.uniform_bill

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.base_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.base_bill

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.decapsulation_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.decapsulation_bill

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.root_bill' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.root_bill

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.fullPostBounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2PostSchedulerBounds.fullPostBounds

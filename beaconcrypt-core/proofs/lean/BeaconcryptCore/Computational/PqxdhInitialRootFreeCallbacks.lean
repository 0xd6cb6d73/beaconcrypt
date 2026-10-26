import BeaconcryptCore.Computational.PqxdhInitialRootLabelBridge
import BeaconcryptCore.Computational.PqxdhBeaconPhase2RoutedBounds

/-!
The non-root callbacks of the actual fused Beacon owner have no private root capability. Their complete interpreted computations can therefore run without a root cache. The zero bound is derived from the actual callback syntax; no callback uniform-cost assumption or caller-supplied state-independence premise is used.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks
open PqxdhInitializerSecrecy
open PqxdhKemIndCca PqxdhChallengeSecretRouting PqxdhJointKdfGame PqxdhCorrelatedExpand
open PqxdhCorrelatedExpandHybrid PqxdhChallengeSecretQueryBounds
variable {ι KemSK Result : Type} {baseSpec : OracleSpec ι}

noncomputable def publicOnly (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (LocalPostSpec baseSpec) ProbComp
  | .inl query => simulateQ (kemAmbientImpl baseImpl) (publicImpl kem secret challenge query)
  | .inr _ => pure none

/-- Every program whose actual syntax has zero private root requests is exactly its original public computation lifted into the root interface. The unused fallback branch is eliminated by the checked zero count. -/
theorem root_free (fixed : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext)
    (work : OracleComp (LocalPostSpec baseSpec) Result) (noRoot : work.IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) 0) :
    simulateQ (rootPost fixed baseImpl kem secret challenge) work =
      rootCoins (simulateQ (publicOnly baseImpl kem secret challenge) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at noRoot
      cases query with
      | inr request => simp [IsPrivateRoot] at noRoot
      | inl query =>
          have notPrivate : ¬ IsPrivateRoot (baseSpec := baseSpec) (.inl query) := by
            simp only [IsPrivateRoot, not_false_eq_true]
          have budget :
              (if IsPrivateRoot (baseSpec := baseSpec) (.inl query) then 0 - 1 else 0) = 0 :=
            Lean.Sym.ite_false _ _ _ (ht := notPrivate)
          have remaining : ∀ answer, (next answer).IsQueryBoundP (IsPrivateRoot (baseSpec := baseSpec)) 0 := by
            simpa only [budget] using noRoot.2
          simp only [simulateQ_bind, simulateQ_spec_query, rootPost, publicOnly, rootCoins, liftComp_bind]
          apply bind_congr
          intro answer
          exact ih answer (remaining answer)

section Callbacks
open PqxdhPhase1AcceptanceOracle
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPrivateKemSource
open PqxdhGeneratedBeaconState (IdentityHandle KemHandle)
open PqxdhPhase2JointIdentity (Converted)
variable {I D K X Response A : Type}

abbrev BaseSpec (I D K X Response Shared : Type) :=
  PqxdhBeaconPhase2Shared.Spec I D K X Response Shared + PqxdhInitialFusedBeacon.DataSpec Response

def original : QueryImpl (BaseSpec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (OracleComp (PqxdhBeaconPhase2Shared.FullSpec I D K X Response PqxdhPhase2DecapsulationRouting.Shared))
  | .inl query => (PqxdhBeaconPhase2Shared.FullSpec I D K X Response PqxdhPhase2DecapsulationRouting.Shared).query (.inl query)
  | .inr (.inl query) => (PqxdhBeaconPhase2Shared.FullSpec I D K X Response PqxdhPhase2DecapsulationRouting.Shared).query (.inr (.inl query))
  | .inr (.inr response) => (PqxdhBeaconPhase2Shared.FullSpec I D K X Response PqxdhPhase2DecapsulationRouting.Shared).query (.inr (.inr (.application response)))

set_option backward.isDefEq.respectTransparency false in
/-- Retained KEM-handle translation preserves the exact private-root query class of every actual current post callback, independently of all local callback costs. -/
theorem handle_roots
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) (challenge : MlKem768Ciphertext)
    (query : (PqxdhPhase2PostScheduler.SharedSpec (I := I) (D := D) (K := K) (X := X) (Response := Response)).Domain)
    (state : SharedState A × BareState count) :
    ((PqxdhPhase2PostScheduler.handles (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge query).run state).IsQueryBoundP
      (IsPrivateRoot (baseSpec := baseSpec)) (if PqxdhBeaconPhase2SharedBounds.rootCall query then 1 else 0) := by
  cases query with
  | inl query =>
      cases query <;> simp only [PqxdhPhase2PostScheduler.handles, QueryImpl.compose,
        PqxdhPhase2SharedKemHandles.full, PqxdhPhase2SharedKemHandles.preparation,
        PqxdhBeaconPhase2Shared.preLift, simulateQ_spec_query]
      all_goals
        simpa only [PqxdhBeaconPhase2SharedBounds.rootCall] using
          (PqxdhBeaconPhase2RoutedBounds.handles_root_step fixed challenge
            (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl) _ state)
  | inr query =>
      simp only [PqxdhPhase2PostScheduler.handles, QueryImpl.compose,
        PqxdhPhase2SharedKemHandles.full, simulateQ_spec_query]
      exact PqxdhBeaconPhase2RoutedBounds.handles_root_step fixed challenge
        (borrowedAux (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl) (.inr query) state

abbrev ActualBaseSpec (I D K X Response : Type) :=
  BaseSpec (IdentityHandle I) D (KemHandle K) (X ⊕ Converted) Response PqxdhPhase2DecapsulationRouting.Shared

noncomputable def work
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) (challenge : MlKem768Ciphertext)
    (query : (ActualBaseSpec I D K X Response).Domain) (state : SharedState A × BareState count) :
    OracleComp (LocalPostSpec baseSpec) ((ActualBaseSpec I D K X Response).Range query × (SharedState A × BareState count)) :=
  (simulateQ (PqxdhPhase2PostScheduler.handles attachedVerify primitives count fixed localImpl challenge)
    (original query)).run state

set_option backward.isDefEq.respectTransparency false in
/-- All actual preparation, raw-record and application callbacks have zero private-root queries, with their full optional replies and shared/private state effects retained. -/
theorem callback_no_root
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp)) (challenge : MlKem768Ciphertext)
    (query : (ActualBaseSpec I D K X Response).Domain) (state : SharedState A × BareState count) :
    (work (baseSpec := baseSpec) attachedVerify primitives count fixed localImpl challenge query state).IsQueryBoundP
      (IsPrivateRoot (baseSpec := baseSpec)) 0 := by
  cases query with
  | inl query =>
      simp only [work, original, simulateQ_spec_query]
      simpa only [PqxdhBeaconPhase2SharedBounds.rootCall, PqxdhBeaconPhase2SharedBounds.isRoot, Bool.false_eq_true, ite_false] using
        (handle_roots attachedVerify primitives count fixed localImpl challenge (.inl query) state)
  | inr query =>
      cases query with
      | inl query =>
          simp only [work, original, simulateQ_spec_query]
          simpa only [PqxdhBeaconPhase2SharedBounds.rootCall, PqxdhBeaconPhase2SharedBounds.isRoot, Bool.false_eq_true, ite_false] using
            (handle_roots attachedVerify primitives count fixed localImpl challenge (.inr (.inl query)) state)
      | inr response =>
          simp only [work, original, simulateQ_spec_query]
          simpa only [PqxdhBeaconPhase2SharedBounds.rootCall, PqxdhBeaconPhase2SharedBounds.isRoot, Bool.false_eq_true, ite_false] using
            (handle_roots attachedVerify primitives count fixed localImpl challenge (.inr (.inr (.application response))) state)

noncomputable def interpreted
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (ActualBaseSpec I D K X Response) (StateT (SharedState A × BareState count) ProbComp) :=
  fun query state => simulateQ (publicOnly baseImpl kem secret challenge)
    (work attachedVerify primitives count fixed localImpl challenge query state)

/-- The actual complete non-root callback is a root-cache-free computation; this follows from its derived syntax, not an assumed independent continuation. -/
theorem callback_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (ActualBaseSpec I D K X Response).Domain) (state : SharedState A × BareState count) :
    simulateQ (rootPost fixed baseImpl kem secret challenge)
      (work attachedVerify primitives count fixed localImpl challenge query state) =
        rootCoins ((interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state) :=
  root_free fixed baseImpl kem secret challenge _
    (callback_no_root attachedVerify primitives count fixed localImpl challenge query state)

/-- The actual non-root callback preserves the entire private root cache while retaining all original callback replies, local sampling and shared/identity state effects. -/
theorem cache_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (ActualBaseSpec I D K X Response).Domain) (state : SharedState A × BareState count)
    (cache : RootOracle.QueryCache) :
    (simulateQ uniformImpl (simulateQ (rootPost fixed baseImpl kem secret challenge)
      (work attachedVerify primitives count fixed localImpl challenge query state))).run cache =
        (fun result => (result, cache)) <$>
          (interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state := by
  rw [callback_source, PqxdhInitialRootContext.coins_complete]

end Callbacks
end BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.root_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.root_free

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.handle_roots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.handle_roots

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.callback_no_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.callback_no_root

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.callback_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.callback_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.cache_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialRootFreeCallbacks.cache_source

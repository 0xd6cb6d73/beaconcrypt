-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointOpenInitializedUniform
import BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityCosts

/-! All-reply randomness accounting for the executable ordinary joint-identity client. The bound includes both coin routes and actual local KEM/runtime work; it does not rely on interpreting the identity challenger honestly. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform
open PqxdhRegistrationJointServiceCosts (Kind poolClass)
open PqxdhRegistrationJointIdentityCompiler
open PqxdhRegistrationJointIdentityCosts (sourceKind dynamicKind)
open PqxdhServerAuthExperiment
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK A Result Reader Response : Type}

/-- Local evaluated randomness is forwarded one-for-one to the ordinary client's uniform interface. -/
theorem coins_bound (work : ProbComp Result) (bound : Nat) (bounded : work.IsTotalQueryBound bound) :
    (coins work).IsQueryBoundP (fun query => sourceKind query = some .uniform) bound := by
  induction work using OracleComp.inductionOn generalizing bound with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [coins, simulateQ_bind, simulateQ_spec_query, isQueryBoundP_query_bind_iff,
        sourceKind, not_true_eq_false, false_or, ite_true]
      exact ⟨bounded.1, fun reply => ih reply _ (bounded.2 reply)⟩

/-- Indexed local KEM work pays key generation and optional decapsulation, including base callbacks. Reveals remain pure local reads. -/
def kemCost (caps : KemCaps) : PqxdhLiveKemBirth.Query → Nat
  | .create => caps.keygenCost
  | .decapsulate _ _ => caps.decapsCost
  | .reveal _ => 0

theorem kem_bound (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (query : PqxdhLiveKemBirth.Query) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run pool).IsTotalQueryBound (kemCost caps query) := by
  cases query with
  | create =>
      change (PqxdhLiveKemBirth.created pool <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen).IsTotalQueryBound caps.keygenCost
      rw [IsTotalQueryBound, isQueryBound_map_iff]
      exact PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded
  | decapsulate index ciphertext =>
      exact PqxdhLiveKemBirth.decapsulate_uniform setup.baseImpl setup.kem pool index ciphertext caps.decapsCost
        (fun secret => PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl caps.baseUniform bounded.base
          (setup.kem.decaps secret ciphertext) caps.decapsUniform caps.decapsBase
          (bounded.decapsUniform secret ciphertext) (bounded.decapsBase secret ciphertext))
  | reveal index => trivial

private instance : Fintype Kind where
  elems := {.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate, .uniform,
    .other, .tail, .accept, .build, .hmac, .hash, .read}
  complete := by intro kind; cases kind <;> simp

/-- A complete finite partition counts both coin routes as uniform, while preserving private KEM and constructor work. -/
def classify : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain → Kind ⊕ Bool
  | .inl query => .inl (if PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK) query then .uniform else poolClass (KemSK := KemSK) query)
  | .inr .initialize => .inr true
  | .inr (.importSeed _) => .inr false

def cost (caps : KemCaps) (qInit : Nat) : Kind ⊕ Bool → Nat
  | .inl .uniform => 1
  | .inl .kemCreate => caps.keygenCost
  | .inl .decapsulate => caps.decapsCost
  | .inr true => qInit
  | _ => 0

set_option backward.isDefEq.respectTransparency false in
/-- Every compiler callback pays its complete local randomness bill, independently of subsequent challenger replies. -/
theorem compiler_step (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain) (state : Local KemSK A) :
    ((impl setup ensureInit query).run state).IsQueryBoundP
      (fun query => sourceKind query = some .uniform) (cost caps qInit (classify (KemSK := KemSK) query)) := by
  rcases query with (query | (coin | query)) | request
  case inl.inr.inr =>
    have paid := kem_bound setup caps bounded query state.1
    have billed : cost caps qInit (classify (KemSK := KemSK) (.inl (.inr (.inr query)))) = kemCost caps query := by
      cases query <;> rfl
    rw [billed]
    apply coins_bound
    change ((fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run state.1).IsTotalQueryBound _
    rw [IsTotalQueryBound, isQueryBound_map_iff]
    exact paid
  case inl.inl =>
    rcases query with coin | request
    · simp [impl, forward, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        sourceKind, dynamicKind, classify, cost, PqxdhDynamicKemJointBounds.IsUniform,
        PqxdhDynamicIdentityPool.IsUniform]
    · cases request
      case service index service => cases service <;>
        simp [impl, forward, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
          sourceKind, dynamicKind, classify, cost, poolClass, PqxdhDynamicKemJointBounds.IsUniform,
          PqxdhDynamicIdentityPool.IsUniform]
      all_goals simp [impl, forward, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
        sourceKind, dynamicKind, classify, cost, poolClass, PqxdhDynamicKemJointBounds.IsUniform,
        PqxdhDynamicIdentityPool.IsUniform]
  case inl.inr.inl =>
    simp [impl, forward, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
      sourceKind, classify, cost, PqxdhDynamicKemJointBounds.IsUniform]
  case inr =>
    cases request with
    | «initialize» =>
        apply coins_bound
        change ((fun result => (result.1, (state.1, result.2))) <$> ensureInit.run state.2).IsTotalQueryBound qInit
        rw [IsTotalQueryBound, isQueryBound_map_iff]
        exact initBound state.2
    | importSeed seed =>
        simp [impl, forward, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
          sourceKind, classify, cost]

/-- The uniform partition is exactly both explicit source coin interfaces. -/
theorem classify_coin (query : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain) :
    classify (KemSK := KemSK) query = .inl .uniform ↔
      PqxdhRegistrationJointOpenInitializedUniform.IsCoin (KemSK := KemSK) query := by
  cases query with
  | inl query =>
      by_cases coin : PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK) query
      · simp [classify, PqxdhRegistrationJointOpenInitializedUniform.IsCoin, coin]
      · simp only [classify, coin, ite_false, Sum.inl.injEq, PqxdhRegistrationJointOpenInitializedUniform.IsCoin]
        exact ⟨fun same => coin (PqxdhRegistrationJointOpenInitializedUniform.local_uniform_implies query same), False.elim⟩
  | inr query => cases query <;> simp [classify, PqxdhRegistrationJointOpenInitializedUniform.IsCoin]

/-- Every nonuniform request in the refined partition remains in its old private-service class. Ordinary joint coin calls have been removed from the old catch-all class. -/
theorem classify_private (query : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain)
    (kind : Kind) (nonuniform : kind ≠ .uniform) :
    classify (KemSK := KemSK) query = .inl kind →
      PqxdhRegistrationJointOpenInitializedCosts.classify (KemSK := KemSK) query = some kind := by
  cases query with
  | inl query =>
      by_cases coin : PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK) query <;>
        simp_all [classify, PqxdhRegistrationJointOpenInitializedCosts.classify, Ne.symm nonuniform]
  | inr query => cases query <;> simp [classify]

/-- Runtime initialization and caller-known imports retain their exact constructor partition. -/
theorem classify_local (query : (PqxdhRegistrationJointServerBirth.Spec KemSK).Domain) (kind : Bool) :
    classify (KemSK := KemSK) query = .inr kind ↔
      PqxdhRegistrationJointOpenInitializedCosts.localClass (KemSK := KemSK) query = some kind := by
  cases query with
  | inl query => simp [classify, PqxdhRegistrationJointOpenInitializedCosts.localClass]
  | inr query => cases query <;> simp [classify, PqxdhRegistrationJointOpenInitializedCosts.localClass]

/-- Source-derived bounds for the complete partition; generated identity creation remains external work. -/
def allowances (caps : KemCaps) (supplied : Option Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) : Kind ⊕ Bool → Nat
  | .inl .uniform => PqxdhRegistrationJointOpenUniform.total caps budget
  | .inl kind => (if kind = .identityCreate ∧ supplied.isNone = true then 1 else 0) +
      PqxdhRegistrationJointOpenCosts.privateTotal budget kind
  | .inr true => 1
  | .inr false => if supplied.isSome then 1 else 0

/-- The original fourteen source caps imply every coordinate of the corrected partition on all possible service replies. -/
theorem initialized_allowances (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (kind : Kind ⊕ Bool) :
    (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program).IsQueryBoundP
      (fun query => classify (KemSK := KemSK) query = kind) (allowances caps supplied budget kind) := by
  cases kind with
  | inl kind =>
      by_cases uniform : kind = .uniform
      · subst kind
        exact (isQueryBoundP_congr_pred classify_coin).mpr
          (PqxdhRegistrationJointOpenInitializedUniform.initialized_coins setup codec checks caps bounded supplied program budget certified)
      · have prior := PqxdhRegistrationJointOpenInitializedCosts.initialized_private setup codec checks supplied program budget certified kind uniform
        have transferred := IsQueryBoundP.of_imp (fun query => classify_private query kind uniform) prior
        cases kind <;> first | exact (uniform rfl).elim | exact transferred
  | inr kind =>
      have prior := PqxdhRegistrationJointOpenInitializedCosts.initialized_local setup codec checks supplied program kind
      have transferred := (isQueryBoundP_congr_pred (fun query => classify_local query kind)).mpr prior
      cases kind <;> exact transferred

/-- The client's complete uniform bill excludes only external generated-identity work, which the ordinary reduction charges separately. -/
def total (caps : KemCaps) (qInit : Nat) (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) : Nat :=
  qInit + PqxdhRegistrationJointOpenUniform.total caps budget +
    caps.keygenCost * budget (.inl 1) + caps.decapsCost * budget (.inl 5)

/-- Evaluate the full weighted partition without treating local KEM/base/runtime work as free. -/
theorem total_eq (caps : KemCaps) (qInit : Nat) (supplied : Option Pqxdh.Bytes)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat) :
    (∑ kind, cost caps qInit kind * allowances caps supplied budget kind) = total caps qInit budget := by
  rw [Fintype.sum_sum_type, Fintype.sum_bool]
  change (∑ kind ∈ ({.identityCreate, .signing, .staticDh, .kemCreate, .decapsulate, .uniform,
    .other, .tail, .accept, .build, .hmac, .hash, .read} : Finset Kind),
      cost caps qInit (.inl kind) * allowances caps supplied budget (.inl kind)) + _ = _
  simp [cost, allowances, PqxdhRegistrationJointOpenCosts.privateTotal, total]
  omega

/-- The literal initialized client has its full explicit randomness cap for every possible ordinary joint challenger reply. No real-interpreter or honest-owner restriction is used. -/
theorem initialized (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (caps : KemCaps) (bounded : KemBound setup caps) (supplied : Option Pqxdh.Bytes)
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (runtime : A)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → Nat)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source)) :
    (PqxdhRegistrationJointIdentityCompiler.initialized setup codec checks ensureInit supplied program runtime).IsQueryBoundP
      (fun query => dynamicKind query = .uniform) (total caps qInit budget) := by
  apply PqxdhRegistrationJointIdentityCosts.route_program
  rw [← total_eq caps qInit supplied budget]
  exact FinitePartitionQueryBounds.weighted_bound (classify (KemSK := KemSK)) (cost caps qInit)
    (allowances caps supplied budget) (impl setup ensureInit) (fun query => sourceKind query = some .uniform)
    (PqxdhRegistrationJointOpenInitialization.client setup codec checks supplied program)
    (initialized_allowances setup codec checks caps bounded supplied program budget certified)
    (fun query state => compiler_step setup ensureInit qInit initBound caps bounded query state)
    (PqxdhLiveKemBirth.empty, runtime)

end BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.coins_bound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.coins_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.kem_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.kem_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.compiler_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.compiler_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.classify_coin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.classify_coin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.classify_private' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.classify_private

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.classify_local' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.classify_local

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.initialized_allowances' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.initialized_allowances

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.total_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.total_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointIdentityUniform.initialized

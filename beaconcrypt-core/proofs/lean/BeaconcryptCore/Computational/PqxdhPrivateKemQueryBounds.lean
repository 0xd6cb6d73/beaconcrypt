import BeaconcryptCore.Computational.PqxdhPrivateKemSource

/-!
Structural source-class bounds preserve arbitrary selector continuations and non-uniform source services. Private primitive sampling remains separate from public identity queries; no opaque base or KEM operation is assigned free computational work.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhJointPhase1AcceptanceComposition PqxdhPrivateSourceCoins
open PqxdhKemIndCca PqxdhPrivateKemSource
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

set_option backward.isDefEq.respectTransparency false in
/-- Private evaluated work has no non-coin source requests; its actual uniform and primitive work must be budgeted separately. -/
theorem localCoins_excluded {Result : Type} (client : ProbComp Result)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (coinsExcluded : ∀ coin, ¬ predicate (.inl (.inl coin))) :
    (localCoins client).IsQueryBoundP (fun query => predicate (translated query)) 0 := by
  induction client using OracleComp.inductionOn with
  | pure value => simp [localCoins]
  | query_bind query next ih =>
      simp only [localCoins, simulateQ_bind, simulateQ_spec_query]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (coinsExcluded query), ?_⟩
      intro answer
      simpa only [localCoins, translated, coinsExcluded query, ite_false] using ih answer

set_option backward.isDefEq.respectTransparency false in
/-- Forwarding a public source program preserves every original class count through all possible replies. -/
theorem publicSource_bound {Result : Type} (client : OracleComp SourceSpec Result)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (bounded : client.IsQueryBoundP predicate bound) :
    (publicSource client).IsQueryBoundP (fun query => predicate (translated query)) bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => simp [publicSource]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [publicSource, simulateQ_bind, simulateQ_spec_query]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨bounded.1, ?_⟩
      intro answer
      exact ih answer _ (bounded.2 answer)

/-- Source-service classes remain distinct from logical CCA, primitive base and private coin requests. -/
def SelectorSource (predicate : SourceSpec.Domain → Prop) : (SelectorSpec baseSpec).Domain → Prop
  | .inl query => predicate query
  | .inr _ => False
instance (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (SelectorSource (baseSpec := baseSpec) predicate) := fun query => by
  cases query <;> dsimp [SelectorSource] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Actual local decapsulation and its internal coins add no signing/creation/service request; every original source request is still counted. -/
theorem localSelector_source_bound {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK)
    (client : OracleComp (SelectorSpec baseSpec) Result)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (coinsExcluded : ∀ coin, ¬ predicate (.inl (.inl coin))) (bound : Nat)
    (bounded : client.IsQueryBoundP (SelectorSource (baseSpec := baseSpec) predicate) bound) :
    (simulateQ (localSelector baseImpl kem secret) client).IsQueryBoundP
      (fun query => predicate (translated query)) bound := by
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_spec_query]
      cases query with
      | inl query =>
          change ((publicSource (SourceSpec.query query) : OracleComp PrivateSourceSpec (SourceSpec.Range query)) >>=
            fun answer => simulateQ (localSelector baseImpl kem secret) (next answer)).IsQueryBoundP _ bound
          rw [publicSource_query, isQueryBoundP_query_bind_iff]
          refine ⟨bounded.1, ?_⟩
          intro answer
          exact ih answer _ (bounded.2 answer)
      | inr query =>
          have continuation : ∀ answer, (simulateQ (localSelector baseImpl kem secret) (next answer)).IsQueryBoundP
              (fun query => predicate (translated query)) bound := fun answer =>
            ih answer bound (by simpa only [SelectorSource, ite_false] using bounded.2 answer)
          change ((localCoins (evalKem baseImpl kem secret ((MlKemCCAOracleSpec baseSpec).query query)) :
            OracleComp PrivateSourceSpec ((MlKemCCAOracleSpec baseSpec).Range query)) >>=
            fun answer => simulateQ (localSelector baseImpl kem secret) (next answer)).IsQueryBoundP _ bound
          simpa only [Nat.zero_add] using isQueryBoundP_bind
            (localCoins_excluded (evalKem baseImpl kem secret ((MlKemCCAOracleSpec baseSpec).query query)) predicate coinsExcluded)
            (fun answer _ => continuation answer)

end BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds.localCoins_excluded' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds.localCoins_excluded

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds.publicSource_bound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds.publicSource_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds.localSelector_source_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateKemQueryBounds.localSelector_source_bound

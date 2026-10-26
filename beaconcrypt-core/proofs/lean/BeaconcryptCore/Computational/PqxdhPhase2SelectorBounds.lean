import BeaconcryptCore.Computational.PqxdhPhase2Selector
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds

/-!
The actual source-facing native compiler charges every callback before any identity interpretation. Local source work, joint-service calls and logical selected-key decapsulation remain explicit. The source signing and creation restrictions are derived from the concrete auxiliary compiler, including rejected Phase2 attempts.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds
open PqxdhPhase2Selector PqxdhPhase2SourceAux PqxdhKemIndCca PqxdhPrivateKemSource PqxdhJointKdfGame
open PqxdhGeneratedBeaconState (IdentityHandle)
open PqxdhPhase2JointIdentity (Converted)
variable {ι I D K X Response A : Type} {baseSpec : OracleSpec ι}

/-- Every callback has an explicit selected-source budget, including source auxiliary work and the original selected decapsulation. -/
theorem step_bound
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (predicate : (SelectorSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (qAux qDecapsulation : Nat)
    (auxBound : ∀ query state, ((sourceAux (baseSpec := baseSpec) source localImpl query).run state).IsQueryBoundP predicate qAux)
    (decapsulationBound : ∀ ciphertext, (if predicate (.inr (.inr ciphertext)) then 1 else 0) ≤ qDecapsulation)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D (Option K) (X ⊕ Converted) Response).Domain)
    (state : SharedState A) :
    ((sourcePre (baseSpec := baseSpec) source localImpl query).run state).IsQueryBoundP predicate (qAux + qDecapsulation) := by
  rcases query with (query | (query | query)) <;> cases query <;> simp only [sourcePre] <;>
    try exact (auxBound _ state).mono (Nat.le_add_right _ _)
  case inl.decapsulate value key =>
    cases key with
    | some prior => exact (auxBound (.localDecapsulation value prior) state).mono (Nat.le_add_right _ _)
    | none =>
      change OracleComp.IsQueryBoundP
        ((fun reply => (Option.map PqxdhRootTableInitialization.rootArray reply, state)) <$>
        (((SelectorSpec baseSpec).query (.inr (.inr (PqxdhPhase2InputBytes.ciphertext value)))) :
          OracleComp (SelectorSpec baseSpec) (Option MlKemSharedSecret))) predicate _
      rw [isQueryBoundP_map_iff]
      exact (isQueryBoundP_query_iff (spec := SelectorSpec baseSpec) (p := predicate)
        (.inr (.inr (PqxdhPhase2InputBytes.ciphertext value))) _).2 (by
          have bounded := decapsulationBound (PqxdhPhase2InputBytes.ciphertext value)
          intro selected
          simp only [ite_eq_left selected] at bounded
          omega)
  all_goals simp [StateT.run_pure]

/-- A source class absent from every concrete callback stays absent through every adaptive native continuation. -/
theorem run_zero {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (predicate : (SelectorSpec baseSpec).Domain → Prop) [DecidablePred predicate]
    (auxBound : ∀ query state, ((sourceAux (baseSpec := baseSpec) source localImpl query).run state).IsQueryBoundP predicate 0)
    (excluded : ∀ ciphertext, ¬ predicate (.inr (.inr ciphertext)))
    (client : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D
      (Option K) (X ⊕ Converted) Response) Result) (state : SharedState A) :
    ((simulateQ (sourcePre (baseSpec := baseSpec) source localImpl) client).run state).IsQueryBoundP predicate 0 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact isQueryBoundP_bind
        (step_bound source localImpl predicate 0 0 auxBound
          (fun ciphertext => by simp [excluded ciphertext]) query state)
        (fun result _ => ih result.1 result.2)

/-- Native Phase2 cannot sign or create an identity, on any reply or rejection branch. -/
theorem source_restrictions {Result : Type}
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D
      (Option K) (X ⊕ Converted) Response) Result) (state : SharedState A) :
    let work := (simulateQ (sourcePre (baseSpec := baseSpec) source localImpl) client).run state
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhJointPhase1AcceptanceComposition.IsSigning) 0 ∧
    work.IsQueryBoundP (PqxdhPrivateKemQueryBounds.SelectorSource (baseSpec := baseSpec)
      PqxdhPrivatePhase1Prefix.Creating) 0 := by
  constructor
  · exact run_zero source localImpl _ (PqxdhPhase2SourceAux.source_no_sign source localImpl)
      (fun _ => by simp [PqxdhPrivateKemQueryBounds.SelectorSource]) client state
  · exact run_zero source localImpl _ (PqxdhPhase2SourceAux.source_no_create source localImpl)
      (fun _ => by simp [PqxdhPrivateKemQueryBounds.SelectorSource]) client state

/-- Total source syntax charges actual local coins, each joint-service call and the selected decapsulation channel before interpretation. -/
theorem step_total
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec (IdentityHandle I) D (Option K) (X ⊕ Converted) Response).Domain)
    (state : SharedState A) :
    ((sourcePre (baseSpec := baseSpec) source localImpl query).run state).IsTotalQueryBound (max qLocal 64 + 1) := by
  exact (isQueryBoundP_true_iff _ _).1
    (step_bound source localImpl (fun _ => True) (max qLocal 64) 1
      (fun query state => (isQueryBoundP_true_iff _ _).2
        (PqxdhPhase2SourceAux.source_total_bound source localImpl qLocal localBound query state))
      (fun _ => by simp) query state)

/-- A complete original Phase2 attempt keeps the 69-callback source bill even when it rejects before publication. -/
theorem owner_total
    (source : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((localImpl query).run state).IsTotalQueryBound qLocal)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State (IdentityHandle I) D (Option K)) (state : SharedState A) :
    ((simulateQ (sourcePre (baseSpec := baseSpec) source localImpl)
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run state).IsTotalQueryBound
      (69 * (max qLocal 64 + 1)) := by
  exact (isQueryBoundP_true_iff _ _).1
    (PqxdhBeaconPhase2Bounds.native_interpreted_bound (sourcePre source localImpl) (fun _ => True)
      (max qLocal 64 + 1) (fun query state => (isQueryBoundP_true_iff _ _).2
        (step_total source localImpl qLocal localBound query state)) decode raw owner state)

end BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.step_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.run_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.run_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.source_restrictions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.source_restrictions

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.step_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.step_total

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.owner_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2SelectorBounds.owner_total

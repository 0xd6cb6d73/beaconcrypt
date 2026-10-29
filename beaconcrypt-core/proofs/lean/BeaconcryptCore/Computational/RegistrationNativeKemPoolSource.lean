-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSource
import BeaconcryptCore.Computational.RegistrationNativeKemReservation

/-! The selected-handle stopped source reconstructs the complete actual reserved native key pool at every affordable non-reveal callback. Native production KEM adapters never request private key revelation; the whole-program zero-reveal certificate, rather than target honesty from public bytes, discharges that restriction. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemPoolSource
open RegistrationNativeKemInterface (Spec)
open RegistrationNativeKemGame (State stopped combine)
open RegistrationNativeKemReservation (reserved IsCreate)
open PqxdhKemIndCca (MlKemScheme MlKem768PublicKey)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

def IsReveal : (Spec ambient KemSK).Domain → Prop
  | .inr (.inl (.reveal _)) => True
  | _ => False

instance : DecidablePred (IsReveal (ambient := ambient) (KemSK := KemSK)) := fun query => by
  rcases query with query | (query | query)
  · exact inferInstanceAs (Decidable False)
  · cases query <;> simp only [IsReveal] <;> infer_instance
  · exact inferInstanceAs (Decidable False)

def project (pairs : List (MlKem768PublicKey × KemSK)) (before : State Auxiliary KemSK) :=
  (before.1, PqxdhDynamicKemRouter.sourcePool pairs before.2)

/-- All native production KEM callback steps have the real reserved private pool and the full source reply after erasing only the monitor. -/
theorem step_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (query : (Spec ambient KemSK).Domain)
    (before : State Auxiliary KemSK) (noReveal : ¬IsReveal query)
    (room : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((stopped baseImpl kem other selected pairs query).run).run before) =
    (fun result => (some result.1, result.2)) <$>
      (reserved baseImpl kem other pairs query).run (project pairs before) := by
  rcases query with query | (query | key)
  · simp only [stopped, combine, OptionT.run_mk, StateT.run, reserved,
      RegistrationNativeKemInterface.source, project, Functor.map_map]
    rfl
  · cases query with
    | reveal index => exact False.elim (noReveal trivial)
    | create =>
      have beforeRoom : before.2.created < pairs.length := by simpa only [IsCreate, ite_true] using Nat.lt_of_succ_le room
      have found : pairs[before.2.created]? = some pairs[before.2.created] :=
        List.getElem?_eq_some_iff.mpr ⟨beforeRoom, rfl⟩
      have amount : (PqxdhDynamicKemRouter.sourcePool pairs before.2).keys.length = before.2.created := by
        simp only [PqxdhDynamicKemRouter.sourcePool, List.length_take, Nat.min_eq_left (Nat.le_of_lt beforeRoom)]
      simp only [stopped, combine, OptionT.run_mk, StateT.run, PqxdhDynamicKemRouter.source,
        found, map_pure, reserved, project, amount]
      have full := PqxdhDynamicKemSource.created_pool pairs before.2 pairs[before.2.created] found
      exact congrArg (fun value => (pure (some value.1, (before.1, value.2)) : ProbComp _)) full
    | decapsulate handle ciphertext =>
      have full := PqxdhDynamicKemSource.decapsulation_source baseImpl kem selected pairs before.2 handle ciphertext
      have mapped := congrArg (fun work => (fun result => (result.1, (before.1, result.2))) <$> work) full
      simpa only [stopped, combine, OptionT.run_mk, StateT.run, reserved,
        RegistrationNativeKemInterface.source, project, Functor.map_map, Prod.map, id_eq] using mapped
  · simp only [stopped, combine, OptionT.run_mk, StateT.run, reserved,
      RegistrationNativeKemInterface.source, project, Functor.map_map]
    change ((fun value => (some value, project pairs before)) <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key)) =
      (fun result => (some result.1, result.2)) <$> (do
        let value ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key)
        pure (value, project pairs before))
    rw [bind_pure_comp, Functor.map_map]

/-- The native source's actual creation allowance prevents reservation exhaustion on every supported step. -/
theorem step_capacity (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (query : (Spec ambient KemSK).Domain)
    (before : State Auxiliary KemSK) (clear : before.2.exhausted = false)
    (room : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((Spec ambient KemSK).Range query) × State Auxiliary KemSK)
    (supported : result ∈ support (((stopped baseImpl kem other selected pairs query).run).run before)) :
    result.2.2.exhausted = false ∧ result.2.2.created ≤ before.2.created + (if IsCreate query then 1 else 0) := by
  rcases query with query | (query | key)
  · simp only [stopped, combine, OptionT.run_mk, StateT.run, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    exact ⟨clear, by simp [IsCreate]⟩
  · simp only [stopped, combine, OptionT.run_mk, StateT.run, support_map] at supported
    obtain ⟨inner, actual, rfl⟩ := supported
    have same : (if IsCreate (ambient := ambient) (KemSK := KemSK) (.inr (.inl query)) then 1 else 0) =
        (if PqxdhDynamicKemSource.IsCreation query then 1 else 0) := by cases query <;> rfl
    rw [same] at room ⊢
    exact PqxdhDynamicKemSource.step_capacity baseImpl kem selected pairs query before.2 clear room inner actual
  · simp only [stopped, combine, OptionT.run_mk, StateT.run, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    exact ⟨clear, by simp [IsCreate]⟩


private theorem step_answer (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (query : (Spec ambient KemSK).Domain)
    (before : State Auxiliary KemSK) (noReveal : ¬IsReveal query)
    (room : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length)
    (result : Option ((Spec ambient KemSK).Range query) × State Auxiliary KemSK)
    (supported : result ∈ support (((stopped baseImpl kem other selected pairs query).run).run before)) :
    result.1.isSome = true := by
  have mapped : Prod.map id (project pairs) result ∈ support
      (Prod.map id (project pairs) <$> (((stopped baseImpl kem other selected pairs query).run).run before)) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [step_source baseImpl kem other selected pairs query before noReveal room, support_map] at mapped
  obtain ⟨reply, _, same⟩ := mapped
  exact congrArg (fun value => value.1.isSome) same.symm

/-- The full actual native non-revealing program equals its concrete reserved key-pool execution, with no artificial stop or missing generated owner. -/
theorem program_source (baseImpl : QueryImpl base ProbComp) (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) (work : OracleComp (Spec ambient KemSK) Result) (qCreate : Nat)
    (bounded : work.IsQueryBoundP (IsCreate (ambient := ambient) (KemSK := KemSK)) qCreate)
    (noReveal : work.IsQueryBoundP (IsReveal (ambient := ambient) (KemSK := KemSK)) 0)
    (before : State Auxiliary KemSK) (clear : before.2.exhausted = false)
    (room : before.2.created + qCreate ≤ pairs.length) :
    Prod.map id (project pairs) <$>
      (((simulateQ (stopped baseImpl kem other selected pairs) work).run).run before) =
    (fun result => (some result.1, result.2)) <$>
      (simulateQ (reserved baseImpl kem other pairs) work).run (project pairs before) := by
  induction work using OracleComp.inductionOn generalizing qCreate before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [isQueryBoundP_query_bind_iff] at bounded noReveal
    have quiet : ¬IsReveal query := noReveal.1.resolve_right (Nat.not_lt_zero _)
    have affordable : before.2.created + (if IsCreate query then 1 else 0) ≤ pairs.length := by
      split_ifs with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega
    have sameHead := congrArg (fun work => work >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun reply =>
          (fun output => (some output.1, output.2)) <$>
            (simulateQ (reserved baseImpl kem other pairs) (next reply)).run result.2))
      (step_source baseImpl kem other selected pairs query before quiet affordable)
    simp only [bind_map_left, Prod.map_def, id_eq, Option.elim_some] at sameHead
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
    refine Eq.trans ?_ sameHead
    apply bind_congr_of_forall_mem_support
    rintro ⟨answer, after⟩ supported
    have present := step_answer baseImpl kem other selected pairs query before quiet affordable (answer, after) supported
    have capacity := step_capacity baseImpl kem other selected pairs query before clear affordable (answer, after) supported
    dsimp only at capacity
    cases answer with
    | none => exact False.elim (Bool.noConfusion present)
    | some answer =>
      have tailRoom : after.2.created + (if IsCreate query then qCreate - 1 else qCreate) ≤ pairs.length := by
        split_ifs at capacity ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      exact ih answer _ (bounded.2 answer) (by simpa using noReveal.2 answer) after capacity.1 tailRoom

end BeaconcryptCore.Computational.RegistrationNativeKemPoolSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPoolSource.step_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPoolSource.step_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPoolSource.step_capacity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPoolSource.step_capacity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemPoolSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemPoolSource.program_source

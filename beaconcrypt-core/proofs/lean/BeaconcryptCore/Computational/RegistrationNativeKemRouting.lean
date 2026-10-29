-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemCut

/-! Public accept ordinals count rejected authentication attempts as well as successful agreements. The selected accept can expose its actual getter while every other accept routes encapsulation to an ordinary public service. This translation preserves the complete real native source state; the selected cut ordinal is therefore independent of the number of earlier successful KEM callbacks. -/

open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemRouting
open PqxdhKemIndCca
open RegistrationNativeKemInterface (Spec EncapsulationSpec)
variable {κ ι KemSK Auxiliary Result : Type} {ambient : OracleSpec κ} {base : OracleSpec ι}

/-- Public encapsulation has no access to the private indexed pool. -/
noncomputable def publicAmbient (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) :
    QueryImpl (ambient + EncapsulationSpec) (StateT Auxiliary ProbComp)
  | .inl query => other query
  | .inr key => StateT.lift
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps key))

/-- The caller chooses this flag from the public accept ordinal before executing that accept's actual controller. -/
def route (selected : Bool) : QueryImpl (Spec ambient KemSK)
    (OracleComp (Spec (ambient + EncapsulationSpec) KemSK))
  | .inl query => (Spec (ambient + EncapsulationSpec) KemSK).query (.inl (.inl query))
  | .inr (.inl query) => (Spec (ambient + EncapsulationSpec) KemSK).query (.inr (.inl query))
  | .inr (.inr key) => if selected then
      (Spec (ambient + EncapsulationSpec) KemSK).query (.inr (.inr key))
    else (Spec (ambient + EncapsulationSpec) KemSK).query (.inl (.inr key))

/-- Both routes are the actual same real callback on all public, private-pool and encapsulation queries. -/
theorem query_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Bool)
    (query : (Spec ambient KemSK).Domain)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (RegistrationNativeKemInterface.source baseImpl kem (ambient + EncapsulationSpec)
      (publicAmbient baseImpl kem other)) (route selected query)).run before =
      (RegistrationNativeKemInterface.source baseImpl kem ambient other query).run before := by
  rcases query with query | (query | key)
  · simp only [route, simulateQ_spec_query]
    rfl
  · simp only [route, simulateQ_spec_query]
    rfl
  · cases selected <;>
      simp only [route, Bool.false_eq_true, ite_false, ite_true, simulateQ_spec_query,
        RegistrationNativeKemInterface.source, publicAmbient, StateT.run]
    · simp only [StateT.lift, bind_pure_comp, Functor.map_map]
      rfl

/-- Routing an arbitrary complete actual program preserves every output, local effect and private key/history coordinate. -/
theorem program_source (baseImpl : QueryImpl base ProbComp)
    (kem : MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp)) (selected : Bool)
    (work : OracleComp (Spec ambient KemSK) Result)
    (before : Auxiliary × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (RegistrationNativeKemInterface.source baseImpl kem (ambient + EncapsulationSpec)
      (publicAmbient baseImpl kem other)) (simulateQ (route selected) work)).run before =
      (simulateQ (RegistrationNativeKemInterface.source baseImpl kem ambient other) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        query_source]
      congr 1
      funext result
      exact ih result.1 result.2

def IsExposed : (Spec (ambient + EncapsulationSpec) KemSK).Domain → Prop
  | .inr (.inr _) => True
  | _ => False

instance : DecidablePred (IsExposed (ambient := ambient) (KemSK := KemSK)) := fun query => by
  rcases query with query | (query | key)
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable True)

/-- A nonselected accept can execute any number of actual public encapsulations without contributing a selected-cut callback. -/
theorem ordinary_step (query : (Spec ambient KemSK).Domain) :
    (route (ambient := ambient) (KemSK := KemSK) false query).IsQueryBoundP
      (IsExposed (ambient := ambient) (KemSK := KemSK)) 0 := by
  rcases query with query | (query | key)
  all_goals simp [route, IsExposed, isQueryBoundP_query_iff]

/-- Rejected authentication attempts and arbitrary ordinary agreement work cannot move the selected encapsulation cut. -/
theorem ordinary_program (work : OracleComp (Spec ambient KemSK) Result) :
    (simulateQ (route (ambient := ambient) (KemSK := KemSK) false) work).IsQueryBoundP
      (IsExposed (ambient := ambient) (KemSK := KemSK)) 0 := by
  exact OracleComp.IsQueryBoundP.simulateQ_of_step (OracleComp.isQueryBoundP_false work 0)
    (fun _ impossible => impossible.elim) (fun query _ => ordinary_step query)

end BeaconcryptCore.Computational.RegistrationNativeKemRouting

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRouting.query_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRouting.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRouting.program_source' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRouting.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRouting.ordinary_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRouting.ordinary_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemRouting.ordinary_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemRouting.ordinary_program

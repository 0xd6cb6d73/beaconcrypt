import BeaconcryptCore.Computational.PqxdhKemCoordinateController
import BeaconcryptCore.Computational.PqxdhLiveKemReservation

/-!
Authentication-only generation control exposes a fresh indexed creation origin and an optional public key, never a secret key. Concrete control runs the actual KEM generator in source order and retains the complete joint identity/KEM services. Arbitrary control replies, including failure and aliased public keys, strengthen the authentication observer; this is neither a KEM secrecy assumption nor a claim that generation is free.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhKemCreationController
open PqxdhKemIndCca PqxdhLiveKemBirth
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Result : Type}

/-- The request is the public fresh creation index. The reply can be arbitrary public-key bytes or a failure in the strengthened interface. -/
abbrev GenerationSpec : OracleSpec Nat := fun _ => Option MlKem768PublicKey
abbrev Observation := Nat × Option MlKem768PublicKey
abbrev ObservedState (KemSK : Type) := PqxdhLiveKemBirth.State KemSK × List Observation

/-- The private interpreter runs the actual generator and records its exact optional public reply. It never adds the private key to the generation observation. -/
def concrete (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    QueryImpl GenerationSpec (StateT (ObservedState KemSK) ProbComp) := fun origin state =>
  (fun result => (some result.1.2, (result.2, state.2 ++ [(origin, some result.1.2)]))) <$>
    ((PqxdhLiveKemBirth.impl baseImpl primitives kem (.inr (.inr .create))).run state.1)

/-- Only the newly returned public key is controller-selected. The exact next source index identifies the request; a controller failure stops before supplying a native constructor reply. -/
def controlled (controller : QueryImpl GenerationSpec (StateT (ObservedState KemSK) ProbComp))
    (native : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (StateT (PqxdhLiveKemBirth.State KemSK) ProbComp)) :
    QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (OptionT (StateT (ObservedState KemSK) ProbComp)) :=
  fun query => OptionT.mk fun state => match query with
  | .inr (.inr .create) =>
      (fun result => (result.1.map (fun key => (state.1.2.keys.length, key)), result.2)) <$>
        (controller state.1.2.keys.length).run state
  | query => (fun result => (some result.1, (result.2, state.2))) <$> (native query).run state.1

set_option backward.isDefEq.respectTransparency false in
/-- One source operation retains its exact optional reply and complete joint private state. Generation reveals only the exact added public audit; all source generator work still executes. -/
theorem step_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (state : ObservedState KemSK) :
    (fun result => (result.1, result.2.1)) <$>
      (((controlled (concrete baseImpl primitives kem) (PqxdhLiveKemBirth.impl baseImpl primitives kem) query).run).run state) =
        (fun result => (some result.1, result.2)) <$>
          (PqxdhLiveKemBirth.impl baseImpl primitives kem query).run state.1 := by
  rcases query with query | (query | query)
  case inl => simp only [controlled, OptionT.run_mk, StateT.run, Functor.map_map]
  case inr.inl => simp only [controlled, OptionT.run_mk, StateT.run, Functor.map_map]
  case inr.inr =>
    cases query <;> simp only [controlled, concrete, OptionT.run_mk, StateT.run, Functor.map_map,
      PqxdhLiveKemBirth.impl, PqxdhLiveKemBirth.poolImpl, PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, Option.map_some, Functor.map_map]

set_option backward.isDefEq.respectTransparency false in
/-- Concrete generation control preserves the entire adaptive joint/KEM program, after erasing only its added public generation audit. The optional controller failure branch is unreachable for the correct source generator. -/
theorem program_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : ObservedState KemSK) :
    (fun result => (result.1, result.2.1)) <$>
      (((simulateQ (controlled (concrete baseImpl primitives kem) (PqxdhLiveKemBirth.impl baseImpl primitives kem)) client).run).run state) =
        (fun result => (some result.1, result.2)) <$>
          (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem) client).run state.1 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      let native := PqxdhLiveKemBirth.impl baseImpl primitives kem
      let observed := controlled (concrete baseImpl primitives kem) native
      let followingSource : Option ((PqxdhLiveKemBirth.Spec KemSK).Range query) × PqxdhLiveKemBirth.State KemSK →
          ProbComp (Option Result × PqxdhLiveKemBirth.State KemSK) := fun result => match result.1 with
        | none => pure (none, result.2)
        | some answer => (fun result => (some result.1, result.2)) <$> (simulateQ native (next answer)).run result.2
      have following (result : Option ((PqxdhLiveKemBirth.Spec KemSK).Range query) × ObservedState KemSK) :
          (fun result => (result.1, result.2.1)) <$>
            ((result.1.elim (pure none) (fun answer => (simulateQ observed (next answer)).run)).run result.2) =
              followingSource (result.1, result.2.1) := by
        rcases result with ⟨none | answer, after⟩
        · rfl
        · exact ih answer after
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
      change (((observed query).run).run state >>= fun result =>
        (fun result => (result.1, result.2.1)) <$>
          ((result.1.elim (pure none) (fun answer => (simulateQ observed (next answer)).run)).run result.2)) = _
      simp only [following]
      rw [← bind_map_left]
      rw [show (fun result => (result.1, result.2.1)) <$> (((observed query).run).run state) =
        (fun result => (some result.1, result.2)) <$> (native query).run state.1
        from step_source baseImpl primitives kem query state]
      simp only [bind_map_left, followingSource, native]

/-- The exact original sampling bill survives creation control, including every failed earlier source path. This equality concerns syntactic oracle computations, not merely output distributions. -/
theorem uniform_iff (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (state : ObservedState KemSK) (q : Nat) :
    (((simulateQ (controlled (concrete baseImpl primitives kem) (PqxdhLiveKemBirth.impl baseImpl primitives kem)) client).run).run state).IsTotalQueryBound q ↔
      ((simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem) client).run state.1).IsTotalQueryBound q := by
  have equal := congrArg (fun work => work.IsTotalQueryBound q) (program_source baseImpl primitives kem client state)
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using Iff.of_eq equal

/-- The literal owner constructor keeps the source identity/prekey/KEM sampling order, full private joint service and generated pool, while publishing only the indexed KEM public key. -/
theorem constructor_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec) (state : ObservedState KemSK) :
    (fun result => (result.1, result.2.1)) <$>
      (((simulateQ (controlled (concrete baseImpl primitives kem) (PqxdhLiveKemBirth.impl baseImpl primitives kem))
        (PqxdhLiveKemBirth.create baseImpl setup)).run).run state) = (do
          let value ← PqxdhLiveBeaconBirth.create baseImpl primitives kem setup
          pure (some (some (PqxdhLiveKemBirth.handle primitives state.1.1.seeds.length state.1.2.keys.length value)),
            ((PqxdhDynamicIdentityPool.createdReply primitives state.1.1 value.seed).2,
              (PqxdhLiveKemBirth.created state.1.2 (value.target, value.secret)).2))) := by
  rw [program_source, PqxdhLiveKemBirth.create_source]
  simp only [map_bind, map_pure]

set_option backward.isDefEq.respectTransparency false in
/-- Honest generation records precisely the current fresh index and generated public key, while retaining the generated secret solely in the original private pool. -/
theorem generation_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (state : ObservedState KemSK) :
    (concrete baseImpl primitives kem state.1.2.keys.length).run state =
      (fun pair => (some pair.1,
        ((state.1.1, (PqxdhLiveKemBirth.created state.1.2 pair).2),
          state.2 ++ [(state.1.2.keys.length, some pair.1)]))) <$>
        simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen := by
  simp only [concrete, StateT.run, PqxdhLiveKemBirth.impl, PqxdhLiveKemBirth.poolImpl,
    Functor.map_map, PqxdhLiveKemBirth.created]

end BeaconcryptCore.Computational.PqxdhKemCreationController

/-- info: 'BeaconcryptCore.Computational.PqxdhKemCreationController.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCreationController.step_source
/-- info: 'BeaconcryptCore.Computational.PqxdhKemCreationController.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCreationController.program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhKemCreationController.uniform_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCreationController.uniform_iff
/-- info: 'BeaconcryptCore.Computational.PqxdhKemCreationController.constructor_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCreationController.constructor_source
/-- info: 'BeaconcryptCore.Computational.PqxdhKemCreationController.generation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCreationController.generation_source

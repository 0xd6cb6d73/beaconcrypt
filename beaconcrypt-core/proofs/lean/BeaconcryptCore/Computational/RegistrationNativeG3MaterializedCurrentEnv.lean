-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedFrontendBuild
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconComplete

/-! Server compilation owns its current Env receipt list, while the mixed private interpreter retains a separate publication receipt list. Reassociating that private list with the key-service state gives the concrete Server interface without merging either receipt coordinate. The comparison excludes direct private publication callbacks; actual inlined Server compilation derives that footprint separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnv
open RegistrationNativeG3MaterializedFrontend (State ServiceSpec)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedBeaconComplete (localImpl)
variable {n : Nat} {KemSK KeyState Value : Type}

abbrev Moved (n : Nat) (KeyState : Type) := (KeyState × List RegistrationSigningShared.Receipt) × PqxdhRecordLiftWorld.State n

def move (before : State n KeyState) : Moved n KeyState := ((before.1, before.2.1), before.2.2)
def back (before : Moved n KeyState) : State n KeyState := (before.1.1, (before.1.2, before.2))

def keys (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp)) :
    QueryImpl (ServiceSpec n) (StateT (KeyState × List RegistrationSigningShared.Receipt) ProbComp) := fun message before =>
  (fun result => (result.1, (result.2, before.2))) <$> (service message).run before.1

def fallback (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp)) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (Moved n KeyState) ProbComp) := fun query before =>
  Prod.map id move <$> (implementation query).run (back before)

def Allowed : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain → Prop
  | .inr (.inl (.inr (.inl _))) => False
  | _ => True

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Reassociation preserves every concrete demand, environment and fallback callback while leaving the current caller Env outside this private frame. -/
theorem query_source (full : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) (allowed : Allowed (KemSK := KemSK) query)
    (before : State n KeyState) :
    Prod.map id move <$> (localImpl full source writer sign seeds service implementation query).run before =
      (RegistrationNativeG3MaterializedFrontendInterface.interface full seeds (keys service) (fallback implementation) query).run
        (move before) := by
  rcases query with message | (message | (publication | effect)) | kem
  · rfl
  · cases full <;>
      simp only [localImpl, RegistrationNativeG3MaterializedBeaconComplete.paired,
        RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
        RegistrationNativeG3MaterializedFrontend.keys, RegistrationNativeG3MaterializedFrontendInterface.interface,
        RegistrationNativeG3MaterializedFrontendInterface.keys, keys, state_map_apply, StateT.run,
        Bool.false_eq_true, ite_true, ite_false, Functor.map_map, Prod.map_def, id_eq, move]
  · exact allowed.elim
  · cases effect with
    | inl coin => cases full <;> simp only [localImpl, RegistrationNativeG3MaterializedBeaconComplete.paired,
        RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
        RegistrationNativeG3MaterializedFrontend.common, RegistrationNativeG3Common.handler,
        RegistrationNativeG3MaterializedCommon.handler, RegistrationNativeG3Common.effect,
        RegistrationNativeG3MaterializedCommon.effect, RegistrationNativeG3MaterializedFrontendInterface.interface,
        RegistrationNativeG3MaterializedFrontendInterface.effect, StateT.run,
        Bool.false_eq_true, ite_true, ite_false, Functor.map_map, Prod.map_def, id_eq, move]
    | inr capability =>
        cases capability
        all_goals try (solve | cases full <;> simp only [localImpl, RegistrationNativeG3MaterializedBeaconComplete.paired,
        RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
        RegistrationNativeG3MaterializedFrontend.common, RegistrationNativeG3Common.handler,
        RegistrationNativeG3MaterializedCommon.handler, RegistrationNativeG3Common.effect,
        RegistrationNativeG3MaterializedCommon.effect, RegistrationNativeG3MaterializedFrontendInterface.interface,
        RegistrationNativeG3MaterializedFrontendInterface.effect, StateT.run,
        Bool.false_eq_true, ite_true, ite_false, Functor.map_map, Prod.map_def, id_eq, move])
        case installServer keyId binding tag =>
          cases tag <;> cases full <;> simp only [localImpl, RegistrationNativeG3MaterializedBeaconComplete.paired,
        RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
        RegistrationNativeG3MaterializedFrontend.common, RegistrationNativeG3Common.handler,
        RegistrationNativeG3MaterializedCommon.handler, RegistrationNativeG3Common.effect,
        RegistrationNativeG3MaterializedCommon.effect, RegistrationNativeG3MaterializedFrontendInterface.interface,
        RegistrationNativeG3MaterializedFrontendInterface.effect, StateT.run,
        Bool.false_eq_true, ite_true, ite_false, Functor.map_map, Prod.map_def, id_eq, move]
          rfl
        case installBeacon owner shell tag =>
          cases tag <;> cases full <;> simp only [localImpl, RegistrationNativeG3MaterializedBeaconComplete.paired,
        RegistrationNativeG3MaterializedFrontend.known, RegistrationNativeG3MaterializedFrontend.thin,
        RegistrationNativeG3MaterializedFrontend.common, RegistrationNativeG3Common.handler,
        RegistrationNativeG3MaterializedCommon.handler, RegistrationNativeG3Common.effect,
        RegistrationNativeG3MaterializedCommon.effect, RegistrationNativeG3MaterializedFrontendInterface.interface,
        RegistrationNativeG3MaterializedFrontendInterface.effect, StateT.run,
        Bool.false_eq_true, ite_true, ite_false, Functor.map_map, Prod.map_def, id_eq, move]
          rfl

  · rfl

/-- The receipt-preserving reassociation composes through every actual local program with the derived direct-publication footprint. -/
theorem program_source (full : Bool) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value)
    (allowed : AllQueriesSatisfy work (Allowed (KemSK := KemSK))) (before : State n KeyState) :
    Prod.map id move <$> (simulateQ (localImpl full source writer sign seeds service implementation) work).run before =
      (simulateQ (RegistrationNativeG3MaterializedFrontendInterface.interface full seeds (keys service) (fallback implementation))
        work).run (move before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_def, id_eq]
  | query_bind query next ih =>
      obtain ⟨current, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      rw [← query_source full source writer sign seeds service implementation query current before]
      simp only [bind_map_left]
      apply bind_congr
      intro reached
      exact ih reached.1 (later reached.1) reached.2

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnv
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnv.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnv.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnv.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCurrentEnv.program_source

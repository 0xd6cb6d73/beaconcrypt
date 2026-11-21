-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceSource

/-! The literal native trace is preserved at the actual checked source callback positions. Private Unit audits carry preparation and demand even when optional input checks fail; the unchanged residual callbacks carry installation attempts, successful insertion and evaluated encapsulation replies. These equations permit an audited whole frontend source proof to transport the complete original native trace. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative
open RegistrationNativeSecretWordCheckedFrontend (erase native implementation realization localLift)
open RegistrationNativeSecretWordCheckedTrace (handler)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {n : Nat} {KemSK Value : Type}

private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (first : StateT S m A) (next : A → StateT S m B) (before : S) :
    (first >>= next) before = (first before >>= fun reached => next reached.1 reached.2) := rfl

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

/-- Every actual native callback yields exactly its original chronological trace under the concrete audited checked source. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : RegistrationNativeG2Trace.State) :
    simulateQ (erase ∘ₛ native source inside candidate input)
        ((RegistrationNativeG2Trace.handler query).run before) =
      (simulateQ (handler candidate) (native source inside candidate input query)).run before := by
  rcases query with (message | (message | common) | kem) | record
  · simp only [RegistrationNativeG2Trace.handler, StateT.run, RegistrationNativeG2Trace.begin,
      RegistrationNativeG2Trace.finish, simulateQ_map, simulateQ_spec_query, QueryImpl.compose,
      native, realization, implementation, RegistrationNativeSecretWordChecked.preparation,
      RegistrationNativeSecretWordChecked.audit, simulateQ_bind, simulateQ_pure, localLift,
      state_bind_apply, state_map_apply,
      pure_bind, erase, map_pure, Prod.map_def, id_eq]
    rfl
  · simp only [native, QueryImpl.compose, realization, simulateQ_spec_query, implementation]
    rw [RegistrationNativeSecretWordCheckedTraceSource.material_source]
    simp only [RegistrationNativeG2Trace.handler, StateT.run, RegistrationNativeG2Trace.begin,
      RegistrationNativeG2Trace.finish, simulateQ_map, simulateQ_spec_query, QueryImpl.compose,
      realization, implementation, RegistrationNativeSecretWordCheckedTrace.begin,
      RegistrationNativeSecretWordMessage.eval_literal]
    rfl
  · rcases common with publication | environment
    · rfl
    · rcases environment with coin | capability
      · rfl
      · cases capability <;>
          simp only [RegistrationNativeG2Trace.handler, StateT.run, RegistrationNativeG2Trace.begin,
            RegistrationNativeG2Trace.finish, simulateQ_map, simulateQ_spec_query, QueryImpl.compose,
            native, realization, implementation, handler, erase, RegistrationNativeSecretWordCheckedTrace.begin,
            RegistrationNativeSecretWordCheckedTrace.finish] <;> rfl
  · rcases kem with (other | key) | (pool | key)
    · rfl
    · simp only [RegistrationNativeG2Trace.handler, StateT.run, RegistrationNativeG2Trace.begin,
        RegistrationNativeG2Trace.finish, simulateQ_map, simulateQ_spec_query, QueryImpl.compose,
        native, realization, implementation, erase,
        RegistrationNativeSecretWordKemInterface.realize,
        RegistrationNativeSecretWordInterface.routedKem, Functor.map_map, Prod.map_def, id_eq]
      rfl
    · cases pool <;> rfl
    · simp only [RegistrationNativeG2Trace.handler, StateT.run, RegistrationNativeG2Trace.begin,
        RegistrationNativeG2Trace.finish, simulateQ_map, simulateQ_spec_query, QueryImpl.compose,
        native, realization, implementation, erase,
        RegistrationNativeSecretWordKemInterface.realize,
        RegistrationNativeSecretWordInterface.routedKem, Functor.map_map, Prod.map_def, id_eq]
      rfl
  · rfl

/-- Arbitrary adaptive literal native execution transports the entire actual G2 trace through the audited source, with no trace correspondence premise. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value) (before : RegistrationNativeG2Trace.State) :
    simulateQ (erase ∘ₛ native source inside candidate input)
        ((simulateQ RegistrationNativeG2Trace.handler work).run before) =
      (simulateQ (handler candidate) (simulateQ (native source inside candidate input) work)).run before := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, ← QueryImpl.simulateQ_compose]
  have step : ∀ query current, Prod.map id id <$>
      (((erase ∘ₛ native (n := n) (KemSK := KemSK) source inside candidate input).mapStateTBase
        RegistrationNativeG2Trace.handler) query).run current =
      ((handler candidate ∘ₛ native source inside candidate input) query).run (id current) := by
    intro query current
    simpa only [QueryImpl.mapStateTBase, QueryImpl.compose, StateT.run, StateT.mk, Prod.map_def, id_eq, id_map'] using
      (query_source (n := n) (KemSK := KemSK) source inside candidate input query current)
  have result := OracleComp.map_run_simulateQ_eq_of_query_map_eq
    ((erase ∘ₛ native source inside candidate input).mapStateTBase RegistrationNativeG2Trace.handler)
    (handler candidate ∘ₛ native source inside candidate input) id
    step work before
  simpa only [Prod.map_def, id_eq, id_map'] using result

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedTraceNative.program_source

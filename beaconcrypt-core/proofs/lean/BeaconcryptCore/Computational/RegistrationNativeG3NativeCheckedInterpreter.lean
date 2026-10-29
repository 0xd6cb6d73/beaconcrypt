-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordNativePlainInterface

/-! Closing the original retained compiler through its actual native KEM provider and the unchecked native service yields the full native plain interpreter with an additive preparation audit. Every ordinary, provider and audit state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordNativePlain (NativeFrame NativeProvider)
open RegistrationNativeG3NativeChecked (State unchecked)
open RegistrationNativeKeyCompiler (KeySpec)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

def close (provider : NativeProvider KemSK ProviderState) :
    QueryImpl (RegistrationNativeOpenRetained.Spec KemSK)
      (StateT ProviderState (OracleComp RegistrationNativeRetainedService.Spec))
  | .inl query => StateT.lift (RegistrationNativeRetainedService.Spec.query query)
  | .inr query => fun before => simulateQ RegistrationNativePublicRetained.coins ((provider query).run before)

def project (result : ((Value × RegistrationNativePublicInterpreter.State n KemSK) × ProviderState) × State) :
    Value × (State × NativeFrame n KemSK ProviderState) :=
  (result.1.1.1, (result.2, (result.1.1.2, result.1.2)))

noncomputable def compiled (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (State × NativeFrame n KemSK ProviderState) (OracleComp KeySpec)) := fun query before =>
  project <$> (simulateQ (unchecked setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside target))
    ((simulateQ (close provider)
      ((RegistrationNativeOpenRetained.compiler setup wire route sign query).run before.2.1)).run before.2.2)).run before.1

noncomputable def observed (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK)
      (StateT (State × NativeFrame n KemSK ProviderState) (OracleComp KeySpec)) := fun query before =>
  (fun result => (result.1, (RegistrationNativeG3NativeCheckedTrace.nativeStep
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) query before.1, result.2))) <$>
    (RegistrationNativeSecretWordNativePlain.native setup wire route sign seed scalar target provider query).run before.2

/-- Closing the base branch preserves the actual full provider state through arbitrary retained-service work. -/
theorem base_program (provider : NativeProvider KemSK ProviderState)
    (work : OracleComp RegistrationNativeRetainedService.Spec Value) (before : ProviderState) :
    (simulateQ (close provider) (simulateQ RegistrationNativeOpenRetained.baseLift work)).run before =
      (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : close provider ∘ₛ RegistrationNativeOpenRetained.baseLift =
      (QueryImpl.ofLift RegistrationNativeRetainedService.Spec (OracleComp RegistrationNativeRetainedService.Spec)).liftTarget
        (StateT ProviderState (OracleComp RegistrationNativeRetainedService.Spec)) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem base_apply (provider : NativeProvider KemSK ProviderState)
    (work : OracleComp RegistrationNativeRetainedService.Spec Value) (before : ProviderState) :
    simulateQ (close provider) (simulateQ RegistrationNativeOpenRetained.baseLift work) before =
      (fun value => (value, before)) <$> work := base_program provider work before

/-- Original uniform queries preserve both native flags and the sticky marker under the exact original coin compiler. -/
theorem coins_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : ProbComp Value) (before : State) :
    (simulateQ (unchecked source input inside)
      (simulateQ RegistrationNativePublicRetained.coins work)).run before =
        (fun value => (value, before)) <$> simulateQ RegistrationNativeKeyCompiler.coins work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : unchecked source input inside ∘ₛ RegistrationNativePublicRetained.coins =
      RegistrationNativeKeyCompiler.coins.liftTarget (StateT State (OracleComp KeySpec)) := by
    funext query current
    simp only [QueryImpl.compose, RegistrationNativePublicRetained.coins, simulateQ_spec_query,
      unchecked, RegistrationNativeG3NativeChecked.plain, RegistrationNativeG3NativeChecked.bad, QueryImpl.liftTarget,
      Bool.or_false]
    rfl
  rw [same, simulateQ_liftTarget]
  change (simulateQ RegistrationNativeKeyCompiler.coins work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

private theorem coins_apply (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : RegistrationNativeRelatedFamily.Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : ProbComp Value) (before : State) :
    simulateQ (unchecked source input inside)
      (simulateQ RegistrationNativePublicRetained.coins work) before =
        (fun value => (value, before)) <$> simulateQ RegistrationNativeKeyCompiler.coins work :=
  coins_source source input inside work before

private theorem state_map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (map : A → B) (work : StateT S m A) (before : S) :
    (map <$> work) before = Prod.map map id <$> work before := StateT.run_map map work before

private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = work before >>= fun result => next result.1 result.2 := rfl

private theorem state_pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value, before) := rfl

private theorem state_lift_apply {S A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m A) (before : S) :
    (StateT.lift work : StateT S m A) before = (fun value => (value, before)) <$> work := by
  change (work >>= fun value => pure (value, before)) = _
  exact bind_pure_comp _ _

/-- Every original compiler callback agrees with the literal native full-state interpreter and its actual pre-query audit update. -/
theorem query_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) (before : State × NativeFrame n KemSK ProviderState) :
    (compiled setup wire route sign seed scalar target provider query).run before =
      (observed setup wire route sign seed scalar target provider query).run before := by
  change compiled setup wire route sign seed scalar target provider query before =
    observed setup wire route sign seed scalar target provider query before
  rcases query with (prepare | (demand | common) | kem) | record
  all_goals simp only [compiled, observed, RegistrationNativeOpenRetained.compiler,
    RegistrationNativeSecretWordNativePlain.native, StateT.run_lift]
  case inl.inr.inl.inr =>
    simp only [RegistrationNativeOpenRetained.ordinary, StateT.run, simulateQ_map, state_map_apply,
      base_apply, RegistrationNativePublicRetained.ordinary, coins_apply,
      RegistrationNativeSecretWordNativePlain.ordinary,
      RegistrationNativeG3NativeCheckedTrace.nativeStep, Functor.map_map, project, Prod.map_def, id_eq]
  case inr =>
    simp only [RegistrationNativeOpenRetained.ordinary, StateT.run, simulateQ_map, state_map_apply,
      base_apply, RegistrationNativePublicRetained.ordinary, coins_apply,
      RegistrationNativeSecretWordNativePlain.ordinary,
      RegistrationNativeG3NativeCheckedTrace.nativeStep, Functor.map_map, project, Prod.map_def, id_eq]
  all_goals simp only [StateT.run, simulateQ_bind, simulateQ_map, simulateQ_pure,
    simulateQ_spec_query, RegistrationNativeOpenRetained.baseLift, RegistrationNativeOpenRetained.kemLift,
    close, Functor.map_map,
    RegistrationNativeG3NativeCheckedTrace.nativeStep, RegistrationNativeG3NativeCheckedTrace.event,
    pure_bind, map_pure]
  all_goals simp only [state_bind_apply, state_pure_apply, state_lift_apply, state_map_apply,
    simulateQ_map, simulateQ_spec_query, Functor.map_map,
    unchecked, RegistrationNativeG3NativeChecked.plain, RegistrationNativeG3NativeChecked.bad,
    StateT.run, project, Prod.map_def, id_eq, bind_pure_comp, map_pure, Bool.or_false, coins_apply]
  all_goals try rfl
  cases formed : RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar demand with
  | none => simp only [map_pure]; rfl
  | some bytes =>
      cases guarded : RegistrationNativeKeyFamilyPreparation.inside target bytes <;>
        simp only [RegistrationNativeSecretWordNativeMaterial.material, guarded, Bool.false_eq_true,
          ite_false, ite_true, Functor.map_map, map_pure]
      all_goals rfl
noncomputable def providerCompiler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (provider : NativeProvider KemSK ProviderState) :=
  ((close provider).mapStateTBase (RegistrationNativeOpenRetained.compiler (n := n) setup wire route sign)).flattenStateT

noncomputable def source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState) :=
  ((unchecked setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside target)).mapStateTBase
    (providerCompiler (n := n) setup wire route sign provider)).flattenStateT

def reassociate (before : NativeFrame n KemSK ProviderState × State) : State × NativeFrame n KemSK ProviderState :=
  (before.2, before.1)

private theorem flattened_apply {Index₀ Index₁ Index₂ S T : Type}
    {spec₀ : OracleSpec Index₀} {spec₁ : OracleSpec Index₁} {spec₂ : OracleSpec Index₂}
    (outer : QueryImpl spec₁ (StateT T (OracleComp spec₂)))
    (inner : QueryImpl spec₀ (StateT S (OracleComp spec₁)))
    (query : spec₀.Domain) (before : S × T) :
    (outer.mapStateTBase inner).flattenStateT query before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ outer ((inner query).run before.1)).run before.2 := rfl

private theorem query_reassociate (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : NativeFrame n KemSK ProviderState × State) :
    Prod.map id reassociate <$> (source setup wire route sign seed scalar target provider query).run before =
      (observed setup wire route sign seed scalar target provider query).run (reassociate before) := by
  rw [← query_source]
  rcases before with ⟨⟨ordinary, providerState⟩, audit⟩
  simp only [source, providerCompiler, compiled, reassociate, StateT.run, flattened_apply,
    simulateQ_map, state_map_apply, Functor.map_map,
    Prod.map_def, id_eq]
  rfl

/-- The complete original compiler and actual provider preserve every output and private state under the explicit state reassociation. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : NativeFrame n KemSK ProviderState × State) :
    Prod.map id reassociate <$> (simulateQ (source setup wire route sign seed scalar target provider) work).run before =
      (simulateQ (observed setup wire route sign seed scalar target provider) work).run (reassociate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ reassociate
    (query_reassociate setup wire route sign seed scalar target provider) work before

/-- The literal three-stage retained-service execution equals the native full-state interpreter with its additive audit. -/
theorem nested_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : Option PqxdhJointIdentity.DhOutput) (provider : NativeProvider KemSK ProviderState)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (ordinary : RegistrationNativePublicInterpreter.State n KemSK) (providerState : ProviderState) (audit : State) :
    project <$> (simulateQ (unchecked setup.source (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside target))
      ((simulateQ (close provider)
        ((simulateQ (RegistrationNativeOpenRetained.compiler setup wire route sign) work).run ordinary)).run providerState)).run audit =
      (simulateQ (observed setup wire route sign seed scalar target provider) work).run (audit, (ordinary, providerState)) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (close provider)
    (RegistrationNativeOpenRetained.compiler setup wire route sign) work ordinary providerState,
    simulateQ_map, StateT.run_map,
    OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  calc
    _ = Prod.map id reassociate <$>
        (simulateQ (source setup wire route sign seed scalar target provider) work).run ((ordinary, providerState), audit) := by
      simp only [source, providerCompiler, reassociate, Functor.map_map, project, Prod.map_def, id_eq]
    _ = _ := program_source setup wire route sign seed scalar target provider work ((ordinary, providerState), audit)

end BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.base_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.base_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.coins_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.coins_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.nested_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeCheckedInterpreter.nested_source

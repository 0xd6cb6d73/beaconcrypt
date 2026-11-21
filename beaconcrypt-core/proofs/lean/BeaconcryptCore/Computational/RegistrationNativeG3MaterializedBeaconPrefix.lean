-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconComplete
import BeaconcryptCore.Computational.RegistrationNativePublicOwners

/-! Actual mandatory response authentication and selected-prekey preparation reach no material demand or hidden installation. The stronger finite footprint below derives exact known/thin interpreter equality for the entire real prefix, including all failures and the complete current environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeG3KnownWorldFrameCommon (EffectAllowed)
open RegistrationNativeG3MaterializedBeaconComplete (localImpl paired)
open RegistrationNativeG3MaterializedFrontend (ServiceSpec State)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeHiddenAllocationCore (simulation mapped)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}
def Compatible : (Spec n KemSK).Domain → Prop
  | .inr (.inl (.inl _)) => False
  | .inr (.inl (.inr (.inr query))) => EffectAllowed query
  | _ => True

local notation "Safe" => Compatible (n := n) (KemSK := KemSK)

private theorem every {Index : Type} {spec : OracleSpec Index} (work : OracleComp spec Value) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial, ih⟩

private theorem run_safe {Index S : Type} {spec : OracleSpec Index}
    (impl : QueryImpl spec (StateT S (OracleComp (Spec n KemSK))))
    (step : ∀ query before, AllQueriesSatisfy ((impl query).run before) Safe)
    (work : OracleComp spec Value) (before : S) :
    AllQueriesSatisfy ((simulateQ impl work).run before) Safe := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (step query before) (fun result => ih result.1 result.2)

private theorem effect_safe (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (safe : AllQueriesSatisfy work EffectAllowed) :
    AllQueriesSatisfy (simulateQ (effect (KemSK := KemSK)) work) Safe :=
  simulation effect EffectAllowed Safe (fun _query allowed => (allQueriesSatisfy_query_iff _ _).mpr allowed) work safe

private theorem sample_safe (work : ProbComp Value) :
    AllQueriesSatisfy (sample (n := n) (KemSK := KemSK) work) Safe := by
  unfold sample
  apply simulation (fun query => effect (n := n) (KemSK := KemSK) (.inl query)) (fun _ => True) Safe _ work (every work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr (by simp [Compatible, EffectAllowed])

private theorem primitive_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementShared.PrimitiveSpec.Domain) :
    AllQueriesSatisfy (primitive (n := n) setup owner oneTime query) Safe := by
  unfold primitive
  apply simulation _ (fun _ => True) Safe _ _ (every _)
  intro query _
  cases query with
  | inl query => exact sample_safe _
  | inr query => exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem backend_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (query : RegistrationAgreementExecutor.Spec.Domain) (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((backend (n := n) setup owner oneTime query).run before) Safe := by
  simp only [backend, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift, bind_pure_comp]
  apply mapped
  cases query <;> first | exact primitive_safe setup owner oneTime _ | trivial

private theorem prefix_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (query : (PqxdhPhase2GapDhSource.PrefixSpec Unit Unit Unit Unit registration.AuthenticatedResponse).Domain)
    (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
      (RegistrationBeaconRootInterpreter.auxImpl (backend (n := n) setup owner oneTime) authenticated) visit query).run before) Safe := by
  cases query <;> simp only [PqxdhPhase2GapDhSource.prefixImpl, RegistrationBeaconRootInterpreter.auxImpl]
  all_goals first | exact run_safe _ (backend_safe setup owner oneTime) _ before | trivial

private theorem collect_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((collect (n := n) setup owner oneTime authenticated).run before) Safe := by
  unfold collect
  exact run_safe _ (prefix_safe setup owner oneTime authenticated) _ before

private theorem prepare_safe (work : OracleComp RegistrationServerReferenceRoot.PrepareSpec Value) :
    AllQueriesSatisfy (simulateQ (prepare (n := n) (KemSK := KemSK)) work) Safe :=
  simulation prepare (fun _ => True) Safe
    (fun _query _ => (allQueriesSatisfy_query_iff _ _).mpr trivial) work (every work)

private theorem agreement_safe (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((agreement (n := n) setup owner oneTime authenticated).run before) Safe := by
  simp only [agreement, StateT.run_bind]
  apply allQueriesSatisfy_bind (collect_safe setup owner oneTime authenticated before)
  intro result
  cases result.1 with
  | none => trivial
  | some pending =>
      simp only [StateT.run_lift, bind_pure_comp]
      exact mapped _ _ Safe (prepare_safe (n := n) (KemSK := KemSK) (RegistrationBeaconReferenceRoot.client authenticated pending))

private theorem authentication_safe (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    AllQueriesSatisfy (simulateQ (RegistrationAuthenticationCompiler.callbacks (n := n) crypto verify) work) EffectAllowed := by
  apply simulation _ (fun _ => True) EffectAllowed _ work (every work)
  intro query _
  cases query with
  | hash request => exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr (by exact id)) (fun _ => trivial)
  | mldsa request => trivial
  | ed25519 request => trivial

/-- The actual response authentication and selected-prekey preparation reach neither a material demand nor a hidden installation. -/
theorem preparation_compatible (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState Auxiliary) :
    AllQueriesSatisfy (((finishPreparation (n := n) setup source packet).run owner).run before) Safe := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh => trivial
  | freshWithCoins oneTime => trivial
  | established completed => trivial
  | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc]
          apply allQueriesSatisfy_bind (effect_safe _ (authentication_safe setup.source.crypto source.verify _))
          intro accepted
          cases accepted with
          | fail error => trivial
          | div => trivial
          | ok reply => cases reply with
            | Err error => trivial
            | Ok authenticated =>
                simp only [StateT.run_lift, StateT.run_map, bind_pure_comp]
                exact mapped _ _ Safe (agreement_safe setup owner oneTime authenticated before)

private theorem query_same (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    {KeyState : Type} (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (query : (Spec n KemSK).Domain) (quiet : Compatible (KemSK := KemSK) query) :
    localImpl true source writer sign seeds service fallback query = localImpl false source writer sign seeds service fallback query := by
  rcases query with message | ((message | (query | query)) | query)
  · rfl
  · exact quiet.elim
  · rfl
  · simp only [localImpl, paired, Bool.false_eq_true, ite_true, ite_false, RegistrationNativeG3MaterializedFrontend.known,
      RegistrationNativeG3MaterializedFrontend.thin, ]
    apply StateT.ext
    intro before
    change (fun result => (result.1, (before.1, result.2))) <$> (RegistrationNativeG3Common.effect query).run before.2 =
      (fun result => (result.1, (before.1, result.2))) <$> (RegistrationNativeG3MaterializedCommon.effect seeds query).run before.2
    rw [RegistrationNativeG3MaterializedFrontendKnown.effect_unchanged seeds query quiet]
  · rfl

private theorem program_same (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    {KeyState : Type} (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (work : OracleComp (Spec n KemSK) Value) (quiet : AllQueriesSatisfy work (Compatible (KemSK := KemSK))) :
    simulateQ (localImpl true source writer sign seeds service fallback) work =
      simulateQ (localImpl false source writer sign seeds service fallback) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp quiet
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [query_same source writer sign seeds service fallback query allowed]
      congr 1
      funext reply
      exact ih reply (later reply)

/-- The whole actual native preparation prefix retains its exact full owner/environment/private result under both material interpretations, without a caller-supplied source or footprint condition. -/
theorem preparation_source (setup : Setup base KemSK) (mlSource : RegistrationNativeMldsa.Source)
    (writer : RawCtxMixedShared.Writer) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    {KeyState : Type} (seeds : Seeds n) (service : QueryImpl (ServiceSpec n) (StateT KeyState ProbComp))
    (fallback : QueryImpl (Spec n KemSK) (StateT (State n KeyState) ProbComp))
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner mlSource) (env : EnvState Auxiliary) :
    simulateQ (localImpl true setup.source writer sign seeds service fallback)
        (((finishPreparation setup mlSource packet).run owner).run env) =
      simulateQ (localImpl false setup.source writer sign seeds service fallback)
        (((finishPreparation setup mlSource packet).run owner).run env) :=
  program_same setup.source writer sign seeds service fallback _ (preparation_compatible setup mlSource packet owner env)

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix.preparation_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix.preparation_compatible
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedBeaconPrefix.preparation_source

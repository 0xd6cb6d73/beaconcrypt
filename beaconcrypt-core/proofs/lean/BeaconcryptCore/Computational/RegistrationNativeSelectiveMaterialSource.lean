-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialService

/-! The normalized material service is the literal original native CommonCompiler closed by the selective interpreter. This exact current-environment diagram retains all mutable receipts and private material state; no source equality is supplied by a caller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSelectiveMaterialService (Local)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

noncomputable def closedLocal := RegistrationNativeSelectiveHiddenInterpreter.handler (n := n) setup wire sign seed scalar candidate provider ∘ₛ
  RegistrationNativePublicFrontend.liftLocal false

/-- Actual native environment effects retain the same thin private state and use the one shared World surface. -/
theorem effect_query (query : (EnvEffects n).Domain)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (simulateQ (closedLocal setup wire sign seed scalar candidate provider) (RegistrationBeaconReferenceCompiler.effect query)).run before =
      (fun reply => (reply, before)) <$> effectLift query := by
  simp only [closedLocal, QueryImpl.compose, RegistrationBeaconReferenceCompiler.effect, simulateQ_spec_query,
    RegistrationNativePublicFrontend.liftLocal, RegistrationNativeSelectiveHiddenInterpreter.handler,
    RegistrationNativeSelectiveHiddenInterpreter.onBase, RegistrationNativeHiddenInterpreter.handler,
    RegistrationNativeHiddenInterpreter.effect, StateT.run]
  rfl

/-- The same literal environment-effect forwarding holds through every actual adaptive native publication program. -/
theorem effect_program (work : OracleComp (EnvEffects n) Value)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (simulateQ (closedLocal setup wire sign seed scalar candidate provider)
      (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run before =
      (fun reply => (reply, before)) <$> simulateQ effectLift work := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, StateT.run_bind, effect_query, simulateQ_spec_query,
        bind_map_left, map_bind, ih]

noncomputable def original : QueryImpl (RegistrationNativePairedServerService.PublicSpec n)
    (StateT (EnvState Auxiliary) (OracleComp (RegistrationNativePublicFrontend.LocalSpec n KemSK))) :=
  RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect RegistrationServerOpenReferenceCompiler.demand
    setup.source wire.frameWrite sign

private theorem demand_run (message : RegistrationNativeRelatedFamily.Message) (env : EnvState Auxiliary) :
    (original setup wire sign (.inl message)).run env =
      (fun value => (value, env)) <$> RegistrationServerOpenReferenceCompiler.demand (n := n) (KemSK := KemSK) message := by
  simp only [original, RegistrationNativeCommonCompiler.service, StateT.run_lift, bind_pure_comp]
  rfl

private theorem publication_run (query : RegistrationBoundPublication.Spec.Domain) (env : EnvState Auxiliary) :
    (original (n := n) setup wire sign (.inr (.inl query))).run env =
      (fun result => (result.1, { env with receipts := result.2 })) <$>
        simulateQ (RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK))
          ((RegistrationBoundSourceCompiler.compiler setup.source wire.frameWrite sign query).run env.receipts) := rfl

private theorem effect_run (query : (EnvEffects n).Domain) (env : EnvState Auxiliary) :
    (original setup wire sign (.inr (.inr query))).run env =
      (fun value => (value, env)) <$> RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK) query := by
  simp only [original, RegistrationNativeCommonCompiler.service, RegistrationNativeCommonCompiler.common,
    StateT.run_lift, bind_pure_comp]
  rfl

/-- Closing each actual native public material callback gives the normalized current-environment service exactly. -/
theorem query_source (query : (RegistrationNativePairedServerService.PublicSpec n).Domain)
    (before : Local n Auxiliary KemSK ProviderState) :
    (((closedLocal setup wire sign seed scalar candidate provider).mapStateTBase (original (Auxiliary := Auxiliary) setup wire sign)).flattenStateT query).run before =
      (RegistrationNativeSelectiveMaterialService.handler setup wire sign seed scalar candidate provider query).run before := by
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  cases query with
  | inl message =>
      rw [demand_run]
      simp only [simulateQ_map, StateT.run_map, Functor.map_map, RegistrationServerOpenReferenceCompiler.demand,
        simulateQ_spec_query, closedLocal, QueryImpl.compose, RegistrationNativePublicFrontend.liftLocal,
        RegistrationNativeSelectiveMaterialService.handler]
      rfl
  | inr query => cases query with
    | inl query =>
        rw [publication_run]
        simp only [simulateQ_map, StateT.run_map, Functor.map_map, effect_program,
          RegistrationNativeSelectiveMaterialService.handler, RegistrationNativeCommonCompiler.common]
        simp only [StateT.run, RegistrationNativeSelectiveMaterialService.onEnv,
          RegistrationNativeCommonCompiler.publication, Functor.map_map]
    | inr query =>
        rw [effect_run]
        simp only [simulateQ_map, StateT.run_map, Functor.map_map, effect_query,
          RegistrationNativeSelectiveMaterialService.handler, RegistrationNativeCommonCompiler.common, ]
        rfl

/-- The complete original native material AST has the exact normalized current-environment execution, including arbitrary later continuations. -/
theorem program_source (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (env : EnvState Auxiliary) (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (closedLocal setup wire sign seed scalar candidate provider)
        ((simulateQ (original setup wire sign) work).run env)).run before =
      (simulateQ (RegistrationNativeSelectiveMaterialService.handler setup wire sign seed scalar candidate provider) work).run (env, before) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have same : ((closedLocal (n := n) setup wire sign seed scalar candidate provider).mapStateTBase
        (original (n := n) (Auxiliary := Auxiliary) setup wire sign)).flattenStateT =
      RegistrationNativeSelectiveMaterialService.handler (n := n) setup wire sign seed scalar candidate provider := by
    funext query
    apply StateT.ext
    intro state
    exact query_source setup wire sign seed scalar candidate provider query state
  rw [same]
  simp only [Functor.map_map, Prod.mk.eta, id_map']

end BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.effect_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.effect_query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.effect_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.effect_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource.program_source

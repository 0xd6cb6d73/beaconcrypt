-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundSourceCompiler
import BeaconcryptCore.Computational.RegistrationWorldAgreementCompiler
import BeaconcryptCore.Computational.RegistrationNativePairedServerService

/-! The pure paired publication/installation component is interpreted before its caller resumes a mutable environment continuation. Its signing attempts append to that same environment's receipt field. Hash and signing draws use the existing environment effects; all other environment fields are retained. Native analysis-only record callback markers and primitive counters require their separate derived accounting and are not asserted equal by this cache/receipt factorization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeCommonCompiler
open PqxdhRecordLiftInterface (EnvEffects CapabilitySpec)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePairedServerService (Common PublicSpec)
variable {ι Auxiliary Value : Type} {target : OracleSpec ι} {n : Nat}

/-- A receipt lens is used only for the pure component, before any outer mutable continuation. -/
def publication (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBoundPublication.Spec (StateT (EnvState Auxiliary) (OracleComp target)) := fun query before =>
  (fun result => (result.1, { before with receipts := result.2 })) <$>
    simulateQ environment ((RegistrationBoundSourceCompiler.compiler source writer sign query).run before.receipts)

def common (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (Common n) (StateT (EnvState Auxiliary) (OracleComp target))
  | .inl query => publication environment source writer sign query
  | .inr query => StateT.lift (environment query)

/-- The only extra service operation is the opaque material request; all native raw/sign/install work is interpreted with the caller's current environment. -/
def service (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (PublicSpec n) (StateT (EnvState Auxiliary) (OracleComp target))
  | .inl message => StateT.lift (demand message)
  | .inr query => common environment source writer sign query

private theorem publication_run (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (before : EnvState Auxiliary) :
    (publication environment source writer sign query).run before =
      (fun result => (result.1, { before with receipts := result.2 })) <$>
        simulateQ environment ((RegistrationBoundSourceCompiler.compiler source writer sign query).run before.receipts) := rfl

/-- Whole adaptive publication components preserve every other environment coordinate and append the real chronological signing receipts. -/
theorem publication_program (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Value) (before : EnvState Auxiliary) :
    (simulateQ (publication environment source writer sign) work).run before =
      (fun result => (result.1, { before with receipts := result.2 })) <$>
        simulateQ environment ((simulateQ (RegistrationBoundSourceCompiler.compiler source writer sign) work).run before.receipts) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, publication_run,
        bind_map_left, ih, map_bind]

/-- The same-cache native publication interpreter equals the environment compilation after retaining only its complete result, receipt log and cache. -/
theorem publication_source
    (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationBoundPublication.Spec Value)
    (before : EnvState Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (RegistrationBoundSourceCompiler.implementation source writer sign) work).run (before.receipts, cache) =
      (fun result => (result.1.1, (result.1.2.receipts, result.2))) <$>
        (simulateQ (PqxdhDeploymentEnvironment.ctxEffects admin)
          ((simulateQ (publication (QueryImpl.id' (EnvEffects n)) source writer sign) work).run before)).run cache := by
  rw [publication_program]
  simp only [simulateQ_id', simulateQ_map, StateT.run_map, Functor.map_map]
  exact RegistrationBoundSourceCompiler.factor admin source writer sign work before.receipts cache

/-- Ordinary native completion components are natural in their environment-effect embedding, including the current chronological receipt state. -/
theorem common_map (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (Common n).Domain) (before : EnvState Auxiliary) :
    (common environment source writer sign query).run before =
      simulateQ environment ((common (QueryImpl.id' (EnvEffects n)) source writer sign query).run before) := by
  cases query with
  | inl query => simp only [common, publication, StateT.run, simulateQ_id', simulateQ_map]
  | inr query =>
      simp only [common, StateT.run_lift, bind_pure_comp, QueryImpl.id'_apply, simulateQ_map, simulateQ_spec_query]

end BeaconcryptCore.Computational.RegistrationNativeCommonCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCommonCompiler.publication_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCommonCompiler.publication_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCommonCompiler.publication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCommonCompiler.publication_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeCommonCompiler.common_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeCommonCompiler.common_map

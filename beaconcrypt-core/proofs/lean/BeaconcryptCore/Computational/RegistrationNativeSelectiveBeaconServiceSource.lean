-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialSource
import BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion

/-! Beacon's literal paired callback keeps its publication receipts in the existing thin private frame. This exact diagram places that same frame in the normalized current-environment service while retaining all other private fields and the shared World effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconServiceSource
open PqxdhServerAuthExperiment (Setup)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeSelectiveMaterialService (Local)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

def restore (before : Local n Auxiliary KemSK ProviderState) : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState :=
  ({ before.2.1 with receipts := before.1.receipts }, before.2.2)

noncomputable def actual : QueryImpl (RegistrationNativePairedServerService.PublicSpec n)
    (RegistrationNativeSelectiveHiddenInterpreter.M n KemSK ProviderState) :=
  RegistrationNativeSelectiveMaterialSource.closedLocal setup wire sign seed scalar candidate provider ∘ₛ
    RegistrationBeaconReferenceFinish.service

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual Beacon paired callback has precisely the normalized private-frame interpretation. -/
theorem query_source (query : (RegistrationNativePairedServerService.PublicSpec n).Domain)
    (before : Local n Auxiliary KemSK ProviderState) :
    (actual setup wire sign seed scalar candidate provider query).run (restore before) =
      (fun result => (result.1, restore result.2)) <$>
        (RegistrationNativeSelectiveMaterialService.handler setup wire sign seed scalar candidate provider query).run before := by
  rcases query with message | publication | effect
  all_goals simp only [actual, QueryImpl.compose, RegistrationBeaconReferenceFinish.service, simulateQ_spec_query,
    RegistrationNativeSelectiveMaterialSource.closedLocal, RegistrationNativePublicFrontend.liftLocal,
    RegistrationNativeSelectiveHiddenInterpreter.handler, RegistrationNativeSelectiveHiddenInterpreter.onBase,
    RegistrationNativeSelectiveHiddenInterpreter.onKeys,
    RegistrationNativeHiddenInterpreter.handler, RegistrationNativeHiddenInterpreter.publication,
    RegistrationNativeHiddenInterpreter.effect, RegistrationNativeSelectiveMaterialService.handler,
    RegistrationNativeSelectiveMaterialService.onEnv, RegistrationNativeSelectiveMaterialService.onKeys,
    RegistrationNativeCommonCompiler.common, RegistrationNativeCommonCompiler.publication,
    StateT.run, restore, Functor.map_map, ]
  all_goals rfl


/-- Every adaptive actual paired Beacon program uses the same normalized publication frame and complete private poststate. -/
theorem program_source (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (before : Local n Auxiliary KemSK ProviderState) :
    (simulateQ (actual setup wire sign seed scalar candidate provider) work).run (restore before) =
      (fun result => (result.1, restore result.2)) <$>
        (simulateQ (RegistrationNativeSelectiveMaterialService.handler setup wire sign seed scalar candidate provider) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, query_source, bind_map_left, map_bind, ih]

end BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconServiceSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconServiceSource.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconServiceSource.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconServiceSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconServiceSource.program_source

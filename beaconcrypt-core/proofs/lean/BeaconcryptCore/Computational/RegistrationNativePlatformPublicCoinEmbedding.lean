-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceExecution
/-! New external frontend coins compile into old Env coin requests with exact returned values and operational state. The explicitly named World accounting projection removes their differing uniform/native/Env-coin charges; actual original resource bills remain separate. No old/new callback or whole experiment equality is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicCoinView (project)
open RegistrationNativePublicInterpreter (State M)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}

def embed : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK))
  | .inl query => (RegistrationNativePublicFrontend.Spec n KemSK).query query
  | .inr coin => RegistrationNativePublicFrontend.effect (.inl coin)

private theorem coin (coin : unifSpec.Domain) (before : State n KemSK) :
    Prod.map id project <$> ((StateT.lift (RegistrationNativeRelatedRoot.RootSpec.query (.inl coin)) : M n KemSK _).run before) =
      Prod.map id project <$> (RegistrationNativePublicInterpreter.effect (.inl coin)).run before := by
  have charged : RegistrationNativeMldsaWorldView.project (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before.world) =
      RegistrationNativeMldsaWorldView.project before.world := by
    simp only [RegistrationNativeMldsaWorldView.project, RegistrationNativeKemWorldUniform.mask,
      RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
      RegistrationWorldCoinCompiler.eraseCoin, PqxdhRecordLiftWorld.chargeEffect,
      PqxdhRecordLiftInterface.effectKind, Function.update_idem]
  have worldCoin : Prod.map id RegistrationNativeMldsaWorldView.project <$>
      (PqxdhRecordLiftWorld.effects (.inl coin)).run before.world =
      (fun reply => (reply, RegistrationNativeMldsaWorldView.project before.world)) <$> (unifSpec.query coin : ProbComp _) := by
    simpa only [PqxdhRecordLiftWorld.effects, StateT.run, charged] using
      RegistrationNativeMldsaWorldView.sampled (unifSpec.query coin : ProbComp _)
        (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before.world)
  have transported := congrArg (fun script => (fun result => (result.1, {before with world := result.2})) <$>
    simulateQ RegistrationNativePublicInterpreter.coins script) worldCoin
  simp only [RegistrationNativePublicInterpreter.effect, RegistrationNativePublicInterpreter.world,
    StateT.run, simulateQ_map, simulateQ_spec_query,
    RegistrationNativePublicInterpreter.coins, Functor.map_map, project, Prod.map_def, id_eq] at transported ⊢
  exact transported.symm

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
local notation "original" => RegistrationNativePlatformPublicSourceExecution.handler setup wire route sign
local notation "ordinary" => RegistrationNativePublicInterpreter.handler setup wire route sign

/-- Every exact new source query has the same projected result after the explicit coin embedding. -/
theorem query (request : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain) (before : State n KemSK) :
    Prod.map id project <$> (original request).run before =
      Prod.map id project <$> (simulateQ ordinary (embed request)).run before := by
  cases request with
  | inl request => simp only [RegistrationNativePlatformPublicSourceExecution.handler, embed, simulateQ_spec_query]
  | inr request =>
      simpa only [RegistrationNativePlatformPublicSourceExecution.handler, embed,
        RegistrationNativePublicFrontend.effect, RegistrationNativePublicFrontend.liftLocal, simulateQ_spec_query,
        RegistrationNativePublicInterpreter.handler, RegistrationNativePublicInterpreter.common] using coin request before

noncomputable def target : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (M n KemSK) :=
  fun request => simulateQ ordinary (embed request)

private theorem target_stable (request : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain) :
    RegistrationNativePlatformPublicCoinView.Stable (target setup wire route sign request) :=
  RegistrationNativePlatformViewStable.program_stable project RegistrationNativePlatformPublicCoinView.idempotent ordinary
    (RegistrationNativePlatformPublicCoinView.handler setup wire route sign) (embed request)

private noncomputable def masked : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (M n KemSK) :=
  fun request before => Prod.map id project <$> (target setup wire route sign request).run before

/-- Arbitrary new callback trees, with complete returned ledger/frontend/P values, compile without an old callback equality premise. -/
theorem program (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A) (before : State n KemSK) :
    Prod.map id project <$> (simulateQ original work).run before =
      Prod.map id project <$> (simulateQ ordinary (simulateQ embed work)).run before := by
  have left := OracleComp.map_run_simulateQ_eq_of_query_map_eq original (masked setup wire route sign) project
    (fun request current => (query setup wire route sign request current).trans
      (target_stable setup wire route sign request current)) work before
  have right := OracleComp.map_run_simulateQ_eq_of_query_map_eq (target setup wire route sign) (masked setup wire route sign) project
    (target_stable setup wire route sign) work before
  rw [← QueryImpl.simulateQ_compose]
  exact left.trans right.symm

/-- Erasing only interpreter state gives literal returned-value equality, including the original ledger/test bit/fresh state and common P. -/
theorem value (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A) (before : State n KemSK) :
    Prod.fst <$> (simulateQ original work).run before =
      Prod.fst <$> (simulateQ ordinary (simulateQ embed work)).run before := by
  have same := congrArg (Functor.map Prod.fst) (program setup wire route sign work before)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding.value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding.value

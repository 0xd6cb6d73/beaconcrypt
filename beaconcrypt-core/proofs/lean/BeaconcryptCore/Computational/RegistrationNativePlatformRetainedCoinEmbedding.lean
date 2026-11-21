-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRetained
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
/-! The actual retained-material compiler embeds allocator coins in Env coins while preserving arbitrary prepare/full108 material replies. The explicit World accounting projection removes only differing uniform/native/Env-coin charges; roots, provider/pool, receipts and operational state are retained. Thus arbitrary subsequent key and material-table interpreters can consume the same concrete new callback tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicCoinView (project)
open RegistrationNativePublicInterpreter (State)
open RegistrationNativeRetainedService (Spec)
open RegistrationNativePlatformPublicCoinEmbedding (embed)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}

private theorem ordinary_stable (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK A)
    (stable : RegistrationNativePlatformPublicCoinView.Stable work) :
    RegistrationNativePlatformViewStable.Stable project (RegistrationNativePublicRetained.ordinary hmac work) := by
  intro before
  have same := congrArg (fun action => simulateQ RegistrationNativePublicRetained.coins
    (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac) action)) (stable before)
  simpa only [RegistrationNativePublicRetained.ordinary, StateT.run, simulateQ_map] using same

/-- Each actual ordinary retained leaf ignores only the explicitly erased World accounting fields, for arbitrary material replies. -/
theorem compiler_stable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) :
    RegistrationNativePlatformViewStable.Stable project (RegistrationNativePublicRetained.compiler setup wire route sign query) := by
  rcases query with (message | (message | query) | query) | query
  · intro before
    simp only [RegistrationNativePublicRetained.compiler, StateT.run_lift, bind_pure_comp,
      Functor.map_map, Prod.map_def, id_eq, RegistrationNativePlatformPublicCoinView.idempotent]
  · intro before
    simp only [RegistrationNativePublicRetained.compiler, StateT.run_lift, bind_pure_comp,
      Functor.map_map, Prod.map_def, id_eq, RegistrationNativePlatformPublicCoinView.idempotent]
  · exact ordinary_stable _ _ (RegistrationNativePlatformPublicCoinView.common setup wire sign query)
  · exact ordinary_stable _ _ (RegistrationNativePlatformPublicCoinView.routed setup query)
  · exact ordinary_stable _ _ (RegistrationNativePlatformPublicCoinView.world _
      (RegistrationNativePlatformPublicCoinView.records setup wire route query))

private theorem lift_apply {S V : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m V) (before : S) :
    (StateT.lift work : StateT S m V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
local notation "original" => RegistrationNativePlatformPublicRetained.compiler setup wire route sign
local notation "ordinary" => RegistrationNativePublicRetained.compiler setup wire route sign

/-- The exact external-coin embedding is valid before choosing the private key-schedule or full108 service interpreter. -/
theorem query (request : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain) (before : State n KemSK) :
    Prod.map id project <$> (original request).run before =
      Prod.map id project <$> (simulateQ ordinary (embed request)).run before := by
  cases request with
  | inl request => simp only [RegistrationNativePlatformPublicRetained.compiler, embed, simulateQ_spec_query]
  | inr coin =>
      have raw := RegistrationNativePlatformPublicCoinEmbedding.query setup wire route sign (.inr coin) before
      have transported := congrArg (fun action => simulateQ RegistrationNativePublicRetained.coins
        (simulateQ (RegistrationNativePublicRootCoins.localImpl setup.hmac) action)) raw
      simpa only [RegistrationNativePlatformPublicRetained.compiler, embed,
        RegistrationNativePlatformPublicSourceExecution.handler, RegistrationNativePublicFrontend.effect,
        RegistrationNativePublicFrontend.liftLocal, RegistrationNativePublicInterpreter.handler,
        RegistrationNativePublicInterpreter.common, RegistrationNativePublicRetained.compiler,
        RegistrationNativePublicRetained.ordinary, StateT.run, lift_apply, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, RegistrationNativePublicRootCoins.localImpl,
        RegistrationNativePublicRetained.coins] using transported

noncomputable def target : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
    (StateT (State n KemSK) (OracleComp Spec)) := fun request => simulateQ ordinary (embed request)

private theorem target_stable (request : (RegistrationNativePlatformPublicFrontend.Spec n KemSK).Domain) :
    RegistrationNativePlatformViewStable.Stable project (target setup wire route sign request) :=
  RegistrationNativePlatformViewStable.program_stable project RegistrationNativePlatformPublicCoinView.idempotent ordinary
    (compiler_stable setup wire route sign) (embed request)

private noncomputable def masked : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK)
    (StateT (State n KemSK) (OracleComp Spec)) := fun request before =>
  Prod.map id project <$> (target setup wire route sign request).run before

/-- Arbitrary actual adaptive frontend trees retain their complete projected operational result through the same material-service language. -/
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

/-- Whole ledger/frontend/P return values are literal under every later material interpreter; no equality is asserted for erased native accounting. -/
theorem value (work : OracleComp (RegistrationNativePlatformPublicFrontend.Spec n KemSK) A) (before : State n KemSK) :
    Prod.fst <$> (simulateQ original work).run before =
      Prod.fst <$> (simulateQ ordinary (simulateQ embed work)).run before := by
  have same := congrArg (Functor.map Prod.fst) (program setup wire route sign work before)
  simpa only [Functor.map_map, Prod.map_def, id_eq] using same
end BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.compiler_stable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.compiler_stable

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRetainedCoinEmbedding.value

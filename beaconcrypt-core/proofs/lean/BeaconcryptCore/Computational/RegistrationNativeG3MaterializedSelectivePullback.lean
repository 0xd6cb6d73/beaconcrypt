-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedWorld
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
import BeaconcryptCore.Computational.RegistrationNativeSelectiveHiddenServiceInvariant
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationCore

/-! Realizing hidden installation tags commutes with the actual selective native callback interpreter. The source public client remains independent of the fixed seed table until this explicit outer World transformation. The equality retains the complete selective service, provider, receipt and frontend state and the same open World AST. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedSelectivePullback
open PqxdhRecordLiftInterface (WorldSpec EnvEffects effectLift)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeSelectiveHiddenInterpreter (State handler onBase onKeys)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

private def Allowed : (EnvEffects n).Domain → Prop
  | .inr (.installServer _ _ (.hidden _)) | .inr (.installBeacon _ _ (.hidden _)) => False
  | _ => True

private theorem all_true {Index Result : Type} {spec : OracleSpec Index} (work : OracleComp spec Result) :
    AllQueriesSatisfy work (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem effect_query (seeds : Seeds n) (query : (EnvEffects n).Domain) (safe : Allowed query) :
    simulateQ (RegistrationNativeG3MaterializedWorld.realize seeds) (effectLift query) = effectLift query := by
  cases query with
  | inl coin => rfl
  | inr capability => cases capability with
    | installServer keyId binding reference => cases reference <;> first | rfl | exact safe.elim
    | installBeacon owner shell reference => cases reference <;> first | rfl | exact safe.elim
    | _ => rfl

private theorem effect_program (seeds : Seeds n) (work : OracleComp (EnvEffects n) Value)
    (safe : AllQueriesSatisfy work (Allowed (n := n))) :
    simulateQ (RegistrationNativeG3MaterializedWorld.realize seeds) (simulateQ effectLift work) = simulateQ effectLift work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      obtain ⟨allowed, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, effect_query seeds query allowed]
      congr 1
      funext reply
      exact ih reply (later reply)

private theorem capability_free (seeds : Seeds n) (work : OracleComp (EnvEffects n) Value)
    (free : work.IsQueryBoundP RegistrationNativeHiddenServiceBounds.IsCapability 0) :
    simulateQ (RegistrationNativeG3MaterializedWorld.realize seeds) (simulateQ effectLift work) = simulateQ effectLift work := by
  rw [← QueryImpl.simulateQ_compose]
  apply PqxdhDeploymentIdealPool.simulateQ_congr_none _ _ RegistrationNativeHiddenServiceBounds.IsCapability _ work free
  intro query notCapability
  cases query with
  | inl coin => rfl
  | inr capability => exact (notCapability trivial).elim

private theorem coins_allowed (work : ProbComp Value) :
    AllQueriesSatisfy (PqxdhDeploymentEnvironment.coins (n := n) work) Allowed := by
  apply simulation _ (fun _ => True) Allowed _ work (all_true work)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial

private theorem shared_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (query : MldsaSharedNative.Spec.Domain) :
    AllQueriesSatisfy (RegistrationBoundSourceCompiler.sharedCompiler (n := n) source writer query) Allowed := by
  cases query with
  | inl query => exact (allQueriesSatisfy_query_iff _ _).mpr trivial
  | inr query =>
      change AllQueriesSatisfy (simulateQ (PqxdhDeploymentEnvironment.primFwd source.crypto source)
        (RawCtxMixedShared.sharedAdapter source.crypto writer query)) Allowed
      apply simulation _ (fun _ => True) Allowed _ _ (all_true _)
      intro query _
      rcases query with request | (bytes | input)
      · trivial
      · exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
      · trivial

private theorem publication_allowed (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) (receipts : List RegistrationSigningShared.Receipt) :
    AllQueriesSatisfy ((RegistrationBoundSourceCompiler.compiler (n := n) source writer sign query).run receipts) Allowed := by
  cases query with
  | inl query =>
      exact mapped _ _ Allowed (simulation _ (fun _ => True) Allowed
        (fun request _ => shared_allowed source writer request) _ (all_true _))
  | inr query => cases query with
    | hash request => exact mapped _ _ Allowed ((allQueriesSatisfy_query_iff _ _).mpr trivial)
    | sign request payload digest => exact mapped _ _ Allowed (coins_allowed _)

private theorem world_coins (seeds : Seeds n) (work : ProbComp Value) :
    simulateQ (RegistrationNativeG3MaterializedWorld.realize seeds)
      (simulateQ PqxdhRecordLiftInterface.coinLift work) = simulateQ PqxdhRecordLiftInterface.coinLift work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftInterface.coinLift,
        RegistrationNativeG3MaterializedWorld.realize, ih]

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
local notation "implementation" => handler (n := n) setup wire sign seed scalar candidate provider

/-- Each actual callback commutes with outer hidden-tag realization while preserving its complete reached selective state. -/
theorem query_source (seeds : Seeds n) (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK ProviderState) :
    simulateQ (RegistrationNativeG3MaterializedWorld.realize seeds) ((implementation query).run before) =
      (simulateQ implementation (RegistrationNativeG3MaterializedLocal.translate false seeds query)).run before := by
  rcases query with (message | ((message | (publication | effect)) | kem)) | record
  · simp only [handler, RegistrationNativeHiddenInterpreter.handler, onBase,
      RegistrationNativeHiddenInterpreter.onKeys, RegistrationNativeHiddenService.prepare, StateT.run,
      simulateQ_pure, map_pure, RegistrationNativeG3MaterializedLocal.translate, simulateQ_spec_query]
  · simp only [RegistrationNativeG3MaterializedLocal.translate, Bool.false_eq_true, ite_false, simulateQ_spec_query]
    simp only [handler, onKeys, StateT.run, simulateQ_map]
    congr 1
    exact capability_free seeds _ (RegistrationNativeSelectiveHiddenServiceInvariant.demand_free setup.source
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
      candidate message (before.1.keys, before.2))
  · simp only [handler, RegistrationNativeHiddenInterpreter.handler, onBase,
      RegistrationNativeHiddenInterpreter.publication, StateT.run, simulateQ_map,
      RegistrationNativeG3MaterializedLocal.translate, simulateQ_spec_query]
    congr 1
    congr 1
    exact effect_program seeds _ (publication_allowed setup.source wire.frameWrite sign publication before.1.receipts)
  · cases effect with
    | inl coin => rfl
    | inr capability => cases capability with
      | installServer keyId binding reference => cases reference <;>
          simp only [RegistrationNativeG3MaterializedLocal.translate, Bool.false_eq_true, ite_false, simulateQ_spec_query,
            handler, RegistrationNativeHiddenInterpreter.handler, onBase, RegistrationNativeHiddenInterpreter.effect,
            StateT.run, StateT.lift, bind_pure_comp, simulateQ_map, effectLift,
            RegistrationNativeG3MaterializedWorld.realize]; rfl
      | installBeacon owner shell reference => cases reference <;>
          simp only [RegistrationNativeG3MaterializedLocal.translate, Bool.false_eq_true, ite_false, simulateQ_spec_query,
            handler, RegistrationNativeHiddenInterpreter.handler, onBase, RegistrationNativeHiddenInterpreter.effect,
            StateT.run, StateT.lift, bind_pure_comp, simulateQ_map, effectLift,
            RegistrationNativeG3MaterializedWorld.realize]; rfl
      | _ => rfl
  · simp only [handler, RegistrationNativeHiddenInterpreter.handler, onBase,
      RegistrationNativeHiddenInterpreter.routed, StateT.run, simulateQ_map,
      RegistrationNativeG3MaterializedLocal.translate, simulateQ_spec_query]
    rw [world_coins]
  · rfl

/-- The same candidate-free public client may run before outer World tag realization; the seed table is introduced only by the explicit realization on that same completed AST. -/
theorem program_source (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK ProviderState) :
    simulateQ (RegistrationNativeG3MaterializedWorld.realize seeds)
        ((simulateQ implementation work).run before) =
      (simulateQ implementation (simulateQ (RegistrationNativeG3MaterializedLocal.translate false seeds) work)).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind,
        query_source setup wire sign seed scalar candidate provider seeds query before]
      apply bind_congr
      intro result
      exact ih result.1 result.2

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedSelectivePullback

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedSelectivePullback.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedSelectivePullback.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedSelectivePullback.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedSelectivePullback.program_source

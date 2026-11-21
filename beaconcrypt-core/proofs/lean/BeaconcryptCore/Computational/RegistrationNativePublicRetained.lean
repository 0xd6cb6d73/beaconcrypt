-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicRootCoins

/-! The actual mixed native interpreter factors through the private prepare/material service. The compiler keeps the full public World, KEM pool and signing receipts while the service owns the retained roots and protected PRK cache. Ordinary components use their proved non-read/zero-root laws, rather than a desired whole-game equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicRetained
open PqxdhServerAuthExperiment (Setup)
open PqxdhSecretInputKdf (HmacSha512 HmacOracle)
open RegistrationNativePublicInterpreter (State)
open RegistrationNativePublicRootFrame (replace IsRoot)
open RegistrationNativeRetainedService (Spec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def clear (state : State n KemSK) : State n KemSK :=
  replace RegistrationNativeReferenceInterpreter.initial state

def project (before : State n KemSK × HmacOracle.QueryCache) :
    State n KemSK × RegistrationNativeRetainedSource.State :=
  (clear before.1, (before.1.roots, before.2))

def coins : QueryImpl unifSpec (OracleComp Spec) := fun coin => Spec.query (.inl coin)

def ordinary (hmac : HmacSha512) (work : RegistrationNativePublicInterpreter.M n KemSK Value) :
    StateT (State n KemSK) (OracleComp Spec) Value := fun before =>
  simulateQ coins (simulateQ (RegistrationNativePublicRootCoins.localImpl hmac) (work.run before))

noncomputable def compiler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) :
    QueryImpl (RegistrationNativePublicFrontend.Spec n KemSK) (StateT (State n KemSK) (OracleComp Spec))
  | .inl (.inl message) => StateT.lift (Spec.query (.inr (.prepare message)))
  | .inl (.inr (.inl (.inl message))) => StateT.lift
      (Option.map RegistrationNativePairedChoice.Choice.known <$> (Spec.query (.inr (.demand message)) : OracleComp Spec _))
  | .inl (.inr (.inl (.inr query))) => ordinary setup.hmac (RegistrationNativePublicInterpreter.common setup wire sign query)
  | .inl (.inr (.inr query)) => ordinary setup.hmac (RegistrationNativePublicInterpreter.routedKem setup query)
  | .inr query => ordinary setup.hmac (RegistrationNativePublicInterpreter.world
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))))

/-- Every ordinary component keeps its exact World/pool/receipt/counter result when the private memo/cache move to the retained service. -/
theorem ordinary_project (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value)
    (framed : ∀ memo before, Prod.map id (replace memo) <$> work.run before = work.run (replace memo before))
    (free : ∀ before, (work.run before).IsQueryBoundP IsRoot 0)
    (before : State n KemSK) (cache : HmacOracle.QueryCache) :
    (fun result => (result.1.1, project (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
        (work.run before)).run cache =
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        ((ordinary setup.hmac work).run (clear before))).run (before.roots, cache) := by
  rw [RegistrationNativePublicRootCoins.root_run setup.source setup.hmac setup.joint setup.dh seed scalar _ (free before)]
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
      (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
      (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
      (simulateQ (fun coin => (Spec.query (.inl coin) : OracleComp Spec _))
        (simulateQ (RegistrationNativePublicRootCoins.localImpl setup.hmac) (work.run (clear before))))).run
        (before.roots, cache)
  rw [RegistrationNativePublicRootCoins.retained_coins]
  have framedLocal := congrArg (simulateQ (RegistrationNativePublicRootCoins.localImpl setup.hmac))
    (framed RegistrationNativeReferenceInterpreter.initial before)
  simp only [simulateQ_map] at framedLocal
  change Prod.map id clear <$> simulateQ (RegistrationNativePublicRootCoins.localImpl setup.hmac) (work.run before) =
    simulateQ (RegistrationNativePublicRootCoins.localImpl setup.hmac) (work.run (clear before)) at framedLocal
  rw [← framedLocal]
  simp only [Functor.map_map]
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result reached
  apply congrArg pure
  have kept : result.2.roots = before.roots := by
    have same := congrArg (simulateQ (RegistrationNativePublicRootCoins.localImpl setup.hmac))
      (framed before.roots before)
    have restored : replace before.roots before = before := rfl
    rw [restored, simulateQ_map] at same
    rw [← same, support_map] at reached
    obtain ⟨inner, _possible, equal⟩ := reached
    exact (congrArg (fun value : Value × State n KemSK => value.2.roots) equal).symm
  simp only [project, clear, Prod.map, id_eq, kept]

noncomputable def source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :=
  ((RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar).mapStateTBase
    (RegistrationNativePublicInterpreter.handler (n := n) setup wire route sign)).flattenStateT

noncomputable def retained (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :=
  ((RegistrationNativeRetainedSource.implementation setup.source setup.hmac
    (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
    (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))).mapStateTBase
      (compiler (n := n) setup wire route sign)).flattenStateT

/-- The entire actual mixed dispatch retains every reply and semantic state under the explicit private root-service projection. -/
theorem query_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (before : State n KemSK × HmacOracle.QueryCache) :
    Prod.map id project <$> (source setup wire route sign seed scalar query).run before =
      (retained setup wire route sign seed scalar query).run (project before) := by
  rcases before with ⟨state, cache⟩
  simp only [source, retained, project, QueryImpl.flattenStateT_mapStateTBase_apply_run, Functor.map_map]
  rcases query with (message | (message | query) | query) | query
  · simp only [RegistrationNativePublicInterpreter.handler, compiler, StateT.run_bind,
      StateT.run_lift, StateT.run_modify, StateT.run_pure, bind_map_left,
      simulateQ_bind, simulateQ_map, simulateQ_pure, simulateQ_spec_query,
      RegistrationNativeRetainedSource.implementation, RegistrationNativeRetainedRoots.root,
      RegistrationNativeRootCacheProjection.implementation, RegistrationNativeKeyFamilyPreparation.root,
      StateT.run_map, bind_pure_comp, Functor.map_map, project, clear, replace, Prod.map, id_eq]
    simp only [StateT.run, map_pure, bind_pure_comp, Functor.map_map]
    rfl
  · simp only [RegistrationNativePublicInterpreter.handler, compiler,
      StateT.run_lift, StateT.run_get, StateT.run_pure, StateT.run_map, bind_pure_comp,
      simulateQ_pure, simulateQ_map, simulateQ_spec_query,
      RegistrationNativeRetainedSource.implementation, Functor.map_map,
      project, clear, replace, Prod.map, id_eq]
    simp only [StateT.run, map_pure, Option.map_map]
    rfl
  · simp only [RegistrationNativePublicInterpreter.handler, compiler]
    convert ordinary_project setup seed scalar _
        (fun memo state => RegistrationNativePublicRootFrame.common_replace setup wire sign memo query state)
        (RegistrationNativePublicRootFrame.common_free setup wire sign query) state cache using 1 <;> rfl
  · simp only [RegistrationNativePublicInterpreter.handler, compiler]
    convert ordinary_project setup seed scalar _
        (fun memo state => RegistrationNativePublicRootFrame.routed_replace setup memo query state)
        (RegistrationNativePublicRootFrame.routed_free setup query) state cache using 1 <;> rfl
  · simp only [RegistrationNativePublicInterpreter.handler, compiler]
    convert ordinary_project setup seed scalar _
        (fun memo state => RegistrationNativePublicRootFrame.world_replace memo _ state)
        (RegistrationNativePublicRootFrame.world_free _) state cache using 1; rfl

/-- Arbitrary adaptive mixed-role programs preserve their complete result and semantic state after relocating only private root bookkeeping. -/
theorem program_project (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK × HmacOracle.QueryCache) :
    Prod.map id project <$> (simulateQ (source setup wire route sign seed scalar) work).run before =
      (simulateQ (retained setup wire route sign seed scalar) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_project setup wire route sign seed scalar) work before

noncomputable def client (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) : OracleComp Spec Value :=
  (simulateQ (compiler setup wire route sign) work).run' (clear before)

/-- The complete concrete mixed frontend is an executable retained-service client; no source execution equality is assumed. -/
theorem client_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State n KemSK) (cache : HmacOracle.QueryCache) :
    (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      ((simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) work).run' before)).run' cache =
      (simulateQ (RegistrationNativeRetainedSource.implementation setup.source setup.hmac
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))))
        (client setup wire route sign work before)).run' (before.roots, cache) := by
  have projected := congrArg (fun game => Prod.fst <$> game)
    (program_project setup wire route sign seed scalar work (before, cache))
  simp only [source, retained, project, StateT.run'_eq, simulateQ_map, StateT.run_map,
    Functor.map_map, Prod.map, id_eq, client] at projected ⊢
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT,
    simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  simpa only [Functor.map_map, Prod.map, id_eq] using projected

/-- The actual complete mixed frontend, after the ideal related-root hop, pays the five ordinary key-schedule losses through its derived retained-service client. -/
theorem key_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Bool)
    (before : State n KemSK) (count : Nat)
    (bounded : (client setup wire route sign work before).IsQueryBoundP RegistrationNativeRetainedService.IsDemand count) :
    ((simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
      ((simulateQ (RegistrationNativePublicInterpreter.handler setup wire route sign) work).run' (clear before))).run' ∅).boolDistance
      (RegistrationNativeKeyServiceBound.g2 setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
        (RegistrationNativeRetainedService.client (client setup wire route sign work before))) ≤
    ∑ index ∈ Finset.range count, RegistrationBoundKeySchedule.keyLoss setup.source setup.hmac
      (RegistrationNativeKeyHybrid.reduction setup.source setup.hmac
        (RegistrationNativeKeyCompiler.client setup.source
          (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
          (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
          (RegistrationNativeRetainedService.client (client setup wire route sign work before))
          RegistrationNativeKeyPhases.emptyMeta) index) := by
  rw [client_source]
  exact RegistrationNativeRetainedSource.key_bound setup.source setup.hmac correct _ _
    (client setup wire route sign work before) count bounded

end BeaconcryptCore.Computational.RegistrationNativePublicRetained
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRetained.ordinary_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRetained.ordinary_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRetained.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRetained.query_project

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRetained.program_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRetained.program_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRetained.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRetained.client_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicRetained.key_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicRetained.key_bound

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryRandomizedLower
import BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView
/-! The exact uncounted external-coin interpreter embeds in the existing World oracle only under the explicit ML accounting projection: uniform, native-call and Env-coin counters are erased, while operational state, private cache, raw attempts and attempted frames are retained. Returned client decisions remain literal. This is a functional transport, not a bound for arbitrary counter-dependent private-state decisions; external runtime allowances and each security event are handled separately. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (WorldSpec coinLift)
open RegistrationNativeKemCounterIndependence (Stable)
open RegistrationNativePlatformOrdinaryRandomizedLower (Spec)
variable {n : Nat} {I KemSK Reader Response A : Type} {base : OracleSpec I}
abbrev project := RegistrationNativeMldsaWorldView.project (n := n)

noncomputable def native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (WorldSpec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  CborRecordWorldSimulation.guarded setup (CborRawCanonicalBuild.canonical codec) route

def embed : QueryImpl (Spec n) (OracleComp (WorldSpec n))
  | .inl request => (WorldSpec n).query request
  | .inr coin => coinLift coin

private theorem guarded_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (request : (WorldSpec n).Domain) :
    Stable project (native setup codec route request) := by
  intro before
  have shell : CborRecordWorldCursor.worldShell (project before) = CborRecordWorldCursor.worldShell before := rfl
  cases refused : CborRecordWorldClient.refusal request (CborRecordWorldCursor.worldShell before) with
  | some reply =>
      simp only [native, StateT.run, CborRecordWorldSimulation.guarded, shell, refused,
        map_pure, Prod.map_def, id_eq, RegistrationNativeMldsaWorldView.idempotent]
  | none =>
      simpa only [native, StateT.run, CborRecordWorldSimulation.guarded, shell, refused] using
        RegistrationNativeMldsaWorldView.world setup (CborRawCanonicalBuild.canonical codec) route request before

private theorem coin_projected (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (coin : unifSpec.Domain) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (native setup codec route (.inr (.inl (.inl coin)))).run before =
      (fun reply => (reply, project before)) <$> (unifSpec.query coin : ProbComp _) := by
  have charged : project (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before) = project before := by
    simp only [project, RegistrationNativeMldsaWorldView.project, RegistrationNativeKemWorldUniform.mask,
      RegistrationNativeWorldView.project, RegistrationNativeWorldView.eraseNative,
      RegistrationWorldCoinCompiler.eraseCoin, PqxdhRecordLiftWorld.chargeEffect,
      PqxdhRecordLiftInterface.effectKind, Function.update_idem]
  have sampled := RegistrationNativeMldsaWorldView.sampled (unifSpec.query coin : ProbComp _)
    (PqxdhRecordLiftWorld.chargeEffect (.inl coin) before)
  change Prod.map id project <$> (PqxdhRecordLiftWorld.effects (.inl coin)).run before = _
  simpa only [PqxdhRecordLiftWorld.effects, StateT.run, charged] using sampled


noncomputable def uncounted (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (Spec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  RegistrationNativePlatformOrdinaryRandomizedLower.implementation (native setup codec route)

noncomputable def counted (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (Spec n) (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  native setup codec route ∘ₛ embed

private theorem uncounted_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (request : (Spec n).Domain) :
    Stable project (uncounted setup codec route request) := by
  cases request with
  | inl request => exact guarded_stable setup codec route request
  | inr coin =>
      intro before
      simp only [uncounted, RegistrationNativePlatformOrdinaryRandomizedLower.implementation,
        StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq,
        RegistrationNativeMldsaWorldView.idempotent]


private theorem counted_stable (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (request : (Spec n).Domain) :
    Stable project (counted setup codec route request) := by
  cases request with
  | inl request =>
      simpa only [counted, QueryImpl.compose, embed, simulateQ_spec_query] using
        guarded_stable setup codec route request
  | inr coin =>
      simpa only [counted, QueryImpl.compose, embed, coinLift, simulateQ_spec_query] using
        guarded_stable (n := n) setup codec route (.inr (.inl (.inl coin)))


private def masked {J : Type} {spec : OracleSpec J}
    (handler : QueryImpl spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp)) :
    QueryImpl spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp) :=
  fun request before => Prod.map id project <$> (handler request).run before

private theorem normalize {J : Type} {spec : OracleSpec J}
    (handler : QueryImpl spec (StateT (PqxdhRecordLiftWorld.State n) ProbComp))
    (callbacks : ∀ request, Stable project (handler request))
    (work : OracleComp spec A) (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (simulateQ handler work).run before =
      (simulateQ (masked handler) work).run (project before) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ project callbacks work before

private theorem masked_equal (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    masked (uncounted (n := n) setup codec route) = masked (counted setup codec route) := by
  funext request before
  cases request with
  | inl request =>
      simp only [masked, uncounted, RegistrationNativePlatformOrdinaryRandomizedLower.implementation,
        counted, QueryImpl.compose, embed, simulateQ_spec_query]
  | inr coin =>
      have source := coin_projected setup codec route coin before
      convert source.symm using 1
      · rfl
      · simp only [masked, uncounted, RegistrationNativePlatformOrdinaryRandomizedLower.implementation,
          StateT.run_lift, bind_pure_comp, Functor.map_map, Prod.map_def, id_eq]
        rfl
      · simp only [masked, counted, QueryImpl.compose, embed, coinLift, simulateQ_spec_query]


/-- Embedding external coins in ordinary World coins preserves exactly the named accounting projection through every adaptive continuation. -/
theorem projected (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (Spec n) A)
    (before : PqxdhRecordLiftWorld.State n) :
    Prod.map id project <$> (simulateQ (uncounted setup codec route) work).run before =
      Prod.map id project <$> (simulateQ (native setup codec route) (simulateQ embed work)).run before := by
  rw [← QueryImpl.simulateQ_compose]
  change _ = Prod.map id project <$> (simulateQ (counted setup codec route) work).run before
  calc
    _ = (simulateQ (masked (uncounted setup codec route)) work).run (project before) :=
      normalize _ (uncounted_stable setup codec route) work before
    _ = (simulateQ (masked (counted setup codec route)) work).run (project before) := by
      rw [masked_equal]
    _ = _ := (normalize _ (counted_stable setup codec route) work before).symm


/-- The actual returned value, including every original ledger coordinate and common external poststate stored there, needs no accounting projection. -/
theorem value (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (Spec n) A)
    (before : PqxdhRecordLiftWorld.State n) :
    Prod.fst <$> (simulateQ (uncounted setup codec route) work).run before =
      Prod.fst <$> (simulateQ (native setup codec route) (simulateQ embed work)).run before := by
  have same := congrArg (Functor.map Prod.fst) (projected setup codec route work before)
  simpa only [Functor.map_map, Function.comp_def, Prod.map_def, id_eq] using same


def analysisState (before : PqxdhRecordLiftWorld.State n) :=
  (before.primitive.2, before.produced, PqxdhRecordLiftWorld.rawCounters before)

private theorem analysisState_project (before : PqxdhRecordLiftWorld.State n) :
    analysisState (project before) = analysisState before := rfl

/-- The same private cache and attempted-record history are retained for analysis of collisions and ordinary origin; no new source read interface is supplied. -/
theorem record_observation (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (Spec n) A)
    (before : PqxdhRecordLiftWorld.State n) :
    (fun result => (result.1, analysisState result.2)) <$> (simulateQ (uncounted setup codec route) work).run before =
      (fun result => (result.1, analysisState result.2)) <$>
        (simulateQ (native setup codec route) (simulateQ embed work)).run before := by
  have same := congrArg (Functor.map (fun result : A × PqxdhRecordLiftWorld.State n =>
    (result.1, analysisState result.2))) (projected setup codec route work before)
  simpa only [Functor.map_map, Function.comp_def, Prod.map_def, id_eq, analysisState_project] using same


/-- A decision on the actual returned client value has the same probability; counter-dependent private-state decisions are not covered by this statement. -/
theorem observe (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (Spec n) A)
    (before : PqxdhRecordLiftWorld.State n) (decision : A → Bool) :
    (fun result => decision result.1) <$> (simulateQ (uncounted setup codec route) work).run before =
      (fun result => decision result.1) <$>
        (simulateQ (native setup codec route) (simulateQ embed work)).run before := by
  have same := congrArg (Functor.map decision) (value setup codec route work before)
  simpa only [Functor.map_map, Function.comp_def] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.projected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.projected

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.value

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.record_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.record_observation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.observe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExternalCoins.observe

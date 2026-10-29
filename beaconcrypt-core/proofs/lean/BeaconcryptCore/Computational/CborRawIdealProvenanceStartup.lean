-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealProvenanceWorld

/-! Startup of the full raw World invariant: actual parameter and Server-construction coins, one actual Server initialization, then the original adaptive secrecy ledger. Erasing the annotation gives the exact public cursor client, including its full private state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealProvenanceStartup
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Environment WorldSpec EnvQuery)
open PqxdhDeploymentInterface (Entry Spec FreshBounds Mode ModeSpec)
open PqxdhRecordLiftOrigins (Origins)
open PqxdhDeploymentIdealOrigins (IsFixed QuietEntry aEffects isAnnot query_free free_run)
open PqxdhDeploymentEnvironmentJoin (uncount initialized)
open CborRawIdealProvenanceStep (worldStep)
variable {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- Startup coins see the same actual annotated World and counters, before any record command exists. -/
theorem coins_annotated {Result : Type} (draw : ProbComp Result) (state : PqxdhRecordLiftOrigins.State n) :
    (simulateQ (CborRawIdealProvenanceGuard.handler setup codec route)
      (simulateQ PqxdhRecordLiftInterface.coinLift draw)).run state =
    (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
      (simulateQ PqxdhRecordLiftInterface.coinLift draw)).run state := by
  have same : (CborRawIdealProvenanceGuard.handler setup codec route (n := n)) ∘ₛ
      PqxdhRecordLiftInterface.coinLift = (PqxdhRecordLiftOrigins.handler setup codec route) ∘ₛ
        PqxdhRecordLiftInterface.coinLift := by
    funext coin
    simp only [QueryImpl.apply_compose, PqxdhRecordLiftInterface.coinLift, simulateQ_spec_query]
    rfl
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, same]

noncomputable def annotatedRun (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  (simulateQ (CborRawIdealProvenanceGuard.handler setup codec route)
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)).run
      PqxdhRecordLiftOrigins.initial

/-- The annotation erases to the exact raw public cursor client on the complete initialized program. -/
theorem erase (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    Prod.map id Prod.fst <$> annotatedRun setup codec route env serverKid bounds mode adversary =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (CborRecordWorldClient.client
          (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary))).run
        PqxdhRecordLiftWorld.initial :=
  CborRawIdealProvenanceGuard.client_erase setup codec route _ PqxdhRecordLiftOrigins.initial

/-- A relation proved for local fixed/registration steps and actual startup holds on every full raw adaptive World outcome. -/
theorem world_keeps (env : Environment n E)
    (R : List Entry → E → PqxdhRecordLiftWorld.State n → Origins n → Prop)
    (rFixed : ∀ query transcript e w o, IsFixed query → R transcript e w o →
      ∀ result ∈ support ((worldStep setup codec route env query).run (e, (w, o))),
        R transcript result.2.1 result.2.2.1 result.2.2.2)
    (rQuiet : ∀ transcript e w o (entry : Entry), QuietEntry entry → R transcript e w o → R (transcript ++ [entry]) e w o)
    (rStep : ∀ (query : EnvQuery) transcript e w o, R transcript e w o →
      ∀ result ∈ support ((simulateQ (aEffects setup codec route) ((env.step query).run e)).run (w, o)),
        R (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2)
    (born : ∀ created start, some (created, start) ∈ support env.start →
      ∀ w : PqxdhRecordLiftWorld.State n, uncount w = uncount PqxdhRecordLiftWorld.initial →
        R [] start (initialized created w) PqxdhRecordLiftOrigins.empty)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    ∀ result ∈ support (annotatedRun setup codec route env serverKid bounds mode adversary),
      ∀ value, result.1 = some value → R value.2.1.2.transcript value.2.2 result.2.1 result.2.2 := by
  intro result member value found
  unfold annotatedRun at member
  rw [PqxdhDeploymentEnvironmentDraw.program_rest, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨step, stepMember, rest⟩ := member
  have coinsFree : (simulateQ PqxdhRecordLiftInterface.coinLift env.start).IsQueryBoundP
      (fun request => isAnnot request = true) 0 :=
    RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      (fun coin => by
        simp only [ite_false]
        exact query_free (n := n) (.inr (.inl (.inl coin))) rfl)
  have init : (PqxdhRecordLiftOrigins.initial : PqxdhRecordLiftOrigins.State n) =
      (PqxdhRecordLiftWorld.initial, PqxdhRecordLiftOrigins.empty) := rfl
  rw [init, coins_annotated setup codec route env.start, free_run setup codec route _ coinsFree, support_map] at stepMember
  obtain ⟨plain, plainMember, rfl⟩ := stepMember
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup codec route env.start
    (PqxdhRecordLiftWorld.initial (n := n))
  have inMapped : Prod.map id PqxdhDeploymentEnvironmentJoin.uncount plain ∈ support (Prod.map id
      PqxdhDeploymentEnvironmentJoin.uncount <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (simulateQ PqxdhRecordLiftInterface.coinLift env.start)).run (PqxdhRecordLiftWorld.initial (n := n))) := by
    rw [support_map]
    exact ⟨plain, plainMember, rfl⟩
  rw [counted, support_map] at inMapped
  obtain ⟨startValue, startMember, same⟩ := inMapped
  have started : plain.1 ∈ support env.start := by
    have first := congrArg Prod.fst same
    simp only [Prod.map_fst, id_eq] at first
    rw [← first]
    exact startMember
  have fresh : PqxdhDeploymentEnvironmentJoin.uncount plain.2 =
      PqxdhDeploymentEnvironmentJoin.uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have second := congrArg Prod.snd same
    simp only [Prod.map_snd] at second
    exact second.symm
  rcases plain with ⟨_ | ⟨created, start⟩, w⟩
  · simp only [PqxdhDeploymentEnvironmentDraw.worldRest, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at rest
    subst rest
    cases found
  · have vacant : w.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
    have initRun : (CborRawIdealProvenanceGuard.handler setup codec route (.inl created)).run (w, PqxdhRecordLiftOrigins.empty) =
        pure ((), (PqxdhDeploymentEnvironmentJoin.initialized created w, PqxdhRecordLiftOrigins.empty)) := by
      change (PqxdhRecordLiftOrigins.handler setup codec route (.inl created)).run
        (w, PqxdhRecordLiftOrigins.empty) = _
      rw [PqxdhDeploymentIdealOrigins.handler_other setup codec route _ _ rfl]
      change (fun result => (result.1, (result.2, PqxdhRecordLiftOrigins.empty))) <$>
        PqxdhRecordLiftWorld.initializeServer created w = _
      simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
      rfl
    dsimp only [PqxdhDeploymentEnvironmentDraw.worldRest] at rest
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, initRun, pure_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at rest
    obtain ⟨middle, middleMember, final⟩ := rest
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    simp only [Option.some.injEq] at found
    subst found
    exact CborRawIdealProvenanceRun.run_keeps setup codec route env R rFixed rQuiet rStep
      setup.source.crypto serverKid bounds _ PqxdhDeploymentSecrecy.Ledger.empty start
      (PqxdhDeploymentEnvironmentJoin.initialized created w) PqxdhRecordLiftOrigins.empty
      (born created start started w fresh) middle middleMember

end BeaconcryptCore.Computational.CborRawIdealProvenanceStartup

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStartup.coins_annotated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStartup.coins_annotated

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStartup.erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStartup.erase

/-- info: 'BeaconcryptCore.Computational.CborRawIdealProvenanceStartup.world_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealProvenanceStartup.world_keeps

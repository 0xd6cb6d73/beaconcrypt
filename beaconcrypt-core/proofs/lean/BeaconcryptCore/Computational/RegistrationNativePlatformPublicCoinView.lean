-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInterpreter
import BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView
import BeaconcryptCore.Computational.RegistrationNativePlatformViewStable
/-! The root-valued public interpreter is insensitive to the named private accounting coordinates. Roots, KEM pool, raw receipts, operational World data and all returned values remain exact. This view erases uniform/native/Env-coin accounting and makes no equality claim for the removed bills; those are proved separately on the original execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicInterpreter (State M)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}

def project (before : State n KemSK) : State n KemSK :=
  {before with world := RegistrationNativeMldsaWorldView.project before.world}
def Stable (work : M n KemSK A) : Prop := RegistrationNativePlatformViewStable.Stable project work

/-- Only the explicit private accounting observation is idempotently erased. -/
theorem idempotent (before : State n KemSK) : project (project before) = project before := by
  simp only [project, RegistrationNativeMldsaWorldView.idempotent]

theorem world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp A)
    (law : RegistrationNativeKemCounterIndependence.Stable RegistrationNativeMldsaWorldView.project work) :
    Stable (RegistrationNativePublicInterpreter.world (KemSK := KemSK) work) := by
  intro before
  have same := congrArg (fun script => (fun result => (result.1, {before with world := result.2})) <$>
    simulateQ RegistrationNativePublicInterpreter.coins script) (law before.world)
  simp only [RegistrationNativePublicInterpreter.world, StateT.run, simulateQ_map, Functor.map_map,
    project, Prod.map_def, id_eq] at same ⊢
  exact same

theorem effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Stable (RegistrationNativePublicInterpreter.effect (KemSK := KemSK) query) :=
  world _ (RegistrationNativeMldsaWorldView.effects query)

private theorem pure_stable (value : A) : Stable (pure value : M n KemSK A) :=
  RegistrationNativePlatformViewStable.pure_stable project idempotent value

theorem publication (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationBoundPublication.Spec.Domain) :
    Stable (RegistrationNativePublicInterpreter.publication (n := n) setup wire sign query) := by
  intro before
  have program := RegistrationNativePlatformViewStable.program_stable (project (n := n) (KemSK := KemSK)) idempotent
    (RegistrationNativePublicInterpreter.effect (n := n) (KemSK := KemSK)) effect
    ((RegistrationBoundSourceCompiler.compiler (n := n) setup.source (RegistrationNativeWire.ledgerCodec wire).frameWrite sign query).run before.receipts)
  have tail : ∀ result : (RegistrationBoundPublication.Spec).Range query × List RegistrationSigningShared.Receipt, Stable (do
      modify fun current : State n KemSK => {current with receipts := result.2}
      pure result.1 : M n KemSK ((RegistrationBoundPublication.Spec).Range query)) := by
    intro result
    exact RegistrationNativePlatformViewStable.bind_stable project _ _
      (RegistrationNativePlatformViewStable.modify_stable project _ (fun _ => by simp only [project, RegistrationNativeMldsaWorldView.idempotent])) (fun _ => pure_stable _)
  have joined := RegistrationNativePlatformViewStable.bind_stable project _ _ program tail before
  simp only [RegistrationNativePublicInterpreter.publication, StateT.run_bind, StateT.run_get, pure_bind, project] at joined ⊢
  exact joined

/-- The actual KEM callback and unavailable ordinary leaf ignore only erased World accounting. -/
theorem kem (setup : Setup base KemSK)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Stable (RegistrationNativePublicInterpreter.kem (n := n) setup query) := by
  cases query with
  | inl query =>
      intro before
      simp only [RegistrationNativePublicInterpreter.kem, StateT.run_lift, bind_pure_comp,
        Functor.map_map, project, Prod.map_def, id_eq, RegistrationNativeMldsaWorldView.idempotent]
  | inr query => cases query with
    | inl query =>
      intro before
      have sampled := world (n := n) (KemSK := KemSK) _
        (fun current => by
          have source := RegistrationNativeMldsaWorldView.sampled
            ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.pool) current
          have projected := RegistrationNativeMldsaWorldView.sampled
            ((PqxdhLiveKemBirth.poolImpl setup.baseImpl setup.kem query).run before.pool)
            (RegistrationNativeMldsaWorldView.project current)
          rw [RegistrationNativeMldsaWorldView.idempotent] at projected
          exact source.trans projected.symm)
      have tail : ∀ result : (PqxdhLiveKemBirth.PoolSpec KemSK).Range query × PqxdhLiveKemBirth.Pool KemSK,
          Stable (do
            modify fun current : State n KemSK => {current with pool := result.2}
            pure result.1 : M n KemSK _) := by
        intro result
        exact RegistrationNativePlatformViewStable.bind_stable project _ _
          (RegistrationNativePlatformViewStable.modify_stable project _ (fun _ => by simp only [project, RegistrationNativeMldsaWorldView.idempotent])) (fun _ => pure_stable _)
      have joined := RegistrationNativePlatformViewStable.bind_stable project _ _ sampled tail before
      simp only [RegistrationNativePublicInterpreter.kem, StateT.run_bind, StateT.run_get, pure_bind, project] at joined ⊢
      exact joined
    | inr key =>
      apply world
      intro before
      have source := RegistrationNativeMldsaWorldView.sampled
        (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)) before
      have projected := RegistrationNativeMldsaWorldView.sampled
        (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)) (RegistrationNativeMldsaWorldView.project before)
      rw [RegistrationNativeMldsaWorldView.idempotent] at projected
      exact source.trans projected.symm

/-- Every actual routed KEM branch retains its operational state and optional replies. -/
theorem routed (setup : Setup base KemSK) (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) :
    Stable (RegistrationNativePublicInterpreter.routedKem (n := n) setup query) := by
  rcases query with ordinary | query
  · rcases ordinary with query | key
    · exact kem setup (.inl query)
    · exact kem setup (.inr (.inr key))
  · exact kem setup (.inr query)

theorem records (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) :
    RegistrationNativeKemCounterIndependence.Stable RegistrationNativeMldsaWorldView.project
      (CborRecordWorldSimulation.guarded (n := n) setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query))) := by
  intro before
  have shell : CborRecordWorldCursor.worldShell (RegistrationNativeMldsaWorldView.project before) = CborRecordWorldCursor.worldShell before := rfl
  cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr query)) (CborRecordWorldCursor.worldShell before) with
  | some reply =>
      simp only [CborRecordWorldSimulation.guarded, StateT.run, shell, refused, map_pure,
        Prod.map_def, id_eq, RegistrationNativeMldsaWorldView.idempotent]
  | none =>
      simpa only [CborRecordWorldSimulation.guarded, StateT.run, shell, refused] using
        RegistrationNativeMldsaWorldView.world setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr query)) before

/-- Every complete legacy source leaf is insensitive to the precise erased private accounting inputs. -/
theorem handler (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain) :
    Stable (RegistrationNativePublicInterpreter.handler setup wire route sign query) := by
  rcases query with prepare | recordQuery
  · rcases prepare with message | rest
    · intro before
      rw [RegistrationNativePublicInterpreter.prepare_query setup wire route sign message before,
        RegistrationNativePublicInterpreter.prepare_query setup wire route sign message (project before)]
      simp only [bind_pure_comp, Functor.map_map,
        project, Prod.map_def, id_eq, RegistrationNativeMldsaWorldView.idempotent]
    · rcases rest with common | routedQuery
      · rcases common with demand | commonQuery
        · intro before
          simp only [RegistrationNativePublicInterpreter.handler, StateT.run_bind, StateT.run_get,
            StateT.run_pure, pure_bind, map_pure, project, Prod.map_def, id_eq,
            RegistrationNativeMldsaWorldView.idempotent]
        · cases commonQuery with
          | inl query => exact publication setup wire sign query
          | inr query => exact effect query
      · exact routed setup routedQuery
  · exact world _ (records setup wire route recordQuery)

/-- Independent actual source sampling preserves replies under the named erased accounting view. -/
theorem sampled (draw : ProbComp A) :
    Stable (RegistrationNativePublicInterpreter.world (KemSK := KemSK) (PqxdhRecordLiftWorld.sampled (n := n) draw)) := by
  apply world
  intro before
  have source := RegistrationNativeMldsaWorldView.sampled draw before
  have projected := RegistrationNativeMldsaWorldView.sampled draw (RegistrationNativeMldsaWorldView.project before)
  rw [RegistrationNativeMldsaWorldView.idempotent] at projected
  exact source.trans projected.symm

/-- The entire actual ordinary publication/effect dictionary retains its current replies and operational state. -/
theorem common (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) :
    Stable (RegistrationNativePublicInterpreter.common setup wire sign query) := by
  cases query with
  | inl query => exact publication setup wire sign query
  | inr query => exact effect query
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.effect

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.kem

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.routed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.handler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.sampled' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.sampled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.common' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinView.common

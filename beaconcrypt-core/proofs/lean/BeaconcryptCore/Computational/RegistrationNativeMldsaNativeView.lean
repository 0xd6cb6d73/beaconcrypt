-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaWorldView
import BeaconcryptCore.Computational.RegistrationNativeExperiment

/-! The ML accounting view lifts to complete native envelopes. Actual World effects, indexed KEM callbacks and every Beacon source controller ignore the omitted private input counters. All owner metadata, KEM secret pool, mutable control and logs remain present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemCounterIndependence (Stable)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

def server (before : RegistrationServerFrontendCompiler.State n) : RegistrationServerFrontendCompiler.State n :=
  { before with world := { before.world with world :=
    (RegistrationNativeMldsaWorldView.project before.world.world.1, before.world.world.2) } }

def project (before : RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativeExperiment.State n KemSK source := { before with server := server before.server }

/-- Reapplying the full native ML view changes no further field. -/
theorem idempotent (before : RegistrationNativeExperiment.State n KemSK source) : project (project before) = project before := by
  simp only [project, server, RegistrationNativeMldsaWorldView.idempotent]

/-- A stable actual World callback remains stable inside the complete native Server lens. -/
theorem world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (stable : Stable RegistrationNativeMldsaWorldView.project work) :
    Stable (project (KemSK := KemSK) (source := source)) (RegistrationNativeExperiment.world work) := by
  intro before
  have same := congrArg (fun computation => (fun result => (result.1,
    { project before with server := { (project before).server with world :=
      { (project before).server.world with world := (result.2, before.server.world.world.2) } } })) <$> computation)
    (stable before.server.world.world.1)
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server, StateT.run,
    Functor.map_map, Prod.map, id_eq, project, server] at same ⊢
  exact same

/-- All actual trusted callbacks, including real indexed KEM failures and cache effects, retain the same projected native result. -/
theorem trusted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    Stable (project (source := source)) (RegistrationNativeExperiment.trusted setup checks representation created source query) := by
  cases query with
  | inl effect => exact world _ (RegistrationNativeMldsaWorldView.effects effect)
  | inr query =>
      intro before
      have masked := RegistrationNativeMldsaWorldView.sampled
        ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
            (before.server.world.auxiliary, before.pool))
          (RegistrationNativeMldsaWorldView.project before.server.world.world.1)
      rw [RegistrationNativeMldsaWorldView.idempotent] at masked
      have equal := (RegistrationNativeMldsaWorldView.sampled
        ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
          (RegistrationNativeKemBackend.serverOther setup checks representation created.seed) query).run
            (before.server.world.auxiliary, before.pool)) before.server.world.world.1).trans masked.symm
      have lifted := congrArg (fun computation => (fun (result :
          ((RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Range query ×
            (RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK)) × PqxdhRecordLiftWorld.State n) => (result.1.1,
        { project before with pool := result.1.2.2, server := { (project before).server with world := { (project before).server.world with auxiliary := result.1.2.1, world := (result.2, before.server.world.world.2) } } })) <$> computation) equal
      simp only [RegistrationNativeExperiment.trusted, StateT.run, bind_pure_comp,
        Functor.map_map, Prod.map, id_eq, project, server] at lifted ⊢
      exact lifted

/-- Any complete Beacon source controller preserves its exact projected result, phase, authentication history and reached mutable environment. -/
theorem beacon (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    Stable project (RegistrationNativeExperiment.beacon setup checks representation created work) := by
  intro before
  have callbacks := RegistrationNativeKemCounterIndependence.program_stable project idempotent
    (RegistrationNativeExperiment.trusted setup checks representation created source)
    (trusted setup checks representation created)
    ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world)) before
  have lifted := congrArg (fun computation => (fun (result :
      ((Value × RegistrationNativeBeaconFrontend.State source) ×
        RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) ×
          RegistrationNativeExperiment.State n KemSK source) => (result.1.1.1,
    { result.2 with beacons := result.1.1.2, server := { result.2.server with world := RegistrationWorldAgreementCompiler.join result.1.2 result.2.server.world.world.1 } })) <$> computation) callbacks
  simp only [RegistrationNativeExperiment.beacon, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map, id_eq, project, server, RegistrationWorldAgreementCompiler.erase,
    RegistrationWorldAgreementCompiler.join] at lifted ⊢
  exact lifted

private theorem guarded (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) :
    Stable RegistrationNativeMldsaWorldView.project
      (CborRecordWorldSimulation.guarded setup (RegistrationNativeWire.ledgerCodec wire) route query) := by
  intro before
  have shell : CborRecordWorldCursor.worldShell (RegistrationNativeMldsaWorldView.project before) =
      CborRecordWorldCursor.worldShell before := rfl
  simp only [CborRecordWorldSimulation.guarded, StateT.run, shell]
  cases refused : CborRecordWorldClient.refusal query (CborRecordWorldCursor.worldShell before) with
  | none => exact RegistrationNativeMldsaWorldView.world setup (RegistrationNativeWire.ledgerCodec wire) route query before
  | some reply => simp only [map_pure, Prod.map, id_eq, RegistrationNativeMldsaWorldView.idempotent]

/-- Full Server and Beacon raw-record callbacks preserve admission, cache, kernel consumption and frame history under ML accounting erasure. -/
theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery) :
    Stable (project (n := n) (KemSK := KemSK) (source := source)) (RegistrationNativeExperiment.record setup wire route query source) := by
  cases query with
  | inl command => exact world _ (guarded setup wire route _)
  | inr command =>
      rcases command with ⟨index, command⟩
      cases command with
      | inl plaintext =>
          intro before
          simp only [RegistrationNativeExperiment.record, StateT.run]
          cases found : before.beacons[index]? with
          | none => simp only [project, found, map_pure, Prod.map, id_eq, server, RegistrationNativeMldsaWorldView.idempotent]
          | some owner =>
              simp only [project, found]
              exact world _ (guarded setup wire route (.inr (.inr (.inr (owner.worldOwner, .inl plaintext))))) before
      | inr raw =>
          intro before
          simp only [RegistrationNativeExperiment.record, StateT.run]
          cases found : before.beacons[index]? with
          | none => simp only [project, found, map_pure, Prod.map, id_eq, server, RegistrationNativeMldsaWorldView.idempotent]
          | some owner =>
              simp only [project, found]
              exact world _ (guarded setup wire route (.inr (.inr (.inr (owner.worldOwner, .inr raw))))) before

end BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.idempotent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.trusted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.trusted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaNativeView.record

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBeaconFootprint
import BeaconcryptCore.Computational.RegistrationNativeKemParsedRouting

/-! The native compiler preserves private indexed KEM query classes across its actual state wrappers and exposed-getter routing. Concrete Beacon controller bills are lifted from their original nested state ASTs; no full frontend resource certificate is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint
open RegistrationNativeKemBeaconFootprint (Kind Bounded counted)
open PqxdhServerAuthExperiment (Setup Checks)
variable {κ ι KemSK Value : Type} {ambient : OracleSpec κ} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- The ambient interface counts indexed creation/reveal. The source-only `.other` escape marker has already been checked before local callbacks enter this arbitrary ambient type. -/
def predicate (ambient : OracleSpec κ) (KemSK : Type) (kind : Kind) :
    (RegistrationNativeKemInterface.Spec ambient KemSK).Domain → Prop
  | .inr (.inl .create) => kind = .create
  | .inr (.inl (.reveal _)) => kind = .reveal
  | _ => False

instance (ambient : OracleSpec κ) (KemSK : Type) (kind : Kind) : DecidablePred (predicate ambient KemSK kind) := fun query => by
  unfold predicate
  split <;> infer_instance

private theorem source_lift_step (kind : Kind)
    (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    (RegistrationNativeKemServerInterface.lift (n := n) (mlSource := mlSource) query).IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind)
      (if predicate RegistrationNativeKemInterface.OtherSpec KemSK kind query then 1 else 0) := by
  rcases query with other | (pool | key)
  · simp [RegistrationNativeKemServerInterface.lift, predicate, isQueryBoundP_query_iff]
  · cases pool <;> cases kind <;> simp [RegistrationNativeKemServerInterface.lift, predicate, isQueryBoundP_query_iff]
  · simp [RegistrationNativeKemServerInterface.lift, predicate, isQueryBoundP_query_iff]

/-- The actual primitive embedding preserves both indexed creation and reveal allowances. -/
theorem source_lift_bound (kind : Kind)
    (work : OracleComp (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP (predicate RegistrationNativeKemInterface.OtherSpec KemSK kind) cap) :
    (simulateQ (RegistrationNativeKemServerInterface.lift (n := n) (mlSource := mlSource)) work).IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ cap bounded
  exact source_lift_step kind

private theorem trusted_step (kind : Kind) (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain) :
    (RegistrationNativeKemBeaconCompiler.trusted (mlSource := mlSource) query).IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind)
      (if counted (n := n) (KemSK := KemSK) kind query then 1 else 0) := by
  cases query with
  | inl query => simp [RegistrationNativeKemBeaconCompiler.trusted, predicate, counted, isQueryBoundP_query_iff]
  | inr query =>
      cases query with
      | inl other =>
          simp [RegistrationNativeKemBeaconCompiler.trusted, RegistrationNativeKemServerInterface.lift,
            predicate, counted, isQueryBoundP_query_iff]
      | inr lower =>
          have same : counted (n := n) (KemSK := KemSK) kind (.inr (.inr lower)) =
              predicate RegistrationNativeKemInterface.OtherSpec KemSK kind (.inr lower) := by
            cases lower with
            | inl pool => cases pool <;> rfl
            | inr key => rfl
          simpa only [RegistrationNativeKemBeaconCompiler.trusted, same] using source_lift_step (n := n) (mlSource := mlSource) (KemSK := KemSK) kind (.inr lower)

private theorem trusted_bound (kind : Kind)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (counted (n := n) (KemSK := KemSK) kind) cap) :
    (simulateQ (RegistrationNativeKemBeaconCompiler.trusted (mlSource := mlSource)) work).IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ cap bounded
  exact trusted_step kind

private theorem get_bound (kind : Kind) :
    (RegistrationNativeKemServerInterface.get (n := n) (mlSource := mlSource) (KemSK := KemSK)).IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind) 0 := by
  simp [RegistrationNativeKemServerInterface.get, predicate, isQueryBoundP_query_iff]

private theorem put_bound (kind : Kind) (state : RegistrationNativeKemServerState.State n mlSource) :
    (RegistrationNativeKemServerInterface.put (KemSK := KemSK) state).IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind) 0 := by
  simp [RegistrationNativeKemServerInterface.put, predicate, isQueryBoundP_query_iff]

/-- The complete actual local-owner wrapper preserves each derived private KEM allowance. -/
theorem beacon_bound (kind : Kind)
    (work : RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State Value)
    (cap : Nat) (bounded : Bounded kind cap work) :
    (RegistrationNativeKemBeaconCompiler.beacon work).IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind) cap := by
  unfold RegistrationNativeKemBeaconCompiler.beacon
  rw [← Nat.zero_add cap]
  apply isQueryBoundP_bind (get_bound kind)
  intro before _supported
  rw [← Nat.add_zero cap]
  apply isQueryBoundP_bind (trusted_bound kind _ cap (bounded before.beacons _))
  intro result _reached
  apply isQueryBoundP_bind (m := 0) (get_bound kind)
  intro current _reached
  apply isQueryBoundP_bind (m := 0) (put_bound kind _)
  intro returned _reached
  simp

/-- Adding native build/record commands retains every original private indexed KEM allowance. -/
theorem frontend_lift_bound (kind : Kind)
    (work : OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP
      (predicate (RegistrationNativeKemServerInterface.Ambient n mlSource) KemSK kind) cap) :
    (simulateQ RegistrationNativeKemFrontendInterface.lift work).IsQueryBoundP
      (predicate (RegistrationNativeKemFrontendInterface.Ambient n mlSource) KemSK kind) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ cap bounded
  intro query
  rcases query with other | (pool | key)
  · simp [RegistrationNativeKemFrontendInterface.lift, predicate, isQueryBoundP_query_iff]
  · cases pool <;> cases kind <;> simp [RegistrationNativeKemFrontendInterface.lift, predicate, isQueryBoundP_query_iff]
  · simp [RegistrationNativeKemFrontendInterface.lift, predicate, isQueryBoundP_query_iff]

/-- Selected-accept routing changes only the public encapsulation surface and preserves private KEM class budgets. -/
theorem route_bound (kind : Kind) (selected : Bool)
    (work : OracleComp (RegistrationNativeKemFrontendInterface.Spec n mlSource KemSK) Value)
    (cap : Nat) (bounded : work.IsQueryBoundP
      (predicate (RegistrationNativeKemFrontendInterface.Ambient n mlSource) KemSK kind) cap) :
    (simulateQ (RegistrationNativeKemRouting.route selected) work).IsQueryBoundP
      (predicate (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK kind) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ cap bounded
  intro query
  rcases query with other | (pool | key)
  · simp [RegistrationNativeKemRouting.route, predicate, isQueryBoundP_query_iff]
  · cases pool <;> cases kind <;> simp [RegistrationNativeKemRouting.route, predicate, isQueryBoundP_query_iff]
  · cases selected <;> simp [RegistrationNativeKemRouting.route, predicate, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.source_lift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.source_lift_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.beacon_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.frontend_lift_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.frontend_lift_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.route_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemCompilerFootprint.route_bound

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemResourceCaps
import BeaconcryptCore.Computational.RegistrationPublicationQuerySafety
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedBundle
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources
open RegistrationNativeKemResourceFootprint (Kind)
open RegistrationNativePlatformGenericBundle (Spec M liftLegacy trustedLift encoder program)
open RegistrationNativeKemResourceCaps (NativeCounted)
open RegistrationPublicationQuerySafety (Safe pure_safe bind_safe)
attribute [local irreducible] BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
variable {n : Nat} {I E KemSK Auxiliary A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def Counted (kind : Kind) : (Spec E n KemSK).Domain → Prop
  | .inl query => NativeCounted (n := n) (KemSK := KemSK) kind query
  | .inr _ => False
instance (kind : Kind) : DecidablePred (Counted (E := E) (n := n) (KemSK := KemSK) kind) := fun query => by
  cases query with
  | inl query =>
      change Decidable (NativeCounted (n := n) (KemSK := KemSK) kind query)
      exact inferInstance
  | inr query =>
      change Decidable False
      exact isFalse (fun h => h)

abbrev Allowed (kind : Kind) (query : (Spec E n KemSK).Domain) : Prop := ¬ Counted (E := E) (n := n) (KemSK := KemSK) kind query

theorem lift_safe (kind : Kind) (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary A)
    (quiet : RegistrationNativeKemResourceFootprint.Bounded kind 0 work) :
    Safe (queries := Spec E n KemSK) (Allowed (E := E) (n := n) (KemSK := KemSK) kind) (liftLegacy (trustedLift (E := E) (KemSK := KemSK)) work) := by
  intro owners env
  apply (isQueryBoundP_zero_iff _ (Allowed (E := E) (n := n) (KemSK := KemSK) kind)).mp
  simp only [Allowed, not_not]
  change (simulateQ (trustedLift (E := E) (n := n) (KemSK := KemSK)) ((work.run owners).run env)).IsQueryBoundP (Counted (E := E) (n := n) (KemSK := KemSK) kind) 0
  have bounded : ((work.run owners).run env).IsQueryBoundP (NativeCounted (n := n) (KemSK := KemSK) kind) 0 := by
    simpa only [RegistrationNativeKemResourceCaps.native_counted_eq] using quiet owners env
  apply bounded.simulateQ_of_step
  · intro query paid
    simp [trustedLift, Counted, isQueryBoundP_query_iff]
  · intro query free
    simp only [trustedLift, isQueryBoundP_query_iff]
    intro paid
    exact False.elim (free paid)

theorem encoder_safe (kind : Kind) (view : registration.InitView) :
    Safe (queries := Spec E n KemSK) (Allowed (E := E) (n := n) (KemSK := KemSK) kind)
      (encoder (KemSK := KemSK) (source := source) (Auxiliary := Auxiliary) E view) := by
  intro owners env
  apply (isQueryBoundP_zero_iff _ (Allowed (E := E) (n := n) (KemSK := KemSK) kind)).mp
  simp only [Allowed, not_not]
  unfold encoder RegistrationNativePlatformGenericBundle.encoderWith
  simp only [StateT.run_lift, StateT.run_map, bind_pure_comp, isQueryBoundP_map_iff]
  apply (isQueryBoundP_false _ 0).simulateQ_of_step
  · intro query impossible
    exact False.elim impossible
  · intro query free
    simp [RegistrationNativePlatformGenericBundle.writerLift, Counted, isQueryBoundP_query_iff]

theorem program_safe (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) :
    Safe (queries := Spec E n KemSK) (Allowed (E := E) (n := n) (KemSK := KemSK) kind)
      (program (Auxiliary := Auxiliary) E setup source index) := by
  unfold program RegistrationNativePlatformGenericBundle.bundle
  apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _ _ (by intro owners env; exact allQueriesSatisfy_pure _ _)
  intro owners
  cases found : owners[index]? with
  | none => exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _
  | some owner =>
      cases phase : owner.phase <;> simp only [phase]
      all_goals try exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _
      all_goals
        apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _ _ (by first
          | exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _
          | exact lift_safe kind _ (RegistrationNativeKemResourceFootprint.sample_zero kind _))
        intro oneTime
        apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _ _
          (RegistrationPublicationQuerySafety.Beacon.begin (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _
            (fun query => lift_safe kind _ (RegistrationNativeKemResourceFootprint.outgoing_zero setup kind index owner query))
            _ (encoder_safe kind) _ _ _ _)
        intro published
        cases published with
        | fail error | div => exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _
        | ok result => cases result with
          | Err previous => exact pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _
          | Ok finished =>
              simp only
              apply bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _ _ (lift_safe kind _ (by
                intro current env
                simp [RegistrationNativeBeaconFrontend.updatePhase, StateT.run_modify]))
              intro changed
              exact bind_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _ _
                (lift_safe kind _ (RegistrationNativeKemResourceFootprint.effect_zero kind _))
                (fun _ => pure_safe (Allowed (E := E) (n := n) (KemSK := KemSK) kind) _)

theorem handler_bound {Platform : Type} (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (Spec E n KemSK).Domain) (before : RegistrationNativeKemServerState.State n source) (previous : Platform) :
    (((RegistrationNativePlatformKemCountedBundle.handler setup checks representation created writer query).run before).run previous).IsQueryBoundP
      (RegistrationNativeKemResourceCaps.Counted kind) (if Counted (E := E) (n := n) (KemSK := KemSK) kind query then 1 else 0) := by
  cases query with
  | inl query =>
      change ((StateT.lift ((RegistrationNativeKemCountedTrusted.implementation setup checks representation created query).run before)).run previous).IsQueryBoundP _ _
      simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
      exact RegistrationNativeKemResourceCaps.trusted_bound kind setup checks representation created query before
  | inr query =>
      change ((RegistrationNativeKemCountedProgram.liftState
        ((StateT.lift (writer query) : StateT (RegistrationNativeKemServerState.State n source) (StateT Platform ProbComp) _).run before)).run previous).IsQueryBoundP _ 0
      exact RegistrationNativeKemResourceCaps.liftState_free kind _ previous

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : X → Y) (work : StateT S m X) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

theorem counted_program {Platform : Type} (kind : Kind) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : RegistrationNativeKemServerState.State n source) (previous : Platform) :
    (((RegistrationNativePlatformKemCountedBundle.program setup checks representation created writer index).run before).run previous).IsQueryBoundP
      (RegistrationNativeKemResourceCaps.Counted kind) 0 := by
  unfold RegistrationNativePlatformKemCountedBundle.program
  simp only [StateT.run, bind_pure_comp, map_apply, isQueryBoundP_map_iff]
  apply RegistrationNativePlatformQueryBounds.simulate_bound
    (Counted (E := E) (n := n) (KemSK := KemSK) kind) (RegistrationNativeKemResourceCaps.Counted kind) _
    (handler_bound kind setup checks representation created writer) _ 0 _ before previous
  have safe := program_safe (n := n) (E := E) (Auxiliary := RegistrationServerRoleBackend.State) kind setup index before.beacons
    (RegistrationWorldAgreementCompiler.erase before.server.world)
  have bounded := (isQueryBoundP_zero_iff _ (Allowed (E := E) (n := n) (KemSK := KemSK) kind)).mpr safe
  simpa only [Allowed, not_not, StateT.run] using bounded

end BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.lift_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.lift_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.encoder_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.encoder_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.program_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.counted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBundleKemResources.counted_program

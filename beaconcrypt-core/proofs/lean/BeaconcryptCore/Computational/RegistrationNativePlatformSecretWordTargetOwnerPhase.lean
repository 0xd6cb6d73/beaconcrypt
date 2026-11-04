-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOwnerPhase
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordTargetPhaseCore (Selected)
open RegistrationNativeSecretWordMessage (zero)
open RegistrationNativePlatformPublicFrontend (LocalSpec trusted writer)
open RegistrationNativePlatformSecretWordOwnerRealization (base evaluated)
variable {n : Nat} {I KemSK Platform E A : Type} {spec : OracleSpec I}

private theorem program_evaluated
    (implementation : QueryImpl spec (StateT Platform (OracleComp (LocalSpec n KemSK))))
    (work : OracleComp spec A) (previous : Platform) :
    simulateQ (base zero) ((simulateQ implementation work).run previous) =
      (simulateQ (fun query => evaluated zero (implementation query)) work).run previous := by
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_bind]
      congr 1
      funext result
      exact ih result.1 result.2

private theorem trusted_zero (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (previous : Platform) :
    ((evaluated zero (trusted query)).run previous).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  change (simulateQ (base zero) ((trusted query).run previous)).IsQueryBoundP (Selected (KemSK := KemSK)) 0
  simp only [trusted, StateT.run_lift, bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff]
  rcases query with effect | other | pool | key
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
      RegistrationNativePlatformPublicFrontend.localQuery, base, RegistrationNativeSecretWordCheckedFrontend.realization,
      Selected, isQueryBoundP_query_iff]
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativeKemRouting.route, base,
      RegistrationNativeSecretWordCheckedFrontend.realization, RegistrationNativeSecretWordKemInterface.realize,
      RegistrationNativeSecretWordInterface.routedKem, Selected, isQueryBoundP_query_iff]
  · cases pool <;> simp_all [
      RegistrationBeaconReferenceCompiler.trustedLift,
      RegistrationBeaconReferenceCompiler.indexed, RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativeKemRouting.route, base, RegistrationNativeSecretWordCheckedFrontend.realization,
      RegistrationNativeSecretWordKemInterface.realize, RegistrationNativeSecretWordInterface.routedKem,
      Selected, isQueryBoundP_query_iff]
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativeKemRouting.route, base,
      RegistrationNativeSecretWordCheckedFrontend.realization, RegistrationNativeSecretWordKemInterface.realize,
      RegistrationNativeSecretWordInterface.routedKem, Selected, isQueryBoundP_query_iff]

private theorem writer_zero
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E).Domain) (previous : Platform) :
    ((evaluated (n := n) (KemSK := KemSK) zero (writer implementation query)).run previous).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  change (simulateQ (base zero) ((writer implementation query).run previous)).IsQueryBoundP (Selected (KemSK := KemSK)) 0
  simp only [writer, RegistrationNativePlatformPublicFrontend.platform, StateT.run,
    ← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.localCoin, base,
    RegistrationNativeSecretWordFrontend.effect, Selected, isQueryBoundP_query_iff]

private theorem program_zero
    (implementation : QueryImpl spec (StateT Platform (OracleComp (LocalSpec n KemSK))))
    (predicate : I → Prop)
    (queries : ∀ query, predicate query → ∀ previous,
      ((evaluated zero (implementation query)).run previous).IsQueryBoundP (Selected (KemSK := KemSK)) 0)
    (work : OracleComp spec A) (safe : AllQueriesSatisfy work predicate) (previous : Platform) :
    (simulateQ (base zero) ((simulateQ implementation work).run previous)).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  rw [program_evaluated]
  induction work using OracleComp.inductionOn generalizing previous with
  | pure value => trivial
  | query_bind query next ih =>
      obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply isQueryBoundP_bind (n := 0) (m := 0) (queries query first previous)
      intro result _
      exact ih result.1 (later result.1) result.2

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
variable {baseSpec : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- The actual full Word bundle never calls the selected getter on any source or mutable-writer branch. -/
theorem bundle_zero (setup : Setup baseSpec KemSK) (selectedOwner : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (target : Nat) (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) :
    (((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) (KemSK := KemSK) setup source
      selectedOwner publicPrekey reserveFrame implementation (.inr (.bundle target))).run before)).IsQueryBoundP
        (Selected (KemSK := KemSK)) 0 := by
  let joint : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK)
      (StateT Platform (OracleComp (LocalSpec n KemSK)))
    | .inl query => trusted query
    | .inr query => writer implementation query
  have actual := RegistrationNativePlatformGenericBundle.program_evaluate
    (source := source) (Auxiliary := RegistrationServerRoleBackend.State) joint setup target
  change RegistrationNativePlatformGenericBundle.evaluate joint _ =
    RegistrationNativePlatformGenericBundle.bundle trusted setup source
      (RegistrationNativePlatformGenericBundle.encoderWith (writer implementation)) target at actual
  simp only [RegistrationNativePlatformSecretWordOrdinary.handler, isQueryBoundP_map_iff,
    RegistrationNativePlatformSecretWordOrdinary.beacon, StateT.run, simulateQ_map,
    RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    map_apply, isQueryBoundP_map_iff]
  rw [← actual]
  unfold RegistrationNativePlatformGenericBundle.evaluate
  simp only [StateT.run]
  apply program_zero joint (fun _ => True)
  · intro query _safe current
    cases query with
    | inl query => exact trusted_zero query current
    | inr query => exact writer_zero implementation query current
  · have every {J V : Type} {spec : OracleSpec J} (work : OracleComp spec V) :
        AllQueriesSatisfy work (fun _ => True) := by
      induction work using OracleComp.inductionOn with
      | pure value => trivial
      | query_bind query next ih => exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,ih⟩
    exact every _

/-- The actual current constructor never calls the selected encapsulation getter, even if a later constructor stage fails. -/
theorem create_zero (setup : Setup baseSpec KemSK) (selectedOwner : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) (KemSK := KemSK) setup source selectedOwner publicPrekey reserveFrame writer
      (.inr (.create edPin mlPin keyId))).run before).IsQueryBoundP (Selected (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.handler, RegistrationNativePlatformSecretWordOrdinary.beacon,
    RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, simulateQ_map, isQueryBoundP_map_iff]
  change (simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base RegistrationNativeSecretWordMessage.zero)
    ((simulateQ RegistrationNativePlatformPublicFrontend.trusted
      (((RegistrationNativeBeaconFrontend.create (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup source edPin mlPin keyId).run (before.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.environment)).run before.2)).IsQueryBoundP
      (Selected (KemSK := KemSK)) 0
  rw [RegistrationNativePlatformSecretWordAliasCreate.native_program, isQueryBoundP_map_iff,
    RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler, QueryImpl.simulateQ_compose]
  exact RegistrationNativeSecretWordTargetPhaseCore.ordinary_free _

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOwnerPhase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOwnerPhase.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOwnerPhase.bundle_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOwnerPhase.create_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOwnerPhase.create_zero

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleBirth
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleNoCreate
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordTargetPoolFrame (IsCreate)
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
    (allowed : RegistrationNativePlatformSecretWordAliasBundleBirth.Native.Allowed query) (previous : Platform) :
    ((evaluated zero (trusted query)).run previous).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  change (simulateQ (base zero) ((trusted query).run previous)).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0
  simp only [trusted, StateT.run_lift, bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff]
  rcases query with effect | other | pool | key
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
      RegistrationNativePlatformPublicFrontend.localQuery, base, RegistrationNativeSecretWordCheckedFrontend.realization,
      IsCreate, isQueryBoundP_query_iff]
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativeKemRouting.route, base,
      RegistrationNativeSecretWordCheckedFrontend.realization, RegistrationNativeSecretWordKemInterface.realize,
      RegistrationNativeSecretWordInterface.routedKem, IsCreate, isQueryBoundP_query_iff]
  · cases pool <;> simp_all [RegistrationNativePlatformSecretWordAliasBundleBirth.Native.Allowed,
      RegistrationNativeKemBeaconFootprint.counted, RegistrationBeaconReferenceCompiler.trustedLift,
      RegistrationBeaconReferenceCompiler.indexed, RegistrationNativePlatformPublicFrontend.localQuery,
      RegistrationNativeKemRouting.route, base, RegistrationNativeSecretWordCheckedFrontend.realization,
      RegistrationNativeSecretWordKemInterface.realize, RegistrationNativeSecretWordInterface.routedKem,
      IsCreate, isQueryBoundP_query_iff]
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationNativePlatformPublicFrontend.localQuery, RegistrationNativeKemRouting.route, base,
      RegistrationNativeSecretWordCheckedFrontend.realization, RegistrationNativeSecretWordKemInterface.realize,
      RegistrationNativeSecretWordInterface.routedKem, IsCreate, isQueryBoundP_query_iff]

private theorem writer_zero
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E).Domain) (previous : Platform) :
    ((evaluated (n := n) (KemSK := KemSK) zero (writer implementation query)).run previous).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  change (simulateQ (base zero) ((writer implementation query).run previous)).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0
  simp only [writer, RegistrationNativePlatformPublicFrontend.platform, StateT.run,
    ← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.localCoin, base,
    RegistrationNativeSecretWordFrontend.effect, IsCreate, isQueryBoundP_query_iff]

private theorem program_zero
    (implementation : QueryImpl spec (StateT Platform (OracleComp (LocalSpec n KemSK))))
    (predicate : I → Prop)
    (queries : ∀ query, predicate query → ∀ previous,
      ((evaluated zero (implementation query)).run previous).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0)
    (work : OracleComp spec A) (safe : AllQueriesSatisfy work predicate) (previous : Platform) :
    (simulateQ (base zero) ((simulateQ implementation work).run previous)).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
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

/-- The actual full Word bundle creates no private KEM row on any source or writer branch. -/
theorem bundle_zero (setup : Setup baseSpec KemSK) (selectedOwner : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (target : Nat) (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) :
    (((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) (KemSK := KemSK) setup source
      selectedOwner publicPrekey reserveFrame implementation (.inr (.bundle target))).run before)).IsQueryBoundP
        (IsCreate (KemSK := KemSK)) 0 := by
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
  apply program_zero joint RegistrationNativePlatformSecretWordAliasBundleBirth.Allowed
  · intro query safe current
    cases query with
    | inl query => exact trusted_zero query safe current
    | inr query => exact writer_zero implementation query current
  · exact RegistrationNativePlatformSecretWordAliasBundleBirth.program_free setup target _ _
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleNoCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleNoCreate.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasBundleNoCreate.bundle_zero

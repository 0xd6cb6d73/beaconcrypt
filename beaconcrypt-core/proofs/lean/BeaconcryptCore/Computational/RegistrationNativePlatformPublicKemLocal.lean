-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemBundleCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationLocal
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic
/-! Actual common-platform routing preserves private indexed KEM creation and reveal counts. Constructor bounds use the genuine native constructor, while dynamic publication, corrected OPEN and assigned-ID finish retain their full source effects. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativeKemBeaconFootprint (Kind)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I}

def IsPrivate (kind : Kind) : (Spec n KemSK).Domain → Prop
  | .inl query => RegistrationNativeOpenKeyKemPublic.IsPrivate (KemSK := KemSK) kind query
  | .inr _ => False
def LocalPrivate (kind : Kind) : (LocalSpec n KemSK).Domain → Prop
  | .inl query => RegistrationNativeOpenKeyKemPublic.IsPrivate (KemSK := KemSK) kind (.inl query)
  | .inr _ => False
instance (kind : Kind) : DecidablePred (IsPrivate (n := n) (KemSK := KemSK) kind) := fun query => by
  cases query <;> dsimp [IsPrivate] <;> infer_instance
instance (kind : Kind) : DecidablePred (LocalPrivate (n := n) (KemSK := KemSK) kind) := fun query => by
  cases query <;> dsimp [LocalPrivate] <;> infer_instance

/-- The actual local-to-global embedding preserves every private-key query count. -/
theorem embed_bound (kind : Kind) (work : OracleComp (LocalSpec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind) count) :
    (simulateQ embedLocal work).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query =>
    simp only [embedLocal, IsPrivate, LocalPrivate, isQueryBoundP_query_iff]
    intro counted
    simp only [counted, ite_true]
    decide
  | inr query => simp [embedLocal, publicCoin, IsPrivate, LocalPrivate, isQueryBoundP_query_iff]

private theorem local_query (kind : Kind) (selected : Bool) (query : (RegistrationBeaconReferenceCompiler.Spec n KemSK).Domain) :
    (localQuery selected query).IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind)
      (if RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind query then 1 else 0) := by
  rcases query with message | (query | query)
  · simp [localQuery, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]
  · simp [localQuery, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]
  · rcases query with other | (pool | key)
    · simp [localQuery, RegistrationNativeKemRouting.route, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
        RegistrationNativeOpenKeyKemPublic.RoutedPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate,
        RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]
    · cases pool <;> cases kind <;>
        simp [localQuery, RegistrationNativeKemRouting.route, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
          RegistrationNativeOpenKeyKemPublic.RoutedPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate,
          RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]
    · cases selected <;>
        simp [localQuery, RegistrationNativeKemRouting.route, LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
          RegistrationNativeOpenKeyKemPublic.RoutedPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate,
          RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]

/-- Native local source trees retain their complete count through shared P. -/
theorem native_program (kind : Kind) (selected : Bool)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count) (before : Platform) :
    ((simulateQ (localHandler selected) work).run before).IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    have leaf := local_query (KemSK := KemSK) kind selected query
    rw [ite_eq_left counted] at leaf
    simpa only [localHandler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using leaf
  · intro query free current
    have leaf := local_query (KemSK := KemSK) kind selected query
    rw [ite_eq_right free] at leaf
    simpa only [localHandler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff] using leaf

/-- Arbitrary external sampler paths have no private KEM access. -/
theorem platform_zero (kind : Kind) (work : StateT Platform ProbComp A) (before : Platform) :
    ((platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [localCoin, LocalPrivate, isQueryBoundP_query_iff]

/-- The actual trusted dictionary preserves the genuine source constructor count. -/
theorem trusted_program (kind : Kind)
    (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (KemSK := KemSK) kind) count) (before : Platform) :
    ((simulateQ trusted work).run before).IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simp only [trusted, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    rcases query with query | (query | (query | key))
    all_goals simp only [RegistrationBeaconReferenceCompiler.trustedLift,
      RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
      localQuery, RegistrationNativeKemRouting.route, Bool.false_eq_true, ite_false, simulateQ_spec_query]
    all_goals simp [LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
      RegistrationNativeOpenKeyKemPublic.RoutedPrivate, isQueryBoundP_query_iff]
  · intro query free current
    simp only [trusted, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
    rcases query with query | (query | (query | key))
    all_goals simp only [RegistrationBeaconReferenceCompiler.trustedLift,
      RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
      localQuery, RegistrationNativeKemRouting.route, Bool.false_eq_true, ite_false, simulateQ_spec_query]
    all_goals simp_all [LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
      RegistrationNativeOpenKeyKemPublic.RoutedPrivate, RegistrationNativeKemBeaconFootprint.counted,
      isQueryBoundP_query_iff]
    all_goals cases query <;> simp_all

private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual public creation has at most one indexed birth and no reveal, on every constructor failure path. -/
theorem create_bound (kind : Kind) (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.create (trusted (n := n) (KemSK := KemSK)) setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run before).IsQueryBoundP
      (LocalPrivate (KemSK := KemSK) kind) (if kind = .create then 1 else 0) := by
  simp only [RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, isQueryBoundP_map_iff]
  exact trusted_program kind _ _ (RegistrationNativeKemBeaconFootprint.create_bound setup kind edPin mlPin keyId _ _) before

private theorem trusted_quiet (kind : Kind)
    (query : (RegistrationNativeBeaconFrontend.Trusted n KemSK).Domain)
    (safe : RegistrationNativePlatformPublicKemBundleCaps.Native.Allowed query) (before : Platform) :
    ((trusted query).run before).IsQueryBoundP (LocalPrivate (KemSK := KemSK) kind) 0 := by
  simp only [trusted, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
  rcases query with query | (query | (query | key))
  all_goals simp only [RegistrationBeaconReferenceCompiler.trustedLift,
    RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
    localQuery, RegistrationNativeKemRouting.route, Bool.false_eq_true, ite_false, simulateQ_spec_query]
  all_goals first
    | solve | simp [LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
        RegistrationNativeOpenKeyKemPublic.RoutedPrivate, isQueryBoundP_query_iff]
    | cases query <;> simp_all [LocalPrivate, RegistrationNativeOpenKeyKemPublic.IsPrivate,
        RegistrationNativeOpenKeyKemPublic.RoutedPrivate, RegistrationNativePlatformPublicKemBundleCaps.Native.Allowed,
        isQueryBoundP_query_iff]

private theorem owner_program (kind : Kind)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) A)
    (safe : work.AllQueriesSatisfy (RegistrationNativePlatformPublicKemBundleCaps.Allowed (E := E) (KemSK := KemSK))) (before : Platform) :
    ((simulateQ (fun (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain) => match query with | .inl query => trusted query | .inr query => writer implementation query) work).run before).IsQueryBoundP
      (LocalPrivate (KemSK := KemSK) kind) 0 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    obtain ⟨first, later⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp safe
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    apply isQueryBoundP_bind (m := 0)
    · cases query with
      | inl query => exact trusted_quiet kind query first before
      | inr query => exact platform_zero kind (implementation query) before
    · intro result _
      exact ih result.1 (later result.1) result.2

/-- The actual dynamic shared-writer bundle has zero private birth and reveal allowance. -/
theorem bundle_zero (kind : Kind) {source : RegistrationNativeMldsa.Source} (setup : Setup base KemSK)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (index : Nat)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformPublicOwners.bundle (trusted (n := n) (KemSK := KemSK)) (writer implementation) setup source selected publicPrekey index).run owners).run env).run before).IsQueryBoundP
      (LocalPrivate (KemSK := KemSK) kind) 0 := by
  let joint : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (Base n KemSK Platform)
    | .inl query => trusted query
    | .inr query => writer implementation query
  have actual := RegistrationNativePlatformGenericBundle.program_evaluate (Auxiliary := RegistrationServerRoleBackend.State) joint setup source index
  change RegistrationNativePlatformGenericBundle.evaluate joint _ = RegistrationNativePlatformGenericBundle.bundle trusted setup source
    (RegistrationNativePlatformGenericBundle.encoderWith (writer implementation)) index at actual
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal, StateT.run, map_apply, isQueryBoundP_map_iff]
  rw [← actual]
  unfold RegistrationNativePlatformGenericBundle.evaluate
  simp only [StateT.run]
  exact owner_program kind implementation _ (RegistrationNativePlatformPublicKemBundleCaps.program_free setup index _ _) before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.embed_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.embed_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.platform_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.platform_zero

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.trusted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.trusted_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.bundle_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicKemLocal.bundle_zero

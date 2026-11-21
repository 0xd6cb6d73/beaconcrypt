-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundleInterpretation
import BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
/-! Actual bundle publication and scalar sampling preserve every World owner slot and the complete private KEM pool. The no-creation/no-advance query restriction is derived from the real outgoing callbacks and extracted writer tree. Arbitrary failed primitive/writer continuations retain their full shared poststates, so lifecycle readiness follows from initial source material rather than an assumed successful native installation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundleSafety
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationNativePlatformFrontend (Work interpret)
variable {n : Nat} {I KemSK E A B Platform : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Front" => RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK))

def Safe : (Trusted n KemSK).Domain → Prop
  | .inl (.inl _) => True
  | .inl (.inr (.hash _)) => True
  | _ => False

def Allowed : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain → Prop
  | .inl query => Safe (n := n) (KemSK := KemSK) query
  | .inr _ => True

def Snapshot (state : Native) := (state.server.world.world.1.owners, state.pool)

def LegacySafe (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) : Prop :=
  ∀ owners env, ((work.run owners).run env).AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK))

private theorem pure_safe (value : A) : LegacySafe (pure value : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) :=
  fun _ _ => allQueriesSatisfy_pure _ _
private theorem bind_safe (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (next : A → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State B)
    (first : LegacySafe work) (later : ∀ value, LegacySafe (next value)) : LegacySafe (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)
private theorem lift_safe (work : OracleComp (Trusted n KemSK) A)
    (allowed : work.AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK))) :
    LegacySafe (RegistrationNativeAgreementJournal.lift (source := source) (Auxiliary := RegistrationServerRoleBackend.State) work) := by
  intro owners env
  rw [RegistrationNativeAgreementJournal.lift_run, ← bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)
private theorem effect_safe (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (allowed : Safe (KemSK := KemSK) (.inl query)) :
    LegacySafe (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) query) :=
  lift_safe _ ((allQueriesSatisfy_query_iff _ _).mpr allowed)
private theorem simulate_safe {J : Type} {spec : OracleSpec J}
    (handler : QueryImpl spec (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))
    (allowed : ∀ query, LegacySafe (handler query)) (work : OracleComp spec A) : LegacySafe (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using pure_safe value
  | query_bind query next ih => simpa only [simulateQ_bind, simulateQ_spec_query] using bind_safe _ _ (allowed query) ih
private theorem sample_safe (work : ProbComp A) :
    LegacySafe (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) work) :=
  simulate_safe _ (fun query => effect_safe (.inl query) trivial) work

theorem outgoing_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    LegacySafe (RegistrationNativeBeaconFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect_safe _ trivial
    | sign request payload digest => exact pure_safe _
  | inr request =>
      simp only [RegistrationNativeBeaconFrontend.outgoing]
      split
      · exact bind_safe _ _ (fun _ _ => allQueriesSatisfy_pure _ _) (fun _ => pure_safe _)
      · exact pure_safe _

theorem legacy_safe (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (safe : LegacySafe work) : Work (Allowed (E := E) (n := n) (KemSK := KemSK))
      (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) work) := by
  intro owners env
  change (simulateQ (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) ((work.run owners).run env)).AllQueriesSatisfy _
  have transfer {C : Type} (program : OracleComp (Trusted n KemSK) C)
      (allowed : program.AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK))) :
      (simulateQ (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) program).AllQueriesSatisfy
        (Allowed (E := E) (n := n) (KemSK := KemSK)) := by
    induction program using OracleComp.inductionOn with
    | pure value => exact allQueriesSatisfy_pure _ _
    | query_bind query next ih =>
        rw [allQueriesSatisfy_query_bind_iff] at allowed
        rw [simulateQ_bind, simulateQ_spec_query]
        apply allQueriesSatisfy_bind
        · simpa only [RegistrationNativePlatformGenericBundle.trustedLift, allQueriesSatisfy_query_iff, Allowed] using allowed.1
        · exact fun reply => ih reply (allowed.2 reply)
  exact transfer _ (safe owners env)

theorem joint_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Work (Allowed (E := E) (n := n) (KemSK := KemSK)) (RegistrationNativePlatformFrontend.joint setup index owner query) := by
  cases query with
  | inl request => exact legacy_safe _ (outgoing_safe setup index owner request)
  | inr request =>
      apply RegistrationNativePlatformFrontend.lifted_work
      simp only [RegistrationNativePlatformGenericBundle.writerLift, allQueriesSatisfy_query_iff, Allowed]

theorem publication_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes) :
    Work (Allowed (E := E) (n := n) (KemSK := KemSK))
      (RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoder E) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
        ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar)⟩ owner.pin) := by
  rw [← RegistrationNativePlatformFrontend.publication_tree setup index owner _ _ _ _]
  exact RegistrationNativePlatformFrontend.simulate_work _ _ (joint_safe setup index owner) _


variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

theorem query_snapshot (query : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain)
    (allowed : Allowed (E := E) (n := n) (KemSK := KemSK) query) (before : Native) (previous : Platform)
    (result : ((RegistrationNativePlatformGenericBundle.Spec E n KemSK).Range query × Native) × Platform)
    (reached : result ∈ support (((RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer query).run before).run previous)) :
    Snapshot result.1.2 = Snapshot before := by
  cases query with
  | inl query =>
      have actual : result.1 ∈ support ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before) :=
        RegistrationNativePlatformHashReceipt.native_support coins _ result.1 previous result.2 reached
      cases query with
      | inl effect =>
          have safe : RegistrationNativeWorldOwnerFrame.Safe (KemSK := KemSK) (.inl effect) := by
            cases effect with
            | inl coin => trivial
            | inr capability => cases capability <;> trivial
          have owners := RegistrationNativeWorldOwnerFrame.trusted setup checks representation created (.inl effect) safe before result.1 actual
          have pool : result.1.2.pool = before.pool := by
            simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
              RegistrationNativeExperiment.server, StateT.run, Functor.map_map, support_map] at actual
            obtain ⟨inner, _called, same⟩ := actual
            exact (congrArg (fun output => output.2.pool) same).symm
          exact Prod.ext owners pool
      | inr query => exact False.elim allowed
  | inr query =>
      simp only [RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.writer,
        StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at reached
      obtain ⟨inner, _called, same⟩ := reached
      cases same
      rfl

theorem program_snapshot (work : OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK) A)
    (allowed : work.AllQueriesSatisfy (Allowed (E := E) (n := n) (KemSK := KemSK)))
    (before : Native) (previous : Platform) (result : (A × Native) × Platform)
    (reached : result ∈ support (((simulateQ (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before).run previous)) :
    Snapshot result.1.2 = Snapshot before := by
  induction work using OracleComp.inductionOn generalizing before previous result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
      cases reached
      rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨inner, called, continued⟩ := reached
      exact (ih inner.1.1 (allowed.2 inner.1.1) inner.1.2 inner.2 result continued).trans
        (query_snapshot coins setup checks representation created writer query allowed.1 before previous inner called)

theorem interpreted_snapshot (work : Front A)
    (allowed : Work (Allowed (E := E) (n := n) (KemSK := KemSK)) work)
    (before : Native) (previous : Platform) (result : (A × Native) × Platform)
    (reached : result ∈ support (((interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer) work).run before).run previous)) :
    Snapshot result.1.2 = Snapshot before := by
  rw [RegistrationNativePlatformFrontend.run_interpret, StateT.run_map, support_map] at reached
  obtain ⟨inner, called, same⟩ := reached
  cases same
  exact program_snapshot coins setup checks representation created writer _
    (allowed before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world)) before previous inner called


theorem sample_snapshot (draw : ProbComp A) (before : Native) (previous : Platform) (result : (A × Native) × Platform)
    (reached : result ∈ support (((interpret
      (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
        (RegistrationNativeBeaconFrontend.sample draw))).run before).run previous)) :
    Snapshot result.1.2 = Snapshot before :=
  interpreted_snapshot coins setup checks representation created writer _ (legacy_safe _ (sample_safe draw)) before previous result reached

end BeaconcryptCore.Computational.RegistrationNativeBundleSafety

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.outgoing_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.outgoing_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.legacy_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.legacy_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.joint_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.joint_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.publication_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.publication_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.query_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.query_snapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.program_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.program_snapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.interpreted_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.interpreted_snapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundleSafety.sample_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundleSafety.sample_snapshot

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch
import BeaconcryptCore.Computational.RegistrationNativePlatformExperiment
/-! The actual corrected bundle frontend is interpreted on one complete Native state over an arbitrary common platform monad. Its per-query local-state commutation law is derived for the literal Native trusted interpreter and the state-independent writer lift. The complete actual signing/publication and extracted writer request tree satisfies the no-Other restriction, so sequencing retains the same Native state and shared platform effects on every failure. No whole-source-controller or arbitrary-backend frame premise remains in the actual bundle instantiation. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformFrontend
open RegistrationNativeBeaconFrontend (Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeFinishTerminalTree (assemble)
variable {n : Nat} {I J KemSK A B : Type} {base : OracleSpec I} {queries : OracleSpec J}
variable {source : RegistrationNativeMldsa.Source} {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Front" => RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State (OracleComp queries)
local notation "Local" => EnvState RegistrationServerRoleBackend.State
variable (implementation : QueryImpl queries (StateT (RegistrationNativeExperiment.State n KemSK source) m)) (permitted : J → Prop)

def Atomic : Prop := ∀ query, permitted query → ∀ owners env before,
  (implementation query).run (assemble owners env before) =
    (fun result => (result.1, assemble owners env result.2)) <$> (implementation query).run before

theorem program_patch (atomic : Atomic implementation permitted) (work : OracleComp queries A)
    (allowed : work.AllQueriesSatisfy permitted) (owners : List (Owner source)) (env : Local) (before : Native) :
    (simulateQ implementation work).run (assemble owners env before) =
      (fun result => (result.1, assemble owners env result.2)) <$> (simulateQ implementation work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [atomic query allowed.1 owners env before]
      simp only [bind_map_left, map_bind]
      apply bind_congr
      intro result
      exact ih result.1 (allowed.2 result.1) result.2

def interpret (work : Front A) : StateT Native m A := fun before =>
  (fun result => (result.1.1.1, assemble result.1.1.2 result.1.2 result.2)) <$>
    (simulateQ implementation ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before

omit implementation in
def Work (work : Front A) : Prop := ∀ owners env, ((work.run owners).run env).AllQueriesSatisfy permitted

omit [LawfulMonad m] in
theorem run_interpret (work : Front A) (before : Native) :
    (interpret implementation work).run before =
      (fun result => (result.1.1.1, assemble result.1.1.2 result.1.2 result.2)) <$>
        (simulateQ implementation ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before := rfl

theorem pure_interpret (value : A) : interpret implementation (pure value : Front A) = pure value := by
  funext before
  change (interpret implementation (pure value : Front A)).run before = (pure value : StateT Native m A).run before
  rw [run_interpret]
  simp only [StateT.run_pure, simulateQ_pure, map_pure, RegistrationNativeLocalStatePatch.assemble_self]

theorem bind_interpret (atomic : Atomic implementation permitted) (work : Front A) (next : A → Front B)
    (allowed : ∀ value, Work permitted (next value)) :
    interpret implementation (work >>= next) = (interpret implementation work >>= fun value => interpret implementation (next value)) := by
  funext before
  change (interpret implementation (work >>= next)).run before =
    ((interpret implementation work >>= fun value => interpret implementation (next value)) : StateT Native m B).run before
  rw [run_interpret, StateT.run_bind]
  simp only [run_interpret, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]
  apply bind_congr
  intro result
  have ownerView : (assemble result.1.1.2 result.1.2 result.2).beacons = result.1.1.2 := rfl
  simp only [ownerView, RegistrationNativeLocalStatePatch.assemble_erase]
  rw [program_patch implementation permitted atomic _ (allowed result.1.1.1 result.1.1.2 result.1.2)]
  simp only [Functor.map_map, RegistrationNativeLocalStatePatch.assemble_overwrite]

omit implementation [Monad m] [LawfulMonad m] in
theorem pure_work (value : A) : Work permitted (pure value : Front A) := fun _ _ => allQueriesSatisfy_pure _ _

omit implementation [Monad m] [LawfulMonad m] in
theorem bind_work (work : Front A) (next : A → Front B)
    (first : Work permitted work) (later : ∀ value, Work permitted (next value)) : Work permitted (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)

omit implementation [Monad m] [LawfulMonad m] in
theorem simulate_work {K : Type} {spec : OracleSpec K} (handler : QueryImpl spec Front)
    (allowed : ∀ query, Work permitted (handler query)) (work : OracleComp spec A) : Work permitted (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_work permitted value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_work permitted _ _ (allowed query) ih

theorem simulate_interpret {K : Type} {spec : OracleSpec K} (atomic : Atomic implementation permitted)
    (handler : QueryImpl spec Front) (allowed : ∀ query, Work permitted (handler query)) (work : OracleComp spec A) :
    interpret implementation (simulateQ handler work) = simulateQ (fun query => interpret implementation (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, pure_interpret]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [bind_interpret implementation permitted atomic _ _ (fun reply => simulate_work permitted handler allowed (next reply))]
      simp only [ih]


omit implementation permitted in
def AllowedBundle {E : Type} : (RegistrationNativePlatformGenericBundle.Spec E n KemSK).Domain → Prop
  | .inl query => RegistrationNativeLocalEnvironmentFrame.Allowed (n := n) (KemSK := KemSK) query
  | .inr _ => True

omit implementation permitted in
theorem bundle_atomic {E : Type} (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m) :
    Atomic (RegistrationNativePlatformExperiment.bundleHandler (n := n) coins setup checks representation created source writer) (AllowedBundle (E := E) (n := n) (KemSK := KemSK)) := by
  intro query allowed owners env before
  cases query with
  | inl query =>
      change simulateQ coins ((RegistrationNativeExperiment.trusted setup checks representation created source query).run (assemble owners env before)) =
        (fun result => (result.1, assemble owners env result.2)) <$> simulateQ coins ((RegistrationNativeExperiment.trusted setup checks representation created source query).run before)
      rw [RegistrationNativeLocalStatePatch.trusted_patch setup checks representation created query allowed owners env before, simulateQ_map]
  | inr query =>
      simp only [RegistrationNativePlatformExperiment.bundleHandler, RegistrationNativePlatformExperiment.writer,
        StateT.run_lift, bind_pure_comp, Functor.map_map]


omit implementation [Monad m] [LawfulMonad m] in
private theorem raw_simulate {K : Type} {spec : OracleSpec K} (predicate : K → Prop)
    (handler : QueryImpl spec (OracleComp queries))
    (steps : ∀ query, predicate query → (handler query).AllQueriesSatisfy permitted)
    (work : OracleComp spec A) (allowed : work.AllQueriesSatisfy predicate) :
    (simulateQ handler work).AllQueriesSatisfy permitted := by
  induction work using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      rw [simulateQ_bind, simulateQ_spec_query]
      exact allQueriesSatisfy_bind (steps query allowed.1) (fun reply => ih reply (allowed.2 reply))

omit implementation permitted [Monad m] [LawfulMonad m] in
theorem legacy_work {E : Type} (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (allowed : RegistrationNativeLocalStatePatch.Work work) :
    Work (AllowedBundle (E := E) (n := n) (KemSK := KemSK))
      (RegistrationNativePlatformGenericBundle.liftLegacy (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) work) := by
  intro owners env
  change (simulateQ (RegistrationNativePlatformGenericBundle.trustedLift (E := E)) ((work.run owners).run env)).AllQueriesSatisfy _
  exact raw_simulate (AllowedBundle (E := E) (n := n) (KemSK := KemSK))
    (RegistrationNativeLocalEnvironmentFrame.Allowed (n := n) (KemSK := KemSK))
    (RegistrationNativePlatformGenericBundle.trustedLift (E := E) (n := n) (KemSK := KemSK))
    (by
      intro query valid
      simpa only [RegistrationNativePlatformGenericBundle.trustedLift, allQueriesSatisfy_query_iff, AllowedBundle] using valid)
    _ (allowed owners env)


omit implementation [Monad m] [LawfulMonad m] in
theorem lifted_work (work : OracleComp queries A) (allowed : work.AllQueriesSatisfy permitted) :
    Work permitted (StateT.lift (StateT.lift work) : Front A) := by
  intro owners env
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

omit implementation permitted [Monad m] [LawfulMonad m] in
theorem encoder_work {E : Type} (view : registration.SignedInitView) :
    Work (AllowedBundle (E := E) (n := n) (KemSK := KemSK))
      (RegistrationNativePlatformGenericBundle.encoder (n := n) (KemSK := KemSK) (source := source) (Auxiliary := RegistrationServerRoleBackend.State) E view) := by
  unfold RegistrationNativePlatformGenericBundle.encoder RegistrationNativePlatformGenericBundle.encoderWith
  apply lifted_work
  apply raw_simulate _ (fun _ => True)
  · intro query _
    simp only [RegistrationNativePlatformGenericBundle.writerLift, allQueriesSatisfy_query_iff, AllowedBundle]
  · induction (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeInit
        (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
        (RegistrationNativePlatformWriter.initPacket view)).run using OracleComp.inductionOn with
    | pure value => exact allQueriesSatisfy_pure _ _
    | query_bind query next ih => exact ⟨trivial, ih⟩


omit implementation permitted [Monad m] [LawfulMonad m] in
theorem double_simulate {K : Type} {spec : OracleSpec K}
    (handler : QueryImpl spec (OracleComp queries)) (work : OracleComp spec A) :
    simulateQ (fun query => (StateT.lift (StateT.lift (handler query)) : Front _)) work =
      (StateT.lift (StateT.lift (simulateQ handler work)) : Front A) := by
  exact simulateQ_liftTarget handler work

omit implementation permitted [Monad m] [LawfulMonad m] in
noncomputable def joint {E : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source) :
    QueryImpl (RegistrationNativePlatformWriter.Spec E)
      (RegistrationNativePlatformGenericBundle.M source RegistrationServerRoleBackend.State (OracleComp (RegistrationNativePlatformGenericBundle.Spec E n KemSK)))
  | .inl query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)
  | .inr query => StateT.lift (StateT.lift (RegistrationNativePlatformGenericBundle.writerLift query))

omit implementation permitted [Monad m] [LawfulMonad m] in
theorem joint_work {E : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : (RegistrationNativePlatformWriter.Spec E).Domain) :
    Work (AllowedBundle (E := E) (n := n) (KemSK := KemSK)) (joint setup index owner query) := by
  cases query with
  | inl query => exact legacy_work _ (RegistrationNativeLocalStatePatch.outgoing_work setup index owner query)
  | inr query =>
      apply lifted_work
      simp only [RegistrationNativePlatformGenericBundle.writerLift, allQueriesSatisfy_query_iff, AllowedBundle]

omit implementation permitted [Monad m] [LawfulMonad m] in
theorem publication_tree {E : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    simulateQ (joint (n := n) (E := E) setup index owner) (RegistrationNativePlatformWriter.begin E control inputs coins pin mldsa) =
      RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoder E) control inputs coins pin mldsa := by
  rw [RegistrationNativePlatformWriter.begin_interpret]
  simp only [joint, double_simulate]
  rfl

omit implementation permitted [Monad m] [LawfulMonad m] in
theorem publication_work {E : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) :
    Work (AllowedBundle (E := E) (n := n) (KemSK := KemSK))
      (RegistrationNativePlatformBeaconPublication.begin
        (fun query => RegistrationNativePlatformGenericBundle.liftLegacy RegistrationNativePlatformGenericBundle.trustedLift
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
        (RegistrationNativePlatformGenericBundle.encoder E) control inputs coins pin mldsa) := by
  rw [← publication_tree setup index owner control inputs coins pin mldsa]
  exact simulate_work _ _ (joint_work setup index owner) _


omit implementation permitted [Monad m] [LawfulMonad m] in
def publicBytes (reply : RustM (Option (alloc.vec.Vec U8))) : RustM (Option Pqxdh.Bytes) := do
  let optional ← reply
  pure (optional.map TranscriptAuthParts.absSlice)

omit implementation permitted in
theorem actual_bundle {E : Type} (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m) (index : Nat) :
    RegistrationNativePlatformExperiment.bundle (n := n) coins setup checks representation created source writer index =
      publicBytes <$> interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
        (RegistrationNativePlatformGenericBundle.program E setup source index) := by
  funext before
  change (RegistrationNativePlatformExperiment.bundle coins setup checks representation created source writer index).run before =
    ((publicBytes <$> interpret (RegistrationNativePlatformExperiment.bundleHandler coins setup checks representation created source writer)
      (RegistrationNativePlatformGenericBundle.program E setup source index)) : StateT Native m (RustM (Option Pqxdh.Bytes))).run before
  rw [StateT.run_map, run_interpret]
  unfold RegistrationNativePlatformExperiment.bundle publicBytes
  simp only [StateT.run, bind_pure_comp, Functor.map_map]
  rfl


end BeaconcryptCore.Computational.RegistrationNativePlatformFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.program_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.program_patch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.run_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.run_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.pure_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.pure_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.bind_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.bind_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.pure_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.pure_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.bind_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.bind_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.simulate_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.simulate_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.simulate_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.simulate_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.bundle_atomic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.bundle_atomic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.legacy_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.legacy_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.lifted_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.lifted_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.encoder_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.encoder_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.joint_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.joint_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.publication_tree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.publication_tree

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.publication_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.publication_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.actual_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.actual_bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.double_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFrontend.double_simulate

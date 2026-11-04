-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLocalEnvironmentFrame
import BeaconcryptCore.Computational.RegistrationNativeFinishTerminalTree
/-! Actual trusted World and indexed-private-KEM effects commute with local frontend roster/environment overwrites. The property is derived from those implementations, retaining private pools, shared cache and real counters. It yields exact sequencing and free-program interpretation on the actual Beacon paths without OtherSpec calls. Actual outgoing authentication, signing receipts and Ed histories satisfy this restriction; no whole-controller correspondence or read-only private backend premise is used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch
open RegistrationNativeBeaconFrontend (Trusted Owner)
open RegistrationNativeLocalEnvironmentFrame (Allowed)
open RegistrationNativeFinishTerminalTree (assemble)
variable {n : Nat} {I J KemSK Auxiliary A B : Type} {base : OracleSpec I} {ambient : OracleSpec J} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

theorem source_patch (baseImpl : QueryImpl base ProbComp)
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := base) (SK := KemSK))
    (other : QueryImpl ambient (StateT Auxiliary ProbComp))
    (query : PqxdhLiveKemBirth.Query ⊕ PqxdhKemIndCca.MlKem768PublicKey)
    (before after : Auxiliary) (pool : PqxdhLiveKemBirth.Pool KemSK) :
    (RegistrationNativeKemInterface.source baseImpl kem ambient other (.inr query)).run (after, pool) =
      (fun result => (result.1, (after, result.2.2))) <$>
        (RegistrationNativeKemInterface.source baseImpl kem ambient other (.inr query)).run (before, pool) := by
  cases query with
  | inl query => simp only [RegistrationNativeKemInterface.source, StateT.run, Functor.map_map]
  | inr key => simp only [RegistrationNativeKemInterface.source, StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem map_apply {S X Y : Type} (observe : X → Y) (work : StateT S ProbComp X) (state : S) :
    (observe <$> work) state = (fun result => (observe result.1, result.2)) <$> work state := by
  change (observe <$> work).run state = _
  simp only [StateT.run_map]
  rfl


private theorem lift_apply {S X : Type} (work : ProbComp X) (state : S) :
    (StateT.lift work : StateT S ProbComp X) state = (fun value => (value, state)) <$> work := by
  change (StateT.lift work : StateT S ProbComp X).run state = _
  simp only [StateT.run_lift, bind_pure_comp]


theorem trusted_patch (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : (Trusted n KemSK).Domain) (allowed : Allowed query)
    (owners : List (Owner source)) (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Native) :
    (RegistrationNativeExperiment.trusted setup checks representation created source query).run (assemble owners env before) =
      (fun result => (result.1, assemble owners env result.2)) <$>
        (RegistrationNativeExperiment.trusted setup checks representation created source query).run before := by
  cases query with
  | inl effect =>
      simp only [RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
        assemble, RegistrationWorldAgreementCompiler.join, StateT.run, Functor.map_map]
  | inr query => cases query with
    | inl other => exact False.elim allowed
    | inr lower =>
        simp only [RegistrationNativeExperiment.trusted, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map]
        cases lower with
        | inl query =>
            simp only [RegistrationNativeKemInterface.source, StateT.run, Functor.map_map, simulateQ_map, map_apply, assemble, RegistrationWorldAgreementCompiler.join]
        | inr key =>
            simp only [RegistrationNativeKemInterface.source, lift_apply, Functor.map_map, simulateQ_map, map_apply, assemble, RegistrationWorldAgreementCompiler.join]

theorem program_patch (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp (Trusted n KemSK) A) (allowed : work.AllQueriesSatisfy (Allowed (n := n) (KemSK := KemSK)))
    (owners : List (Owner source)) (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Native) :
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run (assemble owners env before) =
      (fun result => (result.1, assemble owners env result.2)) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at allowed
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [trusted_patch setup checks representation created query allowed.1 owners env before]
      simp only [bind_map_left, map_bind]
      apply bind_congr
      intro result
      exact ih result.1 (allowed.2 result.1) result.2


theorem assemble_overwrite (owners firstOwners : List (Owner source))
    (env firstEnv : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Native) :
    assemble owners env (assemble firstOwners firstEnv before) = assemble owners env before := rfl

private theorem assemble_owners (owners : List (Owner source))
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Native) :
    (assemble owners env before).beacons = owners := rfl


theorem assemble_erase (owners : List (Owner source))
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Native) :
    RegistrationWorldAgreementCompiler.erase (assemble owners env before).server.world = env := rfl

theorem assemble_self (before : Native) :
    assemble before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world) before = before := by
  unfold assemble
  rw [RegistrationWorldAgreementCompiler.join_erase]

theorem beacon_run (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) (before : Native) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      (fun result => (result.1.1.1, assemble result.1.1.2 result.1.2 result.2)) <$>
        (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
          ((work.run before.beacons).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before := by
  unfold RegistrationNativeExperiment.beacon
  simp only [StateT.run, bind_pure_comp]
  rfl


def Work (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) : Prop :=
  ∀ owners env, ((work.run owners).run env).AllQueriesSatisfy (Allowed (n := n) (KemSK := KemSK))

theorem pure_work (value : A) : Work (pure value : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A) :=
  fun _ _ => allQueriesSatisfy_pure _ _

theorem bind_work (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (next : A → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State B)
    (first : Work work) (later : ∀ value, Work (next value)) : Work (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)

theorem simulate_work {K : Type} {queries : OracleSpec K}
    (handler : QueryImpl queries (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))
    (allowed : ∀ query, Work (handler query)) (work : OracleComp queries A) : Work (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_work value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_work _ _ (allowed query) ih


theorem beacon_pure (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit) (value : A) :
    RegistrationNativeExperiment.beacon (n := n) (mlSource := source) setup checks representation created (pure value) = pure value := by
  funext before
  change (RegistrationNativeExperiment.beacon setup checks representation created (pure value)).run before = (pure value : RegistrationNativeExperiment.M n KemSK source A).run before
  rw [beacon_run]
  simp only [StateT.run_pure, simulateQ_pure, map_pure, assemble_self]

theorem beacon_bind (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State A)
    (next : A → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State B)
    (allowed : ∀ value, Work (next value)) :
    RegistrationNativeExperiment.beacon setup checks representation created (work >>= next) = (do
      let value ← RegistrationNativeExperiment.beacon setup checks representation created work
      RegistrationNativeExperiment.beacon setup checks representation created (next value)) := by
  funext before
  change (RegistrationNativeExperiment.beacon setup checks representation created (work >>= next)).run before =
    ((RegistrationNativeExperiment.beacon setup checks representation created work >>= fun value =>
      RegistrationNativeExperiment.beacon setup checks representation created (next value)) : RegistrationNativeExperiment.M n KemSK source B).run before
  rw [beacon_run, StateT.run_bind]
  simp only [beacon_run, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]
  apply bind_congr
  intro result
  simp only [assemble_owners, assemble_erase]
  rw [program_patch setup checks representation created _ (allowed result.1.1.1 result.1.1.2 result.1.2)]
  simp only [Functor.map_map, assemble_overwrite]


theorem beacon_simulate {K : Type} {queries : OracleSpec K}
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (handler : QueryImpl queries (RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State))
    (allowed : ∀ query, Work (handler query)) (work : OracleComp queries A) :
    RegistrationNativeExperiment.beacon setup checks representation created (simulateQ handler work) =
      simulateQ (fun query => RegistrationNativeExperiment.beacon setup checks representation created (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, beacon_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      rw [beacon_bind setup checks representation created _ _ (fun reply => simulate_work handler allowed (next reply))]
      simp only [ih]


theorem lifted_work (work : OracleComp (Trusted n KemSK) A)
    (allowed : work.AllQueriesSatisfy (Allowed (n := n) (KemSK := KemSK))) :
    Work (RegistrationNativeAgreementJournal.lift (source := source) (Auxiliary := RegistrationServerRoleBackend.State) work) := by
  intro owners env
  rw [RegistrationNativeAgreementJournal.lift_run, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

theorem effect_work (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    Work (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) query) :=
  lifted_work _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)

theorem sample_work (work : ProbComp A) :
    Work (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := RegistrationServerRoleBackend.State) work) := by
  unfold RegistrationNativeBeaconFrontend.sample
  exact simulate_work _ (fun query => effect_work (.inl query)) work

theorem env_work (change : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State → RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) :
    Work (RegistrationNativeBeaconFrontend.updateEnv (n := n) (KemSK := KemSK) (mldsaSource := source) change) := by
  intro owners env
  exact allQueriesSatisfy_pure _ _

theorem log_ed_work (index : Nat) (message : Pqxdh.Bytes) (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Work (RegistrationNativeBeaconFrontend.logEd (n := n) (Auxiliary := RegistrationServerRoleBackend.State) (KemSK := KemSK) (mldsaSource := source) index message signature) := by
  intro owners env
  exact allQueriesSatisfy_pure _ _

theorem outgoing_work (setup : PqxdhServerAuthExperiment.Setup base KemSK) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Work (RegistrationNativeBeaconFrontend.outgoing (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup source index owner query) := by
  cases query with
  | inl query => cases query with
    | hash request => exact effect_work _
    | sign request payload digest =>
        unfold RegistrationNativeBeaconFrontend.outgoing
        exact bind_work _ _ (sample_work _) (fun reply => bind_work _ _ (env_work _) (fun _ => pure_work reply))
  | inr request =>
      simp only [RegistrationNativeBeaconFrontend.outgoing]
      split
      · exact bind_work _ _ (log_ed_work _ _ _) (fun _ => pure_work _)
      · exact pure_work _


theorem outgoing_native (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
    (index : Nat) (owner : Owner source) (work : OracleComp RegistrationBeaconInitExecutor.Spec A) :
    RegistrationNativeExperiment.beacon (n := n) setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner) work) =
      simulateQ (fun query => RegistrationNativeExperiment.beacon setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)) work :=
  beacon_simulate setup checks representation created _ (outgoing_work setup index owner) work


end BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.source_patch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.source_patch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.trusted_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.trusted_patch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.program_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.program_patch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.assemble_overwrite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.assemble_overwrite

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.assemble_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.assemble_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.assemble_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.assemble_self

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.pure_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.pure_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.bind_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.bind_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.simulate_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.simulate_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_simulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.beacon_simulate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.lifted_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.lifted_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.effect_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.effect_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.sample_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.sample_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.env_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.env_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.log_ed_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.log_ed_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.outgoing_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.outgoing_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.outgoing_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeLocalStatePatch.outgoing_native

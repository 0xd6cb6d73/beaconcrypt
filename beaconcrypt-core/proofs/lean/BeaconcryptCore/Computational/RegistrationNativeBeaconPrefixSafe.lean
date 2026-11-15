-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldOwnerFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationNativeWorldOwnerFrame (Safe)
variable {n : Nat} {I KemSK Auxiliary A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

def Work (work : M n KemSK source Auxiliary A) : Prop :=
  ∀ owners env, ((work.run owners).run env).AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK))

theorem pure_safe (value : A) : Work (pure value : M n KemSK source Auxiliary A) := fun _ _ => allQueriesSatisfy_pure _ _

theorem bind_safe (work : M n KemSK source Auxiliary A) (next : A → M n KemSK source Auxiliary B)
    (first : Work work) (later : ∀ value, Work (next value)) : Work (work >>= next) := by
  intro owners env
  rw [StateT.run_bind, StateT.run_bind]
  exact allQueriesSatisfy_bind (first owners env) (fun result => later result.1.1 result.1.2 result.2)

theorem lift_safe (work : OracleComp (Trusted n KemSK) A)
    (allowed : work.AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK))) :
    Work (RegistrationNativeAgreementJournal.lift (source := source) (Auxiliary := Auxiliary) work) := by
  intro owners env
  rw [RegistrationNativeAgreementJournal.lift_run, ← bind_pure_comp]
  exact allQueriesSatisfy_bind allowed (fun _ => allQueriesSatisfy_pure _ _)

theorem effect_safe (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (allowed : Safe (KemSK := KemSK) (Sum.inl query)) :
    Work (RegistrationNativeBeaconFrontend.effect (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) query) :=
  lift_safe _ ((allQueriesSatisfy_query_iff _ _).mpr allowed)

theorem kem_safe (query : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain) :
    Work (RegistrationNativeBeaconFrontend.kem (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) query) :=
  lift_safe _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)

theorem simulate_safe {J : Type} {queries : OracleSpec J}
    (handler : QueryImpl queries (M n KemSK source Auxiliary)) (steps : ∀ query, Work (handler query))
    (work : OracleComp queries A) : Work (simulateQ handler work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_safe _
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_safe _ _ (steps query) ih

theorem sample_safe (work : ProbComp A) :
    Work (RegistrationNativeBeaconFrontend.sample (n := n) (KemSK := KemSK) (mldsaSource := source) (Auxiliary := Auxiliary) work) := by
  unfold RegistrationNativeBeaconFrontend.sample
  apply simulate_safe
  intro query
  exact effect_safe (.inl query) trivial

theorem env_safe (change : RegistrationWorldAgreementCompiler.EnvState Auxiliary → RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    Work (RegistrationNativeBeaconFrontend.updateEnv (n := n) (KemSK := KemSK) (mldsaSource := source) change) := by
  intro owners env
  exact allQueriesSatisfy_pure _ _

theorem authentication_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (query : RegistrationAuthenticationExecutor.Request) :
    Work (RegistrationNativeBeaconFrontend.authentication (n := n) (Auxiliary := Auxiliary) setup source query) := by
  cases query with
  | hash request => exact bind_safe _ _ (effect_safe _ trivial) (fun _ => pure_safe _)
  | mldsa request | ed25519 request => exact pure_safe _

theorem primitive_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementShared.PrimitiveRequest) :
    Work (RegistrationNativeBeaconFrontend.primitive (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.primitive
  apply simulate_safe
  intro lower
  cases lower with
  | inl query => apply sample_safe
  | inr query => exact kem_safe _

theorem agreement_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (query : RegistrationAgreementExecutor.Request) :
    Work (RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := Auxiliary) setup owner oneTime query) := by
  unfold RegistrationNativeBeaconFrontend.agreement
  apply bind_safe _ _ (env_safe _)
  intro unused
  cases query with
  | root request => exact pure_safe _
  | _ => exact primitive_safe setup owner oneTime _

theorem record_safe (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (query : RegistrationRecordPrimitives.Request) :
    Work (RegistrationNativeBeaconFrontend.record (n := n) (mldsaSource := source) (Auxiliary := Auxiliary) setup wire query) := by
  unfold RegistrationNativeBeaconFrontend.record
  apply bind_safe _ _ (env_safe _)
  intro unused
  cases query with
  | hash transcript => exact bind_safe _ _ (effect_safe _ trivial) (fun _ => pure_safe _)
  | adHash request => exact bind_safe _ _ (effect_safe _ trivial) (fun _ => pure_safe _)
  | rootKdf request | initialKdf request | ratchetKdf request | «seal» request | write request | openAead request => apply sample_safe
theorem lower_owners (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : M n KemSK source RegistrationServerRoleBackend.State A) (allowed : Work work)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : A × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created work).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners := by
  simp only [RegistrationNativeExperiment.beacon, StateT.run, mem_support_bind_iff] at reached
  obtain ⟨inner, called, returned⟩ := reached
  simp only [support_pure, Set.mem_singleton_iff] at returned
  cases returned
  exact RegistrationNativeWorldOwnerFrame.program setup checks representation created _
    (allowed before.beacons (RegistrationWorldAgreementCompiler.erase before.server.world)) before inner called

theorem authentication_owners (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : OracleComp RegistrationAuthenticationExecutor.Spec A)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : A × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work)).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners :=
  lower_owners setup checks representation created _ (simulate_safe _ (authentication_safe setup) work) before result reached

theorem agreement_owners (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp RegistrationAgreementExecutor.Spec A)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : A × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) work)).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners :=
  lower_owners setup checks representation created _ (simulate_safe _ (agreement_safe setup owner oneTime) work) before result reached

theorem record_owners (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationRecordPrimitives.Spec A)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : A × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.record setup wire) work)).run before)) :
    result.2.server.world.world.1.owners = before.server.world.world.1.owners :=
  lower_owners setup checks representation created _ (simulate_safe _ (record_safe setup wire) work) before result reached

end BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.pure_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.pure_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.bind_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.bind_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.lift_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.lift_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.effect_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.effect_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.kem_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.kem_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.simulate_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.simulate_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.sample_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.sample_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.env_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.env_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.authentication_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.authentication_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.primitive_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.primitive_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.agreement_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.agreement_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.record_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.record_safe
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.lower_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.lower_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.authentication_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.authentication_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.agreement_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.agreement_owners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.record_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconPrefixSafe.record_owners

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconRoleBackend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The actual native Beacon primitive and root callbacks preserve the entire locally owned identity, one-time scalar and KEM secret. Projecting their return values therefore commutes with arbitrary adaptive agreement work. Optional decapsulation failures and their probability law remain the literal selected KEM service. -/
namespace BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly
open RegistrationAgreementExecutor RegistrationAgreementShared
variable {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def implementation (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationBeaconRoleBackend.State KemSK) : QueryImpl Spec ProbComp :=
  fun query => Prod.fst <$> (auxiliary setup.source (RegistrationBeaconRoleBackend.native setup scalar) query).run before

noncomputable section

theorem query (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationBeaconRoleBackend.State KemSK) (request : Request) :
    (auxiliary setup.source (RegistrationBeaconRoleBackend.native setup scalar) request).run before =
      (fun reply => (reply, before)) <$> implementation setup scalar before request := by
  cases request with
  | convertPublic key => simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]
  | convertSecret role =>
    cases role <;> simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]
  | generate role => simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]
  | encapsulate input => simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]
  | decapsulate input =>
    cases input with
    | none => simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
        RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]
    | some input =>
      cases present : before.kem with
      | none => simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
          RegistrationBeaconRoleBackend.localBackend, StateT.run, present, map_pure]
      | some secret => simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
          RegistrationBeaconRoleBackend.localBackend, StateT.run, present, Functor.map_map]
  | dh request =>
    rcases request with ⟨role, publicKey⟩
    cases role <;> simp [implementation, auxiliary, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]
  | root request => simp [implementation, auxiliary, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]


theorem program {Value : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationBeaconRoleBackend.State KemSK)
    (work : OracleComp Spec Value) :
    (simulateQ (auxiliary setup.source (RegistrationBeaconRoleBackend.native setup scalar)) work).run before =
      (fun reply => (reply, before)) <$> simulateQ (implementation setup scalar before) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind request next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query setup scalar before request]
    simp only [bind_map_left, map_bind, ih]

theorem projection {Value : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before : RegistrationBeaconRoleBackend.State KemSK)
    (work : OracleComp Spec Value) :
    Prod.fst <$> (simulateQ (auxiliary setup.source (RegistrationBeaconRoleBackend.native setup scalar)) work).run before =
      simulateQ (implementation setup scalar before) work := by
  rw [program, Functor.map_map]
  exact id_map _
end
end BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly.query

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly.program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly.projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly.projection

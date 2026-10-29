-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemInterface

/-! Concrete native Server and Beacon primitive callbacks factor through the indexed KEM service. The executable Beacon owns a generated handle rather than a secret. Its mathematical source projection recovers precisely the private pool lookup, while all ordinary role state, optional replies and non-KEM effects remain the actual native ones. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemBackend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemInterface (OtherSpec OtherRequest Spec source)
open RegistrationAgreementShared (PrimitiveSpec PrimitiveRequest)
variable {ι KemSK Result : Type} {base : OracleSpec ι}

noncomputable def serverOther (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl OtherSpec (StateT RegistrationServerRoleBackend.State ProbComp) :=
  fun query => RegistrationServerRoleBackend.native setup checks representation seed query.primitive

noncomputable def server (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : PqxdhJointIdentity.IdentitySeed) :
    QueryImpl PrimitiveSpec (StateT (RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) ProbComp) :=
  (source setup.baseImpl setup.kem OtherSpec (serverOther setup checks representation seed)) ∘ₛ
    RegistrationNativeKemInterface.server checks

private theorem server_other (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : OtherRequest) (before : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :
    (server setup checks representation seed query.primitive).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (RegistrationServerRoleBackend.native setup checks representation seed query.primitive).run before.1 := by
  cases query <;> simp only [OtherRequest.primitive, server, QueryImpl.apply_compose,
    RegistrationNativeKemInterface.server, RegistrationNativeKemInterface.other, simulateQ_spec_query, source, serverOther, StateT.run] <;> rfl

/-- Exposing the actual native encapsulation getter retains the entire original role state and private key pool. -/
theorem server_query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : PrimitiveRequest) (before : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :
    (server setup checks representation seed query).run before =
      (fun result => (result.1, (result.2, before.2))) <$>
        (RegistrationServerRoleBackend.native setup checks representation seed query).run before.1 := by
  cases query with
  | convertPublic key => exact server_other setup checks representation seed (.convertPublic key) before
  | convertSecret role => exact server_other setup checks representation seed (.convertSecret role) before
  | generate role => exact server_other setup checks representation seed (.generate role) before
  | dh request => exact server_other setup checks representation seed (.dh request) before
  | decapsulate ciphertext => simp [server, QueryImpl.apply_compose, RegistrationNativeKemInterface.server,
      RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend]
  | encapsulate key =>
    cases key with
    | none => simp [server, QueryImpl.apply_compose, RegistrationNativeKemInterface.server,
        RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend]
    | some key =>
      by_cases valid : checks.kemKey (RegistrationRootInput.pqKey key) = true
      · simp only [server, QueryImpl.apply_compose, RegistrationNativeKemInterface.server, valid, ite_true,
          RegistrationNativeKemInterface.encapsulate, simulateQ_map, simulateQ_spec_query, source,
          StateT.run_map, RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend,
          PqxdhServerAuthExperiment.encapsulate, StateT.run_lift, Functor.map_map, bind_pure_comp]
        rfl
      · simp [server, QueryImpl.apply_compose, RegistrationNativeKemInterface.server, valid,
          RegistrationServerRoleBackend.native, RegistrationServerRoleBackend.localBackend]

/-- Arbitrary adaptive native Server primitive work is exactly the old concrete backend after dropping only the indexed pool instrumentation. -/
theorem server_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (seed : PqxdhJointIdentity.IdentitySeed)
    (work : OracleComp PrimitiveSpec Result) (before : RegistrationServerRoleBackend.State × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id Prod.fst <$> (simulateQ (server setup checks representation seed) work).run before =
      (simulateQ (RegistrationServerRoleBackend.native setup checks representation seed) work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query state
  rw [server_query, Functor.map_map]
  change id <$> _ = _
  exact id_map _

structure Beacon where
  identity : PqxdhJointIdentity.IdentitySeed
  oneTime : Option PqxdhJointGapDh.ScalarBytes
  kem : Option Nat

def realize (before : Beacon × PqxdhLiveKemBirth.Pool KemSK) : RegistrationBeaconRoleBackend.State KemSK :=
  ⟨before.1.identity, before.1.oneTime, before.1.kem.bind fun handle => (before.2.keys[handle]?).map Prod.snd⟩

noncomputable def beaconOther (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl OtherSpec (StateT Beacon ProbComp) := fun query before =>
  (fun result => (result.1, before)) <$>
    (RegistrationBeaconRoleBackend.native setup scalar query.primitive).run ⟨before.identity, before.oneTime, none⟩

noncomputable def beaconCallback : QueryImpl PrimitiveSpec (StateT Beacon (OracleComp (Spec OtherSpec KemSK))) :=
  fun query before => (fun result => (result, before)) <$>
    RegistrationNativeKemInterface.beacon before.kem query

noncomputable def beacon (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl PrimitiveSpec (StateT (Beacon × PqxdhLiveKemBirth.Pool KemSK) ProbComp) := fun query before =>
  (simulateQ (source setup.baseImpl setup.kem OtherSpec (beaconOther setup scalar))
      (RegistrationNativeKemInterface.beacon before.1.kem query)).run before

private theorem other_project (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : OtherRequest) (before : Beacon × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id realize <$>
      (source setup.baseImpl setup.kem OtherSpec (beaconOther setup scalar) (.inl query)).run before =
      (RegistrationBeaconRoleBackend.native setup scalar query.primitive).run (realize before) := by
  cases query with
  | convertPublic key => rfl
  | convertSecret role => cases role <;> rfl
  | generate role => cases role <;> rfl
  | dh request =>
    cases role : request.secret_role
    all_goals
      simp only [source, beaconOther, OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
        RegistrationBeaconRoleBackend.localBackend, role, StateT.run, realize, map_pure,
        StateT.monad_pure_def, StateT.pure]
      rfl

/-- The native Beacon decapsulation getter is realized at its actual private generated index, including missing handles and all optional fallback replies. -/
theorem beacon_query (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (query : PrimitiveRequest) (before : Beacon × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id realize <$> (beacon setup scalar query).run before =
      (RegistrationBeaconRoleBackend.native setup scalar query).run (realize before) := by
  cases query with
  | convertPublic key => simpa only [OtherRequest.primitive, Spec, OtherSpec, PrimitiveSpec, RegistrationAgreementExecutor.Spec, beacon, StateT.run, RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, simulateQ_spec_query] using other_project setup scalar (.convertPublic key) before
  | convertSecret role => simpa only [OtherRequest.primitive, Spec, OtherSpec, PrimitiveSpec, RegistrationAgreementExecutor.Spec, beacon, StateT.run, RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, simulateQ_spec_query] using other_project setup scalar (.convertSecret role) before
  | generate role => simpa only [OtherRequest.primitive, Spec, OtherSpec, PrimitiveSpec, RegistrationAgreementExecutor.Spec, beacon, StateT.run, RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, simulateQ_spec_query] using other_project setup scalar (.generate role) before
  | dh request => simpa only [OtherRequest.primitive, Spec, OtherSpec, PrimitiveSpec, RegistrationAgreementExecutor.Spec, beacon, StateT.run, RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other, simulateQ_spec_query] using other_project setup scalar (.dh request) before
  | encapsulate key => simp [beacon, StateT.run, StateT.monad_pure_def, StateT.pure, RegistrationNativeKemInterface.beacon, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend]
  | decapsulate ciphertext =>
    cases ciphertext with
    | none => simp [beacon, StateT.run, StateT.monad_pure_def, StateT.pure, RegistrationNativeKemInterface.beacon, RegistrationBeaconRoleBackend.native,
        RegistrationBeaconRoleBackend.localBackend]
    | some ciphertext =>
      cases handleFound : before.1.kem with
      | none => simp [beacon, StateT.run, StateT.monad_pure_def, StateT.pure, RegistrationNativeKemInterface.beacon, handleFound, RegistrationBeaconRoleBackend.native,
          RegistrationBeaconRoleBackend.localBackend, realize]
      | some handle =>
        simp only [beacon, StateT.run, RegistrationNativeKemInterface.beacon, handleFound]
        change Prod.map id realize <$>
          ((fun reply => RegistrationAgreementRoot.nativeOption (reply.map PqxdhRootTableInitialization.rootArray)) <$>
            source setup.baseImpl setup.kem OtherSpec (beaconOther setup scalar)
              (.inr (.inl (.decapsulate handle (PqxdhPhase2InputBytes.ciphertext ciphertext))))).run before = _
        rw [StateT.run_map]
        simp only [source, PqxdhLiveKemBirth.poolImpl, StateT.run, bind_pure_comp, Functor.map_map]
        simp only [RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend,
          realize, handleFound, Option.bind_some]
        cases found : before.2.keys[handle]? with
        | none => simp only [found, Option.map_none, map_pure,
            Prod.map, id_eq, realize, PqxdhLiveKemBirth.record, handleFound, Option.bind_some, RegistrationAgreementRoot.nativeOption]
        | some pair => simp only [found, Option.map_some, Functor.map_map, Prod.map, id_eq,
            realize, PqxdhLiveKemBirth.record, handleFound, Option.bind_some]

/-- Every adaptive native Beacon primitive continuation uses the same actual private key and full concrete role state after the index projection. -/
theorem beacon_program (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp PrimitiveSpec Result) (before : Beacon × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id realize <$> (simulateQ (beacon setup scalar) work).run before =
      (simulateQ (RegistrationBeaconRoleBackend.native setup scalar) work).run (realize before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ realize (beacon_query setup scalar) work before

end BeaconcryptCore.Computational.RegistrationNativeKemBackend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBackend.server_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBackend.server_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBackend.server_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBackend.server_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBackend.beacon_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBackend.beacon_query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemBackend.beacon_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemBackend.beacon_program

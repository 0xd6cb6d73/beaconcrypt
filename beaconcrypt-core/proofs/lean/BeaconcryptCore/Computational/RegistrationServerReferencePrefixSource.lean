-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative

/-! The private source collector retains a redundant CTX cache coordinate. This module derives its projection to the actual native prefix from the primitive callbacks, so the public collector correspondence does not assume an entire phase simulation. The related-root interface used here remains the legacy source interface; the native interface embeds it explicitly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerRootCompiler (Local Shared coins)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem state_map_run {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work).run before = Prod.map f id <$> work.run before := by
  change (work.run before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

noncomputable def sourcePrefix (setup : Setup base KemSK) (checks : Checks) :=
  PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl (RegistrationServerRootCompiler.backend (n := n) setup checks))
    RegistrationServerRootCompiler.visit

noncomputable def collect (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :=
  simulateQ (sourcePrefix (n := n) setup checks)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))

private theorem backend_project (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Shared n) :
    Prod.map id Prod.fst <$> (RegistrationServerRootCompiler.backend setup checks query).run before =
      simulateQ coins ((RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.localBackend setup checks) query).run before.1) := by
  change Prod.map id Prod.fst <$> simulateQ coins
    ((RegistrationAgreementShared.implementation setup.source
      (RegistrationWorldRoot.primitive setup.source (RegistrationServerRoleBackend.localBackend setup checks)) query).run before) = _
  rw [← simulateQ_map, RegistrationWorldRoot.backend_project]

private theorem prep_project (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain) (before : Shared n) :
    Prod.map id Prod.fst <$>
      (RegistrationAgreementInterpreter.prepImpl (RegistrationServerRootCompiler.backend setup checks) query).run before =
      simulateQ coins ((RegistrationAgreementInterpreter.prepImpl
        (RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.localBackend setup checks)) query).run before.1) := by
  cases query <;> simp only [RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | rw [QueryImpl.simulateQ_mapStateTBase_run]
      exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (backend_project setup checks) _ before
    | simp only [StateT.run_pure, simulateQ_pure, map_pure, Prod.map, id_eq]

private theorem visit_project (point : PqxdhBeaconPhase2Preparation.Word32) (before : Shared n) :
    Prod.map id Prod.fst <$> (RegistrationServerRootCompiler.visit point).run before =
      simulateQ coins ((RegistrationWorldRoot.visit point).run before.1) := by
  change Prod.map id Prod.fst <$> simulateQ coins
    ((RegistrationWorldRoot.visitShared point).run before) = _
  simp only [RegistrationWorldRoot.visitShared, RegistrationWorldRoot.visit, StateT.run,
    map_pure, simulateQ_pure, Prod.map, id_eq]

/-- Dropping the redundant outer cache gives the actual native callback, including every optional result and all other state. -/
theorem query_project (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Shared n) :
    Prod.map id Prod.fst <$> (sourcePrefix setup checks query).run before =
      simulateQ coins ((RegistrationServerReferenceCompilerNative.nativePrefix setup checks query).run before.1) := by
  cases query with
  | decode raw => exact prep_project setup checks (.decode raw) before
  | identity packet => exact prep_project setup checks (.identity packet) before
  | identityPoint key => exact prep_project setup checks (.identityPoint key) before
  | pqField packet => exact prep_project setup checks (.pqField packet) before
  | preField packet => exact prep_project setup checks (.preField packet) before
  | oneField packet => exact prep_project setup checks (.oneField packet) before
  | verify key signed => exact prep_project setup checks (.verify key signed) before
  | registrationStatus identifier => exact prep_project setup checks (.registrationStatus identifier) before
  | reserveRegistration => exact prep_project setup checks .reserveRegistration before
  | parseDh point => exact prep_project setup checks (.parseDh point) before
  | generate => exact prep_project setup checks .generate before
  | parseKem key => exact prep_project setup checks (.parseKem key) before
  | encapsulate key => exact prep_project setup checks (.encapsulate key) before
  | publicConversion key => exact prep_project setup checks (.publicConversion key) before
  | privateConversion => exact prep_project setup checks .privateConversion before
  | ephemeralDh secret point => exact prep_project setup checks (.ephemeralDh secret point) before
  | staticDh point =>
      simp only [sourcePrefix, RegistrationServerReferenceCompilerNative.nativePrefix,
        PqxdhServerStaticDhSource.prefixImpl, RegistrationServerRootCompiler.visit,
        RegistrationServerRootCompiler.liftProb, RegistrationWorldRoot.visitShared,
        RegistrationWorldRoot.visit, StateT.run, StateT.monad_pure_def, StateT.pure,
        StateT.monad_bind_def, StateT.bind, simulateQ_pure, map_pure, pure_bind,
        Prod.map, id_eq]

/-- The whole source collector projects by derived callback laws, without a cache-diagonal or prefix-simulation premise. -/
theorem collect_project (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Shared n) :
    Prod.map id Prod.fst <$> (collect setup checks packet authenticated).run before =
      simulateQ coins ((simulateQ (RegistrationServerReferenceCompilerNative.nativePrefix setup checks)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run before.1) := by
  rw [collect, QueryImpl.simulateQ_mapStateTBase_run]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst (query_project setup checks) _ before

private theorem coins_source (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : PqxdhJointIdentity.Primitives)
    (dh : PqxdhJointGapDh.DhInterface joint) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : ProbComp Value)
    (before : RegistrationServerRootCompiler.Family) :
    (simulateQ (RegistrationServerRootCompiler.family hmac joint dh seed scalar)
      (simulateQ coins work)).run before = (fun value => (value, before)) <$> work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationServerRootCompiler.family hmac joint dh seed scalar ∘ₛ coins =
      (QueryImpl.ofLift unifSpec ProbComp).liftTarget
        (StateT RegistrationServerRootCompiler.Family ProbComp) := by
    funext query
    rfl
  rw [same, simulateQ_liftTarget, simulateQ_ofLift_eq_self, StateT.run_liftM, bind_pure_comp]

private theorem coins_source_drop (hmac : PqxdhSecretInputKdf.HmacSha512) (joint : PqxdhJointIdentity.Primitives)
    (dh : PqxdhJointGapDh.DhInterface joint) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (work : ProbComp Value)
    (before : RegistrationServerRootCompiler.Family) :
    Prod.fst <$> (simulateQ (RegistrationServerRootCompiler.family hmac joint dh seed scalar)
      (simulateQ coins work)).run before = work := by
  rw [coins_source, Functor.map_map]
  exact id_map _

private theorem interpret_run {A Result : Type}
    (family : QueryImpl PqxdhJointDhExtractRoot.RootSpec
      (StateT RegistrationServerRootCompiler.Family ProbComp))
    (work : StateT A (OracleComp PqxdhJointDhExtractRoot.RootSpec) Result)
    (before : RegistrationServerRootCompiler.Family × A) :
    (RegistrationServerRootCompiler.interpret family work).run before =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        (simulateQ family (work.run before.2)).run before.1 := rfl

private theorem interpret_project {A B Result : Type}
    (family : QueryImpl PqxdhJointDhExtractRoot.RootSpec
      (StateT RegistrationServerRootCompiler.Family ProbComp))
    (work : StateT A (OracleComp PqxdhJointDhExtractRoot.RootSpec) Result)
    (project : A → B) (before : RegistrationServerRootCompiler.Family × A) :
    Prod.map id (fun state => project state.2) <$>
      (RegistrationServerRootCompiler.interpret family work).run before =
      Prod.fst <$> (simulateQ family (Prod.map id project <$> work.run before.2)).run before.1 := by
  simp only [interpret_run, simulateQ_map, state_map_run, Functor.map_map, Prod.map, id_eq]

/-- Restoring the actual private related-root interpreter leaves the entire concrete prefix unchanged, including failed callbacks; only the private family and redundant cache coordinates are forgotten. -/
theorem collect_native (setup : Setup base KemSK) (checks : Checks)
    (hmac : PqxdhSecretInputKdf.HmacSha512) (dh : PqxdhJointGapDh.DhInterface setup.joint)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (familyBefore : RegistrationServerRootCompiler.Family) (before : Shared n) :
    Prod.map id (fun state : RegistrationServerRootCompiler.Family × Shared n => state.2.1) <$>
      (RegistrationServerRootCompiler.interpret
        (RegistrationServerRootCompiler.family hmac setup.joint dh seed scalar)
        (collect setup checks packet authenticated)).run (familyBefore, before) =
      (simulateQ (RegistrationServerReferenceCompilerNative.nativePrefix setup checks)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run before.1 := by
  have projected := congrArg (fun work => (simulateQ
    (RegistrationServerRootCompiler.family hmac setup.joint dh seed scalar) work).run familyBefore)
    (collect_project setup checks packet authenticated before)
  have mapped := congrArg (fun work => Prod.fst <$> work) projected
  rw [coins_source_drop] at mapped
  rw [interpret_project]
  exact mapped

end BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource.collect_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource.collect_project
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource.collect_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferencePrefixSource.collect_native

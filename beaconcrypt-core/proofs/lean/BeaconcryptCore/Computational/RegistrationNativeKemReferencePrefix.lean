-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceBackend

/-! Closing the actual open native KEM prefix preserves the complete native agreement result and World. The native correspondence is derived for every primitive query, including the exposed encapsulation, before lifting it to the adaptive source collector. Only the independently accounted extra Env coin ledger is projected. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativeKemReferenceBackend (State project)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Extra Value Index : Type} {base : OracleSpec ι} {spec : OracleSpec Index}

noncomputable def lower (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (work : StateT Environment (OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK)) Value) :
    StateT (State n KemSK Extra) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (implementation setup callbacks) (work.run before.1)).run before.2

private theorem lower_run (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (work : StateT Environment (OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK)) Value)
    (before : State n KemSK Extra) :
    (lower setup callbacks work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (implementation setup callbacks) (work.run before.1)).run before.2 := rfl

private theorem lower_program (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (interpreter : QueryImpl spec (StateT Environment (OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK))))
    (work : OracleComp spec Value) : lower setup callbacks (simulateQ interpreter work) =
      simulateQ (fun query => lower setup callbacks (interpreter query)) work := by
  have same : (fun query => lower setup callbacks (interpreter query)) =
      ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT := rfl
  rw [same]
  funext before
  change (lower setup callbacks (simulateQ interpreter work)).run before =
    (simulateQ ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT work).run before
  rw [lower_run, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change id <$> (simulateQ ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT work).run before = _
  exact id_map _

noncomputable def sourcePrefix (setup : Setup base KemSK) (checks : Checks) :=
  PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend (n := n) setup checks))
    RegistrationNativeKemReferenceCompiler.visit

private theorem prep_project (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain)
    (before : State n KemSK Extra) :
    Prod.map id project <$> (lower setup callbacks
      (RegistrationAgreementInterpreter.prepImpl (RegistrationNativeKemReferenceCompiler.backend setup checks) query)).run before =
      (RegistrationAgreementInterpreter.prepImpl
        (RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.localBackend setup checks)) query).run (project before) := by
  cases query <;> simp only [RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | rw [lower_program]
      exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
        (RegistrationNativeKemReferenceBackend.query_project setup checks callbacks) _ before
    | simp only [lower_run, StateT.run_pure, simulateQ_pure, map_pure, Prod.map, id_eq]

/-- Every actual decoded prefix callback keeps the native reply and complete projected World. -/
theorem query_project (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : State n KemSK Extra) :
    Prod.map id project <$> (lower setup callbacks (sourcePrefix setup checks query)).run before =
      (RegistrationServerReferenceCompilerNative.nativePrefix setup checks query).run (project before) := by
  cases query with
  | decode raw => exact prep_project setup checks callbacks (.decode raw) before
  | identity packet => exact prep_project setup checks callbacks (.identity packet) before
  | identityPoint key => exact prep_project setup checks callbacks (.identityPoint key) before
  | pqField packet => exact prep_project setup checks callbacks (.pqField packet) before
  | preField packet => exact prep_project setup checks callbacks (.preField packet) before
  | oneField packet => exact prep_project setup checks callbacks (.oneField packet) before
  | verify key signed => exact prep_project setup checks callbacks (.verify key signed) before
  | registrationStatus identifier => exact prep_project setup checks callbacks (.registrationStatus identifier) before
  | reserveRegistration => exact prep_project setup checks callbacks .reserveRegistration before
  | parseDh point => exact prep_project setup checks callbacks (.parseDh point) before
  | generate => exact prep_project setup checks callbacks .generate before
  | parseKem key => exact prep_project setup checks callbacks (.parseKem key) before
  | encapsulate key => exact prep_project setup checks callbacks (.encapsulate key) before
  | publicConversion key => exact prep_project setup checks callbacks (.publicConversion key) before
  | privateConversion => exact prep_project setup checks callbacks .privateConversion before
  | ephemeralDh secret point => exact prep_project setup checks callbacks (.ephemeralDh secret point) before
  | staticDh point =>
      simp only [sourcePrefix, RegistrationServerReferenceCompilerNative.nativePrefix,
        PqxdhServerStaticDhSource.prefixImpl]
      rw [lower_run]
      simp only [RegistrationNativeKemReferenceCompiler.visit,
        RegistrationNativeKemReferenceCompiler.ordinary, RegistrationServerReferenceCompiler.visit,
        RegistrationWorldRoot.visit, StateT.run,
        StateT.monad_pure_def, StateT.pure, StateT.monad_bind_def, StateT.bind,
        simulateQ_pure, map_pure, pure_bind, Prod.map, id_eq, project,
        RegistrationWorldAgreementProgramCompiler.project,
        RegistrationWorldAgreementCompiler.join, RegistrationWorldAgreementCompiler.mask]

/-- The literal open indexed-KEM collector has its actual native source interpretation; this is derived from the real callbacks rather than assumed for the whole phase. -/
theorem collect_project (setup : Setup base KemSK) (checks : Checks) (callbacks : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Extra) :
    Prod.map id project <$> (lower setup callbacks
      (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated)).run before =
      (simulateQ (RegistrationServerReferenceCompilerNative.nativePrefix setup checks)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run (project before) := by
  change Prod.map id project <$> (lower setup callbacks (simulateQ (sourcePrefix setup checks)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))).run before = _
  rw [lower_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_project setup checks callbacks) _ before

end BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix.query_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix.query_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix.collect_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemReferencePrefix.collect_project

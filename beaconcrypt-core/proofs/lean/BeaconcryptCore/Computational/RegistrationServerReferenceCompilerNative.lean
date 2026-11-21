-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceCompiler
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! The actual World-free Server prefix forwards local primitive draws to the record World and retains its real auxiliary state and callback ledger. Only the proved additional EnvEffects coin counter is projected. Every optional reply and all remaining World fields agree with the actual native reference prefix. Authentication hashes factor into that same World without any counter projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationWorldAgreementCompiler (join mask)
open RegistrationWorldAgreementProgramCompiler (project)
variable {n : Nat} {ι KemSK Reader Response Value Index : Type} {base : OracleSpec ι} {spec : OracleSpec Index}

abbrev Local (n : Nat) := Environment × PqxdhRecordLiftWorld.State n

noncomputable def lower (work : StateT Environment (OracleComp (EnvEffects n)) Value) :
    StateT (Local n) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ PqxdhRecordLiftWorld.effects (work.run before.1)).run before.2

private theorem lower_run (work : StateT Environment (OracleComp (EnvEffects n)) Value) (before : Local n) :
    (lower work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects (work.run before.1)).run before.2 := rfl

private theorem lower_program (implementation : QueryImpl spec (StateT Environment (OracleComp (EnvEffects n))))
    (work : OracleComp spec Value) : lower (simulateQ implementation work) =
      simulateQ (fun query => lower (implementation query)) work := by
  have same : (fun query => lower (implementation query)) =
      (PqxdhRecordLiftWorld.effects.mapStateTBase implementation).flattenStateT := rfl
  rw [same]
  funext before
  change (lower (simulateQ implementation work)).run before =
    (simulateQ (PqxdhRecordLiftWorld.effects.mapStateTBase implementation).flattenStateT work).run before
  rw [lower_run, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change (id <$> (simulateQ (PqxdhRecordLiftWorld.effects.mapStateTBase implementation).flattenStateT work).run before) = _
  exact id_map _

def visit (point : PqxdhBeaconPhase2Preparation.Word32) : StateT Environment (OracleComp (EnvEffects n)) Unit :=
  fun before => pure ((), { before with requests := before.requests ++ [.dh ⟨.LocalIdentity, point⟩] })

private theorem visit_run (point : PqxdhBeaconPhase2Preparation.Word32) (before : Environment) :
    (visit (n := n) point).run before =
      pure ((), { before with requests := before.requests ++ [.dh ⟨.LocalIdentity, point⟩] }) := rfl

private theorem reference_visit_run (point : PqxdhBeaconPhase2Preparation.Word32) (before : Environment) :
    (RegistrationServerReferenceCompiler.visit (n := n) point).run before =
      pure ((), { before with requests := before.requests ++ [.dh ⟨.LocalIdentity, point⟩] }) := rfl

private theorem native_visit_run (point : PqxdhBeaconPhase2Preparation.Word32)
    (before : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State) :
    (RegistrationWorldRoot.visit point).run before =
      pure ((), { before with requests := before.requests ++ [.dh ⟨.LocalIdentity, point⟩] }) := rfl

noncomputable def backend (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT Environment (OracleComp (EnvEffects n))) :=
  RegistrationWorldAgreementCompiler.compiler setup.source (RegistrationServerRoleBackend.localBackend setup checks)

noncomputable def prefixCompiler (setup : Setup base KemSK) (checks : Checks) :=
  PqxdhServerStaticDhSource.prefixImpl setup.serverDomain (RegistrationAgreementInterpreter.prepImpl (backend (n := n) setup checks)) visit

noncomputable def collect (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :=
  simulateQ (prefixCompiler (n := n) setup checks)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))

noncomputable def nativePrefix (setup : Setup base KemSK) (checks : Checks) :=
  PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl
      (RegistrationWorldAgreement.agreement (n := n) setup.source (RegistrationServerRoleBackend.localBackend setup checks)))
    RegistrationWorldRoot.visit

private theorem backend_embedded (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl.mapStateTBase (RegistrationServerReferenceCompiler.effect (n := n)) (backend (n := n) setup checks) =
      RegistrationServerReferenceCompiler.backend setup checks := rfl

private theorem prefix_embedded (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl.mapStateTBase (RegistrationServerReferenceCompiler.effect (n := n)) (prefixCompiler (n := n) setup checks) =
      PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
        (RegistrationAgreementInterpreter.prepImpl (RegistrationServerReferenceCompiler.backend setup checks))
        RegistrationServerReferenceCompiler.visit := by
  funext query before
  change simulateQ RegistrationServerReferenceCompiler.effect ((prefixCompiler setup checks query).run before) =
    (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
      (RegistrationAgreementInterpreter.prepImpl (RegistrationServerReferenceCompiler.backend setup checks))
      RegistrationServerReferenceCompiler.visit query).run before
  cases query <;> simp only [prefixCompiler, PqxdhServerStaticDhSource.prefixImpl, RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | rw [QueryImpl.simulateQ_mapStateTBase_run, backend_embedded]
    | simp only [visit_run, reference_visit_run, StateT.run_bind,
        StateT.run_pure, pure_bind, simulateQ_pure]

/-- The actual executable collector is precisely the EnvEffects collector embedded into its prepare/material interface. -/
theorem collect_embedded (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Environment) :
    (RegistrationServerReferenceCompiler.collect (n := n) setup checks packet authenticated).run before =
      simulateQ RegistrationServerReferenceCompiler.effect ((collect setup checks packet authenticated).run before) := by
  rw [collect, QueryImpl.simulateQ_mapStateTBase_run, prefix_embedded]
  rfl

private theorem backend_native (setup : Setup base KemSK) (checks : Checks)
    (query : RegistrationAgreementExecutor.Request) (before : Local n) :
    Prod.map id project <$> (lower (backend setup checks query)).run before =
      (RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.localBackend setup checks) query).run
        (project before) :=
  RegistrationWorldAgreementProgramCompiler.query_project setup.source (RegistrationServerRoleBackend.localBackend setup checks) query before

private theorem prep_native (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit Unit).Domain) (before : Local n) :
    Prod.map id project <$>
      (lower (RegistrationAgreementInterpreter.prepImpl (backend setup checks) query)).run before =
      (RegistrationAgreementInterpreter.prepImpl
        (RegistrationWorldAgreement.agreement setup.source (RegistrationServerRoleBackend.localBackend setup checks)) query).run
          (project before) := by
  cases query <;> simp only [RegistrationAgreementInterpreter.prepImpl]
  all_goals first
    | rw [lower_program]
      exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (backend_native setup checks) _ before
    | simp only [lower_run, StateT.run_pure, simulateQ_pure, map_pure, Prod.map, id_eq]

/-- Every concrete prefix callback has the actual native optional reply and full poststate after erasing only the proved extra coin effect. -/
theorem query_native (setup : Setup base KemSK) (checks : Checks)
    (query : (PqxdhServerRootPreparation.Spec registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding).Domain)
    (before : Local n) :
    Prod.map id project <$> (lower (prefixCompiler setup checks query)).run before =
      (nativePrefix setup checks query).run (project before) := by
  cases query with
  | decode raw => exact prep_native setup checks (.decode raw) before
  | identity packet => exact prep_native setup checks (.identity packet) before
  | identityPoint key => exact prep_native setup checks (.identityPoint key) before
  | pqField packet => exact prep_native setup checks (.pqField packet) before
  | preField packet => exact prep_native setup checks (.preField packet) before
  | oneField packet => exact prep_native setup checks (.oneField packet) before
  | verify key signed => exact prep_native setup checks (.verify key signed) before
  | registrationStatus identifier => exact prep_native setup checks (.registrationStatus identifier) before
  | reserveRegistration => exact prep_native setup checks .reserveRegistration before
  | parseDh point => exact prep_native setup checks (.parseDh point) before
  | generate => exact prep_native setup checks .generate before
  | parseKem key => exact prep_native setup checks (.parseKem key) before
  | encapsulate key => exact prep_native setup checks (.encapsulate key) before
  | publicConversion key => exact prep_native setup checks (.publicConversion key) before
  | privateConversion => exact prep_native setup checks .privateConversion before
  | ephemeralDh secret point => exact prep_native setup checks (.ephemeralDh secret point) before
  | staticDh point =>
      simp only [prefixCompiler, nativePrefix, PqxdhServerStaticDhSource.prefixImpl, lower_run,
        visit_run, native_visit_run, StateT.run_bind, StateT.run_pure,
        pure_bind, simulateQ_pure, map_pure, Prod.map, id_eq, project, join, mask]

/-- Arbitrary post-verification source continuations keep the complete native auxiliary/World result; the collector equality is derived from actual callbacks. -/
theorem collect_native (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Local n) :
    Prod.map id project <$> (lower (collect setup checks packet authenticated)).run before =
      (simulateQ (nativePrefix setup checks)
        (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))).run (project before) := by
  rw [collect, lower_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project (query_native setup checks) _ before

/-- Incoming native authentication compiles into the actual same World before any agreement effect, with no counter or cache projection. -/
theorem authentication_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (world : PqxdhRecordLiftWorld.State n) :
    (simulateQ PqxdhRecordLiftWorld.effects
      (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)).run world =
      (RegistrationWorldAuthentication.begin setup codec route verify pin packet).run world := by
  rw [RegistrationAuthenticationCompiler.begin_native setup codec route verify pin packet]

end BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.collect_embedded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.collect_embedded
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.query_native
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.collect_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.collect_native
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.authentication_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceCompilerNative.authentication_native

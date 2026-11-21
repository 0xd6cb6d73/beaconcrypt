-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementCapture
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh
import BeaconcryptCore.Computational.RegistrationBeaconBackendReadonly
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Actual source private objects select the corresponding native Beacon owner state. The only additional selected operation contract is the individual KEM decapsulation law; all DH, conversion, root and capture equalities are derived. The complete original Core program supplies query coverage, and its failed replies and unchanged caller RNG remain present. This is a native role-backend correspondence, before enclosing owner/Env instrumentation. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 CipherArray Keys)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open AdapterPublicAgreementCommonModel (Model)
open PqxdhRootTableInitialization (rootArray)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable [crypto : CryptoOperations (RustT ProbComp)]
variable {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

noncomputable def nativeState (view : AdapterPublicWrapperState.MaterialView source KemSK) (keys : Keys) :
    RegistrationBeaconRoleBackend.State KemSK :=
  ⟨view.edSecret keys.identity_secret, _root_.Option.map view.kxSecret keys.beacon_one_time, _root_.Option.map view.kemSecret keys.beacon_kem⟩

noncomputable def nativeDecapsulation (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (ciphertext : CipherArray) (secret : KemSK) : ProbComp (core.option.Option Array32) :=
  (fun reply => RegistrationAgreementRoot.nativeOption (reply.map rootArray)) <$>
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.decaps secret (PqxdhPhase2InputBytes.ciphertext ciphertext))

structure Decapsulation (model : Model (m := ProbComp) setup view) : Prop where
  operation : ∀ ciphertext secret, model.decapsulate ciphertext secret = nativeDecapsulation setup ciphertext secret

noncomputable section

theorem query (model : Model (m := ProbComp) setup view) (decap : Decapsulation model)
    (keys : Keys) (prekey : material.KxSecretKey) (stored : keys.beacon_prekey = .Some prekey)
    (request : Request) (allowed : RegistrationAgreementBeaconCoverage.Allowed request) :
    AdapterPublicAgreementCapture.implementation model keys request =
      RegistrationBeaconBackendReadonly.implementation setup (view.kxSecret prekey) (nativeState view keys) request := by
  cases request with
  | convertPublic key =>
    simp [AdapterPublicAgreementCapture.implementation, RegistrationBeaconBackendReadonly.implementation,
      RegistrationAgreementShared.auxiliary, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure]
  | convertSecret role =>
    change role = .LocalIdentity at allowed
    subst role
    simp [AdapterPublicAgreementCapture.implementation, RegistrationBeaconBackendReadonly.implementation,
      RegistrationAgreementShared.auxiliary, RegistrationBeaconRoleBackend.native,
      RegistrationBeaconRoleBackend.localBackend, StateT.run, nativeState,
      RegistrationServerRoleBackend.selected_conversion setup model.representation]
  | generate role => exact False.elim allowed
  | encapsulate input => exact False.elim allowed
  | decapsulate input =>
    cases input with
    | none =>
      simp [AdapterPublicAgreementCapture.implementation, RegistrationBeaconBackendReadonly.implementation,
        RegistrationAgreementShared.auxiliary, RegistrationBeaconRoleBackend.native,
        RegistrationBeaconRoleBackend.localBackend, StateT.run, StateT.monad_pure_def, StateT.pure, map_pure, AdapterPublicAgreementCommonModel.decapsulate]
    | some input =>
      cases present : keys.beacon_kem with
      | none =>
        simp [AdapterPublicAgreementCapture.implementation, RegistrationBeaconBackendReadonly.implementation,
          RegistrationAgreementShared.auxiliary, RegistrationBeaconRoleBackend.native,
          RegistrationBeaconRoleBackend.localBackend, StateT.run, AdapterPublicAgreementCommonModel.decapsulate, nativeState, present]
      | some secret =>
        simp [AdapterPublicAgreementCapture.implementation, RegistrationBeaconBackendReadonly.implementation,
          RegistrationAgreementShared.auxiliary, RegistrationBeaconRoleBackend.native,
          RegistrationBeaconRoleBackend.localBackend, StateT.run, AdapterPublicAgreementCommonModel.decapsulate, nativeState,
          present, decap.operation, nativeDecapsulation, Functor.map_map]
  | dh request =>
    rcases request with ⟨role, publicKey⟩
    cases role with
    | LocalIdentity =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, AdapterPublicAgreementCapture.capture,
        RegistrationBeaconBackendReadonly.implementation, RegistrationAgreementShared.auxiliary,
        RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend, StateT.run, nativeState,
        AdapterPublicAgreementNativeDh.identity_native]
    | ServerEphemeral =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, AdapterPublicAgreementCapture.capture,
        RegistrationBeaconBackendReadonly.implementation, RegistrationAgreementShared.auxiliary,
        RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend, StateT.run, map_pure]
    | BeaconPrekey =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, stored,
        RegistrationBeaconBackendReadonly.implementation, RegistrationAgreementShared.auxiliary,
        RegistrationBeaconRoleBackend.native, AdapterPublicAgreementNativeDh.scalar_native]
      rfl
    | BeaconOneTime =>
      cases present : keys.beacon_one_time with
      | none =>
        simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
          AdapterPublicAgreementPrimitiveModel.selected,
          RegistrationBeaconBackendReadonly.implementation, RegistrationAgreementShared.auxiliary,
          RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend, StateT.run, nativeState, present]
        rfl
      | some secret =>
        simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
          AdapterPublicAgreementPrimitiveModel.selected,
          RegistrationBeaconBackendReadonly.implementation, RegistrationAgreementShared.auxiliary,
          RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend, StateT.run, nativeState, present,
          AdapterPublicAgreementNativeDh.scalar_native]
  | root request =>
    simp [AdapterPublicAgreementCapture.implementation, RegistrationBeaconBackendReadonly.implementation,
      RegistrationAgreementShared.auxiliary]

theorem program {Value : Type} (model : Model (m := ProbComp) setup view) (decap : Decapsulation model)
    (keys : Keys) (prekey : material.KxSecretKey) (stored : keys.beacon_prekey = .Some prekey)
    (work : OracleComp Spec Value) (bounded : RegistrationAgreementBeaconCoverage.Bound work) :
    simulateQ (AdapterPublicAgreementCapture.implementation model keys) work =
      simulateQ (RegistrationBeaconBackendReadonly.implementation setup (view.kxSecret prekey) (nativeState view keys)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind request next ih =>
    rw [RegistrationAgreementBeaconCoverage.Bound, isQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [query model decap keys prekey stored request bounded.1]
    apply bind_congr
    intro reply
    exact ih reply (bounded.2 reply)

theorem beacon {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (model : Model (m := ProbComp) setup view) (decap : Decapsulation model)
    (keys : Keys) (prekey : material.KxSecretKey) (stored : keys.beacon_prekey = .Some prekey)
    (authenticated : registration.AuthenticatedResponse) (rng : R) :
    ((do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
         beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT ProbComp) generator phase keys rng) :
      RustT ProbComp (agreement.AgreementEffect × R)).run =
      (fun result => do let completed ← result.1; .ok (completed, rng)) <$>
        (simulateQ (RegistrationAgreementShared.auxiliary setup.source
          (RegistrationBeaconRoleBackend.native setup (view.kxSecret prekey)))
            (RegistrationAgreementExecutor.beacon authenticated)).run (nativeState view keys) := by
  rw [AdapterPublicAgreementCapture.beacon generator model keys authenticated rng,
    program model decap keys prekey stored _ (RegistrationAgreementBeaconCoverage.beacon_bound authenticated),
    RegistrationBeaconBackendReadonly.program, Functor.map_map]
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconNative.beacon

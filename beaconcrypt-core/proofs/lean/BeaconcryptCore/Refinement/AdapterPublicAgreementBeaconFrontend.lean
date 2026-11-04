-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementCapture
import BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh
import BeaconcryptCore.Computational.RegistrationNativeBeaconFrontend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The unchanged SDK agreement entry executes the actual native Beacon agreementCore in its full shared owner/Env monad. Private source objects are linked to the actual owner scalars and generated KEM handle. The selected indexed decapsulation interpretation is an individual primitive operation contract; all controller and remaining query equalities are proved. Native request-journal instrumentation belongs to the enclosing wrapper interpretation. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 CipherArray Keys)
open BeaconcryptCore.Computational RegistrationAgreementExecutor
open AdapterPublicAgreementCommonModel (Model)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner M)
variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {ι KemSK Auxiliary : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
variable [crypto : CryptoOperations (RustT (M n KemSK source Auxiliary))]
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

structure PrivateKeys (view : AdapterPublicWrapperState.MaterialView source KemSK) (keys : Keys)
    (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes) where
  prekey : material.KxSecretKey
  oneTimeKey : material.KxSecretKey
  kem : material.KemSecretKey
  identity : view.edSecret keys.identity_secret = owner.identitySeed
  prekeyStored : keys.beacon_prekey = .Some prekey
  prekeyView : view.kxSecret prekey = owner.prekeyScalar
  oneTimeStored : keys.beacon_one_time = .Some oneTimeKey
  oneTimeView : view.kxSecret oneTimeKey = oneTime
  kemStored : keys.beacon_kem = .Some kem

noncomputable def indexedDecapsulation (owner : Owner source) (ciphertext : CipherArray) :
    M n KemSK source Auxiliary (core.option.Option Array32) :=
  (fun reply => RegistrationAgreementRoot.nativeOption (reply.map rootArray)) <$>
    RegistrationNativeBeaconFrontend.kem (.inr (.inl (.decapsulate owner.kemHandle (PqxdhPhase2InputBytes.ciphertext ciphertext))))

structure Decapsulation (model : Model (m := M n KemSK source Auxiliary) setup view)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : PrivateKeys view keys owner oneTime) : Prop where
  operation : ∀ ciphertext, model.decapsulate ciphertext (view.kemSecret related.kem) =
    indexedDecapsulation owner ciphertext

noncomputable section

theorem query (model : Model (m := M n KemSK source Auxiliary) setup view)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : PrivateKeys view keys owner oneTime) (decap : Decapsulation model keys owner oneTime related)
    (request : Request) (allowed : RegistrationAgreementBeaconCoverage.Allowed request) :
    AdapterPublicAgreementCapture.implementation model keys request =
      RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime request := by
  cases request with
  | convertPublic key =>
    simp [AdapterPublicAgreementCapture.implementation, RegistrationNativeBeaconFrontend.agreementCore,
      RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
      RegistrationNativeKemInterface.other, RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive,
      RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend,
      RegistrationNativeBeaconFrontend.sample, StateT.run, StateT.monad_pure_def, StateT.pure]
    change (pure (RegistrationPublicConversion.convert setup.source.crypto key) :
      M n KemSK source Auxiliary (core.option.Option Array32)) =
      Prod.fst <$> (pure (RegistrationPublicConversion.convert setup.source.crypto key,
        (⟨owner.identitySeed, some oneTime, none⟩ : RegistrationNativeKemBackend.Beacon)) :
          M n KemSK source Auxiliary (core.option.Option Array32 × RegistrationNativeKemBackend.Beacon))
    exact (map_pure _ _).symm
  | convertSecret role =>
    change role = .LocalIdentity at allowed
    subst role
    simp [AdapterPublicAgreementCapture.implementation, RegistrationNativeBeaconFrontend.agreementCore,
      RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
      RegistrationNativeKemInterface.other, RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive,
      RegistrationBeaconRoleBackend.native, RegistrationBeaconRoleBackend.localBackend,
      RegistrationNativeBeaconFrontend.sample, StateT.run,
      RegistrationServerRoleBackend.selected_conversion setup model.representation]
  | generate role => exact False.elim allowed
  | encapsulate input => exact False.elim allowed
  | decapsulate input =>
    cases input with
    | none =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.decapsulate,
        RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeBeaconFrontend.primitive,
        RegistrationNativeKemInterface.beacon]
    | some input =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.decapsulate,
        related.kemStored, decap.operation, RegistrationNativeBeaconFrontend.agreementCore,
        RegistrationNativeBeaconFrontend.primitive, RegistrationNativeKemInterface.beacon,
        indexedDecapsulation]
  | dh request =>
    rcases request with ⟨role, publicKey⟩
    cases role with
    | LocalIdentity =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, AdapterPublicAgreementCapture.capture,
        related.identity, AdapterPublicAgreementNativeDh.identity_native,
        RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeBeaconFrontend.primitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
        RegistrationBeaconRoleBackend.localBackend, RegistrationNativeBeaconFrontend.sample, StateT.run]
    | ServerEphemeral =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, AdapterPublicAgreementCapture.capture,
        RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeBeaconFrontend.primitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
        RegistrationBeaconRoleBackend.localBackend, RegistrationNativeBeaconFrontend.sample, StateT.run]
    | BeaconPrekey =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, related.prekeyStored, related.prekeyView,
        AdapterPublicAgreementNativeDh.scalar_native,
        RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeBeaconFrontend.primitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
        RegistrationNativeBeaconFrontend.sample, StateT.run, StateT.monad_pure_def, StateT.pure]
      rfl
    | BeaconOneTime =>
      simp [AdapterPublicAgreementCapture.implementation, AdapterPublicAgreementCommonModel.dh,
        AdapterPublicAgreementPrimitiveModel.selected, related.oneTimeStored, related.oneTimeView,
        AdapterPublicAgreementNativeDh.scalar_native,
        RegistrationNativeBeaconFrontend.agreementCore, RegistrationNativeBeaconFrontend.primitive,
        RegistrationNativeKemInterface.beacon, RegistrationNativeKemInterface.other,
        RegistrationNativeKemBackend.beaconOther, RegistrationNativeKemInterface.OtherRequest.primitive, RegistrationBeaconRoleBackend.native,
        RegistrationBeaconRoleBackend.localBackend, RegistrationNativeBeaconFrontend.sample, StateT.run]
  | root request => rfl

theorem program {Value : Type} (model : Model (m := M n KemSK source Auxiliary) setup view)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : PrivateKeys view keys owner oneTime) (decap : Decapsulation model keys owner oneTime related)
    (work : OracleComp Spec Value) (bounded : RegistrationAgreementBeaconCoverage.Bound work) :
    simulateQ (AdapterPublicAgreementCapture.implementation model keys) work =
      simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure]
  | query_bind request next ih =>
    rw [RegistrationAgreementBeaconCoverage.Bound, isQueryBound_query_bind_iff] at bounded
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [query model keys owner oneTime related decap request bounded.1]
    apply bind_congr
    intro reply
    exact ih reply (bounded.2 reply)

theorem beacon {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (model : Model (m := M n KemSK source Auxiliary) setup view)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : PrivateKeys view keys owner oneTime) (decap : Decapsulation model keys owner oneTime related)
    (authenticated : registration.AuthenticatedResponse) (rng : R) :
    ((do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
         beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT (M n KemSK source Auxiliary)) generator phase keys rng) :
      RustT (M n KemSK source Auxiliary) (agreement.AgreementEffect × R)).run =
      (fun result => do let completed ← result; .ok (completed, rng)) <$>
        simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime)
          (RegistrationAgreementExecutor.beacon authenticated) := by
  rw [AdapterPublicAgreementCapture.beacon generator model keys authenticated rng,
    program model keys owner oneTime related decap _ (RegistrationAgreementBeaconCoverage.beacon_bound authenticated)]
variable [pureCrypto : PublicWrapperPlatform.CryptoOperations]

private theorem noentropy_body (effect : agreement.AgreementEffect) (keys : Keys) :
    beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m := RustT (M n KemSK source Auxiliary)) effect keys =
      Prod.fst <$> beaconcrypt_public_request.pqxdh.execute_agreement
        beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError effect keys () := rfl

omit material primitive crypto pureCrypto in
private theorem run_map {A B : Type} (function : A → B) (work : RustT (M n KemSK source Auxiliary) A) :
    (function <$> work).run = (fun result => function <$> result) <$> work.run := by
  change (work >>= fun value => pure (function value)).run = _
  rw [RustT.run_bind, ← bind_pure_comp]
  apply bind_congr
  intro result
  cases result <;> rfl

theorem source_beacon (model : Model (m := M n KemSK source Auxiliary) setup view)
    (keys : Keys) (owner : Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (related : PrivateKeys view keys owner oneTime) (decap : Decapsulation model keys owner oneTime related)
    (authenticated : registration.AuthenticatedResponse) :
    ((do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
         beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m := RustT (M n KemSK source Auxiliary)) phase keys) :
      RustT (M n KemSK source Auxiliary) agreement.AgreementEffect).run =
      simulateQ (RegistrationNativeBeaconFrontend.agreementCore setup owner oneTime)
        (RegistrationAgreementExecutor.beacon authenticated) := by
  have factored :
      (do let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
          beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m := RustT (M n KemSK source Auxiliary)) phase keys) =
      Prod.fst <$> (do
        let phase ← AdapterRecordRequestMonad.liftRust (agreement.begin_beacon_agreement authenticated)
        beaconcrypt_public_request.pqxdh.execute_agreement (m := RustT (M n KemSK source Auxiliary))
          beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError phase keys ()) := by
    simp only [noentropy_body, map_bind]
  rw [factored, run_map,
    beacon beaconcrypt_public_request.pqxdh.NoEntropy.Insts.Rand_coreTryCryptoRngCryptoError model keys owner oneTime related decap authenticated (),
    Functor.map_map]
  have same : (fun result : RustM agreement.AgreementEffect =>
      Prod.fst <$> (do let completed ← result; .ok (completed, ()))) = id := by
    funext result
    cases result <;> rfl
  rw [same]
  exact id_map _

end
end BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.query

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.program

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.beacon

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.source_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend.source_beacon

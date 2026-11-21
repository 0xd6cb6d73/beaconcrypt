-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicAgreementFunctional
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
/-! Actual source private-key DH fields are the concrete native setup's scalar or selected-identity DH operations. The linkage uses byte-preserving MaterialView and the existing selected primitive SourceWiring; public-key equality never selects a secret. -/
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicAgreementFields (Array32 LocalIdentity KeyPair)
open BeaconcryptCore.Computational
open PqxdhRootTableInitialization (rootArray)
open AdapterPublicAgreementFunctional (scalarReply)
variable {ι KemSK : Type} {base : OracleSpec ι}

theorem scalar_view (scalar : PqxdhJointGapDh.ScalarBytes) :
    PqxdhPhase2GapDhSource.peer (rootArray scalar) = scalar := by
  apply Subtype.ext
  exact PqxdhRootTableInitialization.rootArray_bytes scalar

theorem scalar_native (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (publicKey : Array32) :
    scalarReply setup.source.crypto (rootArray scalar) publicKey =
      RegistrationAgreementRoot.nativeOption ((setup.dh.dh scalar (PqxdhPhase2GapDhSource.peer publicKey)).map rootArray) := by
  rw [scalarReply, scalar_view]
  rfl

theorem identity_native (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (seed : PqxdhJointIdentity.IdentitySeed) (publicKey : Array32) :
    scalarReply setup.source.crypto (representation.converted seed) publicKey =
      RegistrationAgreementRoot.nativeOption ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer publicKey)).map rootArray) := by
  rw [setup.wiring.staticDh]
  unfold scalarReply PqxdhJointGapDh.sourceScalarDh PqxdhJointIdentity.sourceDhReply
  simp only [PqxdhPhase2GapDhSource.peer, List.Vector.toList_mk, representation.bytes]
  rfl

variable [material : PublicWrapperPlatform.Material] [primitive : AdapterInitEdPrimitive.Operations]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable [crypto : CryptoOperations (RustT m)]
variable {source : RegistrationNativeMldsa.Source}

noncomputable section

theorem local_identity {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (contract : AdapterPublicAgreementFunctional.Scalar (m := m) setup.source.crypto)
    (secret : LocalIdentity) (seed : PqxdhJointIdentity.IdentitySeed)
    (stored : secret.value = representation.converted seed) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_4.Insts.CoreOpsFunctionFnOnceTupleSharedZeroizingArrayU832OptionArrayU832.call_once
      (m := RustT m) generator publicKey secret =
      pure (RegistrationAgreementRoot.nativeOption
        ((setup.joint.staticDh seed (PqxdhPhase2GapDhSource.peer publicKey)).map rootArray)) := by
  rw [AdapterPublicAgreementFunctional.local_dh generator setup.source.crypto contract secret publicKey,
    stored, identity_native setup representation seed publicKey]

theorem ephemeral {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicAgreementFunctional.KeyGetters (m := m) view)
    (contract : AdapterPublicAgreementFunctional.Scalar (m := m) setup.source.crypto)
    (key : KeyPair) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_5.Insts.CoreOpsFunctionFnOnceTupleSharedKeyPairOptionArrayU832.call_once
      (m := RustT m) generator publicKey key =
      pure (RegistrationAgreementRoot.nativeOption
        ((setup.dh.dh (view.kxSecret key.secret_key) (PqxdhPhase2GapDhSource.peer publicKey)).map rootArray)) := by
  rw [AdapterPublicAgreementFunctional.ephemeral_dh generator view getters setup.source.crypto contract key publicKey,
    scalar_native]

theorem prekey {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicAgreementFunctional.KeyGetters (m := m) view)
    (contract : AdapterPublicAgreementFunctional.Scalar (m := m) setup.source.crypto)
    (key : beaconcrypt_crypto.crypto_kx.SecretKey) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_6.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
      (m := RustT m) generator publicKey key =
      pure (RegistrationAgreementRoot.nativeOption
        ((setup.dh.dh (view.kxSecret key) (PqxdhPhase2GapDhSource.peer publicKey)).map rootArray)) := by
  rw [AdapterPublicAgreementFunctional.prekey_dh generator view getters setup.source.crypto contract key publicKey,
    scalar_native]

theorem one_time {R Error : Type} (generator : rand_core.TryCryptoRng R Error)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (getters : AdapterPublicAgreementFunctional.KeyGetters (m := m) view)
    (contract : AdapterPublicAgreementFunctional.Scalar (m := m) setup.source.crypto)
    (key : beaconcrypt_crypto.crypto_kx.SecretKey) (publicKey : Array32) :
    beaconcrypt_public_request.pqxdh.execute_agreement.closure_7.Insts.CoreOpsFunctionFnOnceTupleSharedSecretKeyOptionArrayU832.call_once
      (m := RustT m) generator publicKey key =
      pure (RegistrationAgreementRoot.nativeOption
        ((setup.dh.dh (view.kxSecret key) (PqxdhPhase2GapDhSource.peer publicKey)).map rootArray)) := by
  rw [AdapterPublicAgreementFunctional.one_time_dh generator view getters setup.source.crypto contract key publicKey,
    scalar_native]
end
end BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.scalar_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.scalar_view

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.scalar_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.scalar_native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.identity_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.identity_native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.local_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.local_identity

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.ephemeral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.ephemeral

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.prekey' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.prekey

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.one_time' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementNativeDh.one_time

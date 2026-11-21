-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAgreementJournal
import BeaconcryptCore.Refinement.AdapterPublicAgreementBeaconFrontend
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicAgreementJournal
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M Owner Trusted)
open RegistrationWorldAgreementCompiler (EnvState)
variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [PublicWrapperPlatform.CryptoOperations]
variable {I KemSK Auxiliary : Type} {base : OracleSpec I} {n : Nat} {source : RegistrationNativeMldsa.Source}
variable [crypto : CryptoOperations (RustT (M n KemSK source Auxiliary))]
variable {setup : PqxdhServerAuthExperiment.Setup base KemSK}
variable {view : AdapterPublicWrapperState.MaterialView source KemSK}

noncomputable def tree (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (journal : RegistrationNativeAgreementJournal.Journal) :
    OracleComp (Trusted n KemSK) (RustM agreement.AgreementEffect × RegistrationNativeAgreementJournal.Journal) :=
  (simulateQ (RegistrationNativeAgreementJournal.traced (RegistrationNativeAgreementJournal.core setup owner scalar))
    (RegistrationAgreementExecutor.beacon authenticated)).run journal

theorem source_erasure (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (keys : AdapterPublicAgreementFields.Keys) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view keys owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model keys owner scalar related)
    (authenticated : registration.AuthenticatedResponse) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    ((((do let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
           beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m := RustT (M n KemSK source Auxiliary)) phase keys) :
      RustT (M n KemSK source Auxiliary) agreement.AgreementEffect).run.run owners).run env) =
      (fun result => ((result.1, owners), env)) <$> tree setup owner scalar authenticated env.requests := by
  rw [AdapterPublicAgreementBeaconFrontend.source_beacon model keys owner scalar related decap authenticated,
    RegistrationNativeAgreementJournal.core_program]
  have erased := congrArg (fun computation : OracleComp (Trusted n KemSK) (RustM agreement.AgreementEffect) =>
      (fun reply => ((reply, owners), env)) <$> computation)
    (RegistrationNativeAgreementJournal.traced_erasure
      (RegistrationNativeAgreementJournal.core (n := n) setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated) env.requests)
  simpa only [tree, Functor.map_map] using erased.symm

theorem source_with_journal (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source Auxiliary) setup view)
    (keys : AdapterPublicAgreementFields.Keys) (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (related : AdapterPublicAgreementBeaconFrontend.PrivateKeys view keys owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model keys owner scalar related)
    (authenticated : registration.AuthenticatedResponse) (owners : List (Owner source)) (env : EnvState Auxiliary) :
    (((simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner scalar)
      (RegistrationAgreementExecutor.beacon authenticated) : M n KemSK source Auxiliary (RustM agreement.AgreementEffect)).run owners).run env =
      (fun result => ((result.1, owners), {env with requests := result.2})) <$> tree setup owner scalar authenticated env.requests) ∧
    (((((do let phase ← liftRust (agreement.begin_beacon_agreement authenticated)
            beaconcrypt_public_request.pqxdh.execute_beacon_agreement (m := RustT (M n KemSK source Auxiliary)) phase keys) :
      RustT (M n KemSK source Auxiliary) agreement.AgreementEffect).run.run owners).run env) =
      (fun result => ((result.1, owners), env)) <$> tree setup owner scalar authenticated env.requests) := by
  exact ⟨RegistrationNativeAgreementJournal.native_program setup owner scalar _ owners env,
    source_erasure model keys owner scalar related decap authenticated owners env⟩
end BeaconcryptCore.Refinement.AdapterPublicAgreementJournal
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementJournal.source_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementJournal.source_erasure
/-- info: 'BeaconcryptCore.Refinement.AdapterPublicAgreementJournal.source_with_journal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicAgreementJournal.source_with_journal

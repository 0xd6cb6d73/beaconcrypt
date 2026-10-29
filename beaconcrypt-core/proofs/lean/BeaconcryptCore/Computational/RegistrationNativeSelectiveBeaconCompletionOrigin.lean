-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconUniversalOrigin

/-! Successful terminal native Beacon completion retains the actual selected paired installation. Rejected, failed, or diverging material replies cannot produce a successful public completion. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionOrigin
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSelectiveBeaconCompletionSource (Result execute pure_source bind_source map_source)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Reader Response Secret : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response)
local notation "run" => execute setup wire route sign seed scalar candidate provider service codec

private theorem after (owner current : SelectedOwner source) (env : EnvState Auxiliary)
    (completed : RustM RegistrationNativePairedBeaconService.Result)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n KemSK ProviderState Secret ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary))
    (supported : result ∈ support (run
      (((RegistrationBeaconReferenceCompletion.after (RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK))
        owner completed).run current).run env) before shell world secret))
    (bytes : Pqxdh.Bytes) (successful : result.1.1.1.1.1.1 = .ok (some bytes)) :
    ∃ published, completed = .ok (.Ok published) ∧ result.1.2 = world := by
  cases completed with
  | fail error | div =>
      simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
        StateT.run_lift, StateT.run_map, seqRight_eq_bind, bind_pure_comp,
        Functor.map_map] at supported
      rw [map_source, support_map] at supported
      obtain ⟨middle, _called, returned⟩ := supported
      subst result
      cases successful
  | ok completed => cases completed with
    | Err previous =>
        simp only [RegistrationBeaconReferenceCompletion.after, RegistrationBeaconReferenceCompletion.abort,
          StateT.run_lift, StateT.run_map, seqRight_eq_bind, bind_pure_comp,
          Functor.map_map] at supported
        rw [map_source, support_map] at supported
        obtain ⟨middle, _called, returned⟩ := supported
        subst result
        cases successful
    | Ok published =>
        simp only [RegistrationBeaconReferenceCompletion.after, StateT.run_bind, StateT.run_modify,
          StateT.run_pure, pure_bind, pure_source, mem_support_pure_iff] at supported
        subst result
        exact ⟨published, rfl, rfl⟩


/-- A successful original terminal Beacon completion retains its same selected installed hidden origin. -/
theorem complete (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n KemSK ProviderState Secret ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary))
    (supported : result ∈ support (run
      (((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run current).run env) before shell world secret))
    (bytes : Pqxdh.Bytes) (successful : result.1.1.1.1.1.1 = .ok (some bytes))
    (selected : ∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.owner owner.worldOwner) = some slot := by
  rw [RegistrationNativeSelectiveBeaconCompletionSource.complete_source, bind_source, mem_support_bind_iff] at supported
  obtain ⟨middle, demanded, continued⟩ := supported
  obtain ⟨published, same, advanced⟩ := after setup wire route sign seed scalar candidate provider service codec
    owner current env middle.1.1.1.1 middle.1.1.1.2 middle.1.1.2 middle.1.2 middle.2 result continued bytes successful
  have installed := RegistrationNativeSelectiveBeaconUniversalOrigin.admitted setup wire route sign seed scalar candidate provider service codec
    owner.worldOwner owner.pin.binding.identity_key_id ready ({ env with receipts := before.1.receipts }, before)
    shell world secret middle (by
      simpa only [execute, RegistrationNativeSelectiveBeaconServiceSource.actual,
        RegistrationNativeSelectiveBeaconServiceSource.restore, QueryImpl.simulateQ_compose] using demanded)
    published same selected
  rw [advanced]
  exact installed

end BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionOrigin.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionOrigin.complete

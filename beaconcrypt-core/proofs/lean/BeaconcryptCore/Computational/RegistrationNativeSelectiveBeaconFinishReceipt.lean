-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource

/-! Successful original native finish retains the same actual preparation, Ready, current owner, environment and reached private World used by the subsequent completion. No independently sampled readiness witness is substituted for this controller path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconFinishReceipt
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
attribute [local irreducible] RegistrationBeaconReferenceCompiler.finishPreparation RegistrationBeaconReferenceFinish.complete

/-- Every successful original terminal finish has its own same-run preparation and completion receipts. -/
theorem finish (owner : SelectedOwner source) (env : EnvState Auxiliary) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n KemSK ProviderState Secret ((RustM (Option Pqxdh.Bytes) × SelectedOwner source) × EnvState Auxiliary))
    (supported : result ∈ support (run
      (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner).run env) before shell world secret))
    (application : Pqxdh.Bytes) (successful : result.1.1.1.1.1.1 = .ok (some application)) :
    ∃ ready : RegistrationBeaconReferenceRoot.Ready,
    ∃ middle : Result n KemSK ProviderState Secret
      ((RustM (Option RegistrationBeaconReferenceRoot.Ready) × SelectedOwner source) × EnvState Auxiliary),
      middle ∈ support (run (((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner).run env)
        before shell world secret) ∧
      middle.1.1.1.1.1.1 = .ok (some ready) ∧
      result ∈ support (run
        (((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run middle.1.1.1.1.1.2).run middle.1.1.1.1.2)
          middle.1.1.1.2 middle.1.1.2 middle.1.2 middle.2) := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [phase, StateT.run_pure, pure_source, mem_support_pure_iff] at supported
      subst result
      cases successful
  | initSent pending oneTime =>
      simp only [phase] at supported
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, StateT.run_pure, pure_source, mem_support_pure_iff] at supported
          subst result
          cases successful
      | ok aborted =>
          simp only [moved, StateT.run_bind, bind_source, mem_support_bind_iff] at supported
          obtain ⟨prepared, possible, continued⟩ := supported
          cases outcome : prepared.1.1.1.1.1.1 with
          | fail error | div =>
              simp only [outcome, RegistrationBeaconReferenceFinish.abort, StateT.run_lift, StateT.run_map,
                seqRight_eq_bind, bind_pure_comp, Functor.map_map] at continued
              rw [map_source, support_map] at continued
              obtain ⟨middle, _called, returned⟩ := continued
              subst result
              cases successful
          | ok result => cases result with
            | none =>
                simp only [outcome, RegistrationBeaconReferenceFinish.abort, StateT.run_lift, StateT.run_map,
                  seqRight_eq_bind, bind_pure_comp, Functor.map_map] at continued
                rw [map_source, support_map] at continued
                obtain ⟨middle, _called, returned⟩ := continued
                subst result
                cases successful
            | some ready =>
                exact ⟨ready, prepared, possible, outcome, by simpa only [outcome] using continued⟩

end BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconFinishReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconFinishReceipt.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconFinishReceipt.finish

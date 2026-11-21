-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
/-! Arbitrary-choice source Beacon agreement is composed from the literal opaque-word collector and the actual stateful prepare echo. The physical World remains free and the same private provider/root-service state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconAgreement
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider

noncomputable def wordPreparation : QueryImpl RegistrationNativeSecretWordMessage.PrepareSpec
    (StateT (Symbolic n KemSK) (World n)) := fun message => symbolic (.inl (.inl message))
noncomputable def nativePreparation : QueryImpl RegistrationServerReferenceRoot.PrepareSpec
    (StateT (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase) (World n)) :=
  fun message => actual (.inl (.inl message))

theorem root_source (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse) (before : Symbolic n KemSK) :
    Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) (frame candidate) <$>
      (simulateQ (wordPreparation setup wire sign seed scalar candidate unused selected pairs publicKey challenge)
        (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)).run before =
      (simulateQ (nativePreparation (n := n) setup wire sign seed scalar candidate selected pairs publicKey challenge)
        (RegistrationBeaconReferenceRoot.client authenticated (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending))).run (frame candidate before) := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client,RegistrationBeaconReferenceRoot.client,
    simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure,
    wordPreparation,nativePreparation]
  rw [←RegistrationNativeSecretWordBeaconRoot.message_eval candidate pending]
  have sourceEq := RegistrationNativePlatformLorCtxLeaves.prepare_source setup wire sign seed scalar candidate unused
    symbolicProvider actualProvider (RegistrationNativeSecretWordBeaconRoot.message pending) before
  rw [←sourceEq,bind_map_left]
  simp only [map_bind,map_pure]
  apply bind_congr
  rintro ⟨reference,after⟩
  cases reference <;> rfl
private theorem word_cap :
    (symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false) ∘ₛ RegistrationNativeSecretWordInterface.prepare =
      wordPreparation setup wire sign seed scalar candidate unused selected pairs publicKey challenge := by
  funext message
  simp only [QueryImpl.compose,RegistrationNativeSecretWordInterface.prepare,simulateQ_spec_query,
    RegistrationNativeSecretWordInterface.liftLocal,wordPreparation]

private theorem native_cap :
    (actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false) ∘ₛ RegistrationBeaconReferenceCompiler.prepare =
      nativePreparation (n := n) setup wire sign seed scalar candidate selected pairs publicKey challenge := by
  funext message
  simp only [QueryImpl.compose,RegistrationBeaconReferenceCompiler.prepare,simulateQ_spec_query,
    RegistrationNativePublicFrontend.liftLocal,nativePreparation]

variable {source : RegistrationNativeMldsa.Source}
theorem agreement_source (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (before : Symbolic n KemSK) :
    Prod.map (Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) id) (frame candidate) <$>
      (simulateQ (symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false)
        ((RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated).run env)).run before =
      (simulateQ (actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false)
        ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env)).run (frame candidate before) := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement,RegistrationBeaconReferenceCompiler.agreement,
    StateT.run_bind,simulateQ_bind,StateT.run_bind,map_bind]
  have collectEq := RegistrationNativePlatformLorCtxRealization.beacon_collect_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    owner oneTime authenticated env before
  rw [←collectEq,bind_map_left]
  apply bind_congr
  rintro ⟨⟨collected,envAfter⟩,after⟩
  cases collected with
  | none =>
    simp only [Prod.map_apply,id_eq,Option.map_none,StateT.run_pure,simulateQ_pure,map_pure,
      RegistrationNativeSecretWordBeaconRoot.restore]
  | some pending =>
    simp only [Prod.map_apply,id_eq,Option.map_some,StateT.run_lift,bind_pure_comp,simulateQ_map,
      StateT.run_map,Functor.map_map]
    simp only [←QueryImpl.simulateQ_compose,word_cap,native_cap]
    have rooted := root_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge authenticated pending after
    have lifted := congrArg (Functor.map (fun result => ((result.1,envAfter),result.2))) rooted
    simpa only [Functor.map_map,Prod.map_def,id_eq] using lifted

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconAgreement.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconAgreement.root_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconAgreement.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconAgreement.agreement_source

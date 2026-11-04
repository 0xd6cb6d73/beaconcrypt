-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFinishSuffix
/-! Concrete source leaf instantiation for the actual post-agreement Beacon suffix. Material addresses are evaluated before the same selective demand; hidden, known and refused choices and every stateful World continuation remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider
local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "nativeLocal" => wordLocal ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate
local notation "actualLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false

theorem demand_coherence (reference : RegistrationNativeSecretWordMessage.Message) :
    symbolic (.inl (.inr (.inl (.inl (RegistrationNativeSecretWordMessage.literal
      (RegistrationNativeSecretWordMessage.eval candidate reference)))))) =
      symbolic (.inl (.inr (.inl (.inl reference)))) := by
  apply StateT.ext
  rintro ⟨word,roots⟩
  rw [RegistrationNativePlatformLorCtxLeaves.lower,
    QueryImpl.flattenStateT_mapStateTBase_apply_run,
    RegistrationNativePlatformLorOpenDictionary.demand_run]
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run,
    RegistrationNativePlatformLorOpenDictionary.demand_run]
  simp only [simulateQ_map,RegistrationNativePlatformLorOpenDictionary.root,simulateQ_spec_query,
    RegistrationNativePlatformLorCtxLeaves.closing,RegistrationNativePlatformLorOpenDictionary.actualRoots,
    QueryImpl.mapStateTBase,StateT.mk,RegistrationNativeSecretWordMessage.eval_literal]
  rfl

theorem effects (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    simulateQ nativeLocal (RegistrationBeaconReferenceCompiler.effect query) =
      simulateQ wordLocal (RegistrationNativeSecretWordInterface.effect query) := by
  rw [QueryImpl.simulateQ_compose,RegistrationNativeSecretWordServerSource.effect_query]

theorem demand (reference : RegistrationNativeSecretWordMessage.Message) :
    simulateQ nativeLocal (RegistrationNativePlatformBeaconMaterialInterpreter.demand (RegistrationNativeSecretWordMessage.eval candidate reference)) =
      simulateQ wordLocal (RegistrationNativeSecretWordInterface.demand reference) := by
  simp only [QueryImpl.compose,RegistrationNativePlatformBeaconMaterialInterpreter.demand,
    RegistrationNativeSecretWordServerSource.realize,RegistrationNativeSecretWordInterface.demand,
    simulateQ_spec_query,RegistrationNativeSecretWordInterface.liftLocal]
  exact demand_coherence setup wire sign seed scalar candidate unused selected pairs publicKey challenge reference

theorem afterPrepared_source (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (prepared : RustM (Option RegistrationNativeSecretWordMessage.BeaconReady))
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ wordLocal
        (((RegistrationNativePlatformSecretWordFinish.afterPrepared setup.source wire.frameWrite owner prepared).run current).run env)).run before =
      (simulateQ actualLocal
        (((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner
          (RegistrationNativeSecretWordBeaconRoot.restore candidate prepared)).run current).run env)).run (frame candidate before) := by
  have shared := RegistrationNativePlatformLorIdealFinishSuffix.afterPrepared_source nativeLocal wordLocal
    (effects setup wire sign seed scalar candidate unused selected pairs publicKey challenge) candidate
    (demand setup wire sign seed scalar candidate unused selected pairs publicKey challenge)
    setup.source wire.frameWrite owner current prepared env
  simp only [QueryImpl.simulateQ_compose] at shared
  have nativeEq := RegistrationNativePlatformLorCtxRealization.local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge false
    (((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner
      (RegistrationNativeSecretWordBeaconRoot.restore candidate prepared)).run current).run env) before
  simp only [QueryImpl.simulateQ_compose] at nativeEq
  rw [shared] at nativeEq
  simpa only [QueryImpl.simulateQ_compose] using nativeEq
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.demand_coherence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.demand_coherence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.demand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.afterPrepared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix.afterPrepared_source

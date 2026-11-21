-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconSuffix
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild
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

local notation "reified" => RegistrationNativePlatformLorCtxRealization.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge

theorem compatible : (reified ∘ₛ RegistrationNativePlatformLorIdealBuild.nativeEmbedding) ∘ₛ
    RegistrationNativePlatformSecretWordBuild.realize candidate = symbolic ∘ₛ RegistrationNativePlatformLorIdealBuild.wordEmbedding := by
  funext query
  rcases query with message | effect | coin
  · simp only [QueryImpl.compose,RegistrationNativePlatformSecretWordBuild.realize,
      RegistrationNativePlatformLorIdealBuild.nativeEmbedding,RegistrationNativePlatformLorIdealBuild.wordEmbedding,
      RegistrationNativePlatformSecretWordBuild.wordEmbedding,RegistrationNativePlatformPublicFrontend.buildEmbedding,
      RegistrationNativePlatformPublicFrontend.localQuery,RegistrationNativeSecretWordInterface.liftLocal,
      RegistrationNativePlatformPublicFrontend.embedLocal,RegistrationNativePlatformPublicCoinEmbedding.embed,
      simulateQ_spec_query,RegistrationNativePlatformLorCtxRealization.implementation,
      RegistrationNativeSecretWordCheckedFrontend.realization,RegistrationNativeSecretWordInterface.demand]
    exact RegistrationNativePlatformLorIdealBeaconSuffix.demand_coherence setup wire sign seed scalar candidate unused selected pairs publicKey challenge message
  · rfl
  · rfl

variable {Platform E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool)
theorem build_source (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : Symbolic n KemSK) :
    Prod.map (Prod.map id (RegistrationNativePlatformSecretWordOrdinary.evaluate candidate)) (frame candidate) <$>
      (simulateQ symbolic ((RegistrationNativePlatformSecretWordFrontend.build setup sign view failure allocation erased helper writer reserve handle application source).run before)).run privateBefore =
      (simulateQ actual (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run
            (RegistrationNativePlatformSecretWordOrdinary.evaluate candidate before)))).run (frame candidate privateBefore) := by
  have compared := RegistrationNativePlatformLorIdealBuild.build setup source sign view failure allocation erased helper writer reserve candidate reified symbolic
    (compatible setup wire sign seed scalar candidate unused selected pairs publicKey challenge) handle application before
  have nativeEq := RegistrationNativePlatformLorCtxRealization.program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reserve handle application source)).run
          (RegistrationNativePlatformSecretWordOrdinary.evaluate candidate before))) privateBefore
  rw [compared] at nativeEq
  simpa only [StateT.run_map,Functor.map_map,Prod.map_def,id_eq] using nativeEq
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild.compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild.compatible

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild.build_source

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconPhase
/-! Arbitrary-choice source Beacon agreement is composed from the literal opaque-word collector and the actual stateful prepare echo. The physical World remains free and the same private provider/root-service state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconFinish
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

local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "actualLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false
variable {source : RegistrationNativeMldsa.Source}
theorem effects_source {A : Type} (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$> (simulateQ wordLocal
      (simulateQ RegistrationNativeSecretWordInterface.effect work)).run before =
      (simulateQ actualLocal (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run (frame candidate before) := by
  have sourceEq := RegistrationNativePlatformLorCtxRealization.local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge false
    (simulateQ RegistrationBeaconReferenceCompiler.effect work) before
  have same : RegistrationNativeSecretWordServerSource.realize (n := n) (KemSK := KemSK) candidate ∘ₛ
      RegistrationBeaconReferenceCompiler.effect = RegistrationNativeSecretWordInterface.effect := by
    funext query
    exact RegistrationNativeSecretWordServerSource.effect_query candidate query
  rw [←QueryImpl.simulateQ_compose (RegistrationNativeSecretWordServerSource.realize candidate) RegistrationBeaconReferenceCompiler.effect, same] at sourceEq
  exact sourceEq

theorem finish_source (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (packet : Option registration.ResponsePacket)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ wordLocal
        (((RegistrationNativePlatformSecretWordFinish.finish setup wire source packet).run owner).run env)).run before =
      (simulateQ actualLocal
        (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env)).run (frame candidate before) := by
  cases phase : owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted aborted =>
    simp only [RegistrationNativePlatformSecretWordFinish.finish,RegistrationNativePlatformBeaconReferenceFinish.finish,
      StateT.run_bind,StateT.run_get,pure_bind,phase,StateT.run_pure,simulateQ_pure,map_pure]
    rfl
  | initSent pending oneTime =>
    simp only [RegistrationNativePlatformSecretWordFinish.finish,RegistrationNativePlatformBeaconReferenceFinish.finish,
      StateT.run_bind,StateT.run_get,pure_bind,phase]
    cases moved : pending.aborted_state with
    | fail error | div =>
      simp only [StateT.run_pure,simulateQ_pure,map_pure]
      rfl
    | ok aborted =>
      simp only [StateT.run_modify,pure_bind,StateT.run_bind,StateT.run_lift,
        bind_pure_comp,simulateQ_bind,map_bind,bind_map_left]
      have authEq := effects_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
        (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
          (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value))) before
      simp only [StateT.run] at authEq ⊢
      refine Eq.trans ?_ (congrArg (fun work => work >>= _) authEq)
      simp only [bind_map_left]
      apply bind_congr
      rintro ⟨authenticated,after⟩
      simp only [Prod.map_apply,id_eq]
      cases authenticated with
      | fail error =>
        exact RegistrationNativePlatformLorIdealBeaconSuffix.afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
          owner {owner with phase := .aborted aborted} (.fail error) env after
      | div =>
        exact RegistrationNativePlatformLorIdealBeaconSuffix.afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
          owner {owner with phase := .aborted aborted} .div env after
      | ok result => cases result with
        | Err error =>
          exact RegistrationNativePlatformLorIdealBeaconSuffix.afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
            owner {owner with phase := .aborted aborted} (.ok none) env after
        | Ok accepted =>
          exact RegistrationNativePlatformLorIdealBeaconPhase.phase_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
            owner {owner with phase := .aborted aborted} oneTime accepted env after
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconFinish.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconFinish.effects_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconFinish.finish_source

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish
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
variable (localScalar : PqxdhJointGapDh.ScalarBytes)
local notation "wordLocal" => (symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false) ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup localScalar
local notation "nativeLocal" => wordLocal ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate
local notation "actualLocal" => (actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false) ∘ₛ RegistrationNativePublicOwners.ordinary setup localScalar

theorem effects (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    simulateQ nativeLocal (RegistrationBeaconReferenceCompiler.effect query) =
      simulateQ wordLocal (RegistrationNativeSecretWordInterface.effect query) := by
  rw [QueryImpl.simulateQ_compose,RegistrationNativeSecretWordServerSource.effect_query]

theorem demand (reference : RegistrationNativeSecretWordMessage.Message) :
    simulateQ nativeLocal (RegistrationNativePlatformBeaconMaterialInterpreter.demand (RegistrationNativeSecretWordMessage.eval candidate reference)) =
      simulateQ wordLocal (RegistrationNativeSecretWordInterface.demand reference) := by
  simp only [QueryImpl.compose,RegistrationNativePlatformBeaconMaterialInterpreter.demand,
    RegistrationNativeSecretWordServerSource.realize,RegistrationNativeSecretWordInterface.demand,
    simulateQ_spec_query]
  simp only [RegistrationNativeSecretWordOwners.ordinary,simulateQ_spec_query,QueryImpl.compose,RegistrationNativeSecretWordInterface.liftLocal]
  exact RegistrationNativePlatformLorIdealBeaconSuffix.demand_coherence setup wire sign seed scalar candidate unused selected pairs publicKey challenge reference

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
    (effects setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar) candidate
    (demand setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar)
    setup.source wire.frameWrite owner current prepared env
  simp only [QueryImpl.simulateQ_compose] at shared
  have nativeEq := RegistrationNativePlatformLorIdealOrdinaryBeacon.local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
    (((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner
      (RegistrationNativeSecretWordBeaconRoot.restore candidate prepared)).run current).run env) before
  simp only [QueryImpl.simulateQ_compose] at nativeEq
  rw [shared] at nativeEq
  simpa only [QueryImpl.simulateQ_compose] using nativeEq
theorem phase_source (owner current : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ wordLocal
        (((RegistrationNativePlatformSecretWordFinish.phase setup wire owner oneTime authenticated).run current).run env)).run before =
      (simulateQ actualLocal
        (((RegistrationNativePlatformBeaconPhase.phase setup wire owner oneTime authenticated).run current).run env)).run (frame candidate before) := by
  simp only [RegistrationNativePlatformSecretWordFinish.phase,RegistrationNativePlatformBeaconPhase.phase,
    StateT.run_bind,StateT.run_lift,bind_pure_comp,simulateQ_bind,bind_map_left,map_bind]
  have sourceEq := RegistrationNativePlatformLorIdealOrdinaryBeacon.agreement_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
    owner oneTime authenticated env before
  rw [←sourceEq,bind_map_left]
  apply bind_congr
  rintro ⟨⟨prepared,envAfter⟩,after⟩
  simp only [Prod.map_apply,id_eq]
  exact afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
    owner current prepared envAfter after
theorem effects_source {A : Type} (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$> (simulateQ wordLocal
      (simulateQ RegistrationNativeSecretWordInterface.effect work)).run before =
      (simulateQ actualLocal (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run (frame candidate before) := by
  have sourceEq := RegistrationNativePlatformLorIdealOrdinaryBeacon.local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
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
      have authEq := effects_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
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
        exact afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
          owner {owner with phase := .aborted aborted} (.fail error) env after
      | div =>
        exact afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
          owner {owner with phase := .aborted aborted} .div env after
      | ok result => cases result with
        | Err error =>
          exact afterPrepared_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
            owner {owner with phase := .aborted aborted} (.ok none) env after
        | Ok accepted =>
          exact phase_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
            owner {owner with phase := .aborted aborted} oneTime accepted env after
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.demand

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.afterPrepared_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.afterPrepared_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.phase_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.effects_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish.finish_source

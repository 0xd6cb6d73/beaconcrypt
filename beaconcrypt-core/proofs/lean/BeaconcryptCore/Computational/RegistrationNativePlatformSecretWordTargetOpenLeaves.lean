-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomSessionShape
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCollectAtom
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetServerPhase
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveServerOriginOuter
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLift
/-! Exact actual environment, external reserve and ordered agreement leaves retain the full Server/environment/platform/private states. Environment/reserve prefixes preserve the selected getter marker; successful agreement exposes its own source collector and pure root echo. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message ServerReady)
open RegistrationNativeSecretWord (Key Word)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordAtomSessionCredit (count)
open RegistrationNativePlatformSecretWordAtomOpenRun (State Base close)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
open PqxdhKemIndCca
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey)
    (challenge : MlKem768Ciphertext) (outer : QueryImpl Combined ProbComp)
local notation "provider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "impl" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer

local notation "localImpl" => RegistrationNativeSecretWordTargetServerExecution.localImpl
  (n := n) setup wire route sign input inside provider outer true

/-- The exact reached environment program has its same local environment/private support. -/
theorem environment_source (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (before : State n KemSK Platform) (result : A × State n KemSK Platform)
    (supported : result ∈ support ((close impl (StateT.lift (StateT.lift
      (simulateQ (RegistrationNativePlatformSecretWordOpen.effects (wordLocal true)) work)))).run before)) :
    (result.1,(result.2.2.1,result.2.2.2.2)) ∈ support
      ((RegistrationNativeSecretWordTargetServerExecution.lower localImpl
        (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect work))).run
          (before.2.1,before.2.2.2)) := by
  rw [RegistrationNativePlatformSecretWordTargetOpenLift.environment_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  exact called

/-- Mandatory authentication and all other environment programs cannot spend the early getter marker. -/
theorem environment_phase (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A)
    (before : State n KemSK Platform) (result : A × State n KemSK Platform)
    (supported : result ∈ support ((close impl (StateT.lift (StateT.lift
      (simulateQ (RegistrationNativePlatformSecretWordOpen.effects (wordLocal true)) work)))).run before)) :
    result.2.2.2.2.kem.2 = before.2.2.2.kem.2 :=
  RegistrationNativeSecretWordTargetServerPhase.effect_phase setup wire route sign input inside selected pairs publicKey challenge outer
    work (before.2.1,before.2.2.2) (result.1,(result.2.2.1,result.2.2.2.2))
    (environment_source setup wire route sign input inside selected pairs publicKey challenge outer work before result supported)

private theorem platform_free (work : StateT Platform ProbComp A) (before : Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP
      (RegistrationNativeSecretWordTargetPhaseCore.Selected (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false (work.run before) 0)
  intro coin
  simp [RegistrationNativeSecretWordFrontend.effect,RegistrationNativeSecretWordTargetPhaseCore.Selected,isQueryBoundP_query_iff]

/-- Arbitrary stateful external reserve outcomes retain the private selected-getter marker. -/
theorem platform_phase (work : StateT Platform ProbComp A) (before : State n KemSK Platform)
    (result : A × State n KemSK Platform)
    (supported : result ∈ support ((close impl (StateT.lift (StateT.lift
      (RegistrationNativePlatformSecretWordOrdinary.platform work)))).run before)) :
    result.2.2.2.2.kem.2 = before.2.2.2.kem.2 := by
  rw [RegistrationNativePlatformSecretWordTargetOpenLift.lifted_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  have kept := RegistrationNativeSecretWordTargetPhaseCore.program_phase setup wire route sign input inside selected pairs publicKey challenge outer
    _ (platform_free work before.2.2.1) before.2.2.2 reached called
  cases equal
  exact kept

/-- Actual repeated pin hashing has no selected getter, for every hash result and private poststate. -/
theorem pin_phase (current : session.ServerAuthenticationPin) (before : State n KemSK Platform)
    (result : RegistrationNativeServerPinRecompute.PinReply × State n KemSK Platform)
    (supported : result ∈ support ((close impl (StateT.lift (StateT.lift
      (RegistrationNativePlatformServerReferenceAccept.pin
        (RegistrationNativePlatformSecretWordOpen.effects (wordLocal true)) current)))).run before)) :
    result.2.2.2.2.kem.2 = before.2.2.2.kem.2 := by
  rw [RegistrationNativePlatformSecretWordTargetOpenLift.pin,
    RegistrationNativePlatformSecretWordTargetOpenLift.lifted_map,support_map] at supported
  obtain ⟨hashed,called,equal⟩ := supported
  have kept := environment_phase setup wire route sign input inside selected pairs publicKey challenge outer
    (((PqxdhRecordLiftInterface.EnvEffects n).query (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))) :
      OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _) before hashed
    (by simpa only [simulateQ_spec_query] using called)
  cases equal
  exact kept

/-- The same successful actual agreement exposes its own collector and pure root echo. -/
theorem agreement (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Platform) (result : RustM (Option ServerReady) × State n KemSK Platform)
    (supported : result ∈ support ((close impl
      (RegistrationNativePlatformSecretWordOpen.agreement (wordLocal true) setup checks packet authenticated)).run before))
    (ready : ServerReady) (returned : result.1 = .ok (some ready)) :
    ∃ collected middle,
      (some collected,middle) ∈ support
        ((RegistrationNativeSecretWordTargetServerExecution.lower localImpl
          (RegistrationNativeSecretWordServerCompiler.collect setup checks packet authenticated)).run
          (before.2.1,before.2.2.2)) ∧
      (.ok (some ready),(result.2.2.1,result.2.2.2.2)) ∈ support
        ((RegistrationNativeSecretWordTargetServerExecution.lower localImpl
          (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.prepare
            (RegistrationNativeSecretWordServerRoot.client authenticated.binding collected)))).run middle) ∧
      ready.reference = RegistrationNativeSecretWordServerRoot.message collected := by
  rw [RegistrationNativePlatformSecretWordAtomOpenRun.agreement_run,support_map] at supported
  obtain ⟨reached,called,equal⟩ := supported
  cases equal
  have actual : ((.ok (some ready),reached.1.2),reached.2) ∈ support
      ((RegistrationNativeSecretWordTargetServerExecution.lower localImpl
        ((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before.1)).run
          (before.2.1,before.2.2.2)) := by
    rw [←returned]
    exact called
  exact RegistrationNativeSecretWordLiveServerOriginOuter.agreement setup wire route sign input inside provider outer true
    checks packet authenticated before.1 reached.1.2 (before.2.1,before.2.2.2) reached.2 ready actual

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.environment_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.environment_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.environment_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.environment_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.platform_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.platform_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.pin_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.pin_phase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenLeaves.agreement

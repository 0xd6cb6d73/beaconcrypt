-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinary
/-! Arbitrary-choice source Beacon agreement is composed from the literal opaque-word collector and the actual stateful prepare echo. The physical World remains free and the same private provider/root-service state is retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon
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
variable (localScalar : PqxdhJointGapDh.ScalarBytes)
local notation "wordOrdinary" => wordLocal ∘ₛ RegistrationNativeSecretWordOwners.ordinary setup localScalar
local notation "actualOrdinary" => actualLocal ∘ₛ RegistrationNativePublicOwners.ordinary setup localScalar

theorem local_program_source {A : Type} (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A)
    (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      (simulateQ wordOrdinary (simulateQ (RegistrationNativeSecretWordServerSource.realize candidate) work)).run before =
      (simulateQ actualOrdinary work).run (frame candidate before) := by
  have sourceEq := RegistrationNativePlatformLorCtxRealization.local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge false
    (simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar) work) before
  rw [←QueryImpl.simulateQ_compose (RegistrationNativeSecretWordServerSource.realize candidate),
    RegistrationNativeSecretWordCheckedOrdinary.ordinary_realize,QueryImpl.simulateQ_compose] at sourceEq
  simpa only [QueryImpl.simulateQ_compose] using sourceEq

theorem prepare_source (message : RegistrationNativeSecretWordMessage.Message) (before : Symbolic n KemSK) :
    Prod.map (Option.map (RegistrationNativeSecretWordMessage.eval candidate)) (frame candidate) <$>
      (simulateQ wordLocal (RegistrationNativeSecretWordOwners.ordinary setup localScalar (.inl message))).run before =
      (simulateQ actualLocal (RegistrationNativePublicOwners.ordinary setup localScalar (.inl (RegistrationNativeSecretWordMessage.eval candidate message)))).run (frame candidate before) := by
  have translated := RegistrationNativeSecretWordLocalMessage.eval_materialize setup.joint setup.dh localScalar candidate message
  cases formed : RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh localScalar message with
  | none =>
    have original : RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar (RegistrationNativeSecretWordMessage.eval candidate message) = none := by
      simpa only [formed,Option.map_none] using translated.symm
    simp only [RegistrationNativeSecretWordOwners.ordinary,RegistrationNativePublicOwners.ordinary,formed,original,
      simulateQ_pure,StateT.run_pure,map_pure]
    rfl
  | some supplied =>
    have original : RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar (RegistrationNativeSecretWordMessage.eval candidate message) = some (RegistrationNativeSecretWordMessage.eval candidate supplied) := by
      simpa only [formed,Option.map_some] using translated.symm
    simp only [RegistrationNativeSecretWordOwners.ordinary,RegistrationNativePublicOwners.ordinary,formed,original,
      simulateQ_spec_query,QueryImpl.compose,RegistrationNativeSecretWordInterface.liftLocal,RegistrationNativePublicFrontend.liftLocal]
    exact RegistrationNativePlatformLorCtxLeaves.prepare_source setup wire sign seed scalar candidate unused symbolicProvider actualProvider supplied before

theorem collect_source (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (before : Symbolic n KemSK) :
    Prod.map (Prod.map (Option.map (RegistrationNativeSecretWordBeaconPrepare.eval candidate)) id) (frame candidate) <$>
      (simulateQ wordOrdinary ((RegistrationNativeSecretWordBeaconCompiler.collect setup owner oneTime authenticated).run env)).run before =
      (simulateQ actualOrdinary ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env)).run (frame candidate before) := by
  have sourceEq := local_program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
    ((RegistrationBeaconReferenceCompiler.collect setup owner oneTime authenticated).run env) before
  rw [RegistrationNativeSecretWordBeaconSource.collector_source] at sourceEq
  simpa only [simulateQ_map,StateT.run_map,Functor.map_map,Prod.map_def,id_eq] using sourceEq

noncomputable def wordPreparation : QueryImpl RegistrationNativeSecretWordMessage.PrepareSpec (StateT (Symbolic n KemSK) (World n)) :=
  wordOrdinary ∘ₛ RegistrationNativeSecretWordInterface.prepare
noncomputable def nativePreparation : QueryImpl RegistrationServerReferenceRoot.PrepareSpec
    (StateT (RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase) (World n)) :=
  actualOrdinary ∘ₛ RegistrationBeaconReferenceCompiler.prepare

theorem root_source (authenticated : registration.AuthenticatedResponse)
    (pending : RegistrationNativeSecretWordBeaconPrepare.Prepared registration.AuthenticatedResponse) (before : Symbolic n KemSK) :
    Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) (frame candidate) <$>
      (simulateQ (wordPreparation setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar)
        (RegistrationNativeSecretWordBeaconRoot.client authenticated pending)).run before =
      (simulateQ (nativePreparation (n := n) setup wire sign seed scalar candidate selected pairs publicKey challenge localScalar)
        (RegistrationBeaconReferenceRoot.client authenticated (RegistrationNativeSecretWordBeaconPrepare.eval candidate pending))).run (frame candidate before) := by
  simp only [RegistrationNativeSecretWordBeaconRoot.client,RegistrationBeaconReferenceRoot.client,
    simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure,
    wordPreparation,nativePreparation,QueryImpl.compose,RegistrationNativeSecretWordInterface.prepare,
    RegistrationBeaconReferenceCompiler.prepare,simulateQ_spec_query]
  rw [←RegistrationNativeSecretWordBeaconRoot.message_eval candidate pending]
  have sourceEq := prepare_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
    (RegistrationNativeSecretWordBeaconRoot.message pending) before
  rw [←sourceEq,bind_map_left]
  simp only [map_bind,map_pure]
  apply bind_congr
  rintro ⟨reference,after⟩
  cases reference <;> rfl

theorem agreement_source (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (before : Symbolic n KemSK) :
    Prod.map (Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) id) (frame candidate) <$>
      (simulateQ wordOrdinary ((RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated).run env)).run before =
      (simulateQ actualOrdinary ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env)).run (frame candidate before) := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.agreement,RegistrationBeaconReferenceCompiler.agreement,
    StateT.run_bind,simulateQ_bind,StateT.run_bind,map_bind]
  have collectEq := collect_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
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
    simp only [←QueryImpl.simulateQ_compose]
    have rooted := root_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar authenticated pending after
    have lifted := congrArg (Functor.map (fun result => ((result.1,envAfter),result.2))) rooted
    simpa only [wordPreparation,nativePreparation,Functor.map_map,Prod.map_def,id_eq] using lifted
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.local_program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.local_program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.prepare_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.collect_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.collect_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.root_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryBeacon.agreement_source

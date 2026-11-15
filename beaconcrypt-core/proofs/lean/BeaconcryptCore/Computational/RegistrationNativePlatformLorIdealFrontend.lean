-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorCtxRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendAccept
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend
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

variable {Platform E : Type} [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (checks : PqxdhServerAuthExperiment.Checks)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "evaluate" => RegistrationNativePlatformSecretWordOrdinary.evaluate candidate
local notation "nativeController" => RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "wordController" => RegistrationNativePlatformSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

theorem ordinary_source (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (ordinary : RegistrationNativePlatformSecretWordOrdinary.Ordinary query)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : Symbolic n KemSK) :
    Prod.map (Prod.map id evaluate) (frame candidate) <$>
      (simulateQ symbolic ((RegistrationNativePlatformSecretWordOrdinary.handler setup source selectedOwner publicPrekey reserveFrame writer query).run before)).run privateBefore =
      (simulateQ actual (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((nativeController query).run (evaluate before)))).run (frame candidate privateBefore) := by
  have freeEq := RegistrationNativePlatformLorIdealOrdinary.handler_source (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer candidate query ordinary before
  have compared := congrArg (simulateQ symbolic) freeEq
  simp only [simulateQ_map] at compared
  have nativeEq := RegistrationNativePlatformLorCtxRealization.program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed ((nativeController query).run (evaluate before))) privateBefore
  simp only [RegistrationNativePlatformLorCtxRealization.implementation,QueryImpl.simulateQ_compose] at nativeEq
  rw [compared] at nativeEq
  simpa only [StateT.run_map,Functor.map_map,Prod.map_def,id_eq] using nativeEq

theorem handler_source (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : Symbolic n KemSK) :
    Prod.map (Prod.map id evaluate) (frame candidate) <$>
      (simulateQ symbolic ((wordController query).run before)).run privateBefore =
      (simulateQ actual (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((nativeController query).run (evaluate before)))).run (frame candidate privateBefore) := by
  cases query with
  | inl coin =>
    exact ordinary_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inl coin) (by trivial) before privateBefore
  | inr query =>
    cases query
    case accept packet =>
      exact RegistrationNativePlatformLorIdealFrontendAccept.accept_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before privateBefore
    case build handle application =>
      simpa only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformPublicFrontend.handler] using
          RegistrationNativePlatformLorIdealFrontendBuild.build_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
            view failure allocation erased helper writer reservePeer _ _ before privateBefore
    case finish index packet =>
      simpa only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformPublicFrontend.handler] using
          RegistrationNativePlatformLorIdealFrontendFinish.finish_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
            _ _ before privateBefore
    all_goals
      exact ordinary_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ (by trivial) before privateBefore

noncomputable def wordTyped : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (RegistrationNativePlatformSecretWordOrdinary.State source Platform × Symbolic n KemSK) (World n)) :=
  (QueryImpl.mapStateTBase symbolic wordController).flattenStateT
noncomputable def nativeTyped : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (RegistrationNativePlatformPublicFrontend.State source Platform ×
      RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase) (World n)) :=
  ((actual ∘ₛ RegistrationNativePlatformPublicCoinEmbedding.embed).mapStateTBase nativeController).flattenStateT

def projectState : RegistrationNativePlatformSecretWordOrdinary.State source Platform × Symbolic n KemSK →
    RegistrationNativePlatformPublicFrontend.State source Platform ×
      RegistrationNativeSelectiveHiddenInterpreter.State n KemSK RegistrationNativeKemSwitchSource.Phase := Prod.map evaluate (frame candidate)
local notation "wordTypedImpl" => wordTyped setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "nativeTypedImpl" => nativeTyped setup wire sign seed scalar candidate selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

theorem query_source (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform × Symbolic n KemSK) :
    Prod.map id (projectState candidate) <$> (wordTypedImpl query).run before =
      (nativeTypedImpl query).run (projectState candidate before) := by
  rcases before with ⟨before,privateBefore⟩
  unfold wordTyped nativeTyped
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [projectState,Prod.map_apply]
  rw [QueryImpl.flattenStateT_mapStateTBase_apply_run]
  have core := handler_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before privateBefore
  have lifted := congrArg (Functor.map (fun result => (result.1.1,(result.1.2,result.2)))) core
  simpa only [QueryImpl.simulateQ_compose,Functor.map_map,projectState,Prod.map_def,id_eq] using lifted

theorem program_source {A : Type} (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform × Symbolic n KemSK) :
    Prod.map id (projectState candidate) <$> (simulateQ wordTypedImpl work).run before =
      (simulateQ nativeTypedImpl work).run (projectState candidate before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq wordTypedImpl nativeTypedImpl (projectState candidate)
    (query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer) work before

theorem full_source {A : Type} (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform × Symbolic n KemSK) :
    Prod.map id (projectState candidate) <$>
      (simulateQ wordTypedImpl (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run before =
      (simulateQ nativeTypedImpl (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run (projectState candidate before) :=
  program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ before

theorem physical_source {A Physical : Type}
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform × Symbolic n KemSK) (physicalBefore : Physical) :
    Prod.map (Prod.map id (projectState candidate)) id <$>
      (simulateQ physical ((simulateQ wordTypedImpl work).run before)).run physicalBefore =
      (simulateQ physical ((simulateQ nativeTypedImpl work).run (projectState candidate before))).run physicalBefore := by
  have related := program_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge checks selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer work before
  have closed := congrArg (fun script => (simulateQ physical script).run physicalBefore) related
  simpa only [simulateQ_map,StateT.run_map,Prod.map_def,id_eq] using closed
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.ordinary_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.ordinary_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.full_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.full_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.physical_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontend.physical_source

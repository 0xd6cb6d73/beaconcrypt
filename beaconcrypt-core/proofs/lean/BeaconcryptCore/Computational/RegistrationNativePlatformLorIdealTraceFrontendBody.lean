-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBuildMap
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceAcceptLift
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceAcceptLift
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendBuild
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World)
open RegistrationNativePlatformLorIdealTraceRealization (Symbolic)
local notation "frame" => RegistrationNativePlatformLorIdealTraceLeaves.project
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolic" => RegistrationNativePlatformLorIdealTraceLeaves.symbolicTrace setup wire sign seed scalar candidate unused selected pairs publicKey challenge
local notation "actual" => RegistrationNativePlatformLorIdealTraceLeaves.nativeTrace setup wire sign seed scalar candidate selected pairs publicKey challenge
local notation "wordLocal" => symbolic ∘ₛ RegistrationNativeSecretWordInterface.liftLocal false
local notation "nativeLocal" => wordLocal ∘ₛ RegistrationNativeSecretWordServerSource.realize candidate
local notation "actualLocal" => actual ∘ₛ RegistrationNativePublicFrontend.liftLocal false

local notation "reified" => RegistrationNativePlatformLorIdealTraceRealization.implementation setup wire sign seed scalar candidate unused selected pairs publicKey challenge

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

omit primitive in
private theorem map_apply {S B C : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : B → C) (work : StateT S m B) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

omit primitive in
private theorem bind_apply {S B C : Type} {m : Type → Type} [Monad m]
    (work : StateT S m B) (next : B → StateT S m C) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
omit primitive in
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before,before) := rfl
omit primitive in
private theorem modify_apply {S : Type} {m : Type → Type} [Monad m] (f : S → S) (before : S) :
    (modify f : StateT S m Unit) before = pure ((),f before) := rfl

theorem accept_source (packet : registration.InitPacket)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : Symbolic n KemSK) :
    Prod.map (Prod.map id evaluate) (frame candidate) <$>
      (simulateQ symbolic ((wordController (.inr (.accept packet))).run before)).run privateBefore =
      (simulateQ actual (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((nativeController (.inr (.accept packet))).run (evaluate before)))).run (frame candidate privateBefore) := by
  have core := RegistrationNativePlatformLorIdealTraceAcceptLift.accept_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
    checks reserveRegistration (decide (before.1.parsedAccepts = selectedAccept)) source.verify packet before.1.server before.1.environment before.2 privateBefore
  have observed := congrArg (Functor.map (fun result => ((result.1.1.1.1,
    ({(evaluate before).1 with server := result.1.1.1.2,environment := result.1.1.2,parsedAccepts := before.1.parsedAccepts+1},result.1.2)),result.2))) core
  simp only [RegistrationNativePlatformSecretWordFrontend.handler,RegistrationNativePlatformSecretWordFrontend.accept,
    RegistrationNativePlatformPublicFrontend.handler,RegistrationNativePlatformPublicFrontend.executeLocal,
    bind_apply,get_apply,modify_apply,pure_bind,
    RegistrationNativePlatformSecretWordFrontend.serverOpen,RegistrationNativePlatformPublicFrontend.serverOpen,
    StateT.run,simulateQ_map,map_apply,Functor.map_map,
    RegistrationNativePlatformSecretWordOrdinary.evaluate,RegistrationNativeSecretWordMessage.State.eval,
    RegistrationNativePlatformLorIdealTraceAcceptLift.nativeBase,QueryImpl.simulateQ_compose,Prod.map_def,id_eq] at observed ⊢
  convert observed using 1
  rfl
omit primitive in
private theorem pure_apply {S B : Type} {m : Type → Type} [Monad m]
    (value : B) (before : S) : (pure value : StateT S m B) before = pure (value,before) := rfl

omit primitive in
theorem finish_source (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : Symbolic n KemSK) :
    Prod.map (Prod.map id evaluate) (frame candidate) <$>
      (simulateQ symbolic ((RegistrationNativePlatformSecretWordFrontend.finish setup wire source index packet).run before)).run privateBefore =
      (simulateQ actual (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
          (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run (evaluate before)))).run (frame candidate privateBefore) := by
  cases found : before.1.beacons[index]? with
  | none =>
    simp [RegistrationNativePlatformSecretWordFrontend.finish,RegistrationNativePlatformPublicFrontend.executeLocal,
      RegistrationNativePlatformPublicFrontend.beacon,RegistrationNativePlatformPublicFrontend.finish,
      RegistrationNativePlatformSecretWordOrdinary.evaluate,RegistrationNativeSecretWordMessage.State.eval,
      StateT.run,Prod.map_def,found,pure_apply]
  | some owner =>
    have actualFound : (evaluate before).1.beacons[index]? = some owner := found
    have outer := RegistrationNativePlatformLorIdealFrontendFinish.native_called (n := n) setup wire index packet (evaluate before) owner actualFound
    rw [outer]
    simp only [RegistrationNativePlatformSecretWordFrontend.finish,StateT.run,found,simulateQ_map]
    simp only [map_apply,Functor.map_map]
    cases scalarCase : owner.scalar with
    | none =>
      have same := RegistrationNativePlatformLorIdealTraceBeacon.finish_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge none
        owner.view packet before.1.environment privateBefore
      have lifted := congrArg (Functor.map (fun result =>
        ((result.1.1.1,({(evaluate before).1 with beacons := before.1.beacons.set index {owner with view := result.1.1.2},environment := result.1.2},before.2)),result.2))) same
      simp only [scalarCase,RegistrationNativePlatformLorIdealTraceBeacon.wordLocalScalar,RegistrationNativePlatformLorIdealTraceBeacon.nativeLocalScalar,QueryImpl.simulateQ_compose,Functor.map_map,
        RegistrationNativePlatformSecretWordOrdinary.evaluate,RegistrationNativeSecretWordMessage.State.eval,
        Prod.map_def,id_eq,StateT.run] at lifted ⊢
      convert lifted using 1
    | some localScalar =>
      have same := RegistrationNativePlatformLorIdealTraceBeacon.finish_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge (some localScalar)
        owner.view packet before.1.environment privateBefore
      have lifted := congrArg (Functor.map (fun result =>
        ((result.1.1.1,({(evaluate before).1 with beacons := before.1.beacons.set index {owner with view := result.1.1.2},environment := result.1.2},before.2)),result.2))) same
      simp only [scalarCase,RegistrationNativePlatformLorIdealTraceBeacon.wordLocalScalar,RegistrationNativePlatformLorIdealTraceBeacon.nativeLocalScalar,QueryImpl.simulateQ_compose,Functor.map_map,
        RegistrationNativePlatformSecretWordOrdinary.evaluate,RegistrationNativeSecretWordMessage.State.eval,
        Prod.map_def,id_eq,StateT.run] at lifted ⊢
      convert lifted using 1
omit primitive in
theorem build_compatible (query : (RegistrationNativePlatformSecretWordBuild.Spec n).Domain) (before : Symbolic n KemSK) :
    Prod.map id (frame candidate) <$>
      ((symbolic ∘ₛ RegistrationNativePlatformLorIdealBuildMap.wordEmbedding) query).run before =
      (((actual ∘ₛ RegistrationNativePlatformLorIdealBuildMap.nativeEmbedding) ∘ₛ
        RegistrationNativePlatformSecretWordBuild.realize candidate) query).run (frame candidate before) := by
  rcases query with message | effect | coin
  · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
      (.inl (.inr (.inl (.inl message)))) before using 1 <;>
      simp only [QueryImpl.compose,RegistrationNativePlatformLorIdealBuildMap.wordEmbedding,RegistrationNativePlatformLorIdealBuildMap.nativeEmbedding,
        RegistrationNativePlatformSecretWordBuild.realize,RegistrationNativePlatformSecretWordBuild.wordEmbedding,
        RegistrationNativeSecretWordInterface.demand,RegistrationNativeSecretWordInterface.liftLocal,
        RegistrationNativePlatformPublicFrontend.buildEmbedding,RegistrationNativePlatformPublicFrontend.localQuery,
        RegistrationNativePlatformPublicFrontend.embedLocal,RegistrationNativePlatformPublicCoinEmbedding.embed,
        RegistrationNativePlatformLorCtxLeaves.nativeQuery,simulateQ_spec_query]; rfl
  · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
      (.inl (.inr (.inl (.inr (.inr effect))))) before using 1 <;>
      simp only [QueryImpl.compose,RegistrationNativePlatformLorIdealBuildMap.wordEmbedding,RegistrationNativePlatformLorIdealBuildMap.nativeEmbedding,
        RegistrationNativePlatformSecretWordBuild.realize,RegistrationNativePlatformSecretWordBuild.wordEmbedding,
        RegistrationNativeSecretWordInterface.effect,RegistrationNativeSecretWordInterface.liftLocal,
        RegistrationNativePlatformPublicFrontend.buildEmbedding,

        RegistrationNativePlatformLorCtxLeaves.nativeQuery,simulateQ_spec_query] <;> rfl
  · convert RegistrationNativePlatformLorIdealTraceLeaves.query_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
      (.inl (.inr (.inl (.inr (.inr (.inl coin)))))) before using 1 <;>
      simp only [QueryImpl.compose,RegistrationNativePlatformLorIdealBuildMap.wordEmbedding,RegistrationNativePlatformLorIdealBuildMap.nativeEmbedding,
        RegistrationNativePlatformSecretWordBuild.realize,RegistrationNativePlatformSecretWordBuild.wordEmbedding,
        RegistrationNativeSecretWordInterface.effect,RegistrationNativeSecretWordInterface.liftLocal,
        RegistrationNativePlatformPublicFrontend.buildEmbedding,
        RegistrationNativePlatformPublicFrontend.embedLocal,RegistrationNativePlatformPublicCoinEmbedding.embed,
        RegistrationNativePlatformPublicFrontend.localCoin,RegistrationNativePlatformPublicFrontend.publicCoin,
        RegistrationNativePlatformLorCtxLeaves.nativeQuery,simulateQ_spec_query] <;> rfl

theorem build_source (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform) (privateBefore : Symbolic n KemSK) :
    Prod.map (Prod.map id evaluate) (frame candidate) <$>
      (simulateQ symbolic ((RegistrationNativePlatformSecretWordFrontend.build setup sign view failure allocation erased helper writer reservePeer handle application source).run before)).run privateBefore =
      (simulateQ actual (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal
          (RegistrationNativePlatformPublicFrontend.build setup sign view failure allocation erased helper writer reservePeer handle application source)).run (evaluate before)))).run (frame candidate privateBefore) :=
  (RegistrationNativePlatformLorIdealBuildMap.build setup source sign view failure allocation erased helper writer reservePeer candidate actual symbolic (frame candidate)
    (build_compatible setup wire sign seed scalar candidate unused selected pairs publicKey challenge) handle application before privateBefore).symm
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.accept_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.build_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.build_compatible

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealTraceFrontendBody.build_source

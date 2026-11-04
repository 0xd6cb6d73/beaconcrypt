-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealBeaconFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinaryFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
/-! The complete actual public finish envelope retains its common platform state and every optional owner/scalar branch under the concrete state-projected source dictionary. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish
open PqxdhServerAuthExperiment (Setup)
open PqxdhKemIndCca
open RegistrationNativePlatformLorCtxLeaves (World Symbolic frame)
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem local_embedding :
    (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK) ∘ₛ
      RegistrationNativePlatformPublicFrontend.embedLocal) ∘ₛ RegistrationNativePlatformPublicFrontend.localQuery false =
      RegistrationNativePublicFrontend.liftLocal false := by
  funext query
  rcases query with message | common | kem
  · rfl
  · rfl
  · rcases kem with other | birth | key <;> rfl

private theorem local_thread (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (previous : Platform) :
    (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work).run previous =
      (fun value => (value,previous)) <$> simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
      RegistrationNativePlatformPublicFrontend.localHandler,StateT.run_lift,bind_pure_comp,bind_map_left,map_bind]
    apply bind_congr
    intro reply
    exact ih reply

theorem local_run (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) A) (previous : Platform) :
    simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      (simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
        ((simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work).run previous)) =
      (fun value => (value,previous)) <$> simulateQ (RegistrationNativePublicFrontend.liftLocal false) work := by
  rw [local_thread]
  simp only [simulateQ_map]
  rw [←QueryImpl.simulateQ_compose,←QueryImpl.simulateQ_compose,local_embedding]

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (candidate : MlKemSharedSecret)
    (unused : QueryImpl RegistrationNativeSecretWordService.Combined (World n))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
local notation "symbolicProvider" => RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected pairs publicKey challenge
local notation "actualProvider" => RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected pairs publicKey challenge candidate
local notation "symbolic" => RegistrationNativePlatformLorCtxLeaves.lower setup wire sign seed scalar candidate unused symbolicProvider
local notation "actual" => RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate actualProvider
local notation "evaluate" => RegistrationNativePlatformSecretWordOrdinary.evaluate candidate

private theorem map_apply {S B C : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : B → C) (work : StateT S m B) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map _ _ _

private theorem pure_apply {S B : Type} {m : Type → Type} [Monad m]
    (value : B) (before : S) : (pure value : StateT S m B) before = pure (value,before) := rfl

theorem native_called (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.1.beacons[index]? = some owner) :
    simulateQ (RegistrationNativePlatformPublicCoinEmbedding.embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
        (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run before) =
      (fun result => (result.1.1,
        ({before.1 with beacons := before.1.beacons.set index {owner with view := result.1.2}, environment := result.2},before.2))) <$>
        simulateQ (RegistrationNativePublicFrontend.liftLocal false)
          (match owner.scalar with
            | none => (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view).run before.1.environment)
            | some localScalar => simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
              (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view).run before.1.environment)) := by
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal,RegistrationNativePlatformPublicFrontend.beacon,
    RegistrationNativePlatformPublicFrontend.finish,StateT.run,found,simulateQ_map]
  simp only [map_apply,simulateQ_map,Functor.map_map]
  have transported := local_run (n := n) (KemSK := KemSK)
    (match owner.scalar with
      | none => (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view).run before.1.environment)
      | some localScalar => simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
        (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view).run before.1.environment)) before.2
  simp only [StateT.run] at transported
  have lifted := congrArg (Functor.map (fun result => (result.1.1.1,
    ({before.1 with beacons := before.1.beacons.set index {owner with view := result.1.1.2},environment := result.1.2},result.2)))) transported
  simp only [Functor.map_map,Prod.map_def,id_eq] at lifted ⊢
  convert lifted using 1



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
    have outer := native_called (n := n) setup wire index packet (evaluate before) owner actualFound
    rw [outer]
    simp only [RegistrationNativePlatformSecretWordFrontend.finish,StateT.run,found,simulateQ_map]
    simp only [map_apply,Functor.map_map]
    cases scalarCase : owner.scalar with
    | none =>
      have same := RegistrationNativePlatformLorIdealBeaconFinish.finish_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge
        owner.view packet before.1.environment privateBefore
      have lifted := congrArg (Functor.map (fun result =>
        ((result.1.1.1,({(evaluate before).1 with beacons := before.1.beacons.set index {owner with view := result.1.1.2},environment := result.1.2},before.2)),result.2))) same
      simp only [scalarCase,QueryImpl.simulateQ_compose,Functor.map_map,
        RegistrationNativePlatformSecretWordOrdinary.evaluate,RegistrationNativeSecretWordMessage.State.eval,
        Prod.map_def,id_eq,StateT.run] at lifted ⊢
      convert lifted using 1
    | some localScalar =>
      have same := RegistrationNativePlatformLorIdealOrdinaryFinish.finish_source setup wire sign seed scalar candidate unused selected pairs publicKey challenge localScalar
        owner.view packet before.1.environment privateBefore
      have lifted := congrArg (Functor.map (fun result =>
        ((result.1.1.1,({(evaluate before).1 with beacons := before.1.beacons.set index {owner with view := result.1.1.2},environment := result.1.2},before.2)),result.2))) same
      simp only [scalarCase,QueryImpl.simulateQ_compose,Functor.map_map,
        RegistrationNativePlatformSecretWordOrdinary.evaluate,RegistrationNativeSecretWordMessage.State.eval,
        Prod.map_def,id_eq,StateT.run] at lifted ⊢
      convert lifted using 1
end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish.local_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish.local_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish.native_called' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish.native_called

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealFrontendFinish.finish_source

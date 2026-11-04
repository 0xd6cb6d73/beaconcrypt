-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontendPrograms
/-! The corrected whole finish callback joins its exact local Word source equation to the actual global envelope. The original opaque owner roster, scalar route, complete environment and persistent platform state are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishSource
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (input)
open RegistrationNativePlatformSecretWordOrdinary (State evaluate)
open RegistrationNativePlatformSecretWordFrontendView (nativeBase)
variable {n : Nat} {I KemSK Platform : Type} {base : OracleSpec I}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before =
      (fun value => (value, before)) <$> work := bind_pure_comp _ _

theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (index : Nat) (packet : Option registration.ResponsePacket) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
          (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          ((RegistrationNativePlatformSecretWordFrontend.finish setup wire source index packet).run before) := by
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.beacon,
    RegistrationNativePlatformPublicFrontend.finish, RegistrationNativePlatformSecretWordFrontend.finish,
    evaluate, Prod.map_def, id_eq, RegistrationNativeSecretWordMessage.State.eval, StateT.run]
  cases found : before.1.beacons[index]? with
  | none => simp only [StateT.monad_pure_def, StateT.pure, simulateQ_pure, map_pure]
  | some owner =>
    let nativeWork := match owner.scalar with
      | none => ((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner.view).run before.1.environment
      | some localScalar => simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
          (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner.view).run before.1.environment)
    let wordWork := match owner.scalar with
      | none => ((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner.view).run before.1.environment
      | some localScalar => simulateQ (RegistrationNativeSecretWordOwners.ordinary setup localScalar)
          (((RegistrationNativePlatformSecretWordFinish.finish (n := n) setup wire source packet).run owner.view).run before.1.environment)
    have same : simulateQ (RegistrationNativeSecretWordChecked.native (n := n) (KemSK := KemSK) setup.source inside candidate (input setup.joint setup.dh seed scalar)) nativeWork =
        simulateQ (RegistrationNativeSecretWordChecked.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar)) wordWork := by
      have sourceEq := RegistrationNativePlatformSecretWordFinish.finish_source (n := n)
        setup inside candidate seed scalar owner.scalar wire source packet owner.view before.1.environment
      cases ownScalar : owner.scalar with
      | none => simpa only [nativeWork, wordWork, ownScalar, RegistrationNativePlatformSecretWordFinish.nativeImpl,
          RegistrationNativePlatformSecretWordFinish.wordImpl] using sourceEq
      | some localScalar => simpa only [nativeWork, wordWork, ownScalar,
          RegistrationNativePlatformSecretWordFinish.nativeImpl, RegistrationNativePlatformSecretWordFinish.wordImpl,
          RegistrationNativeSecretWordCheckedOrdinary.original, RegistrationNativeSecretWordCheckedOrdinary.symbolic,
          QueryImpl.simulateQ_compose] using sourceEq
    have compared := congrArg (fun action => action.run before.2)
      (RegistrationNativePlatformSecretWordFrontendPrograms.source_program (Platform := Platform)
        setup.source inside candidate (input setup.joint setup.dh seed scalar) false nativeWork wordWork same)
    have lifted := congrArg (fun action => (fun result => (result.1.1.1,
      (({ server := before.1.server.eval candidate,
          beacons := before.1.beacons.set index { owner with view := result.1.1.2 },
          environment := result.1.2, parsedAccepts := before.1.parsedAccepts } : RegistrationNativePublicFrontend.State source), result.2))) <$> action) compared
    simp only [nativeBase, RegistrationNativePlatformInterpret.state, QueryImpl.simulateQ_compose,
      StateT.run, map_apply, lift_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq,
      nativeWork, wordWork] at lifted ⊢
    convert lifted using 1

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishSource.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinishSource.finish

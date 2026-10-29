-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeySource

/-! The actual public-only candidate prefix has the same final matching analysis under the ideal related family and the proved protected-root cache projection. Only private Family history/cache instrumentation is projected; startup, full native ledger and trace are unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyFamilySource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
open RegistrationNativeKnownFirstKeySource (matched)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

theorem point_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : IdentitySeed) (scalar : ScalarBytes) (publicValue : PublicChallenge) :
    matched setup seed scalar <$>
      (simulateQ (RegistrationNativeRelatedFamily.idealImpl setup.hmac setup.joint setup.dh seed scalar)
        (RegistrationNativeRootCandidates.familyClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary publicValue)).run' RegistrationNativeRelatedFamily.empty =
      (simulateQ (RegistrationNativeRootCacheProjection.implementation setup.source setup.hmac setup.joint setup.dh seed scalar)
        (matched setup seed scalar <$> RegistrationNativeRootCandidates.rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary publicValue)).run' ∅ := by
  have projected := congrArg (fun experiment => Prod.fst <$> experiment)
    (RegistrationNativeRootCacheProjection.program_project setup.source setup.hmac correct setup.joint setup.dh seed scalar
      (matched setup seed scalar <$> RegistrationNativeRootCandidates.rootClient (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept bounds mode adversary publicValue)
      RegistrationNativeRelatedFamily.empty)
  have emptyCache : RegistrationNativeRootCacheProjection.project setup.joint setup.dh seed scalar
      RegistrationNativeRelatedFamily.empty = ∅ := by
    apply QueryCache.ext
    intro bytes
    simp [RegistrationNativeRootCacheProjection.project, RegistrationNativeRelatedFamily.empty,
      RegistrationNativeKeyFamilyPreparation.cacheOf]
  simpa only [RegistrationNativeRootCandidates.familyClient, simulateQ_map, StateT.run_map,
    StateT.run'_eq, Functor.map_map, Prod.map, id_eq, emptyCache] using projected

end BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyFamilySource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyFamilySource.point_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKnownFirstKeyFamilySource.point_source

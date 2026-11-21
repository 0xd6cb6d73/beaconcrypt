-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCaps

/-! The concrete symbolic local collectors retain the original structural material bills under their exact open callback source equations. These equalities concern oracle programs before interpretation: mapping the returned collector value does not remove queries. They do not infer syntax from equality of sampled output distributions. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal
open RegistrationNativeSecretWordInterface (LocalSpec)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι}

def IsDemand : (LocalSpec n KemSK).Domain → Prop
  | .inr (.inl (.inl _)) => True
  | _ => False

instance : DecidablePred (IsDemand (n := n) (KemSK := KemSK)) := fun query => by
  rcases query with _ | (_ | _) | _ <;> first | exact isTrue trivial | exact isFalse id

/-- The literal native-to-word query lowering preserves the demand predicate and its original allowance for every possible reply. -/
theorem realize_bound (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) cap) :
    (simulateQ (RegistrationNativeSecretWordServerSource.realize candidate) work).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  rcases query with message | (message | common) | other | pool | key
  all_goals try cases pool
  all_goals simp [RegistrationNativeSecretWordServerSource.realize,
    RegistrationNativeSecretWordInterface.prepare, RegistrationNativeSecretWordInterface.demand,
    RegistrationNativeSecretWordInterface.common, RegistrationNativeSecretWordInterface.localKem,
    RegistrationBeaconReferenceCaps.IsDemand, IsDemand, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- The complete actual symbolic Server prefix makes no material demand, including all optional KEM and native failures. -/
theorem server_collect_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerReferenceCompiler.Environment) :
    ((RegistrationNativeSecretWordServerCompiler.collect (n := n) setup checks packet authenticated).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  have original := realize_bound RegistrationNativeSecretWordMessage.zero _ 0
    (RegistrationServerOpenReferenceCaps.collect_free (n := n) setup checks packet authenticated before)
  rw [RegistrationNativeSecretWordServerSource.collector_source] at original
  simpa only [isQueryBoundP_map_iff] using original

/-- The actual arbitrary-pin symbolic Beacon prefix preserves the source's zero material-demand bill and complete current environment. -/
theorem beacon_collect_free (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : RegistrationBeaconReferenceCompiler.SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    ((RegistrationNativeSecretWordBeaconCompiler.collect (n := n) setup owner oneTime authenticated).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  have original := realize_bound RegistrationNativeSecretWordMessage.zero _ 0
    (RegistrationBeaconReferenceCaps.collect_free (n := n) setup owner oneTime authenticated before)
  rw [RegistrationNativeSecretWordBeaconSource.collector_source] at original
  simpa only [isQueryBoundP_map_iff] using original

/-- Actual environment callbacks are literal Common queries and never demand a root's material. -/
theorem effect_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    (simulateQ (RegistrationNativeSecretWordInterface.effect (KemSK := KemSK)) work).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeSecretWordInterface.effect, IsDemand, isQueryBoundP_query_iff]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.realize_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.realize_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.server_collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.server_collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.beacon_collect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.beacon_collect_free
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.effect_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsLocal.effect_free

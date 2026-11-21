-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateServer
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreateBeacon
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPoolFrame
import BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint

/-! Only actual owner creation can create a private symbolic KEM key. Every other full typed controller has a zero private-birth footprint, including failed authentication, source gates, material replies and record operations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreatePublic
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordInterface (LocalSpec Spec liftLocal)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordFrontend
open RegistrationNativeSecretWordTargetPoolFrame (IsCreate)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem local_bound (selected : Bool) (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) count) :
    (simulateQ (liftLocal selected) work).IsQueryBoundP (IsCreate (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  rcases query with message | paired | other | pool | key
  · simp [liftLocal, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · simp [liftLocal, IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
      IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · cases pool <;> simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
      IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  · cases selected <;> simp [liftLocal, RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
      IsCreate, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]

private theorem trusted_bound (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create) count) :
    (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) .create) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  rcases query with effect | other | pool | key
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
      RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemBeaconFootprint.counted, isQueryBoundP_query_iff]
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemBeaconFootprint.counted,
      RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]
  · cases pool <;> simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemBeaconFootprint.counted,
      RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]
  · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
      RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemBeaconFootprint.counted,
      RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]

private theorem owners_local_bound {source : RegistrationNativeMldsa.Source}
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (count : Nat) (bounded : RegistrationNativeKemBeaconFootprint.Bounded .create count work)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativeSecretWordOwners.executeLocal selected publicPrekey work).run owners).run env).IsQueryBoundP
      (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) count := by
  simp only [RegistrationNativeSecretWordOwners.executeLocal, StateT.run]
  apply RegistrationNativeSecretWordTargetNoCreateLocal.realize_bound RegistrationNativeSecretWordMessage.zero _ count
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, isQueryBoundP_map_iff]
  exact trusted_bound _ count (bounded _ _)

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) 0) :
    (simulateQ (RegistrationNativeSecretWordOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativeSecretWordOwners.ordinary, RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, ite_false]
      split <;> simp [RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate, isQueryBoundP_query_iff]
  | inr query =>
      simp only [RegistrationNativeSecretWordOwners.ordinary, isQueryBoundP_query_iff]
      intro counted
      rw [ite_eq_left counted]
      exact Nat.zero_lt_one

private theorem owners_finish_free (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativeSecretWordOwners.finish (n := n) setup source index packet).run owners).run env).IsQueryBoundP
      (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativeSecretWordOwners.finish, StateT.run]
  split
  · trivial
  · rename_i owner found
    rw [isQueryBoundP_map_iff]
    cases owner.scalar with
    | none => exact RegistrationNativeSecretWordTargetNoCreateBeacon.finish_free setup source packet owner.view env
    | some scalar =>
        exact ordinary_bound setup scalar _
          (RegistrationNativeSecretWordTargetNoCreateBeacon.finish_free setup source packet owner.view env)

private theorem server_bound {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (bounded : ∀ before env, ((work.run before).run env).IsQueryBoundP
      (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) 0) (before : State source) :
    ((serverOpen selected work).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact local_bound selected _ 0 (bounded before.server before.environment)

private theorem beacon_bound {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value) (count : Nat)
    (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP
      (RegistrationNativeSecretWordTargetNoCreateLocal.IsCreate (KemSK := KemSK)) count) (before : State source) :
    ((beacon work).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) count := by
  simp only [beacon, StateT.run, isQueryBoundP_map_iff]
  exact local_bound false _ count (bounded before.beacons before.environment)

private theorem record_free {source : RegistrationNativeMldsa.Source}
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [record, StateT.run]
  all_goals try split
  all_goals simp [IsCreate, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Only an actual typed create can consume the one private birth allowance. All other commands have zero. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
      RegistrationNativeSecretWordFrontend.effect, IsCreate, isQueryBoundP_query_iff, RegistrationNativeRawAdapter.kind]
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact beacon_bound _ 1 (fun owners env => owners_local_bound selectedOwner publicPrekey _ 1
          (by simpa using RegistrationNativeKemBeaconFootprint.create_bound setup .create edPin mlPin keyId) owners env) before
    | bundle owner =>
        exact beacon_bound _ 0 (fun owners env => owners_local_bound selectedOwner publicPrekey _ 0
          (RegistrationNativeKemBeaconFootprint.bundle_zero setup .create wire owner) owners env) before
    | finish owner packet => exact beacon_bound _ 0 (owners_finish_free setup source owner packet) before
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind,
          RegistrationNativeRawAdapter.kind]
        exact server_bound _ _ (RegistrationNativeSecretWordTargetNoCreateServer.accept_free setup checks source.verify packet) _
    | build handle application =>
        exact server_bound false _
          (RegistrationNativeSecretWordTargetNoCreateServer.build_free setup.source wire checks sign handle application) before
    | hmac key bytes => trivial
    | hash bytes => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
        RegistrationNativeSecretWordFrontend.effect, IsCreate, isQueryBoundP_query_iff, RegistrationNativeRawAdapter.kind]
    | serverSend keyId plaintext => exact record_free (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_free (.inl (.inr raw)) before
    | beaconSend owner plaintext => exact record_free (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw => exact record_free (.inr (owner, .inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreatePublic
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreatePublic.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetNoCreatePublic.handler_bound

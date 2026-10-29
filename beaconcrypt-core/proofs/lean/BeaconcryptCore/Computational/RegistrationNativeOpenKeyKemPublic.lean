-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemServer
import BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint
import BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup
import BeaconcryptCore.Computational.RegistrationNativeMaterialBudget

/-! Structural private KEM birth/reveal bills for the actual full public native frontend. Creation uses its genuine indexed source; all Server, response, publication, ordinary and record branches preserve the zero reveal allowance without removing their actual callbacks. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {kind : RegistrationNativeKemBeaconFootprint.Kind}

def RoutedPrivate (kind : RegistrationNativeKemBeaconFootprint.Kind) : (RoutedKem KemSK).Domain → Prop
  | .inr (.inl .create) => kind = .create
  | .inr (.inl (.reveal _)) => kind = .reveal
  | _ => False

def IsPrivate (kind : RegistrationNativeKemBeaconFootprint.Kind) : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inr query)) => RoutedPrivate (KemSK := KemSK) kind query
  | _ => False

instance (kind : RegistrationNativeKemBeaconFootprint.Kind) : DecidablePred (RoutedPrivate (KemSK := KemSK) kind) := fun query => by
  rcases query with (other | key) | (pool | key)
  · exact inferInstanceAs (Decidable False)
  · exact inferInstanceAs (Decidable False)
  · cases pool <;> simp only [RoutedPrivate] <;> infer_instance
  · exact inferInstanceAs (Decidable False)

instance (kind : RegistrationNativeKemBeaconFootprint.Kind) : DecidablePred (IsPrivate (n := n) (KemSK := KemSK) kind) := fun query => by
  rcases query with (message | (query | query)) | query <;> simp only [IsPrivate] <;> infer_instance

private theorem local_step (selected : Bool) (query : (LocalSpec n KemSK).Domain) :
    (liftLocal (n := n) selected query).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind)
      (if RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind query then 1 else 0) := by
  rcases query with message | (query | query)
  · simp [liftLocal, IsPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]
  · simp [liftLocal, IsPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]
  · rcases query with other | (pool | key)
    · simp [liftLocal, RegistrationNativeKemRouting.route, liftRoutedKem,
        IsPrivate, RoutedPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate,
        RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]
    · cases pool <;> cases kind <;>
        simp [liftLocal, RegistrationNativeKemRouting.route, liftRoutedKem,
          IsPrivate, RoutedPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate,
          RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]
    · cases selected <;>
        simp [liftLocal, RegistrationNativeKemRouting.route, liftRoutedKem,
          IsPrivate, RoutedPrivate, RegistrationNativeOpenKeyKemBeacon.IsPrivate,
          RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]

private theorem local_bound (selected : Bool) (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count) :
    (simulateQ (liftLocal (n := n) selected) work).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) count :=
  RawCtxSourceOpen.simulate_bound _ _ _ work count bounded (local_step selected)

private theorem trusted_bound (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value)
    (count : Nat) (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) kind) count) :
    (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query => simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect,
      RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemBeaconFootprint.counted,
      isQueryBoundP_query_iff]
  | inr query =>
      rcases query with other | (pool | key)
      · cases kind <;> simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
          RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemBeaconFootprint.counted,
          RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]
      · cases pool <;> cases kind <;> simp [RegistrationBeaconReferenceCompiler.trustedLift,
          RegistrationBeaconReferenceCompiler.indexed, RegistrationNativeOpenKeyKemBeacon.IsPrivate,
          RegistrationNativeKemBeaconFootprint.counted, RegistrationNativeKemCompilerFootprint.predicate,
          isQueryBoundP_query_iff]
      · simp [RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.indexed,
          RegistrationNativeOpenKeyKemBeacon.IsPrivate, RegistrationNativeKemBeaconFootprint.counted,
          RegistrationNativeKemCompilerFootprint.predicate, isQueryBoundP_query_iff]

private theorem owners_local_bound {source : RegistrationNativeMldsa.Source}
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) (count : Nat)
    (bounded : RegistrationNativeKemBeaconFootprint.Bounded kind count work)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePublicOwners.executeLocal selected publicPrekey work).run owners).run env).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count := by
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, isQueryBoundP_map_iff]
  exact trusted_bound _ count (bounded _ _)

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativePublicOwners.ordinary, RegistrationNativeOpenKeyKemBeacon.IsPrivate, ite_false]
      split <;> simp [RegistrationNativeOpenKeyKemBeacon.IsPrivate, isQueryBoundP_query_iff]
  | inr query =>
      simp only [RegistrationNativePublicOwners.ordinary, isQueryBoundP_query_iff]
      intro counted
      rw [ite_eq_left counted]
      exact Nat.zero_lt_one

private theorem owners_finish_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) 0 := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  split
  · trivial
  · rename_i owner found
    rw [isQueryBoundP_map_iff]
    cases owner.scalar with
    | none => exact RegistrationNativeOpenKeyKemBeacon.finish_free setup source packet owner.view env
    | some scalar =>
        exact ordinary_bound setup scalar _ 0
          (RegistrationNativeOpenKeyKemBeacon.finish_free setup source packet owner.view env)

private theorem server_bound {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) (count : Nat)
    (bounded : ∀ before env, ((work.run before).run env).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count) (before : State source) :
    ((serverOpen selected work).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) count := by
  simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact local_bound selected _ count (bounded before.server before.environment)

private theorem beacon_bound {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value) (count : Nat)
    (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) count) (before : State source) :
    ((beacon work).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) count := by
  simp only [beacon, StateT.run, isQueryBoundP_map_iff]
  exact local_bound false _ count (bounded before.beacons before.environment)

private theorem record_free {source : RegistrationNativeMldsa.Source}
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP (IsPrivate (KemSK := KemSK) kind) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [record, StateT.run]
  all_goals try split
  all_goals simp [IsPrivate, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

attribute [local irreducible] RegistrationAuthenticationCompiler.program

/-- Actual public typed commands create at most one private KEM key per create and never reveal a secret. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (IsPrivate (KemSK := KemSK) kind)
      (if kind = .create ∧ RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  cases query with
  | inl coin =>
      simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
        RegistrationNativePublicFrontend.effect, liftLocal, IsPrivate, isQueryBoundP_query_iff,
        RegistrationNativeRawAdapter.kind]
  | inr query => cases query with
    | create edPin mlPin keyId =>
        simpa [handler, RegistrationNativeRawAdapter.kind, RegistrationNativePublicOwners.create] using
          beacon_bound (kind := kind) _ (if kind = .create then 1 else 0)
            (fun owners env => owners_local_bound selectedOwner publicPrekey _ _
              (RegistrationNativeKemBeaconFootprint.create_bound setup kind edPin mlPin keyId) owners env) before
    | bundle owner =>
        simpa [handler, RegistrationNativeRawAdapter.kind, RegistrationNativePublicOwners.bundle] using
          beacon_bound (kind := kind) _ 0
            (fun owners env => owners_local_bound selectedOwner publicPrekey _ 0
              (RegistrationNativeKemBeaconFootprint.bundle_zero setup kind wire owner) owners env) before
    | accept packet =>
        simp [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind,
          RegistrationNativeRawAdapter.kind]
        exact server_bound (kind := kind) _ _ 0 (RegistrationNativeOpenKeyKemServer.accept_free setup checks source.verify packet) _
    | build handle application =>
        simpa [handler, RegistrationNativeRawAdapter.kind] using
          server_bound (kind := kind) false _ 0
            (RegistrationNativeOpenKeyKemServer.build_free setup.source wire checks sign handle application) before
    | finish owner packet =>
        simpa [handler, RegistrationNativeRawAdapter.kind] using
          beacon_bound (kind := kind) _ 0 (owners_finish_bound setup source owner packet) before
    | hmac key bytes => trivial
    | hash bytes =>
        simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
          RegistrationNativePublicFrontend.effect, liftLocal, IsPrivate, isQueryBoundP_query_iff,
          RegistrationNativeRawAdapter.kind]
    | serverSend keyId plaintext =>
        simpa [handler, RegistrationNativeRawAdapter.kind] using
          record_free (n := n) (KemSK := KemSK) (kind := kind) (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw =>
        simpa [handler, RegistrationNativeRawAdapter.kind] using
          record_free (n := n) (KemSK := KemSK) (kind := kind) (.inl (.inr raw)) before
    | beaconSend owner plaintext =>
        simpa [handler, RegistrationNativeRawAdapter.kind] using
          record_free (n := n) (KemSK := KemSK) (kind := kind) (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw =>
        simpa [handler, RegistrationNativeRawAdapter.kind] using
          record_free (n := n) (KemSK := KemSK) (kind := kind) (.inr (owner, .inr raw)) before

/-- Every adaptive typed public program retains its exact constructor/reveal allowance. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (count : Nat)
    (bounded : work.IsQueryBoundP (fun query => kind = .create ∧ RegistrationNativeRawAdapter.kind query = 1) count)
    (before : State source) :
    ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before).IsQueryBoundP
      (IsPrivate (n := n) (KemSK := KemSK) kind) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound (kind := kind) setup checks wire source sign selectedOwner selectedAccept publicPrekey query current
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound (kind := kind) setup checks wire source sign selectedOwner selectedAccept publicPrekey query current

/-- The full original native secrecy ledger creates at most the original public create budget and never reveals a private generated key. -/
theorem run_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State source) :
    (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before).IsQueryBoundP
      (IsPrivate (KemSK := KemSK) kind) (if kind = .create then budget.create else 0) := by
  apply program_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey
  cases kind with
  | create =>
      simpa only [true_and, ite_true] using RegistrationNativeKemFullFootprint.compile_creates setup.source.crypto wire serverKeyId bounds mode work budget bounded
  | reveal | other =>
      simpa only [reduceCtorEq, false_and, ite_false] using
        isQueryBoundP_false (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work) 0

end BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic.program_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemPublic.run_bound

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenPrepareCaps
import BeaconcryptCore.Computational.RegistrationBeaconPrepareCaps
import BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup
import BeaconcryptCore.Computational.RegistrationNativePreparationBudget

/-! Structural root preparation bills for the complete mixed native frontend preserve all native failure branches. Only accepts and finishes consume a root preparation allowance; the literal original secrecy wrapper remains above these commands. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsPrepare : (Spec n KemSK).Domain → Prop
  | .inl (.inl _) => True
  | _ => False
instance : DecidablePred (IsPrepare (n := n) (KemSK := KemSK)) := fun query => by
  rcases query with (_ | _) | _ <;> first | exact isTrue trivial | exact isFalse id

private theorem routed_free (work : OracleComp (RoutedKem KemSK) Value) :
    (simulateQ (liftRoutedKem (n := n)) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [liftRoutedKem, IsPrepare, isQueryBoundP_query_iff]

private theorem local_step (selected : Bool) (query : (LocalSpec n KemSK).Domain) :
    (liftLocal (n := n) selected query).IsQueryBoundP (IsPrepare (KemSK := KemSK))
      (if RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK) query then 1 else 0) := by
  rcases query with message | (message | query) | query
  · simp [liftLocal, IsPrepare, RegistrationBeaconPrepareCaps.IsPrepare, isQueryBoundP_query_iff]
  · simp [liftLocal, IsPrepare, RegistrationBeaconPrepareCaps.IsPrepare, isQueryBoundP_query_iff]
  · simp [liftLocal, IsPrepare, RegistrationBeaconPrepareCaps.IsPrepare, isQueryBoundP_query_iff]
  · exact routed_free _

private theorem local_bound (selected : Bool) (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) count) :
    (simulateQ (liftLocal (n := n) selected) work).IsQueryBoundP (IsPrepare (KemSK := KemSK)) count :=
  RawCtxSourceOpen.simulate_bound _ _ _ work count bounded (local_step selected)

private theorem trusted_free (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work).IsQueryBoundP
      (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationBeaconReferenceCompiler.trustedLift,
    RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
    RegistrationBeaconPrepareCaps.IsPrepare, isQueryBoundP_query_iff]

private theorem owners_local_free {source : RegistrationNativeMldsa.Source}
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePublicOwners.executeLocal selected publicPrekey work).run owners).run env).IsQueryBoundP
      (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, isQueryBoundP_map_iff]
  exact trusted_free _

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) count) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativePublicOwners.ordinary, RegistrationBeaconPrepareCaps.IsPrepare]
      split <;> simp [RegistrationBeaconPrepareCaps.IsPrepare, isQueryBoundP_query_iff]
  | inr query =>
      rcases query with (_ | _) | _ <;>
        simp [RegistrationNativePublicOwners.ordinary, RegistrationBeaconPrepareCaps.IsPrepare, isQueryBoundP_query_iff]

private theorem owners_finish_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env).IsQueryBoundP
      (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) 1 := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  split
  · trivial
  · rename_i owner found
    rw [isQueryBoundP_map_iff]
    cases owner.scalar with
    | none => exact RegistrationBeaconPrepareCaps.finish_bound setup source packet owner.view env
    | some scalar =>
        exact ordinary_bound setup scalar _ 1
          (RegistrationBeaconPrepareCaps.finish_bound setup source packet owner.view env)

private theorem server_bound {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) (count : Nat)
    (bounded : ∀ before env, ((work.run before).run env).IsQueryBoundP
      (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) count) (before : State source) :
    ((serverOpen selected work).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) count := by
  simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact local_bound selected _ count (bounded before.server before.environment)

private theorem beacon_bound {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value) (count : Nat)
    (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP
      (RegistrationBeaconPrepareCaps.IsPrepare (KemSK := KemSK)) count) (before : State source) :
    ((beacon work).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) count := by
  simp only [beacon, StateT.run, isQueryBoundP_map_iff]
  exact local_bound false _ count (bounded before.beacons before.environment)

private theorem record_free {source : RegistrationNativeMldsa.Source}
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP (IsPrepare (KemSK := KemSK)) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [record, StateT.run]
  all_goals try split
  all_goals simp [IsPrepare, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

def IsPreparing : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.accept _) | .inr (.finish _ _) => True
  | _ => False
instance : DecidablePred IsPreparing := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr query => cases query <;> first | exact isTrue trivial | exact isFalse id

attribute [local irreducible] RegistrationAuthenticationCompiler.program

/-- Only actual accept and finish commands can consume a root preparation, at most once per command. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) (if IsPreparing query then 1 else 0) := by
  cases query with
  | inl coin => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, effect, liftLocal, IsPrepare, IsPreparing, isQueryBoundP_query_iff]
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact beacon_bound _ 0
          (fun owners env => owners_local_free selectedOwner publicPrekey _ owners env) before
    | bundle owner =>
        exact beacon_bound _ 0
          (fun owners env => owners_local_free selectedOwner publicPrekey _ owners env) before
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind, IsPreparing, ite_true]
        exact server_bound _ _ 1 (RegistrationServerOpenPrepareCaps.accept_bound setup checks source.verify packet) _
    | build handle application =>
        exact server_bound false _ 0
          (RegistrationServerOpenPrepareCaps.build_free setup.source wire checks sign handle application) before
    | finish owner packet =>
        exact beacon_bound _ 1
          (owners_finish_bound setup source owner packet) before
    | hmac key bytes => trivial
    | hash bytes => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, effect, liftLocal, IsPrepare, IsPreparing, isQueryBoundP_query_iff]
    | serverSend keyId plaintext =>
        simpa only [handler, IsPreparing, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw =>
        simpa only [handler, IsPreparing, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inl (.inr raw)) before
    | beaconSend owner plaintext =>
        simpa only [handler, IsPreparing, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw =>
        simpa only [handler, IsPreparing, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inr (owner, .inr raw)) before

/-- The complete adaptive frontend preserves its native preparation-command cap, including all failed operations. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (count : Nat)
    (bounded : work.IsQueryBoundP IsPreparing count) (before : State source) :
    ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey query current
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey query current

/-- The complete original raw CE wrapper needs at most qAccept+qFinish root preparations; hidden tests and fresh bytes add none. -/
theorem run_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : State source) :
    (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before).IsQueryBoundP
      (IsPrepare (KemSK := KemSK)) (budget.cap 3 + budget.cap 5) := by
  apply program_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey _ _ _ before
  have bill := RegistrationNativePreparationBudget.compile_bound setup.source.crypto wire serverKeyId bounds mode work budget bounded
  rw [RegistrationNativePreparationBudget.allowance_eq] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  cases query with
  | inl coin => exact counted.elim
  | inr query => cases query <;>
      simp_all [IsPreparing, RegistrationNativePreparationBudget.IsPreparing, RegistrationNativeRawAdapter.kind]


end BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicPrepareCaps.run_bound

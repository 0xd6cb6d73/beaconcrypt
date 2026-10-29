-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceCaps
import BeaconcryptCore.Computational.RegistrationNativePublicRetainedStartup
import BeaconcryptCore.Computational.RegistrationNativeMaterialBudget

/-! Structural material bills for the complete mixed native frontend preserve all native failure branches. Only builds and finishes consume a material allowance; the literal original secrecy wrapper remains above these commands. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsDemand : (Spec n KemSK).Domain → Prop
  | .inl (.inr (.inl (.inl _))) => True
  | _ => False
instance : DecidablePred (IsDemand (n := n) (KemSK := KemSK)) := fun query => by
  rcases query with (_ | (_ | _) | _) | _ <;> first | exact isTrue trivial | exact isFalse id

private theorem routed_free (work : OracleComp (RoutedKem KemSK) Value) :
    (simulateQ (liftRoutedKem (n := n)) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [liftRoutedKem, IsDemand, isQueryBoundP_query_iff]

private theorem local_step (selected : Bool) (query : (LocalSpec n KemSK).Domain) :
    (liftLocal (n := n) selected query).IsQueryBoundP (IsDemand (KemSK := KemSK))
      (if RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK) query then 1 else 0) := by
  rcases query with message | (message | query) | query
  · simp [liftLocal, IsDemand, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  · simp [liftLocal, IsDemand, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  · simp [liftLocal, IsDemand, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  · exact routed_free _

private theorem local_bound (selected : Bool) (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count) :
    (simulateQ (liftLocal (n := n) selected) work).IsQueryBoundP (IsDemand (KemSK := KemSK)) count :=
  RawCtxSourceOpen.simulate_bound _ _ _ work count bounded (local_step selected)

private theorem trusted_free (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) Value) :
    (simulateQ RegistrationBeaconReferenceCompiler.trustedLift work).IsQueryBoundP
      (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationBeaconReferenceCompiler.trustedLift,
    RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
    RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]

private theorem owners_local_free {source : RegistrationNativeMldsa.Source}
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePublicOwners.executeLocal selected publicPrekey work).run owners).run env).IsQueryBoundP
      (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePublicOwners.executeLocal, StateT.run, isQueryBoundP_map_iff]
  exact trusted_free _

private theorem ordinary_bound (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count) :
    (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work).IsQueryBoundP
      (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativePublicOwners.ordinary, RegistrationBeaconReferenceCaps.IsDemand, ite_false]
      split <;> simp [RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]
  | inr query =>
      rcases query with (_ | _) | _ <;>
        simp [RegistrationNativePublicOwners.ordinary, RegistrationBeaconReferenceCaps.IsDemand, isQueryBoundP_query_iff]

private theorem owners_finish_bound (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (owners : RegistrationNativePublicOwners.State source) (env : RegistrationServerReferenceCompiler.Environment) :
    (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run env).IsQueryBoundP
      (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) 1 := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  split
  · trivial
  · rename_i owner found
    rw [isQueryBoundP_map_iff]
    cases owner.scalar with
    | none => exact RegistrationBeaconReferenceCaps.finish_bound setup source packet owner.view env
    | some scalar =>
        exact ordinary_bound setup scalar _ 1
          (RegistrationBeaconReferenceCaps.finish_bound setup source packet owner.view env)

private theorem server_bound {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) (count : Nat)
    (bounded : ∀ before env, ((work.run before).run env).IsQueryBoundP
      (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count) (before : State source) :
    ((serverOpen selected work).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) count := by
  simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact local_bound selected _ count (bounded before.server before.environment)

private theorem beacon_bound {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value) (count : Nat)
    (bounded : ∀ owners env, ((work.run owners).run env).IsQueryBoundP
      (RegistrationBeaconReferenceCaps.IsDemand (KemSK := KemSK)) count) (before : State source) :
    ((beacon work).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) count := by
  simp only [beacon, StateT.run, isQueryBoundP_map_iff]
  exact local_bound false _ count (bounded before.beacons before.environment)

private theorem record_free {source : RegistrationNativeMldsa.Source}
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source) :
    ((record (n := n) (KemSK := KemSK) query).run before).IsQueryBoundP (IsDemand (KemSK := KemSK)) 0 := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [record, StateT.run]
  all_goals try split
  all_goals simp [IsDemand, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

def IsMaterial : RegistrationNativeRawAdapter.TypedSpec.Domain → Prop
  | .inr (.build _ _) | .inr (.finish _ _) => True
  | _ => False
instance : DecidablePred IsMaterial := fun query => by
  cases query with
  | inl _ => exact isFalse id
  | inr query => cases query <;> first | exact isTrue trivial | exact isFalse id

attribute [local irreducible] RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Only actual build and finish commands can consume a material demand, at most once per command. -/
theorem handler_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) (if IsMaterial query then 1 else 0) := by
  cases query with
  | inl coin => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, effect, liftLocal, IsDemand, IsMaterial, isQueryBoundP_query_iff]
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact beacon_bound _ 0
          (fun owners env => owners_local_free selectedOwner publicPrekey _ owners env) before
    | bundle owner =>
        exact beacon_bound _ 0
          (fun owners env => owners_local_free selectedOwner publicPrekey _ owners env) before
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind, IsMaterial, ite_false]
        exact server_bound _ _ 0 (RegistrationServerOpenReferenceCaps.accept_free setup checks source.verify packet) _
    | build handle application =>
        exact server_bound false _ 1
          (RegistrationServerOpenReferenceCaps.build_bound setup.source wire checks sign handle application) before
    | finish owner packet =>
        exact beacon_bound _ 1
          (owners_finish_bound setup source owner packet) before
    | hmac key bytes => trivial
    | hash bytes => simp [handler, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, effect, liftLocal, IsDemand, IsMaterial, isQueryBoundP_query_iff]
    | serverSend keyId plaintext =>
        simpa only [handler, IsMaterial, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw =>
        simpa only [handler, IsMaterial, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inl (.inr raw)) before
    | beaconSend owner plaintext =>
        simpa only [handler, IsMaterial, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inr (owner, .inl plaintext)) before
    | beaconRaw owner raw =>
        simpa only [handler, IsMaterial, ite_false] using
          record_free (n := n) (KemSK := KemSK) (.inr (owner, .inr raw)) before

/-- The complete adaptive frontend preserves its native material-command cap, including all failed operations. -/
theorem program_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (count : Nat)
    (bounded : work.IsQueryBoundP IsMaterial count) (before : State source) :
    ((simulateQ (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) count := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey query current
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey query current

/-- The complete original raw CE wrapper needs at most qBuild+qFinish material demands; hidden tests and fresh bytes add none. -/
theorem run_bound (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (before : State source) :
    (run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work before).IsQueryBoundP
      (IsDemand (KemSK := KemSK)) (budget.cap 4 + budget.cap 5) := by
  apply program_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey _ _ _ before
  have bill := RegistrationNativeMaterialBudget.compile_bound setup.source.crypto wire serverKeyId bounds mode work budget bounded
  rw [RegistrationNativeMaterialBudget.allowance_eq] at bill
  apply OracleComp.IsQueryBoundP.of_imp _ bill
  intro query counted
  cases query with
  | inl coin => exact counted.elim
  | inr query => cases query <;>
      simp_all [IsMaterial, RegistrationNativeMaterialBudget.IsMaterial, RegistrationNativeRawAdapter.kind]

private theorem retained_ordinary_free (hmac : PqxdhSecretInputKdf.HmacSha512)
    (work : RegistrationNativePublicInterpreter.M n KemSK Value) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    ((RegistrationNativePublicRetained.ordinary hmac work).run before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand 0 := by
  unfold RegistrationNativePublicRetained.ordinary
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [RegistrationNativePublicRetained.coins, RegistrationNativeRetainedService.IsDemand, isQueryBoundP_query_iff]

private theorem retained_step (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (Spec n KemSK).Domain) (before : RegistrationNativePublicInterpreter.State n KemSK) :
    ((RegistrationNativePublicRetained.compiler setup wire route sign query).run before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand (if IsDemand (KemSK := KemSK) query then 1 else 0) := by
  rcases query with (message | (message | query) | query) | query
  · simp [RegistrationNativePublicRetained.compiler, StateT.run_lift, bind_pure_comp,
      isQueryBoundP_map_iff, RegistrationNativeRetainedService.IsDemand, IsDemand, isQueryBoundP_query_iff]
  · simp [RegistrationNativePublicRetained.compiler, StateT.run_lift, bind_pure_comp,
      isQueryBoundP_map_iff, RegistrationNativeRetainedService.IsDemand, IsDemand, isQueryBoundP_query_iff]
  · exact retained_ordinary_free _ _ before
  · exact retained_ordinary_free _ _ before
  · exact retained_ordinary_free _ _ before

/-- Relocating root bookkeeping preserves the actual complete mixed frontend's material bill. -/
theorem retained_bound (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (Spec n KemSK) Value) (before : RegistrationNativePublicInterpreter.State n KemSK)
    (count : Nat) (bounded : work.IsQueryBoundP (IsDemand (KemSK := KemSK)) count) :
    (RegistrationNativePublicRetained.client setup wire route sign work before).IsQueryBoundP
      RegistrationNativeRetainedService.IsDemand count := by
  unfold RegistrationNativePublicRetained.client
  rw [StateT.run'_eq, isQueryBoundP_map_iff]
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using retained_step setup wire route sign query current
  · intro query free current
    simpa only [ite_eq_right free] using retained_step setup wire route sign query current

end BeaconcryptCore.Computational.RegistrationNativePublicCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicCaps.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicCaps.handler_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicCaps.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicCaps.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicCaps.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicCaps.run_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicCaps.retained_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicCaps.retained_bound

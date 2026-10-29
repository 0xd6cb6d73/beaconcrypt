-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentHandler
import BeaconcryptCore.Computational.RegistrationNativeEntropyInterface

/-! Native registration environment callbacks contain no ongoing record query. This follows from the literal local frontend embedding, independently of the private KEM provider or any World state. Record commands remain outside the restricted environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps
open PqxdhServerAuthExperiment (Setup Checks)
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def IsRecord : (RegistrationNativePublicFrontend.Spec n Unit).Domain → Prop
  | .inr _ => True
  | _ => False

instance : DecidablePred (IsRecord (n := n)) := fun query => by
  cases query <;> simp only [IsRecord] <;> infer_instance

/-- The actual routed local embedding only emits local callbacks, including every routed KEM branch. -/
theorem local_zero (selected : Bool) (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) :
    (simulateQ (RegistrationNativePublicFrontend.liftLocal (n := n) (KemSK := KemSK) selected) work).IsQueryBoundP IsRecord 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _unselected
  rcases query with message | (query | query)
  · simp only [RegistrationNativePublicFrontend.liftLocal, isQueryBoundP_query_iff, IsRecord]
    intro impossible
    exact impossible.elim
  · simp only [RegistrationNativePublicFrontend.liftLocal, isQueryBoundP_query_iff, IsRecord]
    intro impossible
    exact impossible.elim
  · dsimp only [RegistrationNativePublicFrontend.liftLocal]
    apply (isQueryBoundP_false (RegistrationNativeKemRouting.route selected query) 0).simulateQ_of_step
      (fun _ impossible => impossible.elim)
    intro routed _
    simp only [RegistrationNativePublicFrontend.liftRoutedKem, isQueryBoundP_query_iff, IsRecord]
    intro impossible
    exact impossible.elim

/-- Every complete local Beacon lifecycle computation remains in the restricted effect interface. -/
theorem beacon_zero {source : RegistrationNativeMldsa.Source}
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : RegistrationNativePublicFrontend.State source) :
    ((RegistrationNativePublicFrontend.beacon (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP IsRecord 0 := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, isQueryBoundP_map_iff]
  exact local_zero false _

/-- Every complete local Server computation remains in the restricted effect interface. -/
theorem server_zero {source : RegistrationNativeMldsa.Source} (selected : Bool)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : RegistrationNativePublicFrontend.State source) :
    ((RegistrationNativePublicFrontend.serverOpen (n := n) (KemSK := KemSK) selected work).run before).IsQueryBoundP IsRecord 0 := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, isQueryBoundP_map_iff]
  exact local_zero selected _

def IsEnvironment : RegistrationNativeRawAdapter.Command → Prop
  | .create _ _ _ | .bundle _ | .accept _ | .build _ _ | .finish _ _ | .hmac _ _ => True
  | _ => False

/-- The actual typed registration and public HMAC callbacks emit no ongoing record request. -/
theorem typed_zero (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (command : RegistrationNativeRawAdapter.Command)
    (environment : IsEnvironment command)
    (before : RegistrationNativePublicFrontend.State source) :
    ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      (.inr command)).run before).IsQueryBoundP IsRecord 0 := by
  cases command with
  | create edPin mlPin keyId => exact beacon_zero _ before
  | bundle owner => exact beacon_zero _ before
  | finish owner packet => exact beacon_zero _ before
  | build handle application => exact server_zero false _ before
  | hmac key bytes => exact isQueryBoundP_pure IsRecord _ 0
  | accept packet =>
      simp only [RegistrationNativePublicFrontend.handler, StateT.run_bind, StateT.run_get,
        StateT.run_modify, pure_bind]
      exact server_zero (decide (before.parsedAccepts = selectedAccept))
        (RegistrationServerOpenReferenceCompiler.accept setup checks source.verify packet)
        { before with parsedAccepts := before.parsedAccepts + 1 }
  | hash bytes | serverSend keyId bytes | serverRaw raw | beaconSend owner bytes | beaconRaw owner raw =>
      exact environment.elim

end BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.local_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.local_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.beacon_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.beacon_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.server_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.server_zero
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.typed_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenEnvironmentCaps.typed_zero

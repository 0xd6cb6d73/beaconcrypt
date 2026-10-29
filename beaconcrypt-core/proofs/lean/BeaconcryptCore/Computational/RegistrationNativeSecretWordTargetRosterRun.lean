-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRoster
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetLedger

/-! The concrete combined Word interpreter retains every earlier owner handle/PQ pair through arbitrary outer key replies and the original complete native ledger. Public/private sampling and refused sends remain below their original ledger wrapper; this invariant concerns the actual reached roster rather than a substituted real SDK execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetRoster (Prefix)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
  (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
local notation "typed" => RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
  setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey

private theorem reflexive (owners : RegistrationNativePublicOwners.State source) : Prefix owners owners :=
  ⟨[], (List.append_nil _).symm⟩

private theorem transitive (first middle last : RegistrationNativePublicOwners.State source)
    (earlier : Prefix first middle) (later : Prefix middle last) : Prefix first last := by
  obtain ⟨left, old⟩ := earlier
  obtain ⟨right, current⟩ := later
  exact ⟨left ++ right, by rw [current, old, List.append_assoc]⟩

/-- One actual combined typed callback preserves all earlier retained owner KEM metadata. -/
theorem typed_prefix (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed query).run before)) : Prefix before.1.beacons result.2.1.beacons := by
  rw [RegistrationNativeSecretWordTargetSource.typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have original : reached.1 ∈ support
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
        selectedOwner selectedAccept publicPrekey query).run before.1) := by
    apply OracleComp.support_simulateQ_run'_subset
      (RegistrationNativeSecretWordTargetSource.implementation setup wire route sign input inside provider outer) _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  cases equal
  exact RegistrationNativeSecretWordTargetRoster.typed_prefix setup checks wire sign
    selectedOwner selectedAccept publicPrekey query before.1 reached.1 original

/-- Every adaptive typed program retains the same ordered metadata through the concrete combined source. -/
theorem program_prefix (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ typed work).run before)) : Prefix before.1.beacons result.2.1.beacons :=
  OracleComp.simulateQ_run_preserves_inv_of_query typed (fun current => Prefix before.1.beacons current.1.beacons)
    (fun query current prior next called => transitive _ _ _ prior
      (typed_prefix setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
        query current next called)) work before (reflexive before.1.beacons) result supported

/-- The bounded raw native adapter retains the ordered metadata on all malformed and failed paths. -/
theorem raw_program_prefix (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (supported : result ∈ support ((simulateQ (RegistrationNativeRawAdapter.handler wire typed) work).run before)) :
    Prefix before.1.beacons result.2.1.beacons := by
  rw [RegistrationNativeRawAdapter.program_native] at supported
  exact program_prefix setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
    _ before result supported

/-- Complete original secrecy draws and internal native sends preserve earlier owner metadata under the unchanged ledger ordering. -/
theorem full_step_prefix (bounds : PqxdhDeploymentInterface.FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
      typed query).run before)) : Prefix before.2.1.beacons result.2.2.1.beacons := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨inner, called, rfl⟩ := supported
  exact raw_program_prefix setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey
    _ before.2 inner called

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.typed_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.typed_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.program_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.raw_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.raw_program_prefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.full_step_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterRun.full_step_prefix

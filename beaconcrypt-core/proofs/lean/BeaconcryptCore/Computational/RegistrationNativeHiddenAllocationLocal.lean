-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLifecycle
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend

/-! Actual ordinary native commands retain the entire local Beacon roster. Outgoing publication and incoming finish retain its length and physical addresses through their verified finite controllers, independently of every root, KEM or World reply. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLocal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeHiddenAllocationOwners (Indexed)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build

private theorem bind_apply {A B : Type}
    (work : RegistrationNativePublicFrontend.M n KemSK source A)
    (next : A → RegistrationNativePublicFrontend.M n KemSK source B)
    (before : RegistrationNativePublicFrontend.State source) :
    (work >>= next) before = (work before >>= fun result => next result.1 result.2) := rfl

private theorem get_apply (before : RegistrationNativePublicFrontend.State source) :
    (get : RegistrationNativePublicFrontend.M n KemSK source (RegistrationNativePublicFrontend.State source)) before =
      pure (before, before) := rfl

private theorem modify_apply (change : RegistrationNativePublicFrontend.State source → RegistrationNativePublicFrontend.State source)
    (before : RegistrationNativePublicFrontend.State source) :
    (modify change : RegistrationNativePublicFrontend.M n KemSK source Unit) before = pure ((), change before) := rfl

def Ordinary : TypedSpec.Domain → Prop
  | .inr (.create _ _ _) | .inr (.bundle _) | .inr (.finish _ _) => False
  | _ => True

/-- Every actual typed command outside Beacon lifecycle updates retains the complete local owner roster. -/
theorem ordinary (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : TypedSpec.Domain) (before : RegistrationNativePublicFrontend.State source)
    (result : TypedSpec.Range query × RegistrationNativePublicFrontend.State source) (quiet : Ordinary query)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before)) : result.2.beacons = before.beacons := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _reached, rfl⟩ := supported
      rfl
  | inr query => cases query with
    | create edPin mlPin keyId | bundle index | finish index packet => exact quiet.elim
    | accept packet =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run, bind_apply, get_apply, pure_bind,
          modify_apply, RegistrationNativePublicFrontend.serverOpen, support_map] at supported
        obtain ⟨reply, _reached, rfl⟩ := supported
        rfl
    | build handle application =>
        simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.serverOpen,
          StateT.run, support_map] at supported
        obtain ⟨reply, _reached, rfl⟩ := supported
        rfl
    | hmac key bytes =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | hash bytes =>
        simp only [RegistrationNativePublicFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨reply, _reached, rfl⟩ := supported
        rfl
    | serverSend keyId plaintext | serverRaw raw =>
        simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.record, StateT.run, support_map] at supported
        obtain ⟨reply, _reached, rfl⟩ := supported
        rfl
    | beaconSend index plaintext | beaconRaw index raw =>
        simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.record, StateT.run] at supported
        split at supported
        · rw [mem_support_pure_iff] at supported
          cases supported
          rfl
        · rw [support_map] at supported
          obtain ⟨reply, _reached, rfl⟩ := supported
          rfl

/-- Source output receipts of an actual local Beacon program lift through the literal public frontend wrapper. -/
theorem beacon (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : RegistrationNativePublicFrontend.State source) (result : Value × RegistrationNativePublicFrontend.State source)
    (valid : Indexed before.beacons)
    (localReceipt : ∀ owners env output, Indexed owners → output ∈ support ((work.run owners).run env) →
      output.1.2.length = owners.length ∧ Indexed output.1.2)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.beacon work).run before)) :
    result.2.beacons.length = before.beacons.length ∧ Indexed result.2.beacons := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨inner, reached, returned⟩ := supported
  have actual := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  have receipt := localReceipt before.beacons before.environment inner valid actual
  cases returned
  exact receipt

end BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLocal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLocal.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLocal.ordinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLocal.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationLocal.beacon

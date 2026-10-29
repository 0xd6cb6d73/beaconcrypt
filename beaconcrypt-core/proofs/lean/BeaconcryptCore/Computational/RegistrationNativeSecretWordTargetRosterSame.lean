-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape

/-! Every actual symbolic controller preserves the ordered KEM metadata of all earlier owners. Creation only extends that metadata after its actual complete constructor, and bundle/finish retain it through arbitrary material and authentication failures. No owner/private-pool index equality is included in this structural property. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterSame
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordTargetPublication (key pack_keys restore_keys)
open RegistrationNativeSecretWordMessage (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem reflexive (owners : RegistrationNativePublicOwners.State source) : owners.map key = owners.map key := rfl

private theorem server_prefix (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.serverOpen selected work).run before)) :
    result.2.beacons.map key = before.beacons.map key := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact reflexive _

private theorem beacon_prefix
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (keeps : ∀ owners env result, result ∈ support ((work.run owners).run env) → result.1.2.map key = owners.map key)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.beacon work).run before)) :
    result.2.beacons.map key = before.beacons.map key := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  cases equal
  exact keeps before.beacons before.environment inner original

private theorem record_prefix (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    result.2.beacons.map key = before.beacons.map key := by
  rcases query with server | ⟨owner, query⟩
  · simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact reflexive _
  · cases query <;> cases found : before.beacons[owner]? with
    | none =>
        simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
        cases supported
        exact reflexive _
    | some selected =>
        simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, found, support_map] at supported
        obtain ⟨reply, _, rfl⟩ := supported
        exact reflexive _

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build
  RegistrationNativeSecretWordOwners.create RegistrationNativeSecretWordOwners.bundle RegistrationNativeSecretWordOwners.finish
  RegistrationNativeSecretWordFrontend.serverOpen RegistrationNativeSecretWordFrontend.beacon RegistrationNativeSecretWordFrontend.record

private theorem accept_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : registration.InitPacket) (before : State source) :
    (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey (.inr (.accept packet))).run before =
      (RegistrationNativeSecretWordFrontend.serverOpen (decide (before.parsedAccepts = selectedAccept))
        (RegistrationNativeSecretWordServerCompiler.accept setup checks source.verify packet)).run
          { before with parsedAccepts := before.parsedAccepts + 1 } := by
  simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind,
    StateT.run_get, StateT.run_modify, pure_bind]

/-- Every actual symbolic typed command preserves all earlier retained owner KEM metadata. -/
theorem typed_same (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (quiet : RegistrationNativeRawAdapter.kind query ≠ 1)
    (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before)) : result.2.beacons.map key = before.beacons.map key := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact reflexive _
  | inr command => cases command with
    | create edPin mlPin keyId =>
        exact (quiet rfl).elim
    | bundle owner =>
        apply beacon_prefix _ _ before result supported
        intro owners env reached called
        exact RegistrationNativeSecretWordTargetPublication.bundle_keys setup wire selectedOwner owner publicPrekey owners env reached called
    | finish owner packet =>
        apply beacon_prefix _ _ before result supported
        intro owners env reached called
        exact RegistrationNativeSecretWordTargetFinish.finish_keys setup owner packet owners env reached called
    | accept packet =>
        rw [accept_run] at supported
        exact server_prefix _ _ { before with parsedAccepts := before.parsedAccepts + 1 } result supported
    | build handle application => exact server_prefix _ _ before result supported
    | hmac key bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact reflexive _
    | hash bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨reply, _, rfl⟩ := supported
        exact reflexive _
    | serverSend keyId plaintext => exact record_prefix (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record_prefix (.inl (.inr raw)) before result supported
    | beaconSend owner plaintext => exact record_prefix (.inr (owner, .inl plaintext)) before result supported
    | beaconRaw owner raw => exact record_prefix (.inr (owner, .inr raw)) before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterSame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterSame.typed_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetRosterSame.typed_same

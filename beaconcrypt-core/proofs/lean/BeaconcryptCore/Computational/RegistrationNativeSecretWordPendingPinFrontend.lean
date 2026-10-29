-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape

/-! The actual Word frontend preserves the strong stored-owner pending-pin invariant through native creation, bundle publication, terminal finish and all other actual commands. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFrontend
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordPendingPin (Holds)
open RegistrationNativeSecretWordMessage (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem server_prefix (selected : Bool)
    (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source) (prior : Holds before.beacons)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.serverOpen selected work).run before)) :
    Holds result.2.beacons := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact prior

private theorem beacon_prefix
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (keeps : ∀ owners env result, Holds owners → result ∈ support ((work.run owners).run env) → Holds result.1.2)
    (before : State source) (result : Value × State source) (prior : Holds before.beacons)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.beacon work).run before)) :
    Holds result.2.beacons := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  cases equal
  exact keeps before.beacons before.environment inner prior original

private theorem record_prefix (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source) (prior : Holds before.beacons)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    Holds result.2.beacons := by
  rcases query with server | ⟨owner, query⟩
  · simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact prior
  · cases query <;> cases found : before.beacons[owner]? with
    | none =>
        simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
        cases supported
        exact prior
    | some selected =>
        simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, found, support_map] at supported
        obtain ⟨reply, _, rfl⟩ := supported
        exact prior

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

/-- Every actual symbolic typed command preserves the strong pending-pin invariant. -/
theorem typed_keeps (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (prior : Holds before.beacons)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before)) : Holds result.2.beacons := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact prior
  | inr command => cases command with
    | create edPin mlPin keyId =>
        apply beacon_prefix _ _ before result prior supported
        intro owners env reached prior called
        exact RegistrationNativeSecretWordPendingPinSource.create_keeps setup selectedOwner publicPrekey edPin mlPin keyId owners env reached prior called
    | bundle owner =>
        apply beacon_prefix _ _ before result prior supported
        intro owners env reached prior called
        exact RegistrationNativeSecretWordPendingPinSource.bundle_keeps setup wire selectedOwner owner publicPrekey owners env reached prior called
    | finish owner packet =>
        apply beacon_prefix _ _ before result prior supported
        intro owners env reached prior called
        exact RegistrationNativeSecretWordPendingPinFinish.finish_keeps setup owner packet owners env reached prior called
    | accept packet =>
        rw [accept_run] at supported
        exact server_prefix _ _ { before with parsedAccepts := before.parsedAccepts + 1 } result prior supported
    | build handle application => exact server_prefix _ _ before result prior supported
    | hmac key bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact prior
    | hash bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨reply, _, rfl⟩ := supported
        exact prior
    | serverSend keyId plaintext => exact record_prefix (.inl (.inl (plaintext, keyId))) before result prior supported
    | serverRaw raw => exact record_prefix (.inl (.inr raw)) before result prior supported
    | beaconSend owner plaintext => exact record_prefix (.inr (owner, .inl plaintext)) before result prior supported
    | beaconRaw owner raw => exact record_prefix (.inr (owner, .inr raw)) before result prior supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFrontend
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFrontend.typed_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordPendingPinFrontend.typed_keeps

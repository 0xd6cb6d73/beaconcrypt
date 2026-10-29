-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordServerPin
import BeaconcryptCore.Computational.RegistrationNativeSecretWordMaterialPin
import BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource

/-! Every actual Word frontend callback preserves the original Server authentication pin before arbitrary combined private interpretation, including every native rejection path. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendPin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem server (selected : Bool) (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source)
    (keeps : ∀ reached, reached ∈ support ((work.run before.server).run before.environment) →
      reached.1.2.pin = before.server.pin)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.serverOpen selected work).run before)) :
    result.2.server.pin = before.server.pin := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  exact keeps reached (RegistrationNativeResponsePaired.simulation_support
    (RegistrationNativeSecretWordInterface.liftLocal selected) _ _ called)

private theorem beacon
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.beacon work).run before)) :
    result.2.server.pin = before.server.pin := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨reached, _called, returned⟩ := supported
  cases returned
  rfl

private theorem record (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source)
    (supported : result ∈ support
      ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    result.2.server.pin = before.server.pin := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativeSecretWordFrontend.record, StateT.run] at supported
  all_goals try split at supported
  all_goals first
    | (rw [mem_support_pure_iff] at supported; cases supported; rfl)
    | (rw [support_map] at supported; obtain ⟨reached, _called, returned⟩ := supported;
        cases returned; rfl)

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Every actual native frontend callback keeps the original Server authentication pin. -/
theorem query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before)) :
    result.2.server.pin = before.server.pin := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reached, _called, returned⟩ := supported
      cases returned
      rfl
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon _ before result supported
    | bundle owner => exact beacon _ before result supported
    | finish owner packet => exact beacon _ before result supported
    | accept packet =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind, StateT.run_get,
          StateT.run_modify, pure_bind] at supported
        apply server _ _ { before with parsedAccepts := before.parsedAccepts + 1 } result _ supported
        intro reached called
        exact RegistrationNativeSecretWordServerPin.accept setup checks source.verify packet
          before.server before.environment reached called
    | build handle application =>
        apply server false _ before result _ supported
        intro reached called
        simp only [RegistrationNativeSecretWordServerCompiler.build, StateT.run] at called
        have material : reached.1 ∈ support
            ((RegistrationNativeSecretWordServerMaterial.build (n := n) wire checks.reservePeer handle application).run before.server) := by
          apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeSecretWordServerCompiler.service setup.source wire sign)
            _ before.environment
          rw [StateT.run'_eq, support_map]
          exact Set.mem_image_of_mem Prod.fst called
        have same := RegistrationNativeSecretWordMaterialPin.build_pin wire checks.reservePeer handle application
          before.server reached.1 material
        exact same.trans (RegistrationNativeSecretWordMaterialPin.take_pin handle before.server)
    | hmac key bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        rfl
    | hash bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨reached, _called, returned⟩ := supported
        cases returned
        rfl
    | serverSend keyId plaintext => exact record (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record (.inl (.inr raw)) before result supported
    | beaconSend owner plaintext => exact record (.inr (owner, .inl plaintext)) before result supported
    | beaconRaw owner raw => exact record (.inr (owner, .inr raw)) before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendPin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendPin.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendPin.query

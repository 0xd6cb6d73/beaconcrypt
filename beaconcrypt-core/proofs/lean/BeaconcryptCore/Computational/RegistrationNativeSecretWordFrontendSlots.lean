-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordSessionSlots
import BeaconcryptCore.Computational.RegistrationNativeSecretWordResponseSource

/-! Every actual Word frontend callback preserves the identity of each surviving older Server session slot. This statement applies before the arbitrary combined private interpretation and includes all native rejection paths. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendSlots
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordSessionSlots (Preserves)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem server (selected : Bool) (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source)
    (keeps : ∀ reached, reached ∈ support ((work.run before.server).run before.environment) →
      Preserves before.server.sessions reached.1.2.sessions)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.serverOpen selected work).run before)) :
    Preserves before.server.sessions result.2.server.sessions := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨reached, called, returned⟩ := supported
  cases returned
  exact keeps reached (RegistrationNativeResponsePaired.simulation_support
    (RegistrationNativeSecretWordInterface.liftLocal selected) _ _ called)

private theorem beacon
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (before : State source) (result : Value × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.beacon work).run before)) :
    Preserves before.server.sessions result.2.server.sessions := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨reached, _called, returned⟩ := supported
  cases returned
  exact RegistrationNativeSecretWordSessionSlots.refl _

private theorem record (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : State source) (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source)
    (supported : result ∈ support
      ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    Preserves before.server.sessions result.2.server.sessions := by
  rcases query with (_ | _) | ⟨owner, _ | _⟩
  all_goals simp only [RegistrationNativeSecretWordFrontend.record, StateT.run] at supported
  all_goals try split at supported
  all_goals first
    | (rw [mem_support_pure_iff] at supported; cases supported; exact RegistrationNativeSecretWordSessionSlots.refl _)
    | (rw [support_map] at supported; obtain ⟨reached, _called, returned⟩ := supported;
        cases returned; exact RegistrationNativeSecretWordSessionSlots.refl _)

attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build

/-- Native acceptance only appends, native build only consumes, and every other callback keeps Server slots. -/
theorem query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign
      selectedOwner selectedAccept publicPrekey query).run before)) :
    Preserves before.server.sessions result.2.server.sessions := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
      obtain ⟨reached, _called, returned⟩ := supported
      cases returned
      exact RegistrationNativeSecretWordSessionSlots.refl _
  | inr query => cases query with
    | create edPin mlPin keyId => exact beacon _ before result supported
    | bundle owner => exact beacon _ before result supported
    | finish owner packet => exact beacon _ before result supported
    | accept packet =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_bind, StateT.run_get,
          StateT.run_modify, pure_bind] at supported
        apply server _ _ { before with parsedAccepts := before.parsedAccepts + 1 } result _ supported
        intro reached called
        exact RegistrationNativeSecretWordSessionSlots.shape _ _ _
          (RegistrationNativeSecretWordAtomSessionShape.accept setup checks source.verify packet
            before.server before.environment reached called)
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
        have same := RegistrationNativeSecretWordMaterialSessions.build_sessions wire checks.reservePeer handle application
          before.server reached.1 material
        rw [same]
        exact RegistrationNativeSecretWordSessionSlots.take handle before.server
    | hmac key bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact RegistrationNativeSecretWordSessionSlots.refl _
    | hash bytes =>
        simp only [RegistrationNativeSecretWordFrontend.handler, StateT.run_lift, bind_pure_comp, support_map] at supported
        obtain ⟨reached, _called, returned⟩ := supported
        cases returned
        exact RegistrationNativeSecretWordSessionSlots.refl _
    | serverSend keyId plaintext => exact record (.inl (.inl (plaintext, keyId))) before result supported
    | serverRaw raw => exact record (.inl (.inr raw)) before result supported
    | beaconSend owner plaintext => exact record (.inr (owner, .inl plaintext)) before result supported
    | beaconRaw owner raw => exact record (.inr (owner, .inr raw)) before result supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendSlots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendSlots.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendSlots.query

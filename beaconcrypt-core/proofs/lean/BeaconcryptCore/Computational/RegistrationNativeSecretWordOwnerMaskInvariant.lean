-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerCanonical
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource

/-! The complete typed mixed frontend retains its canonical selected-owner mask under every query. The invariant follows the actual open controllers and therefore also holds after their private source interpretation, independently of any winning event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant
open RegistrationNativePublicOwnerMask (Canonical)
open RegistrationNativeSecretWordMessage (State)
open RegistrationNativeSecretWordFrontend (M handler)
open PqxdhServerAuthExperiment (Setup Checks)
attribute [local irreducible] RegistrationNativeSecretWordServerCompiler.accept RegistrationNativeSecretWordServerCompiler.build RegistrationNativeSecretWordBeaconCompiler.finish
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem serverOpen_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (chosen : Bool) (work : RegistrationNativeSecretWordServerCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source) (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.serverOpen chosen work).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  simp only [RegistrationNativeSecretWordFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact valid

private theorem lift_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : State source) (result : Value × State source) (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((StateT.lift work : M n KemSK source Value).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact valid

private theorem beacon_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativeSecretWordOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (law : ∀ owners env result, Canonical selected publicPrekey owners →
      result ∈ support ((work.run owners).run env) → Canonical selected publicPrekey result.1.2)
    (before : State source) (result : Value × State source) (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.beacon work).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  simp only [RegistrationNativeSecretWordFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact law before.beacons before.environment inner valid
    (RegistrationNativePublicSourceSupport.simulate_support _ _ inner reached)

private theorem record_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source)
    (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((RegistrationNativeSecretWordFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  cases query with
  | inl request =>
      simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      exact valid
  | inr request =>
      rcases request with ⟨index, request⟩
      cases request <;> cases found : before.beacons[index]? <;>
        simp only [RegistrationNativeSecretWordFrontend.record, StateT.run, found, support_pure, support_map, Set.mem_singleton_iff] at supported
      all_goals first | cases supported; exact valid | obtain ⟨inner, _, rfl⟩ := supported; exact valid

/-- Every actual typed command preserves the initialized scalar mask, including all failed publications and terminal response outcomes. -/
theorem query_canonical (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source)
    (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((handler (n := n) setup checks wire source sign selected selectedAccept publicPrekey query).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  cases query with
  | inl coin => exact lift_keeps selected publicPrekey _ before result valid supported
  | inr command => cases command with
    | create edPin mlPin keyId =>
        exact beacon_keeps selected publicPrekey _ (fun owners env result _ reached =>
          RegistrationNativeSecretWordOwnerCanonical.executeLocal_canonical selected publicPrekey _ owners env result reached) before result valid supported
    | bundle index =>
        exact beacon_keeps selected publicPrekey _ (fun owners env result _ reached =>
          RegistrationNativeSecretWordOwnerCanonical.executeLocal_canonical selected publicPrekey _ owners env result reached) before result valid supported
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind] at supported
        exact serverOpen_keeps selected publicPrekey _ _ { before with parsedAccepts := before.parsedAccepts + 1 } result valid supported
    | build handle application => exact serverOpen_keeps selected publicPrekey _ _ before result valid supported
    | finish index packet =>
        exact beacon_keeps selected publicPrekey _ (RegistrationNativeSecretWordOwnerCanonical.finish_canonical setup selected publicPrekey index packet) before result valid supported
    | hmac key bytes =>
        change result ∈ support (pure (setup.hmac.eval key bytes, before)) at supported
        rw [mem_support_pure_iff] at supported
        cases supported
        exact valid
    | hash bytes => exact lift_keeps selected publicPrekey _ before result valid supported
    | serverSend keyId plaintext => exact record_keeps selected publicPrekey (.inl (.inl (plaintext, keyId))) before result valid supported
    | serverRaw raw => exact record_keeps selected publicPrekey (.inl (.inr raw)) before result valid supported
    | beaconSend index plaintext => exact record_keeps selected publicPrekey (.inr (index, .inl plaintext)) before result valid supported
    | beaconRaw index raw => exact record_keeps selected publicPrekey (.inr (index, .inr raw)) before result valid supported

/-- The same scalar mask holds through every adaptive typed client, including the complete original secrecy compiler. -/
theorem program_canonical (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value) (before : State source)
    (result : Value × State source) (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((simulateQ (handler (n := n) setup checks wire source sign selected selectedAccept publicPrekey) work).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact ih middle.1 middle.2 (query_canonical setup checks wire sign selected selectedAccept publicPrekey query before middle valid reached) continued

/-- The literal original ledger is retained while the complete symbolic frontend preserves its initialized selected public prekey. -/
theorem run_initialized (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source)
    (result : (Value × RegistrationNativeLedger.State) × State source) (empty : before.beacons = [])
    (supported : result ∈ support (RegistrationNativeSecretWordFrontend.run (n := n) setup checks wire source sign
      selected selectedAccept publicPrekey serverKeyId bounds mode work before)) :
    Canonical selected publicPrekey result.2.beacons := by
  apply program_canonical setup checks wire sign selected selectedAccept publicPrekey _ before result
  · rw [empty]
    exact RegistrationNativePublicOwnerMask.empty selected publicPrekey
  · exact supported

/-- Closing arbitrary private or stateful oracle callbacks retains the selected prekey invariant of the same complete raw-ledger execution. -/
theorem source_initialized {Private : Type} (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source)
    (implementation : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK) (StateT Private ProbComp))
    (initial : Private) (result : (((Value × RegistrationNativeLedger.State) × State source) × Private))
    (empty : before.beacons = [])
    (supported : result ∈ support ((simulateQ implementation
      (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selected selectedAccept publicPrekey
        serverKeyId bounds mode work before)).run initial)) :
    Canonical selected publicPrekey result.1.2.beacons := by
  apply run_initialized setup checks wire sign selected selectedAccept publicPrekey serverKeyId bounds mode work before result.1 empty
  apply OracleComp.support_simulateQ_run'_subset implementation _ initial
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.query_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.query_canonical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.program_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.program_canonical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.run_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.run_initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.source_initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerMaskInvariant.source_initialized

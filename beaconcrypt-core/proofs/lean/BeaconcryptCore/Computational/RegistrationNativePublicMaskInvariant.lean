-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerInvariant
import BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution

/-! The complete typed mixed frontend retains its canonical selected-owner mask under every query. The invariant follows the actual open controllers and therefore also holds after their private source interpretation, independently of any winning event. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant
open RegistrationNativePublicOwnerMask (Canonical)
open RegistrationNativePublicFrontend (State M handler)
open PqxdhServerAuthExperiment (Setup Checks)
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build RegistrationBeaconReferenceFinish.finish
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem serverOpen_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (chosen : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (before : State source) (result : Value × State source) (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.serverOpen chosen work).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact valid

private theorem lift_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State source) (result : Value × State source) (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((StateT.lift work : M n KemSK source Value).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact valid

private theorem beacon_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : RegistrationNativePublicOwners.M n KemSK RegistrationServerRoleBackend.State source Value)
    (law : ∀ owners env result, Canonical selected publicPrekey owners →
      result ∈ support ((work.run owners).run env) → Canonical selected publicPrekey result.1.2)
    (before : State source) (result : Value × State source) (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.beacon work).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  simp only [RegistrationNativePublicFrontend.beacon, StateT.run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact law before.beacons before.environment inner valid
    (RegistrationNativePublicSourceSupport.simulate_support _ _ inner reached)

private theorem record_keeps (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source)
    (valid : Canonical selected publicPrekey before.beacons)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    Canonical selected publicPrekey result.2.beacons := by
  cases query with
  | inl request =>
      simp only [RegistrationNativePublicFrontend.record, StateT.run, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      exact valid
  | inr request =>
      rcases request with ⟨index, request⟩
      cases request <;> cases found : before.beacons[index]? <;>
        simp only [RegistrationNativePublicFrontend.record, StateT.run, found, support_pure, support_map, Set.mem_singleton_iff] at supported
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
          RegistrationNativePublicOwnerInvariant.executeLocal_canonical selected publicPrekey _ owners env result reached) before result valid supported
    | bundle index =>
        exact beacon_keeps selected publicPrekey _ (fun owners env result _ reached =>
          RegistrationNativePublicOwnerInvariant.executeLocal_canonical selected publicPrekey _ owners env result reached) before result valid supported
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind] at supported
        exact serverOpen_keeps selected publicPrekey _ _ { before with parsedAccepts := before.parsedAccepts + 1 } result valid supported
    | build handle application => exact serverOpen_keeps selected publicPrekey _ _ before result valid supported
    | finish index packet =>
        exact beacon_keeps selected publicPrekey _ (RegistrationNativePublicOwnerInvariant.finish_canonical setup selected publicPrekey index packet) before result valid supported
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

/-- Private source closure cannot invalidate the scalar mask established by the actual open frontend. -/
theorem source_canonical (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativePublicSourceServer.State n KemSK source)
    (result : Value × RegistrationNativePublicSourceServer.State n KemSK source)
    (valid : Canonical selected publicPrekey before.1.beacons)
    (supported : result ∈ support ((RegistrationNativePublicSourceExecution.execute setup wire route sign seed scalar
      (simulateQ (handler (n := n) setup checks wire source sign selected selectedAccept publicPrekey) work)).run before)) :
    Canonical selected publicPrekey result.2.1.beacons := by
  exact program_canonical setup checks wire sign selected selectedAccept publicPrekey work before.1 (result.1, result.2.1) valid
    (RegistrationNativePublicSourceExecution.observed_support setup wire route sign seed scalar _ before result supported)

end BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant.query_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant.query_canonical

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant.program_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant.program_canonical
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant.source_canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicMaskInvariant.source_canonical

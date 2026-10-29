-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicInvariantMetadata
import BeaconcryptCore.Computational.RegistrationServerReferenceAcceptRequests
import BeaconcryptCore.Computational.RegistrationServerReferenceBuildRequests
import BeaconcryptCore.Computational.RegistrationNativePublicSourceExecution

/-! Pending coherence and the empty local record-request field hold through every actual public typed query and arbitrary adaptive programs, including the original full secrecy-ledger compiler. Source execution inherits these proved open-client invariants through its actual support projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicFrontend (State M handler)
open RegistrationNativePublicInvariantMetadata (Good)
attribute [local irreducible] RegistrationServerOpenReferenceCompiler.accept RegistrationServerOpenReferenceCompiler.build
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem server_good (selected : Bool) (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (keeps : ∀ state env result, result ∈ support ((work.run state).run env) → result.2.recordRequests = env.recordRequests)
    (before : State source) (result : Value × State source) (valid : Good before)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.serverOpen selected work).run before)) : Good result.2 := by
  simp only [RegistrationNativePublicFrontend.serverOpen, StateT.run, support_map] at supported
  obtain ⟨reached, member, equal⟩ := supported
  have native := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ member
  have kept := keeps before.server before.environment reached native
  cases equal
  exact ⟨valid.1, kept.trans valid.2⟩

private theorem lifted_good (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (before : State source) (result : Value × State source) (valid : Good before)
    (supported : result ∈ support ((StateT.lift work : M n KemSK source Value).run before)) : Good result.2 := by
  simp only [StateT.run_lift, bind_pure_comp, support_map] at supported
  obtain ⟨reply, _member, equal⟩ := supported
  cases equal
  exact valid

private theorem record_good (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × State source) (valid : Good before)
    (supported : result ∈ support ((RegistrationNativePublicFrontend.record (n := n) (KemSK := KemSK) query).run before)) :
    Good result.2 := by
  rcases query with query | ⟨index, query⟩
  · simp only [RegistrationNativePublicFrontend.record, StateT.run, support_map] at supported
    obtain ⟨reply, _member, equal⟩ := supported
    cases equal
    exact valid
  · cases query <;> cases found : before.beacons[index]? with
    | none =>
        simp only [RegistrationNativePublicFrontend.record, StateT.run, found, mem_support_pure_iff] at supported
        cases supported
        exact valid
    | some owner =>
        simp only [RegistrationNativePublicFrontend.record, StateT.run, found, support_map] at supported
        obtain ⟨reply, _member, equal⟩ := supported
        cases equal
        exact valid

/-- Every actual typed public callback preserves the metadata required by native finish, with no public event restriction. -/
theorem query_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source) (valid : Good before)
    (supported : result ∈ support
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before)) :
    Good result.2 := by
  cases query with
  | inl coin => exact lifted_good _ before result valid supported
  | inr query => cases query with
    | create edPin mlPin keyId =>
        exact RegistrationNativePublicInvariantMetadata.create_good setup selectedOwner publicPrekey edPin mlPin keyId before result valid supported
    | bundle index =>
        exact RegistrationNativePublicInvariantMetadata.bundle_good setup wire selectedOwner publicPrekey index before result valid supported
    | finish index packet => exact RegistrationNativePublicInvariantMetadata.finish_good setup index packet before result valid supported
    | accept packet =>
        simp only [handler, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_modify] at supported
        exact server_good (decide (before.parsedAccepts = selectedAccept))
          (RegistrationServerOpenReferenceCompiler.accept setup checks source.verify packet)
          (RegistrationServerReferenceAcceptRequests.accept_keeps setup checks source.verify packet)
          { before with parsedAccepts := before.parsedAccepts + 1 } result valid supported
    | build handle application =>
        exact server_good _ _ (RegistrationServerReferenceBuildRequests.build_keeps setup.source wire checks sign handle application)
          before result valid supported
    | hmac key bytes =>
        simp only [handler, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact valid
    | hash bytes => exact lifted_good _ before result valid supported
    | serverSend keyId plaintext => exact record_good (.inl (.inl (plaintext, keyId))) before result valid supported
    | serverRaw bytes => exact record_good (.inl (.inr bytes)) before result valid supported
    | beaconSend index plaintext => exact record_good (.inr (index, .inl plaintext)) before result valid supported
    | beaconRaw index bytes => exact record_good (.inr (index, .inr bytes)) before result valid supported

/-- The complete adaptive typed client preserves both metadata invariants through every actual query and reply. -/
theorem program_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State source) (result : Value × State source) (valid : Good before)
    (supported : result ∈ support ((simulateQ
      (handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before)) :
    Good result.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, reached, continued⟩ := supported
      exact ih middle.1 middle.2 (query_good setup checks wire sign selectedOwner selectedAccept publicPrekey query before middle valid reached) continued

/-- The actual full original secrecy-ledger controller preserves the metadata invariant, for every mode and adaptive adversary. -/
theorem run_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State source)
    (result : (Value × RegistrationNativeLedger.State) × State source) (valid : Good before)
    (supported : result ∈ support
      (RegistrationNativePublicFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work before)) : Good result.2 :=
  program_good setup checks wire sign selectedOwner selectedAccept publicPrekey _ before result valid supported

/-- Actual source interpretation retains the complete public metadata invariant through arbitrary typed client execution. -/
theorem source_program_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativePublicSourceServer.State n KemSK source)
    (result : Value × RegistrationNativePublicSourceServer.State n KemSK source) (valid : Good before.1)
    (supported : result ∈ support
      ((RegistrationNativePublicSourceExecution.execute setup wire route sign seed scalar
        (simulateQ (handler setup checks wire source sign selectedOwner selectedAccept publicPrekey) work)).run before)) :
    Good result.2.1 := by
  exact program_good setup checks wire sign selectedOwner selectedAccept publicPrekey work before.1 (result.1, result.2.1) valid
    (RegistrationNativePublicSourceExecution.observed_support setup wire route sign seed scalar _ before result supported)

/-- Every supported complete ledger outcome after actual successful startup has the required metadata; no initial coherence or empty-field premise is supplied. -/
theorem initialized_run_good (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (identity : PqxdhJointIdentity.PublicIdentity)
    (before after : RegistrationNativePublicInterpreter.State n KemSK)
    (started : RegistrationNativePublicStartup.Started source)
    (initialized : (some started, after) ∈ support
      ((RegistrationNativePublicStartup.start setup source ensureInit identityIndex serverKeyId identity).run before))
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : (Value × RegistrationNativeLedger.State) × State source)
    (supported : result ∈ support
      (RegistrationNativePublicFrontend.run (n := n) setup checks wire source
        (RegistrationNativeMldsa.owned source started.credential) selectedOwner selectedAccept publicPrekey
        serverKeyId bounds mode work started.frontend)) : Good result.2 :=
  run_good setup checks wire (RegistrationNativeMldsa.owned source started.credential)
    selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work started.frontend result
    (RegistrationNativePublicInvariantStartup.start_good setup ensureInit identityIndex serverKeyId identity before after started initialized) supported

end BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.query_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.run_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.source_program_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.source_program_good
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.initialized_run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicInvariantRun.initialized_run_good

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSessionRaw
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterLedger
import BeaconcryptCore.Computational.RegistrationNativeAcceptHandleLedger

/-! The actual Native run starts with an empty public ledger and allocates successful accept handles by appending session tokens. Original hidden-bit and fresh-message operations cannot allocate accept handles. Therefore the unchanged original registration entries contain only one raw candidate at each successful handle, with no parser-injectivity, initial-session, enrollment or AD-inverse premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSessionLedger
open RegistrationNativeExperiment (State)
open RegistrationNativeWire (Wire)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeAcceptHandleLedger (Growth Holds success)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

noncomputable abbrev native (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) :=
  RegistrationNativeParsedCounterLedger.native (n := n) setup checks wire route representation created credential

private theorem send_nonAccept (query : RegistrationNativeInterface.Spec.Domain)
    (restricted : PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) ≠ false) :
    RegistrationNativeSessionRaw.NonAccept query := by
  cases query with
  | inl coin => trivial
  | inr command => cases command <;> simp_all [RegistrationNativeSessionRaw.NonAccept,
      PqxdhDeploymentSecrecy.coinOrSend, RegistrationNativeInterface.eraseCore,
      RegistrationNativeInterface.eraseCommand]

/-- Actual coins-and-sends continuations preserve the allocated session count. -/
theorem restricted_sessions (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeInterface.Spec Value)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentSecrecy.coinOrSend (RegistrationNativeInterface.eraseCore query) = false) 0)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (reached : result ∈ support ((simulateQ (native setup checks wire route representation created credential) work).run before)) :
    result.2.server.sessions.length = before.server.sessions.length := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      rfl
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have restricted := allowed.resolve_right (by omega)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, tail⟩ := reached
      have same := RegistrationNativeSessionRaw.other setup checks wire route representation created credential query
        (send_nonAccept query restricted) before middle first
      exact (ih middle.1 (by simpa using rest middle.1) middle.2 result tail).trans same

/-- Original secrecy operations issue no accept callback and retain the same source session count. -/
theorem secrecy_sessions (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (bounds : FreshBounds) (query : PqxdhDeploymentInterface.Secrecy)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : Option RawCtxSourceSend.Encrypted × (RegistrationNativeLedger.State × State n KemSK source))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
      (.inr query)).run before)) :
    result.2.2.server.sessions.length = before.2.server.sessions.length := by
  rw [RegistrationNativeFullCompiler.handler, RegistrationNativeLedger.interpreted,
    QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact restricted_sessions setup checks wire route representation created credential _
    (RegistrationNativeLedger.secrecy_frame setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
      created.server.server.metadata.sender bounds query before.1) before.2 inner supported

/-- The actual complete callback derives the fresh-index bookkeeping receipt internally. -/
theorem step_growth (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (bounds : FreshBounds) (query : RegistrationNativeInterface.FullSpec.Domain)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (result : RegistrationNativeInterface.FullSpec.Range query × (RegistrationNativeLedger.State × State n KemSK source))
    (reached : result ∈ support ((RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    Growth ⟨query, result.1⟩ before.2.server.sessions.length result.2.2.server.sessions.length := by
  cases query with
  | inr query =>
      exact secrecy_sessions setup checks wire route representation created credential bounds query before result reached
  | inl query =>
      rw [RegistrationNativeParsedCounterLedger.core_run, support_map] at reached
      obtain ⟨inner, supported, rfl⟩ := reached
      cases query with
      | inl coin =>
          exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
            (.inl coin) trivial before.2 inner supported
      | inr command => cases command with
        | accept raw =>
            have shaped := RegistrationNativeSessionRaw.accept setup checks wire route representation created credential
              raw before.2 inner.2 inner.1 supported
            cases reply : inner.1 <;> simpa only [Growth, success, RegistrationNativeSessionRaw.Shape, reply] using shaped
        | create edPin mlPin keyId =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.create edPin mlPin keyId)) trivial before.2 inner supported
        | bundle owner =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.bundle owner)) trivial before.2 inner supported
        | build handle application =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.build handle application)) trivial before.2 inner supported
        | finish owner packet =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.finish owner packet)) trivial before.2 inner supported
        | hmac key message =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.hmac key message)) trivial before.2 inner supported
        | hash bytes =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.hash bytes)) trivial before.2 inner supported
        | serverSend keyId plaintext =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.serverSend keyId plaintext)) trivial before.2 inner supported
        | serverRaw raw =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.serverRaw raw)) trivial before.2 inner supported
        | beaconSend owner plaintext =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.beaconSend owner plaintext)) trivial before.2 inner supported
        | beaconRaw owner raw =>
            exact RegistrationNativeSessionRaw.other setup checks wire route representation created credential
              (.inr (.beaconRaw owner raw)) trivial before.2 inner supported

/-- Every adaptive actual full-interface program preserves the internal trace invariant. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (bounds : FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value)
    (before : RegistrationNativeLedger.State × State n KemSK source)
    (prior : Holds before.1.transcript before.2.server.sessions.length)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (reached : result ∈ support ((simulateQ (RegistrationNativeFullCompiler.handler setup.source.crypto wire
      created.server.server.metadata.sender bounds
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)) work).run before)) :
    Holds result.2.1.transcript result.2.2.server.sessions.length := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at reached
      subst result
      exact prior
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at reached
      obtain ⟨middle, first, tail⟩ := reached
      have growth := step_growth setup checks wire route representation created credential bounds query before middle first
      have trace := RegistrationNativeParsedCounterLedger.step_trace setup checks wire route representation created credential
        bounds query before middle first
      have current : Holds middle.2.1.transcript middle.2.2.server.sessions.length := by
        rw [trace]
        exact RegistrationNativeAcceptHandleLedger.append before.1.transcript ⟨query, middle.1⟩
          before.2.server.sessions.length middle.2.2.server.sessions.length prior growth
      exact ih middle.1 middle.2 current result tail

/-- Every actual Native run has unique successful accept handles, even with pre-existing sessions. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source)
    (result : Value × (RegistrationNativeLedger.State × State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation
      created source credential bounds mode work before)) :
    Holds result.2.1.transcript result.2.2.server.sessions.length := by
  exact program setup checks wire route representation created credential bounds
    (RegistrationNativeInterface.asModeO mode work) (RegistrationNativeLedger.empty, before)
    (RegistrationNativeAcceptHandleLedger.empty before.server.sessions.length) result supported

end BeaconcryptCore.Computational.RegistrationNativeSessionLedger

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionLedger.restricted_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionLedger.restricted_sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionLedger.secrecy_sessions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionLedger.secrecy_sessions

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionLedger.step_growth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionLedger.step_growth

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionLedger.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionLedger.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionLedger.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionLedger.run

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSessionSource

/-! Raw decoding projects only the reply of the actual Native callback. A successful raw accept returns the next session index; malformed packets, failed acceptance and every other raw operation retain the correct roster length. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSessionRaw
open RegistrationNativeExperiment (State)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeInterface (Spec)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler

def NonAccept : Spec.Domain → Prop
  | .inr (.accept _) => False
  | _ => True

def Shape (reply : Option Nat) (before after : Nat) : Prop :=
  match reply with
  | none => after = before
  | some handle => handle = before ∧ after = before + 1

private theorem project_shape (before after : List (Option beaconcrypt_core.peer.ConsumedRegistration))
    (reply : RustM (Option Nat)) (shaped : RegistrationNativeAcceptSessionShape.Shape before reply after) :
    Shape (RegistrationNativeRawAdapter.resultOption reply) before.length after.length := by
  rcases shaped with ⟨same, absent⟩ | ⟨token, appended, returned⟩
  · cases reply with
    | fail error | div => exact congrArg List.length same
    | ok option => cases option with
      | none => exact congrArg List.length same
      | some handle => exact (absent handle rfl).elim
  · simp only [returned, RegistrationNativeRawAdapter.resultOption, Shape,
      appended, List.length_append, List.length_singleton, and_self]

private theorem projected_other (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (query : TypedSpec.Domain) (nonAccept : RegistrationNativeSessionSource.NonAccept query)
    {Value : Type} (project : TypedSpec.Range query → Value)
    (before : State n KemSK source) (result : Value × State n KemSK source)
    (reached : result ∈ support (Prod.map project id <$>
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    result.2.server.sessions.length = before.server.sessions.length := by
  rw [support_map] at reached
  obtain ⟨inner, supported, rfl⟩ := reached
  exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential query nonAccept before inner supported

theorem other (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source)
    (query : Spec.Domain) (nonAccept : NonAccept query)
    (before : State n KemSK source) (result : Spec.Range query × State n KemSK source)
    (reached : result ∈ support ((RegistrationNativeRawAdapter.handler wire
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) query).run before)) :
    result.2.server.sessions.length = before.server.sessions.length := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
        RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
      exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential
        (.inl coin) trivial before result reached
  | inr command => cases command with
    | accept raw => cases nonAccept
    | create edPin mlPin keyId =>
        cases ed : PqxdhDeploymentInterface.parsePin edPin with
        | none =>
            simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
              RegistrationNativeRawAdapter.adapter, ed, simulateQ_pure, StateT.run_pure,
              mem_support_pure_iff] at reached
            subst result
            rfl
        | some edValue => cases ml : RegistrationNativeWire.parseMldsaPin mlPin with
          | none =>
              simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
                RegistrationNativeRawAdapter.adapter, ed, ml, simulateQ_pure, StateT.run_pure,
                mem_support_pure_iff] at reached
              subst result
              rfl
          | some mlValue =>
              simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
                RegistrationNativeRawAdapter.adapter, ed, ml, simulateQ_map,
                simulateQ_spec_query, StateT.run_map] at reached
              exact projected_other setup checks wire route representation created credential
                (.inr (.create edValue mlValue keyId)) trivial RegistrationNativeRawAdapter.resultOption before result reached
    | bundle owner =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
        exact projected_other setup checks wire route representation created credential (.inr (.bundle owner)) trivial RegistrationNativeRawAdapter.resultOption before result reached
    | build session application =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
        exact projected_other setup checks wire route representation created credential (.inr (.build session (RegistrationNativeRawAdapter.application application))) trivial RegistrationNativeRawAdapter.responseOption before result reached
    | finish owner raw =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_map, simulateQ_spec_query, StateT.run_map] at reached
        exact projected_other setup checks wire route representation created credential (.inr (.finish owner (RegistrationNativeWire.readResponse wire raw))) trivial RegistrationNativeRawAdapter.resultOption before result reached
    | hmac key message =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
        exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential (.inr (.hmac key message)) trivial before result reached
    | hash bytes =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
        exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential (.inr (.hash bytes)) trivial before result reached
    | serverSend keyId plaintext =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
        exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential (.inr (.serverSend keyId plaintext)) trivial before result reached
    | serverRaw raw =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
        exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential (.inr (.serverRaw raw)) trivial before result reached
    | beaconSend owner plaintext =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
        exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential (.inr (.beaconSend owner plaintext)) trivial before result reached
    | beaconRaw owner raw =>
        simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
          RegistrationNativeRawAdapter.adapter, simulateQ_spec_query] at reached
        exact RegistrationNativeSessionSource.typed_other setup checks wire route representation created credential (.inr (.beaconRaw owner raw)) trivial before result reached

/-- Successful decoding, actual authentication/agreement and reply projection retain the exact append index; malformed Init is only a rejected call. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) (raw : Pqxdh.Bytes)
    (before after : State n KemSK source) (reply : Option Nat) :
    (reply, after) ∈ support ((RegistrationNativeRawAdapter.handler wire
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
      (.inr (.accept raw))).run before) →
    Shape reply before.server.sessions.length after.server.sessions.length := by
  cases read : RegistrationNativeWire.readInit wire raw with
  | none =>
      simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
        RegistrationNativeRawAdapter.adapter, read, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff, Prod.mk.injEq]
      rintro ⟨rfl, rfl⟩
      rfl
  | some packet =>
      simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
        RegistrationNativeRawAdapter.adapter, read, simulateQ_map, simulateQ_spec_query,
        StateT.run_map, support_map]
      rintro ⟨inner, _, same⟩
      cases same
      exact project_shape _ _ _ (RegistrationNativeSessionSource.typed_accept setup checks wire route
        representation created credential packet before inner.2 inner.1 (by assumption))

end BeaconcryptCore.Computational.RegistrationNativeSessionRaw

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionRaw.other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionRaw.other

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSessionRaw.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSessionRaw.accept

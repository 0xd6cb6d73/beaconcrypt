-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceRestore

/-! Consumed reference capabilities preserve the actual allocator/occupancy lookup and every public initial-record field. Private root restoration affects only the later KDF input, after preflight, occupancy and reservation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup
open PqxdhSecretInputKdf (RootOutput)
open RegistrationPublicationKernelErasure (mapOk)

def withRoot (lookup : peer.CompletionLookup) (root : RootOutput) : peer.CompletionLookup :=
  { lookup with registration := ⟨{ lookup.registration.agreement with
      root := ⟨PqxdhRootTableInitialization.rootArray root⟩ }⟩ }

/-- Completion lookup uses the same actual allocator result before reading any private root. -/
theorem begin_root (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (ready : RegistrationServerReferenceRoot.Ready) (application : Slice U8) (root : RootOutput) :
    peer.begin_completion_lookup control pin ⟨RegistrationServerReferenceRoot.atRoot ready root⟩ application =
      mapOk (fun lookup => withRoot lookup root) <$>
        peer.begin_completion_lookup control pin (RegistrationServerMaterialFrontend.token ready) application := by
  cases next : pqxdh.server_next_key_id control with
  | fail error => simp only [peer.begin_completion_lookup, next, bind_tc_fail]; rfl
  | div => simp only [peer.begin_completion_lookup, next, bind_tc_div]; rfl
  | ok result =>
      cases result with
      | Err previous => simp only [peer.begin_completion_lookup, next, bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok, mapOk]
      | Ok keyId =>
          simp only [peer.begin_completion_lookup, next, bind_tc_ok, RawCtxMaterialInterpretation.rust_map_ok,
            mapOk, withRoot, RegistrationServerMaterialFrontend.token, RegistrationServerReferenceRoot.atRoot,
            RegistrationBoundGate.atRoot]

/-- Requested peer identifiers remain literal, so complete-message preflight is unchanged. -/
theorem request_root (lookup : peer.CompletionLookup) (root : RootOutput) :
    (withRoot lookup root).request = lookup.request := rfl

/-- Native pin/occupancy admission and every public initial field are independent of the restored private root. -/
theorem resume_public (lookup : peer.CompletionLookup) (root : RootOutput) (occupied : Bool) :
    mapOk RegistrationBoundKeySchedule.publicInitial <$> (withRoot lookup root).resume occupied =
      mapOk RegistrationBoundKeySchedule.publicInitial <$> lookup.resume occupied := by
  let descriptor : RegistrationBoundGate.PublicAgreement :=
    ⟨lookup.registration.agreement.pending, lookup.registration.agreement.binding⟩
  have original : lookup.registration.agreement = RegistrationBoundGate.atRoot descriptor
      (RegistrationBoundSource.rootValue lookup.registration.agreement.root.bytes) := by
    have restored (actual : agreement.ServerAgreement) : actual = RegistrationBoundGate.atRoot
        ⟨actual.pending, actual.binding⟩ (RegistrationBoundSource.rootValue actual.root.bytes) := by
      cases actual
      simp only [RegistrationBoundGate.atRoot, RegistrationBoundSource.root_value_array]
    exact restored lookup.registration.agreement
  have gates (availability : pqxdh.KeyIdAvailability) :
      mapOk RegistrationBoundKeySchedule.publicInitial <$>
        registration.begin_server_completion lookup.control lookup.pin availability
          (RegistrationBoundGate.atRoot descriptor root) lookup.application =
        mapOk RegistrationBoundKeySchedule.publicInitial <$>
          registration.begin_server_completion lookup.control lookup.pin availability
            lookup.registration.agreement lookup.application := by
    have first := RegistrationBoundGate.gate_root lookup.control lookup.pin availability descriptor lookup.application root
    have second := RegistrationBoundGate.gate_root lookup.control lookup.pin availability descriptor lookup.application
      (RegistrationBoundSource.rootValue lookup.registration.agreement.root.bytes)
    rw [← original] at second
    exact first.trans second.symm
  cases occupied <;> simp only [peer.CompletionLookup.resume, Bool.false_eq_true, ite_false, ite_true, bind_tc_ok]
  all_goals exact gates _

/-- A reached source initializer has the actual Server initial64 role and the restored root bytes. -/
theorem resume_role (lookup : peer.CompletionLookup) (root : RootOutput) (occupied : Bool)
    (initial : registration.ServerInitialKdf)
    (actual : (withRoot lookup root).resume occupied = .ok (.Ok initial)) :
    initial.pending = PqxdhInitialRatchetComplementarity.serverPending
      (PqxdhRootTableInitialization.rootArray root) := by
  cases occupied <;>
    simp only [peer.CompletionLookup.resume, Bool.false_eq_true, ite_false, ite_true, bind_tc_ok] at actual
  all_goals exact RegistrationSeedKernel.server_pending _ _ _ _ _ initial actual

end BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.begin_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.begin_root
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.request_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.request_root
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.resume_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.resume_public
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.resume_role' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceLookup.resume_role

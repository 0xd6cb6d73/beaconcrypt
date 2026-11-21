-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
import BeaconcryptCore.Refinement.PeerOwnership
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
/-! Actual source replay membership and the native history select the same branch from the authenticated registration identifier. Fresh native admission is derived from this logical container view, rather than supplied as an independent protocol premise. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership
open AdapterPublicWrapperStorage AdapterPublicWrapperState
open BeaconcryptCore.Computational
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

omit material in
theorem membership (views : Views) (stored : ReplaySet) (history : List Pqxdh.Bytes)
    (related : ReplayRelated views stored history) (identifier : Std.Array U8 64#usize) :
    views.replay stored identifier = history.contains (absBytes identifier) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using related identifier

theorem lookup {source : RegistrationNativeMldsa.Source} {KemSK : Type}
    (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.RegistrationLookup) (identifier : pqxdh.RegistrationId)
    (requested : pending.request = .ok identifier) :
    views.replay self.consumed_registrations identifier.bytes =
      native.consumed.contains (RegistrationReplaySchedule.identifier pending.authenticated) := by
  rw [membership views self.consumed_registrations native.consumed related.replay identifier.bytes]
  obtain ⟨actual, requestRun, canonical⟩ := PeerOwnership.registration_lookup_request_bytes pending
  have same : actual = identifier := RustM.ok.inj (requestRun.symm.trans requested)
  cases same
  rw [canonical]
  rfl

theorem fresh {source : RegistrationNativeMldsa.Source} {KemSK : Type}
    (view : MaterialView source KemSK) (views : Views)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.server.Server) {n : Nat} (native : RegistrationServerFrontendCompiler.State n)
    (related : Server view views created credential self native)
    (pending : peer.RegistrationLookup) (identifier : pqxdh.RegistrationId)
    (requested : pending.request = .ok identifier)
    (absent : views.replay self.consumed_registrations identifier.bytes = false) :
    native.consumed.contains (RegistrationReplaySchedule.identifier pending.authenticated) = false :=
  (lookup view views created credential self native related pending identifier requested).symm.trans absent
end BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership.membership' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership.membership

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership.lookup

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerReplayMembership.fresh

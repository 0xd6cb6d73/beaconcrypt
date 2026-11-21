-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostNative

/-! Actual protected authentication failures at a selected prior birth produce the dynamic ghost observer's candidate or the same-cut shared-cache collision. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaGhostProtected
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaGhostNative (State nativeState rowState callback observe)
open RegistrationNativeMldsaProtectedInvariant (Holds)
open RegistrationNativeMldsaProtectedCoverage (BornKey)
open PqxdhServerAuthExperiment (Setup Checks)
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationSigningShared.historyFor
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source) (selected : Nat) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))

private theorem projected (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source n KemSK) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source n KemSK)
    (supported : result ∈ support ((callback source selected setup checks wire route representation created credential query).run before)) :
    (result.1, nativeState source result.2) ∈ support
      ((RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential query).run (nativeState source before)) := by
  rw [← RegistrationNativeMldsaGhostNative.project, support_map]
  exact ⟨result, supported, rfl⟩

/-- Verification callbacks retain their literal private generation and signing table. -/
theorem pool (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (free : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (before : State source n KemSK) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source n KemSK)
    (supported : result ∈ support ((callback source selected setup checks wire route representation created credential query).run before)) :
    result.2.2.2 = before.2.2 := by
  have possible := projected source selected setup checks wire route representation created credential query before result supported
  have law : RegistrationNativeMldsaProfile.handler (n := n) setup checks wire route representation created credential query =
      RegistrationNativeMldsaProgram.liftState (RegistrationNativeExperiment.handler setup checks wire route representation created
        (handleSource source) credential query) := by
    cases query with
    | inl coin => rfl
    | inr query => cases query with
      | create _ _ _ | bundle _ | build _ _ => exact False.elim free
      | _ => rfl
  simp only [RegistrationNativeMldsaTableStop.callback, StateT.run] at possible
  rw [law, RegistrationNativeMldsaTableProgram.run_liftState, Functor.map_map, support_map] at possible
  obtain ⟨inner, _possible, same⟩ := possible
  exact (congrArg (fun value => value.2.2) same).symm

/-- A protected response origin failure uses the initial Server credential's selected birth at the actual tracked callback. -/
theorem finish (fallback : Credential source) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (before after : State source n KemSK) (application : Pqxdh.Bytes)
    (good : Holds source credential fallback (nativeState source before))
    (rows : RegistrationNativeMldsaGhostRows.Safe source selected (rowState source before))
    (found : before.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (keyProtected : pending.binding.server_pin.public_key = credential.publicKey)
    (born : BornKey source before.2.2 selected credential.publicKey)
    (supported : (.ok (some application), after) ∈ support
      ((callback source selected setup checks wire route representation created credential (.inr (.finish index (some packet)))).run before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before.1)))) :
    CacheHasCollision after.1.server.world.world.1.primitive.2 ∨
      ∃ forgery, observe source (.inr (.finish index (some packet))) before (.ok (some application)) after = some forgery ∧
        RegistrationNativeMldsaTableStop.Good source credential.publicKey (nativeState source after) forgery := by
  have underlying := projected source selected setup checks wire route representation created credential
    (.inr (.finish index (some packet))) before (.ok (some application), after) supported
  rcases RegistrationNativeMldsaProtectedCoverage.finish source setup checks wire route representation created credential fallback index owner pending oneTime packet
    (nativeState source before) (nativeState source after) application good.safe good.provenance found phase keyProtected underlying absent with collision | candidate
  · exact Or.inl collision
  · obtain ⟨_ordinal, _earlier, _born, forgery, chosen, fresh⟩ := candidate
    have afterBorn : BornKey source after.2.2 selected credential.publicKey := by
      rw [pool source selected setup checks wire route representation created credential (.inr (.finish index (some packet))) trivial before (.ok (some application), after) supported]
      exact born
    exact Or.inr ⟨forgery, RegistrationNativeMldsaGhostNative.capture source selected setup checks wire route representation created credential
      (.inr (.finish index (some packet))) before rows (.ok (some application), after) supported credential.publicKey afterBorn forgery chosen, fresh⟩

end BeaconcryptCore.Computational.RegistrationNativeMldsaGhostProtected
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostProtected.pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostProtected.pool


/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaGhostProtected.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaGhostProtected.finish

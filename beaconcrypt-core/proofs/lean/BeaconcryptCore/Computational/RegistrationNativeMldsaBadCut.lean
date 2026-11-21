-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaGhostFamily

/-! The original protected Server response unsigned-origin failure is an actual successful Beacon finish with no earlier same-key payload issuance. A finite simultaneous family covers that cut using its actual prior generation row or the shared-cache collision. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaBadCut
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativeMldsaGhostFamily (State nativeState coordinateState callback)
open RegistrationNativeMldsaProtectedInvariant (Holds)
open RegistrationNativeMldsaProtectedCoverage (BornKey)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationSigningShared.historyFor

inductive Bad (source : Source) (credential : Credential (handleSource source)) :
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) →
      RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) source →
      RegistrationNativeRawAdapter.TypedSpec.Range query → Prop where
  | finish (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
      (before : RegistrationNativeMldsaTableStop.State (n := n) (KemSK := KemSK) source)
      (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
      (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
      (found : before.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
      (keyProtected : pending.binding.server_pin.public_key = credential.publicKey)
      (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
          (RegistrationNativeMldsaShared.nativeProject before.1)))) :
      Bad source credential (.inr (.finish index (some packet))) before (.ok (some application))

variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))

private theorem original (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    (result.1, nativeState source result.2) ∈ support
      ((RegistrationNativeMldsaTableStop.callback source setup checks wire route representation created credential query).run (nativeState source before)) := by
  rw [← RegistrationNativeMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

private theorem selected (ordinal : Fin cap) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK)
    (rows : RegistrationNativeMldsaGhostRows.Safe source ordinal.val (before.2.1 ordinal, before.2.2))
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before))
    (nonSigning : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) (born : BornKey source before.2.2 ordinal.val publicKey)
    (forgery : RegistrationNativeMldsaEuf.Forgery)
    (chosen : RegistrationNativeMldsaTableStop.observe source publicKey query (nativeState source before) result.1
      (nativeState source result.2) = some forgery) :
    RegistrationNativeMldsaGhostNative.observe source query (coordinateState source ordinal before) result.1
      (coordinateState source ordinal result.2) = some forgery := by
  have projected : (result.1, coordinateState source ordinal result.2) ∈ support
      ((RegistrationNativeMldsaGhostNative.callback source ordinal.val setup checks wire route representation created credential query).run
        (coordinateState source ordinal before)) := by
    rw [← RegistrationNativeMldsaGhostFamily.callback_coordinate, support_map]
    exact ⟨result, supported, rfl⟩
  have same := RegistrationNativeMldsaGhostProtected.pool source ordinal.val setup checks wire route representation created credential
    query nonSigning (coordinateState source ordinal before) (result.1, coordinateState source ordinal result.2) projected
  apply RegistrationNativeMldsaGhostNative.capture source ordinal.val setup checks wire route representation created credential query
    (coordinateState source ordinal before) rows (result.1, coordinateState source ordinal result.2) projected publicKey _ forgery chosen
  change BornKey source result.2.2.2 ordinal.val publicKey
  change result.2.2.2 = before.2.2 at same
  rw [same]
  exact born

/-- Every original protected bad cut selects an actual earlier ordinal in the finite family, or has the literal same-cut shared-cache collision. -/
theorem cover (fallback : Credential source) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK)
    (good : Holds source credential fallback (nativeState source before))
    (rows : ∀ ordinal : Fin cap, RegistrationNativeMldsaGhostRows.Safe source ordinal.val (before.2.1 ordinal, before.2.2))
    (room : before.2.2.attempts ≤ cap)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before))
    (bad : Bad source credential query (nativeState source before) result.1) :
    CacheHasCollision result.2.1.server.world.world.1.primitive.2 ∨
      ∃ ordinal : Fin cap, (RegistrationNativeMldsaGhostNative.observe source query (coordinateState source ordinal before) result.1
        (coordinateState source ordinal result.2)).isSome = true := by
  rcases result with ⟨reply, after⟩
  have reached := original source setup checks wire route representation created credential query before (reply, after) supported
  cases bad with
  | finish index packet application _ owner pending oneTime found phase matching absent =>
      rcases RegistrationNativeMldsaProtectedCoverage.finish source setup checks wire route representation created credential fallback index owner pending oneTime packet
        (nativeState source before) (nativeState source after) application good.safe good.provenance found phase matching reached absent with collision | issued
      · exact Or.inl collision
      · obtain ⟨ordinal, earlier, born, forgery, chosen, _fresh⟩ := issued
        let selectedIndex : Fin cap := ⟨ordinal, Nat.lt_of_lt_of_le earlier room⟩
        have captured := selected source setup checks wire route representation created credential selectedIndex (.inr (.finish index (some packet)))
          before (.ok (some application), after) (rows selectedIndex) supported trivial credential.publicKey born forgery chosen
        exact Or.inr ⟨selectedIndex, by rw [captured]; rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeMldsaBadCut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaBadCut.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaBadCut.cover

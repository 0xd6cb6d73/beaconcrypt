-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaReceiptPreservation
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaGhostFamily
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaProtectedCoverage
import BeaconcryptCore.Computational.RegistrationNativeMldsaBadCut

/-! The original protected native unsigned-origin failure is an actual successful Init acceptance or Beacon finish with no earlier same-key payload issuance. A finite simultaneous family covers that cut using its actual prior generation row or the shared-cache collision. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaBadCut
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformOrdinaryMldsaGhostFamily (State nativeState coordinateState callback)
open RegistrationNativePlatformMldsaTableStop (Safe)
open RegistrationNativeMldsaProtectedCoverage (BornKey)
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n cap : Nat} {ι KemSK Platform E : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationSigningShared.historyFor RegistrationAuthenticationNative.trial

abbrev Bad := RegistrationNativeMldsaBadCut.Bad (n := n) (KemSK := KemSK)

variable (source : Source) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : Credential (handleSource source))
variable [primitive : AdapterSealPrimitive.Operations]
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem original (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source cap n KemSK Platform)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before)) :
    (result.1, nativeState source result.2) ∈ support
      ((RegistrationNativePlatformOrdinaryMldsaTableCallback.callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run (nativeState source before)) := by
  rw [← RegistrationNativePlatformOrdinaryMldsaGhostFamily.callback_erase, support_map]
  exact ⟨result, supported, rfl⟩

private theorem selected (ordinal : Fin cap) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (rows : RegistrationNativeMldsaGhostRows.Safe source ordinal.val (before.2.1 ordinal, before.2.2))
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before))
    (nonSigning : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (publicKey : RegistrationNativeMldsaEuf.PublicKey) (born : BornKey source before.2.2 ordinal.val publicKey)
    (forgery : RegistrationNativeMldsaEuf.Forgery)
    (chosen : RegistrationNativePlatformOrdinaryMldsaTableCallback.observe source publicKey query (nativeState source before) result.1
      (nativeState source result.2) = some forgery) :
    RegistrationNativePlatformOrdinaryMldsaGhostNative.observe source query (coordinateState source ordinal before) result.1
      (coordinateState source ordinal result.2) = some forgery := by
  have projected : (result.1, coordinateState source ordinal result.2) ∈ support
      ((RegistrationNativePlatformOrdinaryMldsaGhostNative.callback source ordinal.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run
        (coordinateState source ordinal before)) := by
    rw [← RegistrationNativePlatformOrdinaryMldsaGhostFamily.callback_coordinate, support_map]
    exact ⟨result, supported, rfl⟩
  have underlying := original source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before result supported
  simp only [RegistrationNativePlatformOrdinaryMldsaTableCallback.callback, StateT.run, support_map] at underlying
  obtain ⟨inner, reached, equal⟩ := underlying
  have frame := RegistrationNativePlatformOrdinaryMldsaReceiptPreservation.handler source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    query nonSigning before.1.1 before.1.2 before.2.2 inner reached
  have poolEq := congrArg (fun value => value.2.2) equal
  change inner.2 = result.2.2.2 at poolEq
  have same : result.2.2.2 = before.2.2 := poolEq.symm.trans frame.1
  apply RegistrationNativePlatformOrdinaryMldsaGhostNative.capture source ordinal.val setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query
    (coordinateState source ordinal before) rows (result.1, coordinateState source ordinal result.2) projected publicKey _ forgery chosen
  change BornKey source result.2.2.2 ordinal.val publicKey
  rw [same]
  exact born

/-- Every original protected bad cut selects an actual earlier ordinal in the finite family, or has the literal same-cut shared-cache collision. -/
theorem cover (fallback : Credential source) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State source cap n KemSK Platform) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State source cap n KemSK Platform)
    (good : Safe source credential fallback (nativeState source before))
    (rows : ∀ ordinal : Fin cap, RegistrationNativeMldsaGhostRows.Safe source ordinal.val (before.2.1 ordinal, before.2.2))
    (room : before.2.2.attempts ≤ cap)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before))
    (bad : Bad source credential query (before.1.1, before.2.2) result.1) :
    CacheHasCollision result.2.1.1.server.world.world.1.primitive.2 ∨
      ∃ ordinal : Fin cap, (RegistrationNativePlatformOrdinaryMldsaGhostNative.observe source query (coordinateState source ordinal before) result.1
        (coordinateState source ordinal result.2)).isSome = true := by
  rcases result with ⟨reply, after⟩
  have reached := original source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before (reply, after) supported
  cases bad with
  | accept packet session _ owner owned matching absent =>
      rcases RegistrationNativePlatformOrdinaryMldsaProtectedCoverage.accept source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback packet
        (nativeState source before) (nativeState source after) session good owner owned matching reached absent with collision | issued
      · exact Or.inl collision
      · obtain ⟨ordinal, earlier, born, forgery, chosen, _fresh⟩ := issued
        let index : Fin cap := ⟨ordinal, Nat.lt_of_lt_of_le earlier room⟩
        have captured := selected source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index (.inr (.accept packet))
          before (.ok (some session), after) (rows index) supported trivial owner.mldsa.publicKey born forgery chosen
        exact Or.inr ⟨index, by rw [captured]; rfl⟩
  | finish index packet application _ owner pending oneTime found phase matching absent =>
      rcases RegistrationNativePlatformOrdinaryMldsaProtectedCoverage.finish source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback index owner pending oneTime packet
        (nativeState source before) (nativeState source after) application good found phase matching reached absent with collision | issued
      · exact Or.inl collision
      · obtain ⟨ordinal, earlier, born, forgery, chosen, _fresh⟩ := issued
        let selectedIndex : Fin cap := ⟨ordinal, Nat.lt_of_lt_of_le earlier room⟩
        have captured := selected source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer selectedIndex (.inr (.finish index (some packet)))
          before (.ok (some application), after) (rows selectedIndex) supported trivial credential.publicKey born forgery chosen
        exact Or.inr ⟨selectedIndex, by rw [captured]; rfl⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaBadCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaBadCut.cover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaBadCut.cover

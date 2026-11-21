-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInitOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformResponseTypedOrigin
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop

/-! Actual corrected source accept/finish origin failures at protected generated ML keys select an earlier successful generation attempt and a valid fresh same-cut ordinary forgery, or retain the literal shared-cache collision. Reached stored-pin validity comes from actual initialized execution. Failed generations, all admitted public fields, dynamic writers and assigned-ID finish remain unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProtectedCoverage
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativeMldsaProtectedCoverage (BornKey born_key)
open RegistrationNativePlatformMldsaTableCallback (State callback observe)
open RegistrationNativePlatformMldsaTableStop (Safe Good)
open RegistrationNativePlatformMldsaProgram (coins)
variable {n : Nat} {E Platform ι KemSK : Type} {base : OracleSpec ι}
variable (source : Source)
variable [primitive : AdapterSealPrimitive.Operations]
attribute [local irreducible] RegistrationNativePlatformExperiment.handler RegistrationSigningShared.historyFor

section Actual
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : Credential (handleSource source))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem original (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (free : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query).run before)) :
    ((result.1, result.2.1.1), result.2.1.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created (handleSource source) credential
        view failure allocation reserveRegistration reservePeer erased helper writer query).run before.1.1).run before.1.2) := by
  have law : RegistrationNativePlatformMldsaProfile.handler (n := n) setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query = RegistrationNativePlatformMldsaProgram.lift
      (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created (handleSource source) credential
        view failure allocation reserveRegistration reservePeer erased helper writer query) := by
    cases query with
    | inl coin => rfl
    | inr query => cases query with
      | create _ _ _ | bundle _ | build _ _ => exact False.elim free
      | _ => rfl
  change result ∈ support (RegistrationNativePlatformMldsaTableCallback.arrange source <$>
    RegistrationNativePlatformMldsaTableProgram.runState source
      (RegistrationNativePlatformMldsaProfile.handler setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query) before.1.1 before.1.2 before.2) at supported
  rw [law, RegistrationNativePlatformMldsaTableProgram.run_lift, Functor.map_map, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact possible

/-- The actual corrected protected pending-Server response failure chooses its earlier generated Server row at the same callback cut. -/
theorem finish (fallback : Credential source) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner (handleSource source))
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (before after : State (n := n) (KemSK := KemSK) (Platform := Platform) source) (application : Pqxdh.Bytes)
    (safe : Safe source credential fallback before)
    (selectedOwner : before.1.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (keyProtected : pending.binding.server_pin.public_key = credential.publicKey)
    (supported : (.ok (some application), after) ∈ support
      ((callback source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer (.inr (.finish index (some packet)))).run before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before.1.1)))) :
    CacheHasCollision after.1.1.server.world.world.1.primitive.2 ∨
      ∃ ordinal, ordinal < before.2.attempts ∧ BornKey source before.2 ordinal credential.publicKey ∧
        ∃ forgery, observe source credential.publicKey (.inr (.finish index (some packet))) before (.ok (some application)) after = some forgery ∧
          Good source credential.publicKey after forgery := by
  obtain ⟨ordinal, earlier, born⟩ := born_key source before.2 safe.provenance credential fallback safe.server
  have supportedOriginal := original source setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer (.inr (.finish index (some packet))) trivial before (.ok (some application), after) supported
  rcases RegistrationNativePlatformResponseTypedOrigin.typed coins setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer index owner pending oneTime packet before.1.1 after.1.1 before.1.2 after.1.2 application
    selectedOwner phase supportedOriginal safe.cached absent with weak | collision
  · obtain ⟨forgery, chosen⟩ := RegistrationNativeMldsaTrialObserver.choose_complete source.verify credential.publicKey
      after.1.1.server.world.world.1.primitive.2 _ (by rw [← keyProtected]; rfl) weak
    have selected : observe source credential.publicKey (.inr (.finish index (some packet))) before (.ok (some application)) after = some forgery := by
      simpa only [observe, RegistrationNativeMldsaTrialObserver.observe, RegistrationNativeMldsaTrialObserver.trial,
        selectedOwner, phase, Option.bind_some] using chosen
    exact Or.inr ⟨ordinal, earlier, born, forgery, selected,
      RegistrationNativePlatformMldsaTableStop.captured source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer credential.publicKey fallback (.inr (.finish index (some packet))) before (.ok (some application), after)
        forgery safe supported selected⟩
  · exact Or.inl collision

end Actual
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProtectedCoverage


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProtectedCoverage.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProtectedCoverage.finish

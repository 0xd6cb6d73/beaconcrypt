-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver

/-! Successful original typed Init/response byte-origin failures at a protected displayed ML key are covered by the executable same-cut candidate observer or an actual retained shared-cache collision. This coverage adds no honest classical/PQ-field eligibility condition and claims unsigned payload origin, not signature-byte or CBOR uniqueness. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaEuf (PublicKey Forgery)
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationSigningShared.historyFor RegistrationAuthenticationNative.trial
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- The original protected-key Init acceptance failure is covered at its actual returned callback cut. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (publicKey : PublicKey) (packet : registration.InitPacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (session : Nat)
    (supported : (.ok (some session), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.accept packet))).run before))
    (key : packet.mldsa_public_key = publicKey)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true before.server.pin packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes packet.mldsa_public_key)
        (RegistrationNativeMldsaShared.nativeProject before)))) :
    (∃ forgery, RegistrationNativeMldsaTrialObserver.observe source.verify publicKey (.inr (.accept packet)) before
      (.ok (some session)) after = some forgery) ∨ CacheHasCollision after.server.world.world.1.primitive.2 := by
  rcases RegistrationNativeInitFinal.typed_origin_split setup checks wire route representation created credential packet
    before after session supported true rfl cached absent with weak | collision
  · apply Or.inl
    obtain ⟨forgery, chosen⟩ := RegistrationNativeMldsaTrialObserver.choose_complete source.verify publicKey
      after.server.world.world.1.primitive.2 _ (by rw [← key]; simp only [RegistrationAuthenticationNative.trial]) weak
    exact ⟨forgery, chosen⟩
  · exact Or.inr collision

/-- The original protected pending-Server response failure is covered at its actual returned callback cut. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (publicKey : PublicKey) (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) (packet : registration.ResponsePacket)
    (before after : RegistrationNativeExperiment.State n KemSK source) (application : Pqxdh.Bytes)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (supported : (.ok (some application), after) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
        (.inr (.finish index (some packet)))).run before))
    (key : pending.binding.server_pin.public_key = publicKey)
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
        (RegistrationNativeMldsaShared.nativeProject before)))) :
    (∃ forgery, RegistrationNativeMldsaTrialObserver.observe source.verify publicKey (.inr (.finish index (some packet))) before
      (.ok (some application)) after = some forgery) ∨ CacheHasCollision after.server.world.world.1.primitive.2 := by
  rcases RegistrationNativeResponseFinish.typed_origin_split setup checks representation created wire route credential
    index owner pending oneTime packet before after application selected phase supported true rfl cached absent with weak | collision
  · apply Or.inl
    obtain ⟨forgery, chosen⟩ := RegistrationNativeMldsaTrialObserver.choose_complete source.verify publicKey
      after.server.world.world.1.primitive.2 _ (by rw [← key]; rfl) weak
    refine ⟨forgery, ?_⟩
    simpa only [RegistrationNativeMldsaTrialObserver.observe, RegistrationNativeMldsaTrialObserver.trial,
      selected, phase, Option.bind_some] using chosen
  · exact Or.inr collision

end BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin.finish

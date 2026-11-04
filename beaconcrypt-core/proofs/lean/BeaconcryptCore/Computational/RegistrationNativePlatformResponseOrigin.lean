-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCompletionReceipt
import BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin

/-! Corrected assigned-ID finish retains the actual mandatory response trial and its hash receipt through the complete returned callback. Unsigned-origin failure is covered by the ordinary weak-forgery event or a literal shared-cache collision, with no completed partner or caller-supplied authentication premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend
open RegistrationNativeMldsaShared (Local lower project)
open RegistrationNativeResponseAuthentication (lower_pure)
open RegistrationNativePlatformCompletionReceipt (cut consumed)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativePlatformBeaconFinish.afterAuthentication
  RegistrationNativeBeaconFrontend.authentication RegistrationResponseExecutor.begin

/-- Every successful corrected source finish has its actual verification/hash receipt at the final shared cache. -/
theorem final_receipt (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before)) :
    ∃ owner pending oneTime received digest,
      before.1[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ packet = some received ∧
      RegistrationResponseExecutor.verification source.verify pending received digest = true ∧
      (project after).2 ((), (RegistrationResponseExecutor.payload pending received).transcript) = some digest := by
  obtain ⟨owner, pending, oneTime, aborted, authenticated, middle, selected, phase, _moved, called, continued⟩ :=
    cut setup checks representation created wire index packet before after application supported
  cases packet with
  | none =>
      rw [RegistrationResponseExecutor.begin_malformed, simulateQ_pure, lower_pure] at called
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at called
      cases called
  | some received =>
      have projected : (.ok (.Ok authenticated), project middle) ∈ support
          ((RegistrationResponseExecutor.execute setup.source.crypto source.verify wire.frameWrite
            (RawCtxSourceHkdf.kdfImpl setup.source) pending (.Some received)).run
              (project (consumed before index aborted))) := by
        rw [RegistrationResponseExecutor.execute,
          ← RegistrationNativeResponseAuthentication.program setup checks representation created wire, support_map]
        exact Set.mem_image_of_mem (Prod.map id project) called
      obtain ⟨digest, _same, verified, _receipts, _earlier, cached⟩ := RegistrationResponseExecutor.accepted_receipt
        setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)
        pending received (project (consumed before index aborted)) (project middle) authenticated projected
      have extension := RegistrationNativeWorldCache.localProgram setup checks representation created
        (RegistrationNativePlatformBeaconFinish.afterAuthentication setup wire index owner oneTime authenticated) middle (.ok (some application), after) continued
      exact ⟨owner, pending, oneTime, received, digest, selected, phase, rfl, verified, extension cached⟩

/-- The original complete native finish supplies an ordinary accepted verification trial using its returned cache and literal prior global signing prefix. -/
theorem accepted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket) (before after : Local n KemSK source)
    (application : Pqxdh.Bytes)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index packet)).run before))
    (protectedKey : Bool) (honest : protectedKey = true) :
    ∃ owner pending oneTime received,
      before.1[index]? = some owner ∧ owner.phase = .initSent pending oneTime ∧ packet = some received ∧
      MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash (project after).2) source.verify
        (RegistrationResponseExecutor.trial protectedKey pending received
          (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
            (project before))) := by
  obtain ⟨owner, pending, oneTime, received, digest, selected, phase, same, verified, cached⟩ :=
    final_receipt setup checks representation created wire index packet before after application supported
  refine ⟨owner, pending, oneTime, received, selected, phase, same, honest, ?_, ?_, ?_⟩
  · simpa only [RegistrationResponseExecutor.trial, PqxdhRefinement.absBytes, List.length_map,
      Std.UScalar.ofNatCore_val_eq] using pending.binding.server_pin.public_key.property
  · simpa only [RegistrationResponseExecutor.trial, PqxdhRefinement.absBytes, List.length_map,
      Std.UScalar.ofNatCore_val_eq] using received.signature.property
  · change source.verify (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
      Pqxdh.TranscriptAuth.signingContext (Pqxdh.TranscriptAuth.signatureInput .server
        (MldsaSharedAuthentication.cacheHash (project after).2
          (RegistrationResponseExecutor.payload pending received).transcript)) (PqxdhRefinement.absBytes received.signature) = true
    rw [MldsaSharedAuthentication.cache_hash_reconstruct _ _ digest cached]
    exact verified

/-- A protected displayed pending Server key outside the earlier unsigned prefix yields an actual same-cut forgery or cache collision. -/
theorem origin_split (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (owner : Owner source) (pending : registration.BeaconPending)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (received : registration.ResponsePacket)
    (before after : Local n KemSK source) (application : Pqxdh.Bytes)
    (selected : before.1[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (supported : (.ok (some application), after) ∈ support
      ((lower setup checks representation created
        (RegistrationNativePlatformBeaconFinish.finish setup source wire index (some received))).run before))
    (cached : RegistrationSigningShared.Cached (project before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial true pending received
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) (project before)))) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash (project after).2) source.verify
      (RegistrationResponseExecutor.trial true pending received
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key) (project before))) ∨
      CacheHasCollision (project after).2 := by
  obtain ⟨other, otherPending, otherTime, otherPacket, found, reached, packet, trial⟩ :=
    accepted setup checks representation created wire index (some received) before after application supported true rfl
  have ownerSame : other = owner := Option.some.inj (found.symm.trans selected)
  subst other
  have phaseSame := reached.symm.trans phase
  cases phaseSame
  cases Option.some.inj packet
  rcases MldsaTranscriptAuth.origin_failure_split _ _ _ ⟨trial, absent⟩ with forgery | collision
  · exact Or.inl forgery
  · apply Or.inr
    obtain ⟨other, otherPending, otherTime, otherPacket, digest, found, reached, packet, _verified, hashed⟩ :=
      final_receipt setup checks representation created wire index (some received) before after application supported
    have ownerSame : other = owner := Option.some.inj (found.symm.trans selected)
    subst other
    have phaseSame := reached.symm.trans phase
    cases phaseSame
    cases Option.some.inj packet
    have extension := RegistrationNativeWorldCache.localProgram setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index (some received)) before
      (.ok (some application), after) supported
    apply MldsaSharedAuthentication.transcript_collision_cached _ _ ?_ ⟨digest, hashed⟩ collision
    intro call member
    obtain ⟨value, receipt⟩ := RegistrationSigningShared.history_cached _ _ cached call member
    exact ⟨value, extension receipt⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin.final_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin.final_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin.accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin.origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseOrigin.origin_split

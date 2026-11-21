-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeLowerGenerated

/-! Actual native finish success retains the reached root-bearing agreement, its equality to the matched consumed-token root, the real Beacon initializer, the consumed sequence-one receive kernel, metadata and returned application. Captured private-row provenance is derived through the actual authentication cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeFinishRootReceipt
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRootTableInitialization (rootArray)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower project)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Successful original lower-level finish supplies its actual initial capability and consumed kernel using the root derived from the matched earlier token. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owner : Owner source)
    (original : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes)
    (before after : Local n KemSK source)
    (found : before.1[index]? = some owner) (phase : owner.phase = .initSent original oneTime)
    (supported : (.ok (some application), after) ∈ support ((lower setup checks representation created
      (RegistrationNativeBeaconFrontend.finish setup source wire index (some packet))).run before))
    (prior : RegistrationNativeKemBirthInvariant.Holds setup before.1 before.2.2.pool)
    (coherent : original.control.expected_server_binding = original.binding.server_pin.binding)
    (token : peer.ConsumedRegistration) (pin : session.ServerAuthenticationPin) (cache : CtxRomAuth.CtxRO.QueryCache)
    (serverReceipt : RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token pin cache)
    (prekey : owner.prekeyPublic = rootArray (setup.dh.publicKey owner.prekeyScalar))
    (serverIdentity : packet.public.identity_key = rootArray (setup.joint.publicKeys created.seed).ed25519)
    (ephemeral : packet.public.ephemeral_key = token.agreement.pending.ephemeral_public_key)
    (ciphertext : packet.public.kem_cipher_text = token.agreement.pending.kem_ciphertext)
    (correct : RegistrationNativePairedCoordinates.RecipientCorrect setup) :
    ∃ (capability : agreement.BeaconAgreement) (established : registration.CompletedBeacon)
      (initial : registration.BeaconInitialKdf) (aead : registration.BeaconRecordAead) (plaintext : Slice U8)
      (adDigest : CtxRomAuth.CtxDigest),
      token.agreement.root.bytes = capability.root.bytes ∧
      capability.binding = RegistrationResponseExecutor.completedBinding original adDigest ∧
      established.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding (RegistrationResponseExecutor.completedBinding original adDigest) capability.candidate.assigned_key_id ∧
      registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested aead) ∧
      aead.agreement = capability ∧
      aead.pending.finish (.Some plaintext) = .ok (established.kernel,
        .Some (⟨plaintext, capability.candidate.server_binding.identity_key_id, 1#u64⟩ : record.OpenedRecord (Slice U8))) ∧
      established.application = plaintext.drop 8#usize ∧ application = TranscriptAuthParts.absSlice established.application := by
  obtain ⟨cutOwner, cutPending, cutOneTime, aborted, authenticated, middle,
      selected, cutPhase, _moved, called, continued⟩ :=
    RegistrationNativeResponseFinish.cut setup checks representation created wire index (some packet) before after application supported
  have ownerEq : cutOwner = owner := Option.some.inj (selected.symm.trans found)
  subst cutOwner
  have phases : RegistrationNativeBeaconFrontend.Phase.initSent cutPending cutOneTime = .initSent original oneTime := cutPhase.symm.trans phase
  cases phases
  have projected : (.ok (.Ok authenticated), project middle) ∈ support
      ((RegistrationResponseExecutor.execute setup.source.crypto source.verify wire.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) original (.Some packet)).run
          (project (RegistrationNativeResponseFinish.consumed before index aborted))) := by
    rw [RegistrationResponseExecutor.execute, ← RegistrationNativeResponseAuthentication.program setup checks representation created wire, support_map]
    exact Set.mem_image_of_mem (Prod.map id project) called
  obtain ⟨_digest, same, _verified, _receipts, _earlier, _cached⟩ := RegistrationResponseExecutor.accepted_receipt
    setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) original packet
    (project (RegistrationNativeResponseFinish.consumed before index aborted)) (project middle) authenticated projected
  obtain ⟨adDigest, same⟩ := same
  subst authenticated
  obtain ⟨generatedPool, owned⟩ := RegistrationNativeLowerGenerated.owner setup checks representation created before.1 owner
    (List.mem_of_getElem? found) _ (RegistrationNativeResponseFinish.consumed before index aborted) middle _ prior called
  obtain ⟨capability, established, agreed, recorded, _installed, agreedSupport, recordSupport, _inserted, returned⟩ :=
    RegistrationNativeCompletionReceipt.completion_cut setup checks representation created wire index owner oneTime
      (RegistrationResponseExecutor.acceptedResponse original packet adDigest) middle after application continued
  have rootEq := RegistrationNativeStagedRootAgreement.root setup checks wire route representation created owner oneTime
    token pin cache serverReceipt (RegistrationResponseExecutor.acceptedResponse original packet adDigest)
    (by simpa only [RegistrationResponseExecutor.acceptedResponse, RegistrationResponseExecutor.completedBinding_pin] using coherent) capability middle agreed agreedSupport
    generatedPool owned prekey serverIdentity ephemeral ciphertext correct
  have binding := RegistrationNativeCompletionReceipt.binding setup checks representation created owner oneTime
    (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability middle agreed agreedSupport
  obtain ⟨metadata, initial, aead, plaintext, started, initialSame, reached, sameAgreement, kernel, message⟩ :=
    RegistrationNativeCompletionReceipt.record_consumed setup checks representation created wire capability established agreed recorded recordSupport
  exact ⟨capability, established, initial, aead, plaintext, adDigest, rootEq, binding,
    by simpa only [binding, RegistrationResponseExecutor.acceptedResponse] using metadata, started, initialSame, reached, sameAgreement, kernel, message, returned⟩

end BeaconcryptCore.Computational.RegistrationNativeFinishRootReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishRootReceipt.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishRootReceipt.finish

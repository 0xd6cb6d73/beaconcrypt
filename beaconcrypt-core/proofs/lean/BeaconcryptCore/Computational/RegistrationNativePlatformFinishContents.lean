-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCompletionContents

/-! Actual corrected assigned-ID Platform finish derives complete first-record contents agreement through its mandatory incoming response authentication, original agreement/record cores and actual copy/install suffix. The earlier Server record remains a concrete source cut, without claiming completed Server peer installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformFinishContents
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower project)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

/-- Corrected finish derives actual AD151, sender, assigned ID, returned application and complete populated binding from its actual response and earlier concrete record issuance. -/
theorem finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (owner : Owner source) (original : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (index : Nat) (packet : registration.ResponsePacket) (application : Pqxdh.Bytes) (before after : Local n KemSK source)
    (found : before.1[index]? = some owner) (phase : owner.phase = .initSent original oneTime)
    (supported : (.ok (some application), after) ∈ support ((lower setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index (some packet))).run before))
    (coherent : original.control.expected_server_binding = original.binding.server_pin.binding)
    (serverInitial : registration.ServerInitialKdf) (hashed : registration.ServerResponseHash) (cache : CtxRomAuth.CtxRO.QueryCache)
    (issued : RegistrationNativeServerRecordIssuance.RecordCut (n := n) setup (RegistrationNativeWire.ledgerCodec wire) serverInitial hashed cache)
    (extension : RegistrationNativeWorldCache.cache after.2.2 ≤ cache)
    (ciphertext : hashed.ciphertext = packet.application) (collisionFree : ¬ CacheHasCollision cache) :
    ∃ adDigest capability completed, RegistrationNativeCompletionContents.Outcome serverInitial (RegistrationResponseExecutor.acceptedResponse original packet adDigest) capability completed application := by
  obtain ⟨cutOwner, cutPending, cutOneTime, aborted, authenticated, middle,
      selected, cutPhase, _moved, called, continued⟩ :=
    RegistrationNativePlatformCompletionReceipt.cut setup checks representation created wire index (some packet) before after application supported
  have ownerEq : cutOwner = owner := Option.some.inj (selected.symm.trans found)
  subst cutOwner
  have phases : RegistrationNativeBeaconFrontend.Phase.initSent cutPending cutOneTime = .initSent original oneTime := cutPhase.symm.trans phase
  cases phases
  have projected : (.ok (.Ok authenticated), project middle) ∈ support
      ((RegistrationResponseExecutor.execute setup.source.crypto source.verify wire.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) original (.Some packet)).run
          (project (RegistrationNativePlatformCompletionReceipt.consumed before index aborted))) := by
    rw [RegistrationResponseExecutor.execute, ← RegistrationNativeResponseAuthentication.program setup checks representation created wire, support_map]
    exact Set.mem_image_of_mem (Prod.map id project) called
  obtain ⟨_digest, same, _verified, _receipts, _earlier, _cached⟩ := RegistrationResponseExecutor.accepted_receipt
    setup.source.crypto source.verify wire.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) original packet
    (project (RegistrationNativePlatformCompletionReceipt.consumed before index aborted)) (project middle) authenticated projected
  obtain ⟨adDigest, same⟩ := same
  subst authenticated
  refine ⟨adDigest, ?_⟩
  exact RegistrationNativeCompletionContents.platform setup checks wire representation created index owner oneTime (RegistrationResponseExecutor.acceptedResponse original packet adDigest)
    (by simpa only [RegistrationResponseExecutor.acceptedResponse, RegistrationResponseExecutor.completedBinding_pin] using coherent)
    serverInitial hashed middle after cache application issued continued extension ciphertext collisionFree

end BeaconcryptCore.Computational.RegistrationNativePlatformFinishContents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformFinishContents.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformFinishContents.finish

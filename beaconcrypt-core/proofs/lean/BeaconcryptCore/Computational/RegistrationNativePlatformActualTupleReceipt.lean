-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformAcceptActualToken
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenCacheSource
import BeaconcryptCore.Computational.RegistrationNativePlatformPendingTuple
import BeaconcryptCore.Computational.RegistrationNativeMatchedServerInput

/-! The actual evaluated accept's own source pin, authentication and Root collector determine the matched public tuple of a retained token. The original pending hash and common-cache collision exclusion identify that tuple, while the actual collector-to-log association remains retained by the source cut. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformActualTupleReceipt
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Platform : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationServerNativeSource.authenticate RegistrationServerNativeSource.agree
  RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformSourceBuild.pin

/-- Actual source pin/authentication, the token's own Root receipt and the original pending hash derive the matched Server input without perfect recipient correctness or a desired root equality. -/
theorem receipt (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (before after : RegistrationNativeKemServerState.State n source) (previous finalPlatform : Platform)
    (handle : Nat) (log : RegistrationNativeKemCountedServerTrace.Log KemSK)
    (cut : RegistrationNativePlatformAcceptActualToken.SourceCut setup (RegistrationNativeWire.ledgerCodec wire) checks route representation created
      packet before after previous finalPlatform handle log)
    (cachedPin : RegistrationNativeServerPinRecompute.Cached before.server.pin before.server.world.world.1.primitive.2)
    (token : peer.ConsumedRegistration) (tokenEq : token.agreement = cut.receipt.root.accepted)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (cache : CtxRomAuth.CtxRO.QueryCache) (extension : after.server.world.world.1.primitive.2 ≤ cache)
    (tuple : cut.receipt.authenticated.registration = {
      beacon_identity_public_key := PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519,
      beacon_prekey_public_key := owner.prekeyPublic,
      beacon_one_time_public_key := PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime),
      beacon_pq_public_key := RegistrationNativeBeaconFrontend.pqArray owner.kemPublic }) :
    Nonempty (RegistrationNativeMatchedServerInput.Receipt (n := n) setup checks wire route representation created owner oneTime token before.server.pin cache) := by
  obtain ⟨_pin, stored, checked⟩ := RegistrationNativePlatformTokenCacheSource.authentication RegistrationNativePlatformMldsaProgram.coins
    setup (RegistrationNativeWire.ledgerCodec wire) route source.verify created packet before.server cut.current.server cut.receipt.afterCheck.server
      previous cut.currentPlatform cut.receipt.checkPlatform cut.pin cut.receipt.events cut.receipt.authenticated cachedPin cut.pinned cut.authenticated
  have agreed := RegistrationNativePlatformAcceptActualToken.agreed_native setup checks representation created packet cut.receipt.authenticated
    handle after finalPlatform log cut.receipt.root
  rw [cut.beforeEq, ← tokenEq] at agreed
  have root : RegistrationNativeTokenRootReceipt.Input setup checks representation created packet cut.receipt.authenticated
      cut.receipt.afterCheck.server cut.receipt.root.afterAgreement.server token.agreement := by
    have actual := cut.receipt.root.root.nativeInput
    rw [cut.beforeEq, ← tokenEq] at actual
    exact actual
  have summary := RegistrationNativePlatformAcceptActualToken.SourceCut.summary setup (RegistrationNativeWire.ledgerCodec wire) checks route representation
    created packet before after previous finalPlatform handle log cut
  have cacheEq : cut.receipt.afterCheck.server.world.world.1.primitive.2 = after.server.world.world.1.primitive.2 :=
    congrArg (fun value : RegistrationSigningShared.State => value.2) summary
  have authExtension : cut.receipt.afterCheck.server.world.world.1.primitive.2 ≤ cache := by rw [cacheEq]; exact extension
  exact ⟨⟨cut.current.server, packet, cut.receipt.events, cut.receipt.authenticated, cut.receipt.afterCheck.server,
    cut.receipt.root.afterAgreement.server, checked, agreed, root, tuple, stored, authExtension⟩⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformActualTupleReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformActualTupleReceipt.receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformActualTupleReceipt.receipt

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationSupport
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicationConcrete
import BeaconcryptCore.Computational.RegistrationNativePrekeyPublication
import BeaconcryptCore.Computational.RegistrationNativeBeaconPublication
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicationSupport (Possible)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Platform E Auxiliary : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "writer" => RegistrationNativePlatformPublicFrontend.writer (n := n) (KemSK := KemSK) (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "encode" => RegistrationNativePlatformGenericBundle.encoderWith (source := source) (Auxiliary := Auxiliary) writer
local notation "pureEncode" => (fun view => core.option.Option.Some (RegistrationNativeSourceWriterReadback.initVector view))

private theorem encoding (view : registration.InitView) (bytes : alloc.vec.Vec U8)
    (possible : Possible (encode view) (.ok (.Some bytes))) : pureEncode view = .Some bytes := by
  obtain ⟨owners, env, previous, result, supported, returned⟩ := possible
  exact congrArg core.option.Option.Some
    (RegistrationNativePlatformPublicationConcrete.encoder reserve view owners env previous result supported bytes returned).symm

/-- Actual successful dynamic publication preserves the captured owner's original prekey bytes and derives concrete source readback internally. -/
theorem publication (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform))
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (published : registration.PublishedBeaconInit (alloc.vec.Vec U8))
    (possible : Possible (RegistrationNativePlatformBeaconPublication.begin
      (fun query => RegistrationNativePlatformGenericBundle.liftLegacy trusted
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
      encode ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
      (.ok (.Ok published))) :
    ∃ packet, RegistrationNativeWire.readInit RegistrationNativePlatformConcreteSource.wire
        (TranscriptAuthParts.absSlice published.encoded) = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.prekeyPublic) := by
  have sourceReceipt := RegistrationNativePlatformPublicationSupport.begin
    (fun query => RegistrationNativePlatformGenericBundle.liftLegacy trusted
      (RegistrationNativeBeaconFrontend.outgoing setup source index owner query))
    encode pureEncode (encoding reserve) ⟨owner.pin.binding⟩ (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin published possible
  have receipt := RegistrationNativePrekeyPublication.begin_key pureEncode ⟨owner.pin.binding⟩
    (RegistrationNativeBeaconFrontend.inputs setup owner)
    ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin published sourceReceipt
  have retained : RegistrationNativePrekeyPublication.PublishedKey pureEncode
      (PqxdhPhase2InputBytes.word owner.prekeyPublic) published := by
    simpa only [RegistrationNativeBeaconFrontend.inputs] using receipt
  obtain ⟨view, written, payload⟩ := retained
  have bytesEq := Option.some.inj written
  refine ⟨RegistrationNativeWire.initPacket view, ?_, payload⟩
  rw [← bytesEq]
  exact RegistrationNativePlatformPublicationConcrete.decoded view

private theorem publication_reply
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform))
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (reply : RustM (RegistrationBeaconInitExecutor.Result (alloc.vec.Vec U8))) (bytes : alloc.vec.Vec U8)
    (possible : Possible (match reply with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok finished) => do
          RegistrationNativePlatformGenericBundle.liftLegacy trusted
            (RegistrationNativeBeaconFrontend.updatePhase index (.initSent finished.pending oneTime))
          let _ ← RegistrationNativePlatformGenericBundle.liftLegacy trusted
            (RegistrationNativeBeaconFrontend.effect (.inr (.advanceOwner owner.worldOwner .initSent)))
          pure (.ok (some finished.encoded)) : RegistrationNativePlatformGenericBundle.M source Auxiliary
            (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) (RustM (Option (alloc.vec.Vec U8))))
      (.ok (some bytes))) :
    ∃ finished, reply = .ok (.Ok finished) ∧ finished.encoded = bytes := by
  obtain ⟨owners, env, previous, result, supported, returned⟩ := possible
  cases reply with
  | fail error | div =>
    simp only [StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    cases returned
  | ok selected => cases selected with
    | Err error =>
      simp only [StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      cases returned
    | Ok finished =>
      simp only [StateT.run_bind, StateT.run_pure, mem_support_bind_iff] at supported
      obtain ⟨phase, _changed, advanced, _marked, literal⟩ := supported
      obtain rfl := eq_of_mem_support_pure _ literal
      exact ⟨finished, rfl, Option.some.inj (RustM.ok.inj returned)⟩

/-- A successful concrete dynamic bundle decodes to its captured owner's original signed prekey payload, including fresh and stored-coin entry branches. -/
theorem bundle (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform))
    (index : Nat) (owners : RegistrationNativeBeaconFrontend.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativeBeaconFrontend.State source) × EnvState Auxiliary) × Platform)
    (bytes : alloc.vec.Vec U8) (returned : result.1.1.1 = .ok (some bytes))
    (supported : result ∈ support ((((RegistrationNativePlatformGenericBundle.bundle trusted setup source encode index).run owners).run env).run previous)) :
    ∃ owner packet, owners[index]? = some owner ∧
      RegistrationNativeWire.readInit RegistrationNativePlatformConcreteSource.wire (TranscriptAuthParts.absSlice bytes) = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.prekeyPublic) := by
  simp only [RegistrationNativePlatformGenericBundle.bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none =>
    simp only [found, StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    cases returned
  | some owner =>
    simp only [found] at supported
    cases phase : owner.phase with
    | initSent _ _ | established _ | aborted _ =>
      simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      cases returned
    | fresh =>
      simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨sampled, _sampledCall, published, called, continued⟩ := supported
      obtain ⟨finished, replyEq, encoded⟩ := publication_reply trusted index owner sampled.1.1.1 published.1.1.1 bytes
        ⟨published.1.1.2, published.1.2, published.2, result, (by
          cases valueEq : published.1.1.1 with
          | fail error => simpa only [valueEq] using continued
          | div => simpa only [valueEq] using continued
          | ok outcome => cases outcome <;> simpa only [valueEq] using continued), returned⟩
      obtain ⟨packet, decoded, key⟩ := publication reserve setup trusted index owner sampled.1.1.1 finished
        ⟨sampled.1.1.2, sampled.1.2, sampled.2, published, called, replyEq⟩
      exact ⟨owner, packet, rfl, encoded ▸ decoded, key⟩
    | freshWithCoins oneTime =>
      simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨published, called, continued⟩ := supported
      obtain ⟨finished, replyEq, encoded⟩ := publication_reply trusted index owner oneTime published.1.1.1 bytes
        ⟨published.1.1.2, published.1.2, published.2, result, (by
          cases valueEq : published.1.1.1 with
          | fail error => simpa only [valueEq] using continued
          | div => simpa only [valueEq] using continued
          | ok outcome => cases outcome <;> simpa only [valueEq] using continued), returned⟩
      obtain ⟨packet, decoded, key⟩ := publication reserve setup trusted index owner oneTime finished
        ⟨owners, env, previous, published, called, replyEq⟩
      exact ⟨owner, packet, rfl, encoded ▸ decoded, key⟩

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = (fun result => (f result.1, result.2)) <$> work before := StateT.run_map f work before

/-- Public selected-scalar packing retains the captured owner's exact concrete signed PQ publication and source bytes. -/
theorem public_bundle (setup : Setup base KemSK)
    (trusted : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform))
    (selected index : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) × Platform)
    (bytes : alloc.vec.Vec U8) (returned : result.1.1.1 = .ok (some bytes))
    (supported : result ∈ support ((((RegistrationNativePlatformPublicOwners.bundle trusted writer setup source selected publicPrekey index).run owners).run env).run previous)) :
    ∃ owner packet, owners[index]? = some owner ∧
      RegistrationNativeWire.readInit RegistrationNativePlatformConcreteSource.wire (TranscriptAuthParts.absSlice bytes) = some packet ∧
      (PqxdhRefinement.absBytes packet.pre_key).drop 64 = PqxdhEd25519EufCma.prekeyMessage (PqxdhPhase2InputBytes.word owner.view.prekeyPublic) := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, support_map] at supported
  obtain ⟨middle, called, same⟩ := supported
  have reply : middle.1.1.1 = .ok (some bytes) := (congrArg (fun output => output.1.1.1) same).trans returned
  obtain ⟨restored, packet, found, decoded, key⟩ := bundle reserve setup trusted index
    (owners.map RegistrationNativePublicOwners.restore) env previous middle bytes reply called
  simp only [List.getElem?_map, Option.map_eq_some_iff] at found
  obtain ⟨owner, found, rfl⟩ := found
  exact ⟨owner, packet, found, decoded, key⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey.publication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey.publication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey.bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey.bundle

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey.public_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationBundlePrekey.public_bundle

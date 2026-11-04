-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceOwnerCallbacks
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAcceptRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicRecordNative
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicBuildTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicOtherNative
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceGood
/-! Every actual corrected adaptive public callback restores the literal current fixed-scalar runtime command. Internal canonical-owner, pending-coherence, live-token and source-memo facts come from actual generated startup and source execution. No public event is conditioned on these internal facts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceQueries
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceState (roots restore project nativeView owners)
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativePlatformPublicSourceGood (Good)
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

/-- Actual typed callbacks use the complete final runtime source state and the same persistent platform poststate. -/
theorem query [primitive : AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (selectedOwner selectedAccept : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (command : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State n KemSK Platform source)
    (good : Good setup created.seed scalar selectedOwner before) :
    (fun result => ((result.1, project (roots setup created.seed scalar) scalar result.2.1.1 result.2.2), result.2.1.2)) <$>
      (execute setup (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential) created.seed scalar
        (RegistrationNativePlatformPublicFrontend.handler setup checks (canonicalWire wire) source
          (RegistrationNativeMldsa.owned source credential) selectedOwner selectedAccept (setup.dh.publicKey scalar)
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer command)).run before =
      (fun result => ((result.1.1, nativeView result.1.2), result.2)) <$>
        ((RegistrationNativePlatformOrdinaryScalarEager.handler setup checks wire route representation created source credential view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar command).run
          (restore (roots setup created.seed scalar) scalar before.1.1 before.2)).run before.1.2 := by
  cases command with
  | inl coin =>
    convert RegistrationNativePlatformPublicOtherNative.effect setup (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential)
      created.seed scalar (roots setup created.seed scalar) (.inl coin) before using 1 <;> rfl
  | inr command => cases command with
    | create edPin mlPin keyId =>
      convert RegistrationNativePlatformPublicSourceOwnerCallbacks.create setup checks (canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner selectedAccept scalar (roots setup created.seed scalar)
        edPin mlPin keyId before good.owners.1 using 1; rfl
    | bundle index =>
      convert RegistrationNativePlatformPublicSourceOwnerCallbacks.bundle setup checks (canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner selectedAccept scalar (roots setup created.seed scalar)
        index before good.owners.1 using 1; rfl
    | accept packet =>
      exact RegistrationNativePlatformPublicAcceptRuntime.typed setup checks wire route representation created credential correct
        selectedOwner selectedAccept scalar view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer packet before
    | build handle application =>
      exact RegistrationNativePlatformPublicBuildTyped.build setup checks wire route representation created credential
        selectedOwner selectedAccept scalar view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer handle application before good.live good.memo
    | finish index packet =>
      exact RegistrationNativePlatformPublicFinishRuntime.finish setup checks wire route representation created credential selectedOwner selectedAccept scalar
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer index packet before
        ((RegistrationNativePublicInvariantOwners.restored_holds scalar before.1.1.beacons).mp good.owners.2)
    | hmac key bytes =>
      change (pure ((setup.hmac.eval key bytes, project (roots setup created.seed scalar) scalar before.1.1 before.2), before.1.2) : ProbComp _) =
        pure ((setup.hmac.eval key bytes, nativeView (restore (roots setup created.seed scalar) scalar before.1.1 before.2)), before.1.2)
      rfl
    | hash bytes =>
      convert RegistrationNativePlatformPublicOtherNative.effect setup (canonicalWire wire) route (RegistrationNativeMldsa.owned source credential)
        created.seed scalar (roots setup created.seed scalar) (.inr (.hash bytes)) before using 1 <;> rfl
    | serverSend keyId plaintext =>
      convert RegistrationNativePlatformPublicRecordNative.record setup wire route (RegistrationNativeMldsa.owned source credential)
        created.seed scalar (roots setup created.seed scalar) reserveFrame (.inl (.inl (plaintext, keyId))) before using 1 <;> rfl
    | serverRaw raw =>
      convert RegistrationNativePlatformPublicRecordNative.record setup wire route (RegistrationNativeMldsa.owned source credential)
        created.seed scalar (roots setup created.seed scalar) reserveFrame (.inl (.inr raw)) before using 1 <;> rfl
    | beaconSend owner plaintext =>
      convert RegistrationNativePlatformPublicRecordNative.record setup wire route (RegistrationNativeMldsa.owned source credential)
        created.seed scalar (roots setup created.seed scalar) reserveFrame (.inr (owner, .inl plaintext)) before using 1 <;> rfl
    | beaconRaw owner raw =>
      convert RegistrationNativePlatformPublicRecordNative.record setup wire route (RegistrationNativeMldsa.owned source credential)
        created.seed scalar (roots setup created.seed scalar) reserveFrame (.inr (owner, .inr raw)) before using 1 <;> rfl
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceQueries

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceQueries.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceQueries.query

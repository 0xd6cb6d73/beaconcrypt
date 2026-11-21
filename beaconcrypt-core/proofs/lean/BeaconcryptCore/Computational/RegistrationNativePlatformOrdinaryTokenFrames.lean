-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformTokenFrames

/-! Actual dynamic ordinary routing changes the source World and platform while preserving native owner metadata, private KEM pool and token table. These are literal state-lens facts for every outcome, including failed writer reservations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeTokenSource (Present)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def fields (before : Native) := (before.server.sessions, before.pool, before.beacons)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : X → Y) (work : StateT S m X) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

private theorem world (work : RegistrationNativePlatformOrdinaryWorld.M n Platform Value)
    (before after : Native) (previous next : Platform) (reply : Value)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.world work).run before).run previous)) :
    fields after = fields before := by
  simp only [RegistrationNativePlatformOrdinaryExperiment.world, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  have afterEq : after = RegistrationNativePlatformOrdinaryExperiment.replaceWorld before inner.1.2 :=
    (congrArg (fun result => result.1.2) same).symm
  rw [afterEq]
  rfl

/-- Full ordinary routing preserves every native token, recipient handle and owner phase, including writer rejection. -/
theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before after : Native) (previous next : Platform) (reply : (PqxdhRecordLiftInterface.RecordSpec .O).Range query)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route query source).run before).run previous)) :
    fields after = fields before := by
  cases query with
  | inl query => exact world _ before after previous next reply supported
  | inr query =>
      rcases query with ⟨owner, request⟩
      cases request with
      | inl plaintext =>
          cases found : before.beacons[owner]? with
          | none =>
              simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run] at supported
              rw [found] at supported
              exact congrArg (fun result => fields result.1.2) supported
          | some selected =>
              simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run] at supported
              rw [found] at supported
              exact world _ before after previous next reply supported
      | inr raw =>
          cases found : before.beacons[owner]? with
          | none =>
              simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run] at supported
              rw [found] at supported
              exact congrArg (fun result => fields result.1.2) supported
          | some selected =>
              simp only [RegistrationNativePlatformOrdinaryExperiment.record, StateT.run] at supported
              rw [found] at supported
              exact world _ before after previous next reply supported

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
attribute [local irreducible] RegistrationNativeExperiment.handler

/-- Every runtime callback outside accept only inherits prior tokens, for the single selected dynamic-writer profile. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (allowed : RegistrationNativeTokenCacheTrace.NonAccept query)
    (before after : Native) (previous next : Platform) (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : ((reply, after), next) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before).run previous))
    (token : peer.ConsumedRegistration) (present : Present token after.server) : Present token before.server := by
  have ordinary (same : RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query =
      RegistrationNativePlatformExperiment.handler (n := n) RegistrationNativePlatformMldsaProgram.coins setup checks
        (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential view failure allocation
          reserveRegistration reservePeer erased helper writer query) : Present token before.server := by
    rw [same] at supported
    exact RegistrationNativePlatformTokenFrames.handler RegistrationNativePlatformMldsaProgram.coins setup checks
      (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer query allowed before after previous next reply supported token present
  have routed (query : PqxdhRecordLiftInterface.RecordQuery) (reply : (PqxdhRecordLiftInterface.RecordSpec .O).Range query)
      (called : ((reply, after), next) ∈ support
        (((RegistrationNativePlatformOrdinaryExperiment.record setup wire reserveFrame route query source).run before).run previous)) : Present token before.server := by
    have same : after.server.sessions = before.server.sessions := congrArg Prod.fst (record (n := n) setup wire reserveFrame route query before after previous next reply called)
    simpa only [Present, same] using present
  cases query with
  | inl coin => exact ordinary rfl
  | inr command =>
      cases command with
      | serverSend keyId plaintext => exact routed (.inl (.inl (plaintext, keyId))) _ supported
      | serverRaw raw => exact routed (.inl (.inr raw)) _ supported
      | beaconSend owner plaintext => exact routed (.inr (owner, .inl plaintext)) _ supported
      | beaconRaw owner raw => exact routed (.inr (owner, .inr raw)) _ supported
      | _ => exact ordinary rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames.record

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryTokenFrames.handler

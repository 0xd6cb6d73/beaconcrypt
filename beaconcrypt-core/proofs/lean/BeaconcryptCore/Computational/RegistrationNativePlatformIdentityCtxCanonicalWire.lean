-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTyped
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryPrimitives
/-! The actual dynamic source frame writer makes the mathematical fallback frame encoder operationally irrelevant. This is derived from each literal source primitive and then the current typed dispatcher, preserving every allocator failure and complete persistent state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
variable (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
local notation "canonical" => RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec" => RegistrationNativeWire.ledgerCodec wire
local notation "canonicalCodec" => RegistrationNativeWire.ledgerCodec canonical

/-- Each source ordinary primitive uses the actual dynamic writer; all other leaves omit the fallback frame encoder. -/
theorem primitives (query : RawCtxMixedOwner.NativeSpec.Domain) :
    RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup canonicalCodec reserve query =
      RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup codec reserve query := by
  rcases query with request | input | opening | bytes | frame
  all_goals rfl

/-- Both ordinary role paths retain exactly the same source program and all persistent allocator outcomes. -/
theorem ordinary (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) :
    RegistrationNativePlatformCtxOrdinaryWorld.guarded setup canonicalCodec reserve route query =
      RegistrationNativePlatformCtxOrdinaryWorld.guarded setup codec reserve route query := by
  have dictionary : RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup canonicalCodec reserve =
      RegistrationNativePlatformCtxOrdinaryPrimitives.primitives setup codec reserve := funext (primitives setup wire reserve)
  rcases query with created | effect | (send | raw) | ⟨owner,send | raw⟩
  · rfl
  · rfl
  all_goals funext before
  all_goals simp only [RegistrationNativePlatformCtxOrdinaryWorld.guarded,RegistrationNativePlatformCtxOrdinaryWorld.handler,StateT.run]
  all_goals first
    | (unfold RegistrationNativePlatformCtxOrdinaryWorld.serverStep; rw [dictionary]; rfl)
    | (unfold RegistrationNativePlatformCtxOrdinaryWorld.beaconStep; rw [dictionary]; rfl)

private theorem guardedContext (route : RawCtxServerRouting.SenderDecoder) :
    RegistrationNativePlatformCtxContext.guarded (n := n) setup canonicalCodec reserve route =
      RegistrationNativePlatformCtxContext.guarded setup codec reserve route := by
  funext query
  exact congrArg RegistrationNativePlatformCtxContext.world (ordinary setup wire reserve route query)

/-- Actual indexed owner routing preserves the same source record program for both mathematical fallback encoders. -/
theorem records (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : PqxdhRecordLiftInterface.RecordQuery) :
    RegistrationNativePlatformCtxCommands.record (n := n) setup canonicalCodec reserve route owners query =
      RegistrationNativePlatformCtxCommands.record setup codec reserve route owners query := by
  have dictionary := guardedContext (n := n) setup wire reserve route
  rcases query with request | ⟨owner,plaintext | raw⟩
  all_goals simp only [RegistrationNativePlatformCtxCommands.record,dictionary]

/-- Coins, hashes and all four actual record commands derive literal dictionary equality rather than a source-codec premise. -/
theorem commands (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    RegistrationNativePlatformCtxCommands.command (n := n) setup canonicalCodec reserve route owners query =
      RegistrationNativePlatformCtxCommands.command setup codec reserve route owners query := by
  have dictionary := guardedContext (n := n) setup wire reserve route
  cases query with
  | inl coin => exact congrFun dictionary (.inr (.inl (.inl coin)))
  | inr query =>
      cases query with
      | serverSend keyId plaintext => exact records (n := n) setup wire reserve route owners (.inl (.inl (plaintext,keyId)))
      | serverRaw raw => exact records (n := n) setup wire reserve route owners (.inl (.inr raw))
      | beaconSend owner plaintext => exact records (n := n) setup wire reserve route owners (.inr (owner,.inl plaintext))
      | beaconRaw owner raw => exact records (n := n) setup wire reserve route owners (.inr (owner,.inr raw))
      | hash bytes => exact congrFun dictionary (.inr (.inl (.inr (.hash bytes))))
      | hmac key message | create edPin mlPin keyId | bundle index | accept packet | build handle application | finish index packet => rfl

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {source : RegistrationNativeMldsa.Source}
variable (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Each actual non-Beacon branch keeps its original parser, dynamic source writers and complete state. -/
theorem context (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (owners : RegistrationNativeIdentityFrontend.State source) :
    RegistrationNativePlatformIdentityCtxDispatch.context (n := n) setup checks canonical route representation created credential view failure allocation
      reserveRegistration reservePeer reserve erased helper writer query owners =
    RegistrationNativePlatformIdentityCtxDispatch.context setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserve erased helper writer query owners := by
  cases query with
  | inl coin =>
      simpa only [RegistrationNativePlatformIdentityCtxDispatch.context] using
        commands (n := n) setup wire reserve route (owners.map (fun selected => selected.worldOwner)) (.inl coin)
  | inr query =>
      cases query with
      | accept packet | build handle application => rfl
      | serverSend keyId plaintext =>
          exact commands (n := n) setup wire reserve route (owners.map (fun selected => selected.worldOwner)) (.inr (.serverSend keyId plaintext))
      | serverRaw raw => exact commands (n := n) setup wire reserve route (owners.map (fun selected => selected.worldOwner)) (.inr (.serverRaw raw))
      | beaconSend owner plaintext => exact commands (n := n) setup wire reserve route (owners.map (fun selected => selected.worldOwner)) (.inr (.beaconSend owner plaintext))
      | beaconRaw owner raw => exact commands (n := n) setup wire reserve route (owners.map (fun selected => selected.worldOwner)) (.inr (.beaconRaw owner raw))
      | hash bytes => exact commands (n := n) setup wire reserve route (owners.map (fun selected => selected.worldOwner)) (.inr (.hash bytes))
      | hmac key message | create edPin mlPin keyId | bundle index | finish index packet => rfl

private theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) :
    RegistrationNativePlatformIdentityCtxDispatch.step (n := n) setup checks canonical route representation created credential view failure allocation
      reserveRegistration reservePeer reserve erased helper writer query =
    RegistrationNativePlatformIdentityCtxDispatch.step setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserve erased helper writer query := by
  funext before
  unfold RegistrationNativePlatformIdentityCtxDispatch.step
  rw [context setup wire reserve checks route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer]

/-- The complete current typed free dictionary is exactly independent of its replaced fallback frame encoder, with every source/platform failure retained. -/
theorem handler :
    RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks canonical route representation created credential view failure allocation
      reserveRegistration reservePeer reserve erased helper writer =
    RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserve erased helper writer := by
  funext query
  cases query with
  | inl coin => exact step setup wire reserve checks route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer _
  | inr query =>
      cases query <;> first
        | rfl
        | simp only [RegistrationNativePlatformIdentityCtxTyped.handler,
            step setup wire reserve checks route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer]

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.primitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.primitives

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.commands' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.commands

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.context

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxCanonicalWire.handler

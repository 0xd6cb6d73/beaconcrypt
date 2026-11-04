-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxOrdinaryHashBounds
/-! Literal current-runtime Context commands retain physical shared-hash caps: public coins/HMAC cost zero, explicit hashes and each ordinary record operation cost one, and actual source response build costs ten including pin and all optional failures. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformIdentityCtxHashBoundsCore (ContextBounded context_map_bound world_bound server_bound)
open RegistrationNativeRawAdapter (TypedSpec)
variable {n : Nat} {I KemSK Reader Response Platform E : Type} {base : OracleSpec I}

def commandCap : TypedSpec.Domain → Nat
  | .inr (.hash _) | .inr (.serverSend ..) | .inr (.serverRaw _) | .inr (.beaconSend ..) | .inr (.beaconRaw ..) => 1
  | _ => 0

/-- The actual Context World lens keeps the literal guarded source query allowance. -/
theorem guarded_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (query : (PqxdhRecordLiftInterface.WorldSpec n).Domain) :
    ContextBounded (RegistrationNativePlatformCtxContext.guarded setup codec reserve route query)
      (RegistrationNativePlatformCtxOrdinaryHashBounds.worldCap query) :=
  world_bound _ _ (RegistrationNativePlatformCtxOrdinaryHashBounds.guarded_bound setup codec reserve route query)

/-- Actual public owner lookup preserves one commitment hash per ordinary source operation, including every missing-owner outcome. -/
theorem record_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : PqxdhRecordLiftInterface.RecordQuery) :
    ContextBounded (RegistrationNativePlatformCtxCommands.record (n := n) setup codec reserve route owners query) 1 := by
  cases query with
  | inl query => exact guarded_bound (n := n) setup codec reserve route (.inr (.inr (.inl query)))
  | inr pair =>
    rcases pair with ⟨index, query⟩
    cases query with
    | inl plaintext => cases selected : owners[index]? with
      | none =>
        simp only [RegistrationNativePlatformCtxCommands.record, selected]
        intro _
        exact isQueryBoundP_pure _ _ _
      | some owner =>
        simp only [RegistrationNativePlatformCtxCommands.record, selected]
        exact guarded_bound (n := n) setup codec reserve route (.inr (.inr (.inr (owner, .inl plaintext))))
    | inr raw => cases selected : owners[index]? with
      | none =>
        simp only [RegistrationNativePlatformCtxCommands.record, selected]
        intro _
        exact isQueryBoundP_pure _ _ _
      | some owner =>
        simp only [RegistrationNativePlatformCtxCommands.record, selected]
        exact guarded_bound (n := n) setup codec reserve route (.inr (.inr (.inr (owner, .inr raw))))

/-- The literal auxiliary typed command costs only its explicit hash or its one ordinary commitment hash. -/
theorem command_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (route : RawCtxServerRouting.SenderDecoder) (owners : List Nat) (query : TypedSpec.Domain) :
    ContextBounded (RegistrationNativePlatformCtxCommands.command (n := n) setup codec reserve route owners query) (commandCap query) := by
  cases query with
  | inl query => exact guarded_bound (n := n) setup codec reserve route (.inr (.inl (.inl query)))
  | inr query => cases query with
    | hash bytes => exact guarded_bound (n := n) setup codec reserve route (.inr (.inl (.inr (.hash bytes))))
    | serverSend keyId plaintext => exact record_bound (n := n) setup codec reserve route owners (.inl (.inl (plaintext, keyId)))
    | serverRaw raw => exact record_bound (n := n) setup codec reserve route owners (.inl (.inr raw))
    | beaconSend index plaintext => exact record_bound (n := n) setup codec reserve route owners (.inr (index, .inl plaintext))
    | beaconRaw index raw => exact record_bound (n := n) setup codec reserve route owners (.inr (index, .inr raw))
    | create edPin mlPin keyId | bundle index | finish index packet | accept packet | build handle application | hmac key message =>
      intro _
      exact isQueryBoundP_pure _ _ _

variable [primitive : AdapterSealPrimitive.Operations]
/-- Actual response build inherits its ten physical shared hash calls through the full Context lens. -/
theorem build_bound (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8)) :
    ContextBounded (RegistrationNativePlatformCtxBuild.build (n := n) setup codec view failure allocation erased sign helper writer reserve handle application) 10 :=
  context_map_bound _ _ 10 (server_bound _ 10
    (RegistrationNativePlatformCtxSdkHashBounds.build_bound setup codec view failure allocation erased sign helper writer reserve handle application))
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.guarded_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.guarded_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.record_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.command_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.command_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds.build_bound

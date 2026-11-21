-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCommandHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxDispatch
/-! The actual non-Beacon Main dispatcher inherits the source acceptance, response build and ordinary-record physical hash bills. It retains opaque owner state, full Context/P and every failure while adding no hash-producing operation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbientHashBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformIdentityCtxHashBoundsCore (Bounded ContextBounded ordinary_bound)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "ambient" => RegistrationNativePlatformIdentityCtxDispatch.context (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

def cap : TypedSpec.Domain → Nat
  | .inr (.accept _) => 4
  | .inr (.build ..) => 10
  | query => RegistrationNativePlatformCtxCommandHashBounds.commandCap query

/-- Every literal Context dispatch branch has its derived source hash allowance. -/
theorem context_bound (query : TypedSpec.Domain) (owners : RegistrationNativeIdentityFrontend.State source) :
    ContextBounded (ambient query owners) (cap query) := by
  cases query with
  | inl coin => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inl coin)
  | inr query => cases query with
    | accept packet => exact @RegistrationNativePlatformCtxAcceptHashBounds.accept_bound n I KemSK Platform base setup checks reserveRegistration source.verify representation created packet
    | build handle application => exact RegistrationNativePlatformCtxCommandHashBounds.build_bound setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) keys failure allocation erased (RegistrationNativeMldsa.owned source credential) helper writer reservePeer handle application
    | create edPin mlPin keyId => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.create edPin mlPin keyId))
    | bundle index => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.bundle index))
    | finish index packet => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.finish index packet))
    | hmac key message => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.hmac key message))
    | hash bytes => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.hash bytes))
    | serverSend keyId plaintext => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.serverSend keyId plaintext))
    | serverRaw raw => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.serverRaw raw))
    | beaconSend index plaintext => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.beaconSend index plaintext))
    | beaconRaw index raw => exact RegistrationNativePlatformCtxCommandHashBounds.command_bound setup (RegistrationNativeWire.ledgerCodec wire) reserveFrame route (owners.map (fun selected => selected.worldOwner)) (.inr (.beaconRaw index raw))

attribute [local irreducible] RegistrationNativePlatformIdentityCtxDispatch.context

/-- Closing the real owner/Context/P dispatcher adds no shared hash calls to any source operation. -/
theorem step_bound (query : TypedSpec.Domain) :
    Bounded (RegistrationNativePlatformIdentityCtxDispatch.step (n := n) setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query) (cap query) := by
  intro before
  exact ordinary_bound (ambient query before.1.beacons) (cap query)
    (context_bound setup checks wire route representation created credential keys failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query before.1.beacons) before
end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbientHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbientHashBounds.context_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbientHashBounds.context_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxAmbientHashBounds.step_bound

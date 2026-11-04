-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginObserved
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainHistoryRun
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainProfile

/-! The complete current dynamic-writer native profile is interpreted by one executable ordinary joint-Ed client. Startup constructs the independent Server/ML/KEM auxiliary state internally; the challenged Beacon Ed seed is supplied only by its generated indexed service. Every constructor/API failure and full shared P poststate is retained. This is source correspondence, not yet a publication-security reduction or restricted-root confidentiality client. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativePlatformIdentityMain (M interpret project liftMain)
open RegistrationNativePlatformIdentityMainOwned (Owned)
open PqxdhDynamicIdentityPool (SourceState)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

open RegistrationNativeIdentityMainNoRevealCore (Allowed)
open RegistrationNativeIdentityMainCreateCapsCore (Creates)
local notation "cfgClient" => RegistrationNativePlatformIdentityOriginObserved.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- Keeping the complete source owner/platform observation adds no seed revelation. -/
theorem client_no_reveal (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform) :
    AllQueriesSatisfy (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous) Allowed := by
  have safe := RegistrationNativePlatformIdentityMainBounds.client_no_reveal (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false) previous
  rw [RegistrationNativePlatformIdentityOriginObserved.client_map] at safe
  exact (isQueryBound_map_iff _ _ () _ _).mp safe

/-- The same complete retained source client uses only the original public creation budget. -/
theorem client_creates (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (previous : Platform)
    (budget : PqxdhDeploymentInterface.Budget) (bounded : ∀ publicInput,RegistrationNativeInterface.Respects budget (adversary publicInput)) :
    (cfgClient source ensureInit identityIndex serverKeyId bounds mode adversary previous).IsQueryBoundP Creates budget.create := by
  have boundedClient := RegistrationNativePlatformIdentityMainBounds.client_creates (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary (fun _ => false) previous budget bounded
  rw [RegistrationNativePlatformIdentityOriginObserved.client_map] at boundedClient
  exact (isQueryBoundP_map_iff _ _ _).mp boundedClient

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps.client_no_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps.client_no_reveal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps.client_creates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityOriginCaps.client_creates

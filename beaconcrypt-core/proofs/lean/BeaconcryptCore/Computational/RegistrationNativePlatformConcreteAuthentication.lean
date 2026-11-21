-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxResourceSecurity
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteSource
/-! Protected generated-ML unsigned origin in the actual source-backed runtime pays one concrete classical shared-CTX birthday bound and the ordinary generated-key ML-EUF family. Actual source codecs/serializers and dynamic capacity reservations are fixed. This concerns earlier signing-stage origin under generated protected keys, with all failed prefixes retained; it does not assert full six-field Init origin or prior successful wire publication. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAuthentication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value : Type} {base : OracleSpec ι}

variable (setup : Setup base KemSK) (checks : Checks)
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (source : RegistrationNativeMldsa.Source)
variable (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (reserveBytes : Nat → StateT Platform ProbComp (core.result.Result Unit E))
variable (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
local notation "rawAllocation" => RegistrationNativePlatformConcreteSource.rawAllocation reserveBytes
local notation "serializer" => RegistrationNativePlatformConcreteSource.serializer (Platform := Platform)
local notation "helper" => RegistrationNativePlatformConcreteSource.helper reserveBytes
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
variable (bounds : FreshBounds) (mode : Mode)
variable (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
variable (previous : Platform)


variable (budget : Budget) (bounded : ∀ publicInput, RegistrationNativeInterface.Respects budget (adversary publicInput))

local notation "compiled" => (fun publicValue : RegistrationNativeExperiment.Public => RegistrationNativeFullCompiler.compile setup.source.crypto
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) (RegistrationNativeExperiment.Public.serverKeyId publicValue) bounds mode (adversary publicValue))

include bounded in
/-- The original initialized generated-key unsigned-origin/collision marker has a concrete source codec/writer and no residual collision-mass or callback-cap premise. -/
theorem protected_origin :
    Pr{let bad ← (RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.badGame (n := n) source setup checks wire route representation
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer compiled previous ensureInit identityIndex serverKeyId)}[bad = true] ≤
      (((RegistrationNativePlatformIdentityCtxResourceSecurity.hashBudget bounds budget + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer compiled previous ensureInit identityIndex serverKeyId))) := by
  have prior := RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.compiled (n := n) source setup checks wire route representation
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer previous bounds mode adversary budget bounded ensureInit identityIndex serverKeyId
  have collision := RegistrationNativePlatformIdentityCtxResourceSecurity.raw_bound (n := n) setup checks wire route representation source view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId bounds mode adversary previous budget bounded
  exact prior.trans (add_le_add collision le_rfl)
end BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAuthentication.protected_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAuthentication.protected_origin

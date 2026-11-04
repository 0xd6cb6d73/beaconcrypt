-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAuthentication
/-! The exact original protected unsigned-origin/collision marker is executed by the current extracted source dictionary, on its same complete private/platform run. The bound and primitive loss family are unchanged. This is a source-dictionary corollary; adaptive SDK object interpretation is a separate exact execution diagram. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
variable [primitives : AdapterSealPrimitive.Operations]
variable [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
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


local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

noncomputable def handler (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT ((Native×Platform)×Bool) ProbComp) := by
  classical
  exact fun query before=>(fun result=>(result.1,(result.2,before.2 ||decide
    (RegistrationNativeMldsaOriginEvent.Bad source credential query before.1.1 result.1)))) <$>
    RegistrationNativePlatformPackedState.pack
      (RegistrationNativePlatformExtractedExperiment.handler setup checks wire route representation created source credential
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query) before.1

variable (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)

include sealLength openLength converted edFunctional in
theorem handler_source (created : PqxdhLiveServerConstruction.Created Unit)
    (credential : RegistrationNativeMldsa.Credential source) :
    handler (n:=n) setup checks route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased reserveBytes reservePackets created credential=
      RegistrationNativePlatformOrdinaryMldsaOriginSource.handler source setup checks wire route representation created view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer credential := by
  funext query before
  simp only [handler,RegistrationNativePlatformOrdinaryMldsaOriginSource.handler,
    RegistrationNativePlatformExtractedExperiment.handler_source setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer sealLength openLength converted edFunctional]

noncomputable def game : ProbComp Bool :=by
  classical
  exact do
    let initialized←RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex serverKeyId
    match initialized with
    | none=>pure false
    | some initial=>(fun result : (Value×RegistrationNativeLedger.State)×((Native×Platform)×Bool)=>@decide (result.2.2=true ∨CacheHasCollision result.2.1.1.server.world.world.1.primitive.2) (Classical.propDecidable _)) <$>
        (simulateQ (handler setup checks route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased reserveBytes reservePackets initial.created initial.credential)
          (compiled initial.public)).run ((initial.state,previous),false)

include sealLength openLength converted edFunctional in
theorem game_source :
    game (n:=n) setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      reserveBytes reservePackets bounds mode adversary previous=
      RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.badGame (n:=n) source setup checks wire route representation view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer compiled previous ensureInit identityIndex serverKeyId := by
  unfold game RegistrationNativePlatformOrdinaryMldsaOriginUnionSecurity.badGame
  apply bind_congr
  intro initialized
  cases initialized with
  | none=>rfl
  | some initial=>
    dsimp only
    rw [handler_source setup checks route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased
      reserveBytes reservePackets sealLength openLength converted edFunctional initial.created initial.credential]

include bounded sealLength openLength converted edFunctional in
/-- The original initialized generated-key unsigned-origin/collision marker has a concrete source codec/writer and no residual collision-mass or callback-cap premise. -/
theorem protected_origin :
    Pr{let bad ← (game (n:=n) setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      reserveBytes reservePackets bounds mode adversary previous)}[bad = true] ≤
      (((RegistrationNativePlatformIdentityCtxResourceSecurity.hashBudget bounds budget + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation
          reserveRegistration reservePeer reserveFrame erased helper writer compiled previous ensureInit identityIndex serverKeyId))) := by
  rw [game_source setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
    reserveBytes reservePackets bounds mode adversary previous sealLength openLength converted edFunctional]
  exact RegistrationNativePlatformConcreteAuthentication.protected_origin setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased reserveBytes reservePackets bounds mode adversary previous budget bounded

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication.handler_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication.game_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication.protected_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication.protected_origin

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativePlatformConcreteAgreement
/-! The exact original all-owner staged agreement journal is executed by the current extracted source dictionary. Every complete source callback state, failure and platform poststate remains in the same journal, with identical concrete hash, ordinary ML-EUF and KEM losses. This source-dictionary result does not replace separate SDK-object composition or claim prior response publication. -/
open OracleComp OracleSpec CoreModels ENNReal Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeStageTrace (Call)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativePlatformKemInitializedJournal (History)
variable [primitives : AdapterSealPrimitive.Operations]
variable [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
variable {n : Nat} {ι KemSK Platform E Value AD PT CT : Type} {base : OracleSpec ι}

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
variable (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)


local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

noncomputable def callback (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) :
    QueryImpl TypedSpec (StateT (Native×Platform) ProbComp) :=
  fun query=>RegistrationNativePlatformPackedState.pack
    (RegistrationNativePlatformExtractedExperiment.handler setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query)

variable (sealLength : RegistrationNativePlatformOrdinarySourceWorld.AeadLength setup.source.crypto)
    (openLength : RegistrationNativeExtractedReceive.AeadLength setup.source.crypto)
    (converted : RegistrationNativePlatformOrdinarySourceNative.Conversion view)
    (edFunctional : RegistrationNativePlatformAuthentication.EdFunctional setup.source.crypto)

include sealLength openLength converted edFunctional in
theorem callback_source (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential source) :
    callback (n:=n) setup checks route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased reserveBytes reservePackets created credential=
      RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer := by
  unfold callback RegistrationNativePlatformOrdinaryKemClientJournal.actual
  rw [RegistrationNativePlatformExtractedExperiment.handler_source (n:=n) setup checks wire route representation created source credential
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer sealLength openLength converted edFunctional]

noncomputable def game (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) : ProbComp Bool := by
  classical
  exact do
    let initialized←RegistrationNativeExperiment.start (n:=n) setup source ensureInit identityIndex serverKeyId
    match initialized with
    | none=>pure false
    | some initial=>(fun result=>decide (¬RegistrationNativePlatformOrdinaryAllOwnerAgreement.AllOwners crypto setup checks wire representation initial.created view failure allocation erased
        rawAllocation serializer initial.credential result.2.2)) <$>
      (simulateQ (RegistrationNativeStageTrace.handler
        (callback setup checks route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased reserveBytes reservePackets initial.created initial.credential))
        (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode
          (adversary initial.public))).run ((initial.state,previous),[])

include sealLength openLength converted edFunctional in
theorem game_source (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) :
    game (n:=n) setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      reserveBytes reservePackets bounds mode adversary previous crypto=
      RegistrationNativePlatformOrdinaryAllOwnerNative.game (n:=n) setup checks wire route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
        rawAllocation serializer writer bounds mode adversary previous crypto := by
  unfold game RegistrationNativePlatformOrdinaryAllOwnerNative.game
  apply bind_congr
  intro initialized
  cases initialized with
  | none=>rfl
  | some initial=>
    dsimp only
    rw [callback_source setup checks route representation source view failure allocation reserveRegistration reservePeer reserveFrame erased
      reserveBytes reservePackets sealLength openLength converted edFunctional initial.created initial.credential]
    rfl

include bounded functional sealLength openLength converted edFunctional in
/-- Every protected successful finish of every owner has an actual earlier same-run staged partner except for the concrete shared hash, ML-EUF and ordinary KEM losses. -/
theorem bound (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (correct : view.Correct) :
    Pr{let failed←(game (n:=n) setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
      reserveBytes reservePackets bounds mode adversary previous crypto)}[failed = true] ≤
      (((RegistrationNativePlatformIdentityCtxResourceSecurity.hashBudget bounds budget + 1).choose 2 : ℝ≥0∞) / (2 : ℝ≥0∞)^512 +
      ∑ target : Fin (budget.create + 1), RegistrationNativeMldsaEuf.advantage source (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n := n) source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          (fun publicValue => RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) publicValue.serverKeyId bounds mode (adversary publicValue))
          previous ensureInit identityIndex serverKeyId))) + budget.create * budget.accept * RegistrationNativeRecipientFailure.failureRate setup := by
  rw [game_source setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation reserveRegistration reservePeer reserveFrame erased
    reserveBytes reservePackets bounds mode adversary previous sealLength openLength converted edFunctional crypto]
  exact RegistrationNativePlatformConcreteAgreement.bound (n:=n) setup checks route representation source ensureInit identityIndex serverKeyId view failure allocation
    reserveRegistration reservePeer reserveFrame erased reserveBytes reservePackets bounds mode adversary previous budget bounded functional crypto correct

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement.callback_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement.callback_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement.game_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAgreement.bound

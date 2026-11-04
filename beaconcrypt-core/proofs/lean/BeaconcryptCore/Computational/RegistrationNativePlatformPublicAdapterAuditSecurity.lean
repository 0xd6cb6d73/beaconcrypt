-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerExecution
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedDictionaryAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterInitializationPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterLedgerCompile
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterTypedAuditRaw
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterFullProgram
import BeaconcryptCore.Computational.RegistrationNativeMldsaOriginEvent
/-! Protected generated-key authentication on the initialized typed audit uses the actual source constructor and derives startup and callback budgets internally. The same physical cache collision and ordinary weak-EUF family account for all source authentication attempts, including failed signing and publication prefixes. -/
open CoreModels Aeneas OracleComp OracleSpec ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity
open BeaconcryptCore.Refinement
open AdapterPublicWrapperRequestMonad
open AdapterPublicWrapperRustT (RustT)
variable {n :Nat} {I KemSK P E R Error :Type} {base :OracleSpec I} {source :RegistrationNativeMldsa.Source}
variable [material :PublicWrapperPlatform.Material] [platform :PublicWrapperPlatform.Platform]
variable [ed :AdapterInitEdPrimitive.Operations] [primitives :AdapterSealPrimitive.Operations]
variable [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [PublicWrapperPlatform.CryptoOperations] [AdapterPublicOrdinaryPlatform.LookupOperations] [FrameDispatchFallback.Operations]
variable [originalGenerators :AdapterBeaconConstructorRequestMonad.Operations (RustT ProbComp)]
variable [originalCrypto :CryptoOperations (RustT ProbComp)]
variable [originalLocal :LocalOperations (RustT (StateT P ProbComp))]
variable [originalContainers :ContainerOperations (RustT (StateT P ProbComp))]
variable {setup :PqxdhServerAuthExperiment.Setup base KemSK} {checks :PqxdhServerAuthExperiment.Checks}
variable (configuration :RegistrationNativePlatformPublicAdapterConfiguration.Configuration
  (P:=P) (E:=E) (R:=R) (Error:=Error) (source:=source) setup checks)
variable [AdapterServerConstructorPrimitive.Standard]
variable {Value :Type}
variable (objects :AdapterServerConstructorObjects.Leaves configuration.views)
variable (ensureInit :StateT Unit ProbComp Bool)
variable (serverEd :AdapterServerConstructorJoint.EdContract configuration.generator configuration.view setup.joint (AdapterServerConstructorStartup.edCore ensureInit))
variable (identityIndex :Nat) (identifier :U64) (rng :R)
variable (bounds :PqxdhDeploymentInterface.FreshBounds) (mode :PqxdhDeploymentInterface.Mode)
variable (adversary :RegistrationNativeExperiment.Public→OracleComp (RegistrationNativePlatformPublicAdapterInterface.ModeSpec mode) Value)
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source
local notation "AuditState"=>RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical

noncomputable def game (previous :P) :ProbComp Bool :=by
  classical
  exact do
    let packet←RegistrationNativePlatformPublicAdapterInitializationPhysical.sample (n:=n) setup configuration.generator configuration.view previous identityIndex identifier rng
    match packet.val.1.ready with
    | none=>pure false
    | some ready=>
      (fun result :(Value×RegistrationNativeLedger.State)×RegistrationNativePlatformPublicAdapterAuditLowModel.State n KemSK P source=>
        decide (result.2.2.bad=true ∨CacheHasCollision result.2.1.1.server.world.world.1.primitive.2)) <$>
        ((simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration ready.initial.created ready.initial.credential)
          (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public)).run
          ((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty))

omit [PublicWrapperPlatform.CryptoOperations] in
include objects serverEd in
theorem game_dictionary (previous :P) :
    game (n:=n) configuration identityIndex identifier rng bounds mode adversary previous=
      RegistrationNativePlatformExtractedDictionaryAuthentication.game (n:=n) setup checks RegistrationNativePlatformPublicAdapterRouting.route
        configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
        (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
        configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased configuration.reserveFrame
        configuration.reservePackets bounds mode
        (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous :=by
  have initialized:=RegistrationNativePlatformPublicAdapterInitializationPhysical.native (n:=n) setup configuration.generator configuration.view
    configuration.views objects ensureInit serverEd configuration.mlGeneration configuration.edGetter configuration.mlGetter previous identityIndex identifier rng
  unfold game RegistrationNativePlatformExtractedDictionaryAuthentication.game
  rw [←initialized,bind_map_left]
  apply bind_congr
  rintro ⟨⟨⟨constructor,choice⟩,world⟩,supported⟩
  cases choice with
  | none=>rfl
  | some ready=>
    dsimp only [AdapterServerConstructorRunner.nativeView,Option.map_some]
    have projected:=RegistrationNativePlatformPublicAdapterAuditProgram.flag configuration ready.initial.created ready.initial.credential
      ready.initial.public.serverKeyId bounds mode (adversary ready.initial.public)
      ((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty)
    have observed:=congrArg (fun computation=>(fun result=>@decide
      (result.2.2=true ∨CacheHasCollision result.2.1.1.server.world.world.1.primitive.2) (Classical.propDecidable _)) <$>computation) projected
    simp only [Functor.map_map] at observed
    convert observed using 1
    · apply congrArg (fun observer=>observer <$>
        (simulateQ (RegistrationNativePlatformPublicAdapterAuditLowModel.model configuration ready.initial.created ready.initial.credential)
          (RegistrationNativePlatformPublicAdapterLedgerExecution.work (setup:=setup) bounds mode adversary ready.initial.public)).run
          ((ready.initial.state,previous),RegistrationNativePlatformPublicAdapterTypedAudit.empty))
      funext result
      exact decide_eq_decide.mpr Iff.rfl
    · rfl

noncomputable def loss (previous :P) (budget :PqxdhDeploymentInterface.Budget) :ℝ≥0∞ :=
  (((RegistrationNativePlatformIdentityCtxResourceSecurity.hashBudget bounds budget+1).choose 2 :ℝ≥0∞)/(2 :ℝ≥0∞)^512+
    ∑target :Fin (budget.create+1),RegistrationNativeMldsaEuf.advantage source
      (RegistrationNativeMldsaEufTapeReduction.adversary source target
        (RegistrationNativePlatformOrdinaryMldsaStoppedGame.program (n:=n) source setup checks wire RegistrationNativePlatformPublicAdapterRouting.route
          configuration.agreement.representation configuration.keyView configuration.sealFailure
          (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
          configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased
          (RegistrationNativePlatformConcreteSource.helper configuration.reserveFrame)
          (RegistrationNativePlatformConcreteSource.writer configuration.reservePackets)
          (fun (publication :RegistrationNativeExperiment.Public)=>RegistrationNativeFullCompiler.compile setup.source.crypto canonical publication.serverKeyId bounds mode
            (RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication))) previous ensureInit identityIndex identifier)))

omit [PublicWrapperPlatform.CryptoOperations] in
include objects serverEd in
theorem bound (previous :P) (budget :PqxdhDeploymentInterface.Budget)
    (bounded :∀publication,RegistrationNativePlatformPublicAdapterInterface.Respects mode budget (adversary publication)) :
    Pr{let bad←game (n:=n) configuration identityIndex identifier rng bounds mode adversary previous}[bad=true]≤
      loss (n:=n) configuration ensureInit identityIndex identifier bounds mode adversary previous budget :=by
  rw [game_dictionary configuration objects ensureInit serverEd identityIndex identifier rng bounds mode adversary previous]
  exact RegistrationNativePlatformExtractedDictionaryAuthentication.protected_origin setup checks RegistrationNativePlatformPublicAdapterRouting.route
    configuration.agreement.representation source ensureInit identityIndex identifier configuration.keyView configuration.sealFailure
    (RegistrationNativePlatformExtractedSdkBuildNormal.allocation configuration.allocateJoin)
    configuration.reserveRegistration configuration.reservePeer configuration.reserveFrame configuration.erased configuration.reserveFrame
    configuration.reservePackets bounds mode
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile mode (adversary publication)) previous
    budget
    (fun publication=>RegistrationNativePlatformPublicAdapterInterface.compile_bound mode budget _ (bounded publication))
    configuration.sealLength configuration.openLength configuration.converted configuration.edFunctional

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity.game_dictionary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity.game_dictionary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterAuditSecurity.bound

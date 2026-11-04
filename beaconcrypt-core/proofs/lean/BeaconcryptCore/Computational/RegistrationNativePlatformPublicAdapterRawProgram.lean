-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawModel
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedExperiment
import BeaconcryptCore.Computational.RegistrationNativeConcreteReaders
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRouting
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkServer
/-! The selected raw public-adapter target fixes the actual codec and sender decoder, retains original raw bytes and uses the unchanged extracted dictionary. Its local equations connect the concrete wrapper factories without a caller-supplied callback law. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawProgram
attribute [local irreducible] RegistrationNativePlatformExtractedExperiment.record
  RegistrationNativePlatformExtractedAuthentication.accept RegistrationNativePlatformExtractedBundle.bundle
  RegistrationNativePlatformExtractedFinish.finish RegistrationNativeConcreteCodec.wire
  RegistrationNativePlatformPublicAdapterRouting.route
open BeaconcryptCore.Refinement
open RegistrationNativePlatformOrdinaryExperiment (canonicalWire)
open RegistrationNativeRawAdapter (TypedSpec)
variable {Value : Type}
variable {n : Nat} {Platform E I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [primitives : AdapterSealPrimitive.Operations] [FrameDispatchFallback.Operations] [AdapterInitEdPrimitive.Operations]
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E))
variable (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "coins"=>RegistrationNativePlatformMldsaProgram.coins
local notation "wire"=>RegistrationNativeConcreteCodec.wire
local notation "route"=>RegistrationNativePlatformPublicAdapterRouting.route

local notation "typed"=>RegistrationNativePlatformPublicAdapterRawModel.typed (n:=n) setup checks representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
local notation "raw"=>RegistrationNativePlatformPublicAdapterRawModel.raw (n:=n) setup checks representation created credential
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

theorem program (work : OracleComp RegistrationNativeInterface.Spec Value) :
    simulateQ raw work=simulateQ typed (RegistrationNativeRawAdapter.compile wire work) := by
  unfold RegistrationNativePlatformPublicAdapterRawModel.raw RegistrationNativeRawAdapter.compile
  exact QueryImpl.simulateQ_compose _ _ work

theorem full (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) :
    simulateQ raw (RegistrationNativeLedger.wrap setup.source.crypto (RegistrationNativeWire.ledgerCodec (canonicalWire wire))
      created.server.server.metadata.sender bounds (RegistrationNativeInterface.asModeO mode work))=
    simulateQ typed (RegistrationNativeFullCompiler.compile setup.source.crypto (canonicalWire wire)
      created.server.server.metadata.sender bounds mode work) := by
  rw [program]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawProgram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawProgram.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawProgram.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawProgram.full' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterRawProgram.full

import BeaconcryptCore.Computational.RegistrationNativePlatformRecordOriginSamplerSource
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginInitializedEventCover
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginPublicNormalization
-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointInitial
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointErasure
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveReferenceCrypto
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealPhysical
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationStartup
/-! The genuine effectful constructor, generated credential, shared pin hash and complete corrected dynamic source run have the gated native environment interpretation. Physical allocation is derived from the actual interpreted startup, and all original value, ledger, private/provider, cursor, Protocol, service and persistent platform poststates are retained. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (WorldSpec coinLift effectLift)
open RegistrationNativeHiddenInterpreter (Provider)
open RegistrationNativePlatformSelectiveEntropyEnvironment (State)
open RegistrationNativePlatformSelectiveEntropyEffects (close close_run effect_source)
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK ProviderState Platform E Secret Reader Response Value : Type} {base : OracleSpec I}
local notation "wire" => RegistrationNativePlatformConcreteSource.wire
variable (setup : Setup base KemSK) (checks : Checks)
    (source : RegistrationNativeMldsa.Source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))



open RegistrationNativeHiddenEnvironmentWorld (lower)
open PqxdhRecordLiftInterface (WorldSpec)
open RegistrationNativeEntropyRun (Outcome)



local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "service" => PqxdhRecordLiftIdeal.ctxInterpreter (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) id setup codec
local notation "physical(" route ")" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route


/-- The actual native reference startup and adaptive body have the temporal origin bound at the SAME warmed private state, using only the named public observation normalization. -/
theorem reference_bound (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (previous : Platform) (privateBefore : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public→OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (start : PqxdhRecordLiftIdeal.CtxPrivate n) (virgin : PqxdhRecordFactsPrivateCacheSource.Virgin start [])
    (empty : ∀label,(start.keys label).1.successfulSeals=[]) :
    Pr{let result←(simulateQ service (RegistrationNativeRecordOriginProgram.program codec route
      (RegistrationNativePlatformSelectiveEntropyStartup.referenceProgram setup checks wire source seed scalar candidate provider selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer ensureInit identityIndex serverKeyId previous privateBefore
        bounds mode adversary))).run start}[
      PqxdhRecordLiftIdeal.UnpublishedAccept codec route (PqxdhRecordLiftIdeal.ctxView result)]≤
      budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  let env : RegistrationNativeHiddenStartup.Started source→RegistrationNativeEntropyInterface.Environment n
      (State n KemSK ProviderState Platform source):=fun born=>RegistrationNativePlatformSelectiveEntropyQuery.environment
    setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source born.native.credential seed scalar candidate provider
    selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (pure none)
  let reserve : RegistrationNativeHiddenStartup.Started source→Nat→StateT (State n KemSK ProviderState Platform source) ProbComp (core.result.Result Unit E):=fun _born amount=>
    RegistrationNativePlatformSelectiveEntropyEffects.liftPlatform (reserveFrame amount)
  let work:=fun born : RegistrationNativeHiddenStartup.Started source=>adversary
    ⟨setup.joint.publicKeys seed,born.native.credential.publicKey,serverKeyId⟩
  let initial:=fun born : RegistrationNativeHiddenStartup.Started source=>((born.native.frontend,previous),privateBefore)
  let world:=RegistrationNativePlatformOriginStartupLedgerTails.world setup source ensureInit identityIndex serverKeyId
    (setup.joint.publicKeys seed) env reserve codec bounds mode work initial
  change Pr{let result←(simulateQ service (RegistrationNativeRecordOriginProgram.program codec route world)).run start}[
    PqxdhRecordLiftIdeal.UnpublishedAccept codec route (PqxdhRecordLiftIdeal.viewOf result.1 [])]≤_
  rw [RegistrationNativePlatformOriginPublicNormalization.event (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec
    (fun _=>by intro impossible;cases impossible) (RegistrationNativeRecordOriginProgram.program codec route world) start
    (fun client=>PqxdhRecordLiftIdeal.UnpublishedAccept codec route (PqxdhRecordLiftIdeal.viewOf client []))]
  exact RegistrationNativePlatformOriginInitializedEventCover.bound setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys seed)
    env reserve route bounds mode work initial (PqxdhRecordFactsCounter.zeroCtx start) virgin empty
    (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) (fun _=>by intro impossible;cases impossible) id budget (fun born=>bounded _)

/-- The complete actual Uniform sampler remains inside the source program and supplies the warm starting facts internally; its temporal record-origin probability has exactly the coefficient-two loss. -/
theorem bound (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public→OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create+1)) (previous : Platform) :
    Pr{let result←(simulateQ
      (PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec)
      (RegistrationNativeRecordOriginProgram.program codec route
        (RegistrationNativePlatformG3UniformRecordProgram.program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous))).run
            PqxdhRecordLiftIdeal.CtxPrivate.initial}[
      PqxdhRecordLiftIdeal.UnpublishedAccept codec route (PqxdhRecordLiftIdeal.ctxView result)]≤
      budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  rw [RegistrationNativePlatformG3UniformRecordProgram.program,RegistrationNativePlatformRecordOriginSamplerSource.source]
  apply prEvent_bind_le_of_forall_le_of_support
  intro sampled supported
  obtain ⟨virgin,empty⟩:=RegistrationNativePlatformRecordPartnerWarmKeys.sampler_initial
    (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec route
    (RegistrationNativePlatformG3UniformRecordProgram.sample setup budget selected) sampled supported
  exact reference_bound setup checks source sampled.1.seed sampled.1.scalar sampled.1.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val sampled.1.profile.pairs
      sampled.1.profile.publicKey sampled.1.profile.challenge sampled.1.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route
    ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget sampled.1.materials)
    bounds mode adversary budget bounded sampled.2.2.2 virgin empty


omit primitive in
private def restoreView {count : Nat} {T X : Type} (native : RegistrationNativeRecordPackage.View count T X) :
    PqxdhRecordLiftIdeal.View count (RegistrationNativeRecordPackage.Extra T) X :=
  ⟨native.result.map (fun born=>(born.2.1.1,born.2.1.2.ledger,(born.1,born.2.1.2.transcript,born.2.2))),
    native.produced,native.raw,native.slots⟩
omit primitive in
private theorem restore_view {count : Nat} {T X : Type}
    (old : PqxdhRecordLiftIdeal.View count (RegistrationNativeRecordPackage.Extra T) X) :
    restoreView (RegistrationNativeRecordPackage.view old)=old := by
  rcases old with ⟨result,produced,raw,slots⟩
  cases result <;>rfl
omit primitive in
private theorem restore_native {count : Nat} {T X : Type}
    (outcome : RegistrationNativeEntropyRun.Outcome T X) (control : PqxdhRecordLiftProtocol.Control count)
    (produced : List (PqxdhDeploymentInterface.FrameTag×PqxdhDeploymentNative.Frame)) :
    restoreView (RegistrationNativeRecordPackage.nativeView (outcome,control) produced)=
      PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode outcome,control) produced := by
  cases outcome <;>rfl
/-- The same actual sampler/startup/slot/G2 joint lift has the temporal origin bound on its final physical control; no analysis labels are exposed to a primitive adversary. -/
theorem joint_bound (route : RawCtxServerRouting.SenderDecoder)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public→OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀publication,RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create+1)) (previous : Platform) :
    Pr{let result←(RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)}[
      PqxdhRecordLiftIdeal.UnpublishedAccept codec route
        (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) [])]≤
      budget.sends*(2*budget.receives*((2^512:Nat):ℝ≥0∞)⁻¹) := by
  have observed : Pr{let current←(RegistrationNativeRecordPackage.ctx (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) setup codec route
      (RegistrationNativePlatformG3UniformRecordProgram.program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous))}[
      PqxdhRecordLiftIdeal.UnpublishedAccept codec route (restoreView current)]=
    Pr{let result←(RegistrationNativePlatformRecordPartnerJointUniform.joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous)}[
      PqxdhRecordLiftIdeal.UnpublishedAccept codec route
        (PqxdhRecordLiftIdeal.viewOf (RegistrationNativeRecordPackage.encode result.1,result.2.2.2.2.1) [])] := by
    have observedSource:=RegistrationNativePlatformRecordPartnerJointUniform.observed_source setup checks wire route source
      ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      bounds mode adversary budget selected previous
    have probability:=congrArg (fun distribution=>Pr{let current←distribution}[
      PqxdhRecordLiftIdeal.UnpublishedAccept codec route (restoreView current)]) observedSource
    rw [prEvent_map] at probability
    simp only [restore_native] at probability
    refine probability.trans ?_
    exact prEvent_congr _ _ _ (fun _=>Iff.rfl)
  rw [←observed]
  unfold RegistrationNativeRecordPackage.ctx
  rw [prEvent_map]
  simp only [Function.comp_apply,restore_view]
  exact bound setup checks source view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer route
    ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget bounded selected previous

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound.reference_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound.reference_bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound.bound
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound.joint_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordJointOriginBound.joint_bound

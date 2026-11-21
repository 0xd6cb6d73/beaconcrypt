-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointStartup
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerSampler
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotSourceComparison
import BeaconcryptCore.Computational.RegistrationNativePlatformG3UniformOpaqueSource
/-! The original initialized runtime produced/raw event reaches one all-random gated record client. The bound retains the original startup, one KEM shift, one initialized recovery client, and one complete-prefix client for each ordered record reduction. Primitive security remains expressed by its explicit advantages. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicRecordOpaqueInitialized (Context prior)
variable {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample after program)
open PqxdhRecordLiftCtxProtocolBounds (BudgetKind categoryCost)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_run)
open PqxdhRecordLiftCtxBills (effectBill worldBill)
variable (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (selected : Fin (budget.create + 1)) (previous : Platform)
local notation "work" => program setup checks wire source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous


local notation "codec" => RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
local notation "service" => PqxdhRecordLiftIdeal.ctxInterpreter (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) id setup codec
local notation "physical" => RegistrationNativePlatformLorIdealPhysical.implementation service codec route

noncomputable def joint := do
  let parameters ← (simulateQ physical (simulateQ PqxdhRecordLiftInterface.coinLift (sample setup budget selected))).run
    (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial)
  RegistrationNativePlatformRecordPartnerJointStartup.joint setup checks wire source parameters.1.seed parameters.1.scalar parameters.1.candidate
    (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val parameters.1.profile.pairs parameters.1.profile.publicKey parameters.1.profile.challenge parameters.1.candidate)
    selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer physical
    ensureInit identityIndex serverKeyId previous
    (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget parameters.1.materials)
    bounds mode adversary parameters.2

/-- The original complete-prefix ideal record observation is an exact projection of the actual sampler/startup/slot/G2 joint lift. Sampler state is retained, not resampled or reset. -/
theorem observed_source :
    RegistrationNativeRecordPackage.ctx (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) setup codec route work =
    (fun result => RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced) <$>
      joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous := by
  rw [RegistrationNativeRecordPackage.ctx_source]
  simp only [RegistrationNativePlatformG3UniformRecordProgram.program,CborRawRecordOriginFlatten.interpret_bind,map_bind,joint]
  rw [RegistrationNativePlatformLorIdealPhysical.program_source]
  simp only [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  have framed := RegistrationNativePlatformRecordPartnerSampler.frame service codec route (sample setup budget selected)
    (CborRecordWorldClient.initial,PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial)
    (result.1.1.1,(result.1.1.2,(result.1.2,result.2))) ?_
  · change result.1.1.2=CborRecordWorldClient.initial ∧result.1.2=PqxdhRecordLiftProtocol.initialControl at framed
    simp only [RegistrationNativePlatformG3UniformRecordProgram.after]
    have warm := RegistrationNativePlatformRecordPartnerJointStartup.ctx_warm_source setup checks wire source
      result.1.1.1.seed result.1.1.1.scalar result.1.1.1.candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selected.val result.1.1.1.profile.pairs result.1.1.1.profile.publicKey result.1.1.1.profile.challenge result.1.1.1.candidate)
      selected.val selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (fun _ => PqxdhRecordLiftIdeal.KeyMode.random) route
      ensureInit identityIndex serverKeyId previous (RegistrationNativePlatformG3UniformOpaqueNative.privateState none budget result.1.1.1.materials)
      bounds mode adversary result.2
    simpa only [framed.1,framed.2] using warm.symm
  · rw [RegistrationNativePlatformLorIdealPhysical.program_source,support_map]
    exact ⟨result,supported,rfl⟩

variable (observe : Value × RegistrationNativeLedger.State →
    List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) → PqxdhRecordLiftWorld.RawCounters → Bool)

/-- The same original public decision is the marginal used by the already-derived ordinary source comparison; G2 and slots are retained only in the joint ideal analysis. -/
theorem ideal_source :
    RegistrationNativePlatformRecordSlotSourceComparison.ideal setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous observe =
    (fun result => RegistrationNativePlatformG3UniformOpaqueRecord.event source observe
      (RegistrationNativeRecordPackage.nativeView (result.1,result.2.2.2.2.1) result.2.2.2.2.2.base.produced)) <$>
      joint setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary budget selected previous := by
  rw [←RegistrationNativePlatformRecordSlotSourceComparison.ideal_source]
  unfold RegistrationNativePlatformG3UniformRecordSource.ideal
  rw [observed_source,Functor.map_map]
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform.observed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform.ideal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerJointUniform.ideal_source

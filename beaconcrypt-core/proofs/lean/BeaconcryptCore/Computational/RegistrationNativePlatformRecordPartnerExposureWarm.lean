-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSampler
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureNativeSource
/-! The exact actual uniform sampler and genuine startup feed the same original chronological Word exposure event. A charged-candidate refresh places their complete independent prefix inside one concrete recovery adversary. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSuffixKeyPrf (Secret)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativePlatformG3UniformRecordProgram (Sample sample)
variable {I KemSK Platform E A : Type} {base : OracleSpec I}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public →OracleComp (RegistrationNativeInterface.ModeSpec mode) A)
    (budget : PqxdhDeploymentInterface.Budget) (selected : Fin (budget.create+1)) (previous : Platform)
local notation "cap"=>budget.cap 4+budget.cap 5
local notation "canonical"=>RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire
local notation "codec"=>RegistrationNativeWire.ledgerCodec canonical
local notation "State"=>RegistrationNativePlatformLorIdealPhysical.State cap (PqxdhRecordLiftIdeal.CtxPrivate cap)
local notation "physical"=>RegistrationNativePlatformLorIdealPhysical.implementation
  (PqxdhRecordLiftIdeal.ctxInterpreter (fun _=>PqxdhRecordLiftIdeal.KeyMode.random) id setup codec) codec route
local notation "initial"=>((CborRecordWorldClient.initial,(PqxdhRecordLiftProtocol.initialControl,PqxdhRecordLiftIdeal.CtxPrivate.initial)) : State)
local notation "Ctx"=>RegistrationNativePlatformRecordPartnerExposureAveraged.Context source cap KemSK State Platform A mode

noncomputable def future (parameters : Sample KemSK cap) (before : State) : ProbComp (Option Ctx) := do
  let started←(simulateQ physical
    (RegistrationNativeHiddenStartup.start setup source ensureInit identityIndex serverKeyId (setup.joint.publicKeys parameters.seed))).run before
  pure (started.1.map (fun born=>RegistrationNativePlatformRecordPartnerExposureWarmPrefix.context
    setup source serverKeyId mode adversary budget previous parameters born started.2))

noncomputable def wordGame (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec (budget.cap 4+budget.cap 5)))) : ProbComp Bool := do
  let sampled←(simulateQ physical (simulateQ PqxdhRecordLiftInterface.coinLift (sample setup budget selected))).run initial
  let context←future setup wire route source ensureInit identityIndex serverKeyId mode adversary budget previous sampled.1 sampled.2
  RegistrationNativePlatformRecordPartnerExposureAveraged.after setup checks canonical source selected.val selected.val selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical unused sampled.1.candidate context

noncomputable def refreshed (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec (budget.cap 4+budget.cap 5)))) :=
  RegistrationNativePlatformRecordPartnerExposureAveraged.game setup checks canonical source selected.val selected.val selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical unused
    (RegistrationNativePlatformRecordPartnerExposureWarmPrefix.prior setup source ensureInit identityIndex serverKeyId mode adversary budget selected
      previous physical initial)

noncomputable def client :=
  RegistrationNativePlatformRecordPartnerExposureAveraged.client setup checks canonical source selected.val selected.val selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical
    (RegistrationNativePlatformRecordPartnerExposureWarmPrefix.prior setup source ensureInit identityIndex serverKeyId mode adversary budget selected
      previous physical initial)

omit primitive in
private theorem future_erased (parameters : Sample KemSK cap) (before : State) :
    future setup wire route source ensureInit identityIndex serverKeyId mode adversary budget previous
      (RegistrationNativePlatformRecordPartnerExposureSampler.erase budget parameters) before=
    future setup wire route source ensureInit identityIndex serverKeyId mode adversary budget previous parameters before := by
  rfl

/-- Moving the independent mathematical candidate after the actual warm prefix retains its original physical draw charge and full reached source state. -/
theorem refresh (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec (budget.cap 4+budget.cap 5)))) :
    wordGame setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous unused =ᵈ
    refreshed setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous unused := by
  let next (candidate : Secret) (parameters : Sample KemSK cap) (before : State) :=
    future setup wire route source ensureInit identityIndex serverKeyId mode adversary budget previous parameters before >>=fun context=>
      RegistrationNativePlatformRecordPartnerExposureAveraged.after setup checks canonical source selected.val selected.val selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical unused candidate context
  have sampled:=RegistrationNativePlatformRecordPartnerExposureSampler.refresh setup budget selected codec route initial next
  simp only [next,future_erased] at sampled
  refine sampled.trans ?_
  unfold refreshed RegistrationNativePlatformRecordPartnerExposureAveraged.game
    RegistrationNativePlatformRecordPartnerExposureWarmPrefix.prior
  simp only [bind_assoc,pure_bind]
  apply _root_.EvalDistEq.bind_right
  intro sampled
  simpa only [future,bind_assoc,pure_bind] using OracleComp.EvalDistEq.bind_bind_swap ($ᵗ Secret)
    (future setup wire route source ensureInit identityIndex serverKeyId mode adversary budget previous sampled.1 sampled.2)
    (fun candidate context=>RegistrationNativePlatformRecordPartnerExposureAveraged.after setup checks canonical source selected.val selected.val selectedAccept
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical unused candidate context)

/-- The literal actual warm uniform source exposure is bounded by one explicit complete-prefix recovery client and the original material allowance. -/
theorem bound (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec (budget.cap 4+budget.cap 5)))) (filler : PqxdhServerAuthKeySchedule.Output)
    (bounded : ∀publication,RegistrationNativeInterface.Respects budget (adversary publication)) :
    Pr{let flag←(wordGame setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer bounds mode adversary budget selected previous unused)}[flag=true]≤
    ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
      (RegistrationNativeSuffixKeyRecovery.adversary setup.source
        (RegistrationNativeSecretWordRecoveryCompiler.guesses
          (client setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer bounds mode adversary budget selected previous))))+
      (budget.cap 4+budget.cap 5)*(256^160 : ℝ≥0∞)⁻¹+(budget.cap 4+budget.cap 5)*(256^32 : ℝ≥0∞)⁻¹ := by
  have same:=(refresh setup checks wire route source ensureInit identityIndex serverKeyId selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer bounds mode adversary budget selected previous unused) (fun flag=>flag=true)
  rw [same]
  exact RegistrationNativePlatformRecordPartnerExposureAveraged.bound setup checks canonical source selected.val selected.val selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode physical filler unused _
    budget
    (fun context supported=>(RegistrationNativePlatformRecordPartnerExposureWarmPrefix.fields setup source ensureInit identityIndex serverKeyId mode adversary
      budget selected previous physical initial bounded context supported).2)
    (fun context supported=>(RegistrationNativePlatformRecordPartnerExposureWarmPrefix.fields setup source ensureInit identityIndex serverKeyId mode adversary
      budget selected previous physical initial bounded context supported).1)

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm.refresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm.refresh
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureWarm.bound

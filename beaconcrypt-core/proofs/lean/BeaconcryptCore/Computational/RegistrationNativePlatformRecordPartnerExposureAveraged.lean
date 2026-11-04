-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureSourceBound
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasPriorBound
/-! The entire independent startup/profile/material/physical prefix belongs to one executable recovery client. Refused startup is retained as None; a single explicit recovery advantage controls all following source exposures. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordServiceCaps (Kind Counted)
open RegistrationNativeSuffixKeyPrf (Secret)
attribute [local instance] Classical.propDecidable
variable {n : Nat} {I KemSK Physical Platform E A : Type} {base : OracleSpec I}

private theorem prior_hit {C B : Type}
    (keySource : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (prior : ProbComp C) (next : C →OracleComp Combined B) :
    Pr{let flag←(prior >>=fun context=>($ᵗ Secret >>=fun candidate=>
      (fun result=>decide (candidate∈result.2.2)) <$>RegistrationNativeSecretWordRecoveryBound.logged keySource candidate (next context)))}[flag=true]=
    Pr{let pair←(do
      let candidate←$ᵗ Secret
      let result←RegistrationNativeSecretWordRecoveryBound.logged keySource candidate (RegistrationNativeSecretWordAliasPrior.client prior next)
      pure (candidate,result))}[pair.1∈pair.2.2.2] := by
  have swapped := (OracleComp.EvalDistEq.bind_bind_swap prior ($ᵗ Secret)
    (fun context candidate=>Prod.mk candidate <$>RegistrationNativeSecretWordRecoveryBound.logged keySource candidate (next context)))
    (fun pair=>pair.1∈pair.2.2.2)
  simpa only [RegistrationNativeSecretWordAliasPrior.logged_source,bind_assoc,map_bind,bind_pure_comp,
    Functor.map_map,decide_eq_true_eq] using swapped

structure Context (source : RegistrationNativeMldsa.Source) (n : Nat) (KemSK Physical Platform A : Type)
    (mode : PqxdhDeploymentInterface.Mode) where
  seed : PqxdhJointIdentity.IdentitySeed
  scalar : PqxdhJointGapDh.ScalarBytes
  sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply
  profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK
  front : RegistrationNativePlatformSecretWordOrdinary.State source Platform
  word : RegistrationNativeSecretWordInterpreter.State n KemSK
  materials : (RegistrationNativePairedServices.MaterialSpec n).QueryCache
  known : RegistrationNativeSelectiveHiddenService.KnownOracle.QueryCache
  physical : Physical
  work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (selected selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat →StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
local notation "Ctx"=>Context source n KemSK Physical Platform A mode
local notation "Trace"=>RegistrationNativeSecretWordFrontendTrace.State
local notation "FrontResult"=>((A ×RegistrationNativeLedger.State) ×RegistrationNativePlatformSecretWordOrdinary.State source Platform)
local notation "ClientResult"=>((FrontResult ×Trace) ×RegistrationNativePlatformRecordPartnerExposureClient.Private n KemSK Physical)

noncomputable def body (context : Ctx) :=
  RegistrationNativePlatformSecretWordFrontend.run (n:=n) setup checks wire source context.sign selectedOwner selectedAccept
    (setup.dh.publicKey context.scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    serverKeyId bounds mode context.work context.front

noncomputable def inner : Option Ctx →OracleComp Combined (Option (Ctx ×ClientResult))
  | none=>pure none
  | some context=>(fun result=>some (context,result)) <$>
      RegistrationNativePlatformRecordPartnerExposureClient.client setup wire context.sign context.seed context.scalar
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem selected context.profile.pairs
          context.profile.publicKey context.profile.challenge) physical
        (body setup checks wire source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer serverKeyId bounds mode context)
        RegistrationNativeSecretWordFrontendTrace.initial
        ((context.word,⟨fun _=>none,0,0,context.materials,context.known⟩),context.physical)

noncomputable def client (prior : ProbComp (Option Ctx)) :=
  RegistrationNativeSecretWordAliasPrior.client prior
    (inner setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical)

noncomputable def native
    (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (candidate : Secret) (context : Ctx) :=
  (simulateQ (RegistrationNativePlatformLorStatefulSupport.trace
    (RegistrationNativePlatformLorCtxClosed.implementation setup wire context.sign context.seed context.scalar candidate (unused candidate)
      selected context.profile.pairs context.profile.publicKey context.profile.challenge physical))
    (body setup checks wire source selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode context)).run
      (RegistrationNativeSecretWordFrontendTrace.initial,
        ((context.word,({RegistrationNativeHiddenService.initial with materials:=context.materials},context.known)),context.physical))

noncomputable def after
    (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (candidate : Secret) : Option Ctx →ProbComp Bool
  | none=>pure false
  | some context=>(fun result=>decide (RegistrationNativeSecretWordAliasExposureBound.Exposure
      (RegistrationNativeSecretWordMessage.input setup.joint setup.dh context.seed context.scalar)
      (RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh context.seed (setup.dh.publicKey context.scalar)))
      candidate result.2.1)) <$>
        native setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer serverKeyId bounds mode physical unused candidate context

noncomputable def game
    (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n))) (prior : ProbComp (Option Ctx)) : ProbComp Bool :=
  prior >>=fun context=>($ᵗ Secret >>=fun candidate=>
    after setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical unused candidate context)

/-- Actual prefix coins add neither key nor suffix queries; both complete-client bills are original qBuild+qFinish. -/
theorem client_bound (prior : ProbComp (Option Ctx)) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀context,some context∈support prior →RegistrationNativeInterface.Respects budget context.work) (kind : Kind) :
    (client setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical prior).IsQueryBoundP (Counted kind) (budget.cap 4+budget.cap 5) := by
  unfold client RegistrationNativeSecretWordAliasPrior.client
  apply (OracleComp.isQueryBoundP_bind (n:=0) (m:=budget.cap 4+budget.cap 5) ?_ ?_).mono (by omega)
  · apply RawCtxSourceOpen.simulate_bound _ (fun _=>False) _ prior 0 (isQueryBoundP_false prior 0)
    intro query
    cases kind <;> simp [RegistrationNativeSecretWordService.coins,Counted,
      RegistrationNativeSecretWordRecoveryCompiler.IsKey,RegistrationNativeSecretWordRecoveryCompiler.IsSuffix,
      RegistrationNativeSecretWord.IsKey,isQueryBoundP_query_iff]
  · intro context possible
    have reached := PqxdhDeploymentEnvironment.support_simulateQ_subset RegistrationNativeSecretWordService.coins prior possible
    cases context with
    | none=>trivial
    | some context=>
      simp only [inner,isQueryBoundP_map_iff]
      exact RegistrationNativePlatformRecordPartnerExposureSourceBound.client_bound setup wire context.sign context.seed context.scalar
        selected context.profile.pairs context.profile.publicKey context.profile.challenge physical checks source selectedOwner selectedAccept
        (setup.dh.publicKey context.scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        serverKeyId bounds mode context.work context.front context.word _ context.physical budget (bounded context reached) kind

/-- Each supported successful source context contributes exposure only to its own literal recovery hit. -/
theorem fixed (filler : PqxdhServerAuthKeySchedule.Output)
    (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (candidate : Secret) (context : Ctx) (empty : context.front.1.server.sessions=[]) :
    Pr{let flag←(after setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical unused candidate (some context))}[flag=true]≤
    Pr{let result←(RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (inner setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
        erased helper writer serverKeyId bounds mode physical (some context)))}[candidate∈result.2.2] := by
  have included := RegistrationNativePlatformRecordPartnerExposureSourceBound.cold setup wire context.sign context.seed context.scalar
    candidate filler (unused candidate) selected context.profile.pairs context.profile.publicKey context.profile.challenge physical checks source
    selectedOwner selectedAccept (setup.dh.publicKey context.scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased
    helper writer serverKeyId bounds mode context.work context.front context.word context.materials context.known context.physical empty
  simpa only [after,native,body,inner,RegistrationNativeSecretWordRecoveryBound.logged,simulateQ_map,StateT.run_map,
    prEvent_map,Prod.map_snd,decide_eq_true_eq] using included

/-- One complete independent prefix and one concrete recovery adversary bound the original warm source exposure. -/
theorem bound (filler : PqxdhServerAuthKeySchedule.Output)
    (unused : Secret →QueryImpl Combined (OracleComp (PqxdhRecordLiftInterface.WorldSpec n)))
    (prior : ProbComp (Option Ctx)) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : ∀context,some context∈support prior →RegistrationNativeInterface.Respects budget context.work)
    (empty : ∀context,some context∈support prior →context.front.1.server.sessions=[]) :
    Pr{let flag←(game setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical unused prior)}[flag=true]≤
    ENNReal.ofReal (RegistrationNativeSuffixKeyPrf.advantage setup.source
      (RegistrationNativeSuffixKeyRecovery.adversary setup.source
        (RegistrationNativeSecretWordRecoveryCompiler.guesses
          (client setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
            erased helper writer serverKeyId bounds mode physical prior))))+
      (budget.cap 4+budget.cap 5)*(256^160 : ℝ≥0∞)⁻¹+(budget.cap 4+budget.cap 5)*(256^32 : ℝ≥0∞)⁻¹ := by
  let next : Option Ctx →OracleComp Combined (Option (Ctx ×ClientResult)) :=inner setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
    erased helper writer serverKeyId bounds mode physical
  let hit (context : Option Ctx) (candidate : Secret) : ProbComp Bool :=
    (fun result=>decide (candidate∈result.2.2)) <$>RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate (next context)
  have included :
    Pr{let flag←(game setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical unused prior)}[flag=true]≤
    Pr{let flag←(prior >>=fun context=>($ᵗ Secret >>=fun candidate=>hit context candidate))}[flag=true] := by
    unfold game
    apply prEvent_bind_mono_of_forall_le_of_support
    intro context supported
    apply prEvent_bind_mono_of_forall_le
    intro candidate
    cases context with
    | none=>simp [after,hit,next,inner,RegistrationNativeSecretWordRecoveryBound.logged]
    | some context=>
      simpa only [hit,prEvent_map,decide_eq_true_eq] using
        fixed setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer serverKeyId bounds mode physical filler unused candidate context (empty context supported)
  have sourceMass :
    Pr{let flag←(prior >>=fun context=>($ᵗ Secret >>=fun candidate=>hit context candidate))}[flag=true]=
    Pr{let pair←(do
      let candidate←$ᵗ Secret
      let result←RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
        (client setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
          erased helper writer serverKeyId bounds mode physical prior)
      pure (candidate,result))}[pair.1∈pair.2.2.2] := by
    exact prior_hit setup.source prior next
  rw [sourceMass] at included
  exact included.trans (by simpa only [Nat.cast_add] using (RegistrationNativeSecretWordAliasPriorBound.literal_hit_bound setup.source _ (budget.cap 4+budget.cap 5)
    (client_bound setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical prior budget bounded .suffix)
    (client_bound setup checks wire source selected selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame
      erased helper writer serverKeyId bounds mode physical prior budget bounded .key)))

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged.client_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged.fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged.fixed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged.bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureAveraged.bound

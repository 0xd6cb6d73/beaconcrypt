-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeObservableHybrid
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformSource
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedTracedEarlySource

/-! Every original native ledger observer, including a target selector and its winning event separately, has the exact same uniform-provider full native execution law. The original actual startup prefix, all native callback failures and the chronological trace remain in the execution. No equality between distinct target ideal worlds is used. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι}

def outcomeDecision (observe : Value × RegistrationNativeLedger.State → Bool)
    {source : RegistrationNativeMldsa.Source}
    (outcome : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value) : Bool :=
  outcome.elim false (fun finished => observe finished.2.1)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
  (bounds : FreshBounds) (mode : Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : Budget) (selectedOwner : Fin (budget.create + 1)) (selectedAccept : Nat)
  (observe : Value × RegistrationNativeLedger.State → Bool)

noncomputable def started : ProbComp Bool := do
  let context ← RegistrationNativeG3NativeStartupAlias.prior (n := budget.cap 4 + budget.cap 5) setup wire source route ensureInit identityIndex serverKeyId
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selectedOwner
  let candidate ← $ᵗ MlKemSharedSecret
  outcomeDecision observe <$>
    RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId context.seed context.scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedOwner.val profile.pairs profile.publicKey profile.challenge candidate)
      none selectedOwner.val selectedAccept bounds mode adversary context.initialized

theorem after_source
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (context : RegistrationNativeG3NativeStartupAlias.Context source (budget.cap 4 + budget.cap 5))
    (supported : context ∈ support (RegistrationNativeG3NativeStartupAlias.prior setup wire source route ensureInit identityIndex serverKeyId))
    (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK) (candidate : MlKemSharedSecret) :
    (RegistrationNativeG3NativeStartupDecision.decision observe <$>
      (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem selectedOwner.val
        profile.pairs profile.publicKey profile.challenge candidate)
        (RegistrationNativeG3NativeStartupUniformValue.after setup checks wire source route serverKeyId selectedOwner.val selectedAccept bounds mode adversary context)).run'
          ((PqxdhLiveKemBirth.empty, none), ∅)) =ᵈ
      (outcomeDecision observe <$>
        RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId context.seed context.scalar candidate
          (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedOwner.val profile.pairs profile.publicKey profile.challenge candidate)
          none selectedOwner.val selectedAccept bounds mode adversary context.initialized) := by
  simp only [RegistrationNativeG3NativeStartupAlias.prior, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨seed, _seed, scalar, _scalar, initialized, reached, rfl⟩ := supported
  rcases initialized with ⟨_ | born, world⟩
  · simp only [RegistrationNativeG3NativeStartupUniformValue.after, RegistrationNativeG3MaterializedTracedStartup.fullAfter,
      simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, RegistrationNativeG3NativeStartupDecision.decision,
      outcomeDecision, Option.elim_none]
    exact .rfl
  · have actual := RegistrationNativeG3MaterializedTracedEarlySource.after_source setup checks wire source route ensureInit identityIndex serverKeyId seed scalar
      selectedOwner.val profile.pairs profile.publicKey profile.challenge candidate selectedAccept bounds mode adversary budget bounded born world reached
    have mapped := actual.map (outcomeDecision observe)
    have compared := _root_.EvalDistEq.of_evalDist_eq mapped.symm.evalDist_eq
    simpa only [RegistrationNativeG3NativeStartupUniformValue.after, simulateQ_map, StateT.run'_eq, StateT.run_map,
      Functor.map_map, RegistrationNativeG3NativeStartupDecision.decision, outcomeDecision, Option.elim_some] using compared

theorem conditional_source
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    RegistrationNativeG3NativeStartupUniformSource.conditional (n := budget.cap 4 + budget.cap 5) setup checks wire source route
      ensureInit identityIndex serverKeyId selectedAccept bounds mode adversary budget selectedOwner
      (fun _ result => RegistrationNativeG3NativeStartupDecision.decision observe result) =ᵈ
      started setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe := by
  unfold RegistrationNativeG3NativeStartupUniformSource.conditional started
  apply OracleComp.EvalDistEq.bind_congr_of_support
  exact fun context supported => _root_.EvalDistEq.bind_right _ fun profile =>
    _root_.EvalDistEq.bind_right _ fun candidate =>
      after_source setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe
        bounded context supported profile candidate

theorem uniform_source
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    RegistrationNativeObservableHybrid.uniform (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
      bounds mode adversary budget selectedOwner selectedAccept observe =ᵈ
      started setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe := by
  exact (RegistrationNativeG3NativeStartupUniformSource.uniform_source (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    selectedAccept bounds mode adversary budget bounded selectedOwner (fun _ result => RegistrationNativeG3NativeStartupDecision.decision observe result)).trans
    (conditional_source setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe bounded)

/-- Each native observer pays its own explicit source, KDF and KEM reductions to this same full native uniform-provider execution. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    (RegistrationNativeExperiment.profile (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode adversary (fun result => observe (result.1, result.2.1))).boolDistance
      (started setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe) ≤
      RegistrationNativeObservableHybrid.keyLoss (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
        bounds mode adversary budget selectedOwner selectedAccept observe +
      RegistrationNativeObservableHybrid.kemLoss (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
        bounds mode adversary budget selectedOwner selectedAccept observe := by
  have same := (uniform_source setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe bounded).evalDist_eq
  simpa only [ProbComp.boolDistance, same] using
    RegistrationNativeObservableHybrid.source_distance (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
      bounds mode adversary budget selectedOwner selectedAccept observe representation correct functional bounded

end BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.after_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.after_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.conditional_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.conditional_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.uniform_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource.source_distance

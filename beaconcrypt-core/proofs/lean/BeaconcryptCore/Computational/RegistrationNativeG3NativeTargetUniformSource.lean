-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform
import BeaconcryptCore.Computational.RegistrationNativeProductionPrior
import BeaconcryptCore.Computational.RegistrationNativeG3NativeStartupUniformSource

/-! The production good-target observation of the whole uniform KEM client is exactly its complete cold known108 trace game. The same actual startup support supplies the native frontend and reached World; independent KEM profile/candidate draws only commute in distribution. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniformSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec .P) Value)
  (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))

private noncomputable def started : ProbComp Bool := do
  let context ← RegistrationNativeG3NativeStartupAlias.prior (n := budget.cap 4 + budget.cap 5) setup wire source route ensureInit identityIndex serverKeyId
  let profile ← RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create target.2
  let candidate ← $ᵗ MlKemSharedSecret
  (fun outcome => @decide (RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget target claim outcome) (Classical.propDecidable _)) <$>
    RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId context.seed context.scalar candidate
      (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem target.2.val profile.pairs profile.publicKey profile.challenge candidate)
      none target.2.val target.1.val bounds .P adversary context.initialized

private theorem started_source :
    started setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim =ᵈ
      RegistrationNativeG3NativeTargetUniform.full setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim := by
  simp only [started, RegistrationNativeG3NativeStartupAlias.prior, RegistrationNativeG3NativeTargetUniform.full,
    RegistrationNativeSelectiveRecordTraceUniformSecurity.prior, RegistrationNativeG3MaterializedTracedStartup.fullGame,
    bind_assoc, pure_bind, map_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  let family := RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create target.2
  let startup := RegistrationNativeG3MaterializedTracedStartup.startup (n := budget.cap 4 + budget.cap 5)
    setup wire route source ensureInit identityIndex serverKeyId seed
  let next := fun (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK) (candidate : MlKemSharedSecret)
      (initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) =>
    (fun outcome => @decide (RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget target claim outcome) (Classical.propDecidable _)) <$>
      RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId seed scalar candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem target.2.val profile.pairs profile.publicKey profile.challenge candidate)
        none target.2.val target.1.val bounds .P adversary initialized
  change (startup >>= fun initialized => family >>= fun profile => ($ᵗ MlKemSharedSecret) >>= fun candidate => next profile candidate initialized) =ᵈ
    (family >>= fun profile => ($ᵗ MlKemSharedSecret) >>= fun candidate => startup >>= next profile candidate)
  symm
  calc
    _ =ᵈ (family >>= fun profile => startup >>= fun initialized => ($ᵗ MlKemSharedSecret) >>= fun candidate => next profile candidate initialized) := by
      apply _root_.EvalDistEq.bind_right
      intro profile
      exact OracleComp.EvalDistEq.bind_bind_swap ($ᵗ MlKemSharedSecret) startup (fun candidate initialized => next profile candidate initialized)
    _ =ᵈ _ := OracleComp.EvalDistEq.bind_bind_swap family startup
      (fun profile initialized => ($ᵗ MlKemSharedSecret) >>= fun candidate => next profile candidate initialized)

private theorem after_source
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (context : RegistrationNativeG3NativeStartupAlias.Context source (budget.cap 4 + budget.cap 5))
    (supported : context ∈ support (RegistrationNativeG3NativeStartupAlias.prior setup wire source route ensureInit identityIndex serverKeyId))
    (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK) (candidate : MlKemSharedSecret) :
    (RegistrationNativeProductionPrior.decision setup wire serverKeyId budget target claim <$>
      (simulateQ (RegistrationNativeOpenKeyKemEarlySource.reference setup.baseImpl setup.kem target.2.val
        profile.pairs profile.publicKey profile.challenge candidate)
        (RegistrationNativeG3NativeStartupUniformValue.after setup checks wire source route serverKeyId target.2.val target.1.val bounds .P adversary context)).run'
          ((PqxdhLiveKemBirth.empty, none), ∅)) =ᵈ
      ((fun outcome => @decide (RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget target claim outcome) (Classical.propDecidable _)) <$>
        RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId context.seed context.scalar candidate
          (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem target.2.val profile.pairs profile.publicKey profile.challenge candidate)
          none target.2.val target.1.val bounds .P adversary context.initialized) := by
  simp only [RegistrationNativeG3NativeStartupAlias.prior, mem_support_bind_iff, mem_support_pure_iff] at supported
  obtain ⟨seed, _seed, scalar, _scalar, initialized, reached, rfl⟩ := supported
  rcases initialized with ⟨_ | born, world⟩
  · simp only [RegistrationNativeG3NativeStartupUniformValue.after, RegistrationNativeG3MaterializedTracedStartup.fullAfter,
      simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, RegistrationNativeProductionPrior.decision,
      Option.elim_none, RegistrationNativeG3NativeTargetStartup.Good, decide_false]
    exact .rfl
  · have actual := RegistrationNativeG3MaterializedTracedEarlySource.after_source setup checks wire source route ensureInit identityIndex serverKeyId seed scalar
      target.2.val profile.pairs profile.publicKey profile.challenge candidate target.1.val bounds .P adversary budget bounded born world reached
    have mapped := actual.map (fun outcome => @decide (RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget target claim outcome) (Classical.propDecidable _))
    have compared := _root_.EvalDistEq.of_evalDist_eq mapped.symm.evalDist_eq
    simpa only [RegistrationNativeG3NativeStartupUniformValue.after, simulateQ_map, StateT.run'_eq, StateT.run_map,
      Functor.map_map, RegistrationNativeProductionPrior.decision, RegistrationNativeProductionKeyBound.decision,
      RegistrationNativeG3NativeTargetStartup.Good, Option.elim_some, RegistrationNativePrekeyEvents.targetEvent] using compared

/-- The same supported conditional uniform production good-target observation has exactly the complete cold known108 target law. -/
theorem conditional_source (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    RegistrationNativeG3NativeStartupUniformSource.conditional (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
      target.1.val bounds .P adversary budget target.2 (fun _ result => RegistrationNativeProductionPrior.decision setup wire serverKeyId budget target claim result) =ᵈ
      RegistrationNativeG3NativeTargetUniform.full setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim := by
  refine _root_.EvalDistEq.trans ?_ (started_source setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim)
  unfold RegistrationNativeG3NativeStartupUniformSource.conditional started
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro context supported
  apply _root_.EvalDistEq.bind_right
  intro profile
  apply _root_.EvalDistEq.bind_right
  intro candidate
  exact after_source setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim bounded context supported profile candidate

/-- The whole unchanged production uniform KEM branch has the exact original good target probability of the complete cold known108 game. -/
theorem uniform_source (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    RegistrationNativeProductionPrior.uniform setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim =ᵈ
      RegistrationNativeG3NativeTargetUniform.full setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim := by
  have actual := RegistrationNativeG3NativeStartupUniformSource.uniform_source (n := budget.cap 4 + budget.cap 5) setup checks wire source route ensureInit identityIndex serverKeyId
    target.1.val bounds .P adversary budget bounded target.2 (fun _ result => RegistrationNativeProductionPrior.decision setup wire serverKeyId budget target claim result)
  exact actual.trans (conditional_source setup checks wire route source ensureInit identityIndex serverKeyId bounds adversary budget target claim bounded)

end BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniformSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniformSource.conditional_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniformSource.conditional_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniformSource.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniformSource.uniform_source

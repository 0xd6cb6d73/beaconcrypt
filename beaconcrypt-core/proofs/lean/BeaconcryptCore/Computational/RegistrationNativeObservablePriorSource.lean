-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeObservableUniformSource
import BeaconcryptCore.Computational.RegistrationNativeSelectedTargetSource
import BeaconcryptCore.Computational.RegistrationNativeG3NativeTargetUniform

/-! Complete ledger observations commute with the independent KEM-family and candidate prior while retaining actual effectful startup. Selected good-target provenance is averaged over that same prior, retaining the selector on the original ledger in every branch. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open PqxdhKemIndCca
open RegistrationNativeSelectiveRecordTraceUniformSecurity (Context prior provider)
variable {ι KemSK Value : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
  (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
  (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
  (budget : Budget) (selectedOwner : Fin (budget.create + 1)) (selectedAccept : Nat)
  (observe : Value × RegistrationNativeLedger.State → Bool)

noncomputable def full : ProbComp Bool := do
  let context ← prior setup budget selectedOwner
  RegistrationNativeObservableUniformSource.outcomeDecision observe <$>
    RegistrationNativeG3MaterializedTracedStartup.fullGame (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
      context.seed context.scalar context.candidate (provider setup selectedOwner.val context) none selectedOwner.val selectedAccept bounds mode adversary

/-- Only independent prior draws commute; the actual initialized branch and its complete final ledger remain together. -/
theorem started_source :
    RegistrationNativeObservableUniformSource.started setup checks wire route source ensureInit identityIndex serverKeyId
      bounds mode adversary budget selectedOwner selectedAccept observe =ᵈ
      full setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe := by
  simp only [RegistrationNativeObservableUniformSource.started, RegistrationNativeG3NativeStartupAlias.prior,
    full, prior, RegistrationNativeG3MaterializedTracedStartup.fullGame, bind_assoc, pure_bind, map_bind]
  apply _root_.EvalDistEq.bind_right
  intro seed
  apply _root_.EvalDistEq.bind_right
  intro scalar
  let family := RegistrationNativeG3NativeRepeatUniformBound.prior setup.baseImpl setup.kem budget.create selectedOwner
  let startup := RegistrationNativeG3MaterializedTracedStartup.startup (n := budget.cap 4 + budget.cap 5)
    setup wire route source ensureInit identityIndex serverKeyId seed
  let next := fun (profile : RegistrationNativeSecretWordAliasOuter.Profile KemSK) (candidate : MlKemSharedSecret)
      (initialized : Option (RegistrationNativeHiddenStartup.Started source) × PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) =>
    RegistrationNativeObservableUniformSource.outcomeDecision observe <$>
      RegistrationNativeG3MaterializedTracedStartup.fullAfter setup checks wire route source serverKeyId seed scalar candidate
        (RegistrationNativeSecretWordKemEarly.actual setup.baseImpl setup.kem selectedOwner.val profile.pairs profile.publicKey profile.challenge candidate)
        none selectedOwner.val selectedAccept bounds mode adversary initialized
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

/-- Each selected winning observer and selector observer has this same whole-prior source law. -/
theorem uniform_source
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    RegistrationNativeObservableHybrid.uniform (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
      bounds mode adversary budget selectedOwner selectedAccept observe =ᵈ
      full setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe :=
  (RegistrationNativeObservableUniformSource.uniform_source setup checks wire route source ensureInit identityIndex serverKeyId
    bounds mode adversary budget selectedOwner selectedAccept observe bounded).trans
    (started_source setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe)

/-- The original native profile reaches the whole-prior execution with its observer-specific original KDF and KEM reductions. -/
theorem source_distance (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhFullSecretInputKdf.SourceFullCorrect setup.source setup.hmac)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation setup.kem)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication)) :
    (RegistrationNativeExperiment.profile (n := budget.cap 4 + budget.cap 5) setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode adversary (fun result => observe (result.1, result.2.1))).boolDistance
      (full setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe) ≤
      RegistrationNativeObservableHybrid.keyLoss (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
        bounds mode adversary budget selectedOwner selectedAccept observe +
      RegistrationNativeObservableHybrid.kemLoss (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
        bounds mode adversary budget selectedOwner selectedAccept observe := by
  have same := (started_source setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget selectedOwner selectedAccept observe).evalDist_eq
  simpa only [ProbComp.boolDistance, same] using
    RegistrationNativeObservableUniformSource.source_distance setup checks wire route source ensureInit identityIndex serverKeyId
      bounds mode adversary budget selectedOwner selectedAccept observe representation correct functional bounded


noncomputable def selectedGood (target : Fin budget.accept × Fin budget.capacity)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool)
    (result : Value × RegistrationNativeLedger.State) : Bool :=
  @decide (RegistrationNativePrekeyEvents.GoodAt setup.source.crypto wire serverKeyId budget target claim
    (result.1, (result.2, ())) ∧ select result = true) (Classical.propDecidable _)

theorem good_outcome (target : Fin budget.accept × Fin budget.capacity)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool)
    (outcome : RegistrationNativeEntropyRun.Outcome (RegistrationNativePublicFrontend.State source × RegistrationNativeG2Trace.State) Value) :
    RegistrationNativeObservableUniformSource.outcomeDecision
      (selectedGood setup wire serverKeyId budget target claim select) outcome = true ↔
      RegistrationNativeG3NativeTargetStartup.Good setup wire serverKeyId budget target claim outcome ∧
        RegistrationNativeSelectedRecordTrace.outcomeSelected select outcome = true := by
  cases outcome <;> simp only [RegistrationNativeObservableUniformSource.outcomeDecision,
    RegistrationNativeSelectedRecordTrace.outcomeSelected, RegistrationNativeG3NativeTargetStartup.Good,
    selectedGood, Option.elim_none, Option.elim_some, Bool.false_eq_true, false_and, decide_eq_true_eq]

noncomputable def selectedHit (target : Fin budget.accept × Fin budget.capacity)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool) : ProbComp Bool := do
  let context ← prior setup budget target.2
  (fun outcome => @decide
      (RegistrationNativeSelectiveRecordTraceTarget.Hit setup context.seed context.scalar context.candidate claim outcome ∧
        RegistrationNativeSelectedRecordTrace.outcomeSelected select outcome = true) (Classical.propDecidable _)) <$>
    RegistrationNativeG3MaterializedTracedStartup.fullGame (n := budget.cap 4 + budget.cap 5) setup checks wire route source ensureInit identityIndex serverKeyId
      context.seed context.scalar context.candidate (provider setup target.2.val context) none target.2.val target.1.val bounds mode adversary

/-- The whole-prior original good-target share has its selected receipt on the same final ledger in every supported branch. -/
theorem good_probability (target : Fin budget.accept × Fin budget.capacity)
    (claim : Value → Option (Nat × Pqxdh.Bytes)) (select : Value × RegistrationNativeLedger.State → Bool)
    (bounded : ∀ publication, RegistrationNativeInterface.Respects budget (adversary publication))
    (readback : RegistrationNativeWire.InitReadBack wire) (responseReadback : RegistrationNativeWire.ResponseReadBack wire) :
    Pr{let won ← (full setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget target.2 target.1.val
      (selectedGood setup wire serverKeyId budget target claim select))}[won = true] ≤
    Pr{let won ← (selectedHit setup checks wire route source ensureInit identityIndex serverKeyId bounds mode adversary budget target claim select)}[won = true] := by
  unfold full selectedHit
  apply prEvent_bind_mono_of_forall_le_of_support
  intro context sampled
  obtain ⟨reserved, chosen, chosenAt, publicKey⟩ := RegistrationNativeG3NativeTargetUniform.prior_selected setup budget target.2 context sampled
  simp only [prEvent_map, good_outcome, decide_eq_true_eq]
  have compared := RegistrationNativeSelectedTargetSource.startup_probability (source := source) setup checks wire route context.seed context.scalar
    context.profile.pairs chosen context.profile.challenge serverKeyId bounds mode budget target ensureInit identityIndex adversary
    context.candidate claim select bounded reserved chosenAt readback responseReadback
  rw [publicKey] at compared
  simpa only [provider] using compared

end BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.started_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.started_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.uniform_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.uniform_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.source_distance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.source_distance

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.good_outcome' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.good_outcome

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.good_probability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeObservablePriorSource.good_probability

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerSafe
/-! The actual dynamic Server source publication preserves the complete Word observer until its literal role installation suffix. A material service establishes the same descriptor before either known or hidden publication, and all failures remain in the source tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerTrace
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativeSecretWordFrontendTrace (State handler)
open RegistrationNativeSecretWordAtomInstallTrace (count atom)
open RegistrationNativePlatformPairedServerSafe (output after)
variable {n : Nat} {KemSK E Platform A : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
private theorem forward_run (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (EnvEffects n) A) (before : PublicState Platform) :
    simulateQ (RegistrationNativePlatformSecretWordAtomEffects.effects (KemSK := KemSK))
      ((simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
        (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work)).run before) =
      (fun value => (value, before)) <$> simulateQ RegistrationNativePlatformSecretWordAtomEffects.env work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.forward,
      RegistrationNativePlatformPairedServerCompiler.target, RegistrationNativePlatformEffectCompiler.effect,
      StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind,
      RegistrationNativePlatformSecretWordAtomEffects.effects, RegistrationNativePlatformSecretWordAtomEffects.env]
    apply bind_congr
    intro reply
    exact ih reply

private theorem branch_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (before : PublicState Platform) :
    simulateQ (RegistrationNativePlatformSecretWordAtomEffects.effects (KemSK := KemSK))
      ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before) = (do
      let reached ← simulateQ (RegistrationNativePlatformSecretWordAtomEffects.effects (KemSK := KemSK))
        ((RegistrationNativePlatformBoundCompiler.compile source view failure allocation erased helper sign writer initial (output choice)).run before)
      (fun value => (value, reached.2)) <$> simulateQ RegistrationNativePlatformSecretWordAtomEffects.env (after control choice reached.1)) := by
  cases choice <;>
    simp only [RegistrationNativePlatformServerRestrictedService.branch, RegistrationNativePlatformPairedServerCompiler.known,
      RegistrationNativePlatformPairedServerCompiler.hidden, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, RegistrationNativePlatformPairedServerCompiler.target, output, after]
  all_goals
    apply bind_congr
    intro reached
    exact forward_run source view failure allocation erased helper sign writer initial _ _ reached.2


/-- The actual complete stateful Server branch has at most its one same-descriptor role attempt. -/
theorem branch_count (role : Role) (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (sourceBefore : PublicState Platform) (before : State)
    (result : (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × PublicState Platform) × State)
    (supported : result ∈ support ((simulateQ handler
      (simulateQ (RegistrationNativePlatformSecretWordAtomEffects.effects (KemSK := KemSK))
        ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run sourceBefore))).run before)) :
    count role result.2 ≤ count role before + (if role = .server then 1 else 0) * atom before.current := by
  rw [branch_run, simulateQ_bind, StateT.run_bind] at supported
  rw [RegistrationNativePlatformSecretWordAtomEffects.state_neutral _
    (RegistrationNativePlatformPairedPublicationFree.compile source view failure allocation erased helper sign writer initial (output choice)) sourceBefore before] at supported
  simp only [bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨reached, _actual, continued⟩ := supported
  simp only [simulateQ_map, StateT.run_map, support_map] at continued
  obtain ⟨finished, actual, equal⟩ := continued
  cases equal
  apply (RegistrationNativePlatformSecretWordAtomEffects.continuation role (after control choice reached.1)
    (if role = .server then 1 else 0) _ before finished actual).2
  cases choice with
  | known value => exact RegistrationNativePlatformPairedInstallFacts.server_known_bound role control reached.1
  | hidden reference => exact RegistrationNativePlatformPairedInstallFacts.server_hidden_bound role control reference.slot reached.1

omit primitive in
def embed : QueryImpl (RegistrationNativePlatformSecretWordBuild.Spec n)
    (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK)) :=
  RegistrationNativeSecretWordInterface.liftLocal false ∘ₛ RegistrationNativePlatformSecretWordBuild.wordEmbedding

private theorem service_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeSecretWordMessage.Message) (before : PublicState Platform) :
    simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformSecretWordBuild.service source view failure allocation erased helper sign writer control initial message).run before) = (do
      let selected ← ((RegistrationNativeSecretWordInterface.Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) :
        OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) _)
      match selected with
      | none => pure (.ok (.Err control), before)
      | some choice =>
          simulateQ RegistrationNativePlatformSecretWordAtomEffects.effects
            ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before)) := by
  simp only [RegistrationNativePlatformSecretWordBuild.service, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, simulateQ_spec_query, embed, QueryImpl.apply_compose,
    RegistrationNativePlatformSecretWordBuild.wordEmbedding, RegistrationNativeSecretWordInterface.demand,
    RegistrationNativeSecretWordInterface.liftLocal, simulateQ_spec_query, bind_map_left]
  apply bind_congr
  intro selected
  cases selected with
  | none => simp only [StateT.run_pure, simulateQ_pure]
  | some choice =>
    simp only [RegistrationNativePlatformSecretWordBuild.liftEffects, RegistrationNativePlatformInterpret.state,
      StateT.run, ← QueryImpl.simulateQ_compose]
    rw [RegistrationNativePlatformSecretWordAtomEffects.embedding]

/-- The actual symbolic material demand establishes its own descriptor before every stateful publication/installation outcome. -/
theorem service_count (role : Role) (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeSecretWordMessage.Message) (sourceBefore : PublicState Platform) (before : State)
    (result : (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × PublicState Platform) × State)
    (supported : result ∈ support ((simulateQ handler
      (simulateQ (embed (n := n) (KemSK := KemSK))
        ((RegistrationNativePlatformSecretWordBuild.service source view failure allocation erased helper sign writer control initial message).run sourceBefore))).run before)) :
    count role result.2 ≤ count role before + (if role = .server then 1 else 0) * atom (some message) := by
  rw [service_run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
  simp only [handler, StateT.run, RegistrationNativeSecretWordFrontendTrace.begin,
    RegistrationNativeSecretWordFrontendTrace.finish, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨selected, _actual, supported⟩ := supported
  cases selected with
  | none =>
    rw [simulateQ_pure] at supported
    change result ∈ support (pure ((.ok (.Err control), sourceBefore), ⟨some message, before.events ++ [.demand message]⟩)) at supported
    rw [mem_support_pure_iff] at supported
    cases supported
    simp only [count, List.countP_append, List.countP_singleton,
      RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero]
    omega
  | some choice =>
    let afterDemand : State := ⟨some message, before.events ++ [RegistrationNativeSecretWordFrontendTrace.Event.demand message]⟩
    have actual : result ∈ support ((simulateQ handler
        (simulateQ (RegistrationNativePlatformSecretWordAtomEffects.effects (n := n) (KemSK := KemSK))
          ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run sourceBefore))).run afterDemand) := by
      simpa only [StateT.run, afterDemand] using supported
    have bounded := branch_count (n := n) (KemSK := KemSK) source view failure allocation erased helper sign writer role control initial choice sourceBefore
      afterDemand result actual
    simpa only [afterDemand, count, List.countP_append, List.countP_singleton,
      RegistrationNativeSecretWordAtomInstallTrace.attempt, Bool.false_eq_true, ite_false, Nat.add_zero] using bounded

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerTrace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerTrace.branch_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerTrace.branch_count

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerTrace.service_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAtomServerTrace.service_count

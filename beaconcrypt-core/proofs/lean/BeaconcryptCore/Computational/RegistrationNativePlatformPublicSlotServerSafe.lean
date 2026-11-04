-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEnvSuffix
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerFacts
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerSafe
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
/-! The actual corrected Server publication is noninstalling until its literal final continuation. That continuation uses precisely the material choice returned by its preceding demand. Failed publication and insertion outcomes remain part of the same source tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePlatformPublicSlotKind (State handler Safe)
open RegistrationNativePlatformPublicSlotSuffix (Ready)
open RegistrationNativePlatformBoundCompiler (PublicState)
variable {n : Nat} {KemSK E Platform A : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem forward_run (initial : RegistrationBoundKeySchedule.PublicInitial) (output : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp (EnvEffects n) A) (before : PublicState Platform) :
    simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
      ((simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
        (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work)).run before) =
      (fun value => (value, before)) <$> simulateQ RegistrationNativePairedCompile.effects work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.forward,
      RegistrationNativePlatformPairedServerCompiler.target, RegistrationNativePlatformEffectCompiler.effect,
      StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind,
      RegistrationNativePlatformPublicSlotEffects.effects, RegistrationNativePairedCompile.effects]
    apply bind_congr
    intro reply
    exact ih reply

def output : Choice n → PqxdhServerAuthKeySchedule.Output
  | .known value => value
  | .hidden reference => PqxdhDeploymentHiddenLayout.joinOutput reference.material RegistrationBoundPublication.fixedSeed

def after (control : pqxdh.ServerState) : Choice n →
    RustM (RegistrationWorldServerPublication.Result (alloc.vec.Vec U8)) →
    OracleComp (EnvEffects n) (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)))
  | .known _, published => RegistrationNativePairedServerService.knownAfter control published
  | .hidden reference, published => RegistrationHiddenInstall.after control reference.slot published

private theorem branch_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (before : PublicState Platform) :
    simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
      ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before) = (do
      let reached ← simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
        ((RegistrationNativePlatformBoundCompiler.compile source view failure allocation erased helper sign writer initial (output choice)).run before)
      (fun value => (value, reached.2)) <$> simulateQ RegistrationNativePairedCompile.effects (after control choice reached.1)) := by
  cases choice <;>
    simp only [RegistrationNativePlatformServerRestrictedService.branch, RegistrationNativePlatformPairedServerCompiler.known,
      RegistrationNativePlatformPairedServerCompiler.hidden, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, RegistrationNativePlatformPairedServerCompiler.target, output, after]
  all_goals
    apply bind_congr
    intro reached
    exact forward_run source view failure allocation erased helper sign writer initial _ _ reached.2

/-- The actual stateful known/hidden Server branch checks every final known or hidden kernel constructor against the same raw demand reply. -/
theorem branch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (sourceBefore : PublicState Platform)
    (before : State n) (ready : Ready choice 1 before)
    (result : (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × PublicState Platform) × State n)
    (supported : result ∈ support ((simulateQ handler
      (simulateQ (RegistrationNativePlatformPublicSlotEffects.effects (KemSK := KemSK))
        ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run sourceBefore))).run before)) :
    result.2.bad = false := by
  rw [branch_run, simulateQ_bind, StateT.run_bind] at supported
  rw [RegistrationNativePlatformPublicSlotEffects.state_neutral _
    (RegistrationNativePlatformPairedPublicationFree.compile source view failure allocation erased helper sign writer initial (output choice)) sourceBefore before] at supported
  simp only [bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨reached, _actual, continued⟩ := supported
  simp only [simulateQ_map, StateT.run_map, support_map] at continued
  obtain ⟨finished, actual, rfl⟩ := continued
  apply RegistrationNativePlatformPublicSlotEnvSuffix.continuation .server choice (after control choice reached.1) _ _ before ready finished actual
  · cases choice with
    | known output => exact RegistrationNativePlatformPairedInstallFacts.server_known_bound .server control reached.1
    | hidden reference => exact RegistrationNativePlatformPairedInstallFacts.server_hidden_bound .server control reference.slot reached.1
  · cases choice with
    | known output => exact RegistrationNativePlatformPublicSlotServerFacts.server_known_allowed output control reached.1
    | hidden reference => exact RegistrationNativePlatformPublicSlotServerFacts.server_hidden_allowed reference control reached.1

def embed : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK))
  | .inl message => RegistrationNativePlatformPublicSlotEffects.demand message
  | .inr query => RegistrationNativePlatformPublicSlotEffects.effects query

private theorem service_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : Message) (before : PublicState Platform) :
    simulateQ (embed (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run before) = (do
      let selected ← RegistrationNativePlatformPublicSlotEffects.demand (n := n) (KemSK := KemSK) message
      match selected with
      | none => pure (.ok (.Err control), before)
      | some choice => simulateQ RegistrationNativePlatformPublicSlotEffects.effects ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before)) := by
  simp only [RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, simulateQ_bind, simulateQ_spec_query,
    embed, bind_map_left]
  apply bind_congr
  intro selected
  cases selected with
  | none => rfl
  | some choice =>
    simp only [RegistrationNativePlatformServerFrontendCompiler.liftEffects, StateT.run,
      ← QueryImpl.simulateQ_compose]
    have joined : embed (n := n) (KemSK := KemSK) ∘ₛ RegistrationNativePlatformServerFrontendCompiler.embed = RegistrationNativePlatformPublicSlotEffects.effects := by
      funext query
      simp only [QueryImpl.compose, RegistrationNativePlatformServerFrontendCompiler.embed, simulateQ_spec_query, embed]
    rw [joined]

/-- The executable new Server material service checks constructor-kind matching for every source state and every failure reply. -/
theorem service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : Message) (sourceBefore : PublicState Platform) :
    Safe (simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run sourceBefore)) := by
  intro before result clean supported
  rw [service_run, simulateQ_bind, StateT.run_bind] at supported
  simp only [RegistrationNativePlatformPublicSlotEffects.demand, simulateQ_spec_query,
    handler, StateT.run, bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨selected, _actual, continued⟩ := supported
  have stored := RegistrationNativePlatformPublicSlotEffects.demand_step (KemSK := KemSK) message selected before
  cases selected with
  | none =>
    exact RegistrationNativePlatformPublicSlotKind.pure_safe _ _ result (stored.1.trans clean) continued
  | some choice =>
    exact branch source view failure allocation erased helper sign writer control initial choice sourceBefore _
      ⟨stored.1.trans clean, Or.inr stored.2⟩ result continued

omit primitive in
private theorem lift_effects_safe (work : StateT (PublicState Platform) (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : RegistrationNativePlatformPairedPublicationFree.Quiet work) (before : PublicState Platform) :
    Safe (simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.liftEffects work).run before)) := by
  change Safe (simulateQ embed (simulateQ RegistrationNativePlatformServerFrontendCompiler.embed (work.run before)))
  rw [← QueryImpl.simulateQ_compose]
  have joined : embed (n := n) (KemSK := KemSK) ∘ₛ RegistrationNativePlatformServerFrontendCompiler.embed = RegistrationNativePlatformPublicSlotEffects.effects := by
    funext query
    simp only [QueryImpl.compose, RegistrationNativePlatformServerFrontendCompiler.embed, simulateQ_spec_query, embed]
  rw [joined]
  exact RegistrationNativePlatformPublicSlotEffects.program_safe _ (quiet before)

omit primitive in
private theorem effect_quiet (query : (EnvEffects n).Domain)
    (free : ∀ role, ¬ RegistrationNativeSecretWordAtomInstallCaps.InstallEnv role query) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformEffectCompiler.effect (Platform := Platform) query) := by
  intro before
  simp only [RegistrationNativePlatformEffectCompiler.effect, StateT.run_lift, bind_pure_comp, map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr free) (fun _ => trivial)

/-- Every literal corrected Server frontend leaf checks constructor-kind matching, including real reserve and source writer outcomes. -/
theorem target (reserve : StateT Platform ProbComp Bool)
    (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain) (before : PublicState Platform) :
    Safe (simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reserve query).run before)) := by
  cases query with
  | pin current =>
    apply lift_effects_safe
    exact RegistrationNativePlatformPairedPublicationFree.bind_quiet _ _
      (effect_quiet _ (by intro role; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]))
      (fun _ => RegistrationNativePlatformPairedPublicationFree.pure_quiet _)
  | reserve =>
    apply lift_effects_safe
    intro current
    simp only [RegistrationNativePlatformBoundCompiler.liftPlatform, StateT.run, map_eq_bind_pure_comp]
    exact allQueriesSatisfy_bind (RegistrationNativePlatformPairedPublicationFree.platform_quiet reserve current.2) (fun _ => trivial)
  | present keyId =>
    apply lift_effects_safe
    exact effect_quiet _ (by intro role; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv])
  | service control initial message => exact service source view failure allocation erased helper sign writer control initial message before

/-- The entire actual free frontend controller inherits the literal leaf certificate with full returned source state. -/
theorem program (reserve : StateT Platform ProbComp Bool)
    (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A) (before : PublicState Platform) :
    Safe (simulateQ (embed (n := n) (KemSK := KemSK))
      ((simulateQ (RegistrationNativePlatformServerFrontendCompiler.target source view failure allocation erased helper sign writer reserve) work).run before)) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]; exact RegistrationNativePlatformPublicSlotKind.pure_safe _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact RegistrationNativePlatformPublicSlotKind.bind_safe _ _ (target source view failure allocation erased helper sign writer reserve query before)
      (fun reached => ih reached.1 reached.2)
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.branch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.service
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.target
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe.program

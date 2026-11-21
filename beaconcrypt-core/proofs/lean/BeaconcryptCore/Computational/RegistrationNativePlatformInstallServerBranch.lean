-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInstallEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedServerSafe
import BeaconcryptCore.Computational.RegistrationNativeInstallAfter
/-! The actual dynamic Server source publication preserves the complete Word observer until its literal role installation suffix. A material service establishes the same descriptor before either known or hidden publication, and all failures remain in the source tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerBranch
open PqxdhRecordLiftInterface (EnvEffects Role)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativeG2Trace (State handler)
open RegistrationNativeInstallOrdinals (messages)
open RegistrationNativeInstallInsert (success)
open RegistrationNativeRelatedFamily (Message)
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
    simulateQ (RegistrationNativePlatformInstallEffects.effects (KemSK := KemSK))
      ((simulateQ (RegistrationNativePlatformPairedServerCompiler.target source view failure allocation erased helper sign writer initial output)
        (simulateQ RegistrationNativePlatformPairedServerCompiler.forward work)).run before) =
      (fun value => (value, before)) <$> simulateQ RegistrationNativePlatformInstallEffects.env work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, RegistrationNativePlatformPairedServerCompiler.forward,
      RegistrationNativePlatformPairedServerCompiler.target, RegistrationNativePlatformEffectCompiler.effect,
      StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind,
      RegistrationNativePlatformInstallEffects.effects, RegistrationNativePlatformInstallEffects.env]
    apply bind_congr
    intro reply
    exact ih reply

private theorem branch_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (before : PublicState Platform) :
    simulateQ (RegistrationNativePlatformInstallEffects.effects (KemSK := KemSK))
      ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before) = (do
      let reached ← simulateQ (RegistrationNativePlatformInstallEffects.effects (KemSK := KemSK))
        ((RegistrationNativePlatformBoundCompiler.compile source view failure allocation erased helper sign writer initial (output choice)).run before)
      (fun value => (value, reached.2)) <$> simulateQ RegistrationNativePlatformInstallEffects.env (after control choice reached.1)) := by
  cases choice <;>
    simp only [RegistrationNativePlatformServerRestrictedService.branch, RegistrationNativePlatformPairedServerCompiler.known,
      RegistrationNativePlatformPairedServerCompiler.hidden, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, RegistrationNativePlatformPairedServerCompiler.target, output, after]
  all_goals
    apply bind_congr
    intro reached
    exact forward_run source view failure allocation erased helper sign writer initial _ _ reached.2


/-- The actual stateful publication and insertion retain the exact successful own-role descriptor suffix through every helper, allocator and writer failure. -/
theorem branch_messages (role : Role) (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (sourceBefore : PublicState Platform) (before : State) (message : Message)
    (active : before.current = some message)
    (result : (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × PublicState Platform) × State)
    (supported : result ∈ support ((simulateQ handler
      (simulateQ (RegistrationNativePlatformInstallEffects.effects (KemSK := KemSK))
        ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run sourceBefore))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1.1 = true then [message] else [] := by
  rw [branch_run,simulateQ_bind,StateT.run_bind] at supported
  rw [RegistrationNativePlatformInstallEffects.state_neutral _
    (RegistrationNativePlatformPairedPublicationFree.compile source view failure allocation erased helper sign writer initial (output choice)) sourceBefore before] at supported
  simp only [bind_map_left,mem_support_bind_iff] at supported
  obtain ⟨reached,_actual,continued⟩ := supported
  simp only [simulateQ_map,StateT.run_map,support_map] at continued
  obtain ⟨finished,actual,equal⟩ := continued
  cases equal
  cases choice with
  | known value =>
    exact RegistrationNativeInstallAfter.server role control reached.1 before message active finished actual
  | hidden reference =>
    exact RegistrationNativeInstallAfter.server_hidden role control reference.slot reached.1 before message active finished actual

omit primitive in
def embed : QueryImpl (RegistrationNativePlatformServerFrontendCompiler.Spec n)
    (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) :=
  RegistrationNativePlatformInstallEffects.embed

private theorem service_run (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : RegistrationNativeRelatedFamily.Message) (before : PublicState Platform) :
    simulateQ (embed (n := n) (KemSK := KemSK))
      ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run before) = (do
      let selected ← ((RegistrationNativePublicFrontend.Spec n KemSK).query (.inl (.inr (.inl (.inl message)))) :
        OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) _)
      match selected with
      | none => pure (.ok (.Err control), before)
      | some choice =>
          simulateQ RegistrationNativePlatformInstallEffects.effects
            ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before)) := by
  simp only [RegistrationNativePlatformServerFrontendCompiler.service, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, simulateQ_spec_query, embed,
    RegistrationNativePlatformInstallEffects.embed, simulateQ_spec_query, bind_map_left]
  apply bind_congr
  intro selected
  cases selected with
  | none => simp only [StateT.run_pure, simulateQ_pure]
  | some choice =>
    simp only [RegistrationNativePlatformServerFrontendCompiler.liftEffects, StateT.run, ← QueryImpl.simulateQ_compose]
    rw [RegistrationNativePlatformInstallEffects.embedding]



/-- The actual material service establishes and retains its own descriptor, with exactly the successful source insertion suffix. -/
theorem service_messages (role : Role) (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : Message) (sourceBefore : PublicState Platform) (before : State)
    (result : (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × PublicState Platform) × State)
    (supported : result ∈ support ((simulateQ handler
      (simulateQ (embed (n := n) (KemSK := KemSK))
        ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run sourceBefore))).run before)) :
    messages role result.2.events = messages role before.events ++
      if role = .server ∧ success result.1.1 = true then [message] else [] := by
  rw [service_run,simulateQ_bind,simulateQ_spec_query,StateT.run_bind] at supported
  simp only [handler,StateT.run,RegistrationNativeG2Trace.begin,
    RegistrationNativeG2Trace.finish,bind_map_left,mem_support_bind_iff] at supported
  obtain ⟨selected,_actual,supported⟩ := supported
  cases selected with
  | none =>
    rw [simulateQ_pure] at supported
    change result ∈ support (pure ((.ok (.Err control),sourceBefore),⟨some message,before.events ++ [.demand message]⟩)) at supported
    rw [mem_support_pure_iff] at supported
    cases supported
    simp only [success,Bool.false_eq_true,and_false,ite_false,messages,List.filterMap_append,
      List.filterMap_cons,List.filterMap_nil,List.append_nil]
  | some choice =>
    let afterDemand : State := ⟨some message,before.events ++ [RegistrationNativeG2Trace.Event.demand message]⟩
    have actual : result ∈ support ((simulateQ handler
        (simulateQ (RegistrationNativePlatformInstallEffects.effects (n := n) (KemSK := KemSK))
          ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run sourceBefore))).run afterDemand) := by
      simpa only [StateT.run,afterDemand] using supported
    have counted := branch_messages source view failure allocation erased helper sign writer role control initial choice sourceBefore afterDemand message rfl result actual
    simpa only [afterDemand,messages,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,List.append_nil] using counted

end BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerBranch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerBranch.branch_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerBranch.branch_messages

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerBranch.service_messages' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInstallServerBranch.service_messages

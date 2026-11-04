-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerEffects
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerAfter
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSlotServerSafe
/-! The actual material-selection and stateful response-publication branches record exactly their same-result successful Server key identifiers. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerBranch
open PqxdhDeploymentInterface (Handle)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativePlatformPublicSlotServerSafe (output after)
open RegistrationNativePlatformRecordPartnerSnapshotHandles (update)
open RegistrationNativePlatformRecordPartnerServerAfter (outputHandles)
variable {n : Nat} {KemSK E Platform A : Type}
local notation "serverHandler" => RegistrationNativePlatformRecordPartnerSnapshotHandles.handler (n := n) (KemSK := KemSK) PqxdhRecordLiftInterface.Role.server
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

/-- Every literal material/publication branch records the same final published key, including all mutable source failures. -/
theorem branch (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (choice : Choice n) (sourceBefore : PublicState Platform) (before : List Handle)
    (result : (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × PublicState Platform) × List Handle)
    (supported : result∈support ((simulateQ serverHandler
      (simulateQ RegistrationNativePlatformPublicSlotEffects.effects
        ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run sourceBefore))).run before)) :
    result.2=before++outputHandles result.1.1 := by
  rw [branch_run,simulateQ_bind,StateT.run_bind] at supported
  rw [RegistrationNativePlatformRecordPartnerServerEffects.state_neutral _
    (RegistrationNativePlatformPairedPublicationFree.compile source view failure allocation erased helper sign writer initial (output choice)) sourceBefore before] at supported
  simp only [bind_map_left,mem_support_bind_iff] at supported
  obtain ⟨reached,_called,continued⟩ := supported
  simp only [simulateQ_map,StateT.run_map,support_map] at continued
  obtain ⟨finished,actual,equal⟩ := continued
  cases equal
  cases choice with
  | known value=>exact RegistrationNativePlatformRecordPartnerServerAfter.known control reached.1 before finished actual
  | hidden reference=>exact RegistrationNativePlatformRecordPartnerServerAfter.hidden control reference.slot reached.1 before finished actual
omit primitive in
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

/-- The source material service and its optional raw choice retain exactly the public handle suffix of their same returned result. -/
theorem service (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (message : Message) (sourceBefore : PublicState Platform) (before : List Handle)
    (result : (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8)) × PublicState Platform) × List Handle)
    (supported : result∈support ((simulateQ serverHandler
      (simulateQ embed
        ((RegistrationNativePlatformServerFrontendCompiler.service source view failure allocation erased helper sign writer control initial message).run sourceBefore))).run before)) :
    result.2=before++outputHandles result.1.1 := by
  rw [service_run,simulateQ_bind,StateT.run_bind] at supported
  simp only [RegistrationNativePlatformPublicSlotEffects.demand,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerSnapshotHandles.handler,StateT.run,update,
    bind_map_left,mem_support_bind_iff] at supported
  obtain ⟨selected,_called,supported⟩ := supported
  cases selected with
  | none=>
    change result∈support (pure ((.ok (.Err control),sourceBefore),before)) at supported
    rw [mem_support_pure_iff] at supported
    cases supported
    simp only [outputHandles,List.append_nil]
  | some choice=>exact branch source view failure allocation erased helper sign writer control initial choice sourceBefore before result supported

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerBranch

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerBranch.branch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerBranch.branch
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerBranch.service' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerServerBranch.service

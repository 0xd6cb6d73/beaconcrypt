-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServer
import BeaconcryptCore.Computational.RegistrationNativePlatformServerFrontendCompiler
/-! The actual corrected Server frontend has identical known-material and opaque-slot interpretations. Its literal repeated pin, occupancy, dynamic reservation, moved token and failed source publication paths remain in one free program. Only the outer private seed materialization changes hidden installation references. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend
open RegistrationNativePlatformServerFrontendCompiler (Spec embed target service liftEffects)
open RegistrationNativePlatformMaterializedEffects (realize)
open RegistrationNativeG3AuditedWorld (Seeds)
variable {n : Nat} {E Platform A : Type}

noncomputable def translate (full : Bool) (seeds : Seeds n) : QueryImpl (Spec n) (OracleComp (Spec n))
  | .inl message => if full then
      Option.map (RegistrationNativeG3MaterializedFrontend.materialize seeds) <$> (Spec n).query (.inl message)
    else (Spec n).query (.inl message)
  | .inr query => if full then (Spec n).query (.inr query)
    else simulateQ embed (realize seeds query)

private theorem effects_true (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A) :
    simulateQ (translate true seeds) (simulateQ embed work) = simulateQ embed work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : translate true seeds ∘ₛ embed = embed := by
    funext query
    simp only [QueryImpl.apply_compose, embed, simulateQ_spec_query, translate, ite_true]
  rw [same]

private theorem effects_false (seeds : Seeds n)
    (work : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) A) :
    simulateQ (translate false seeds) (simulateQ embed work) =
      simulateQ embed (simulateQ (realize seeds) work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, embed, simulateQ_spec_query, translate, Bool.false_eq_true, ite_false]

private theorem mapped {I V W : Type} {spec : OracleSpec I} (work : OracleComp spec V)
    (change : V → W) (predicate : I → Prop) (prior : work.AllQueriesSatisfy predicate) :
    (change <$> work).AllQueriesSatisfy predicate := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind prior (fun _ => allQueriesSatisfy_pure _ _)

private theorem effect_quiet {S : Type} (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (allowed : RegistrationNativePlatformPairedPublicationFree.Allowed (.inl query)) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformEffectCompiler.effect (Platform := S) query) := by
  intro before
  change AllQueriesSatisfy ((fun value => (value, before)) <$> ((RegistrationNativePlatformEffectCompiler.Spec n).query (.inl query) : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) _)) RegistrationNativePlatformPairedPublicationFree.Allowed
  exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr allowed)

private theorem lift_source {S : Type} (seeds : Seeds n)
    (work : StateT S (OracleComp (RegistrationNativePlatformEffectCompiler.Spec n)) A)
    (quiet : RegistrationNativePlatformPairedPublicationFree.Quiet work) (before : S) :
    simulateQ (translate true seeds) (simulateQ embed (work.run before)) =
      simulateQ (translate false seeds) (simulateQ embed (work.run before)) := by
  rw [effects_true, effects_false, RegistrationNativePlatformMaterializedEffects.state_free seeds work quiet before]

private theorem pin_quiet (current : session.ServerAuthenticationPin) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformServerRestrictedService.pin (n := n) (Platform := Platform) current) := by
  exact RegistrationNativePlatformPairedPublicationFree.pure_quiet _

private theorem reserve_quiet (reserve : StateT Platform ProbComp Bool) :
    RegistrationNativePlatformPairedPublicationFree.Quiet
      (RegistrationNativePlatformBoundCompiler.liftPlatform (RegistrationNativePlatformEffectCompiler.compile (n := n) reserve)) := by
  intro before
  change ((fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationNativePlatformEffectCompiler.compile reserve).run before.2).AllQueriesSatisfy _
  exact mapped _ _ _ (RegistrationNativePlatformPairedPublicationFree.platform_quiet reserve before.2)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem service_source (seeds : Seeds n) (control : pqxdh.ServerState)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (message : RegistrationNativeRelatedFamily.Message)
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    simulateQ (translate true seeds)
      ((service source view failure allocation erased helper sign writer control initial message).run before) =
      simulateQ (translate false seeds)
        ((service source view failure allocation erased helper sign writer control initial message).run before) := by
  simp only [service, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left,
    simulateQ_bind, simulateQ_spec_query, translate, ite_true, Bool.false_eq_true, ite_false, bind_map_left]
  apply bind_congr
  intro selected
  cases selected with
  | none => simp only [Option.map_none, simulateQ_pure, StateT.run_pure]
  | some choice =>
    simp only [Option.map_some]
    change simulateQ (translate true seeds)
        (simulateQ embed ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial
          (RegistrationNativeG3MaterializedFrontend.materialize seeds choice)).run before)) =
      simulateQ (translate false seeds)
        (simulateQ embed ((RegistrationNativePlatformServerRestrictedService.branch source view failure allocation erased helper sign writer control initial choice).run before))
    rw [effects_true, effects_false, RegistrationNativePlatformMaterializedServer.branch source view failure allocation erased helper sign writer control initial choice seeds before]
/-- Each literal source frontend request has identical full-material and opaque-slot interpretations, including the public pin, actual selected AD hashing and stateful reserve refusal. -/
theorem query_source (reserve : StateT Platform ProbComp Bool) (seeds : Seeds n)
    (query : RegistrationNativePlatformServerFrontendProgram.Spec.Domain)
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    simulateQ (translate true seeds)
      ((target source view failure allocation erased helper sign writer reserve query).run before) =
      simulateQ (translate false seeds)
        ((target source view failure allocation erased helper sign writer reserve query).run before) := by
  cases query with
  | pin current => exact lift_source seeds _ (pin_quiet current) before
  | adHash pending =>
    apply lift_source
    unfold RegistrationNativePlatformServerRestrictedService.adHash RegistrationServerAdHash.runWith
    split
    · exact RegistrationNativePlatformPairedPublicationFree.pure_quiet _
    · exact RegistrationNativePlatformPairedPublicationFree.pure_quiet _
    · apply RegistrationNativePlatformPairedPublicationFree.bind_quiet
      · apply RegistrationNativePlatformPairedPublicationFree.bind_quiet
        · exact effect_quiet _ (fun _ impossible => impossible.elim)
        · intro digest
          exact RegistrationNativePlatformPairedPublicationFree.pure_quiet _
      · intro digest
        exact RegistrationNativePlatformPairedPublicationFree.pure_quiet _
  | reserve => exact lift_source seeds _ (reserve_quiet reserve) before
  | present keyId => exact lift_source seeds _ (effect_quiet (.inr (.peerPresent keyId)) (fun _ impossible => impossible.elim)) before
  | service control initial message => exact service_source source view failure allocation erased helper sign writer seeds control initial message before

/-- Adaptive completion follows the same actual moved-token and failure history after replacing only the private installed kernel by its slot interpretation. -/
theorem program_source (reserve : StateT Platform ProbComp Bool) (seeds : Seeds n)
    (work : OracleComp RegistrationNativePlatformServerFrontendProgram.Spec A)
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    simulateQ (translate true seeds)
      ((simulateQ (target source view failure allocation erased helper sign writer reserve) work).run before) =
      simulateQ (translate false seeds)
        ((simulateQ (target source view failure allocation erased helper sign writer reserve) work).run before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [query_source source view failure allocation erased helper sign writer reserve seeds query before]
    apply bind_congr
    intro reached
    exact ih reached.1 reached.2

/-- The complete actual source Server build, including token take and absent application, has its full known versus opaque materialization law with its entire returned public frontend state. -/
theorem build_source (reserve : StateT Platform ProbComp Bool) (seeds : Seeds n)
    (handle : Nat) (application : Option (Slice U8)) (front : RegistrationServerMaterialFrontend.State)
    (before : RegistrationNativePlatformBoundCompiler.PublicState Platform) :
    simulateQ (translate true seeds)
      ((simulateQ (target source view failure allocation erased helper sign writer reserve)
        ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before) =
      simulateQ (translate false seeds)
        ((simulateQ (target source view failure allocation erased helper sign writer reserve)
          ((RegistrationNativePlatformServerFrontendProgram.program handle application).run front)).run before) :=
  program_source source view failure allocation erased helper sign writer reserve seeds _ before
end BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend.query_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMaterializedServerFrontend.build_source

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptRun
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape

/-! The original open Server controller changes its session list only by one successful literal retention. This structural statement holds for every callback interpreter, including candidate providers; rejected authentication, failed agreement and replay leave all earlier live handles present. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderAcceptRun (State close)
open RegistrationServerOpenReferenceSessionShape (Shape)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}
variable (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
  (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp))
attribute [local irreducible] RegistrationAuthenticationCompiler.program

theorem retain (ready : RegistrationServerReferenceRoot.Ready) (before : State n KemSK ProviderState)
    (result : RustM (Option Nat) × State n KemSK ProviderState)
    (supported : result ∈ support ((close implementation (RegistrationServerOpenReferenceCompiler.retain ready)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationNativeProviderAcceptRun.retain_run] at supported
  cases present : before.1.consumed.contains (absBytes ready.agreement.pending.registration_id.bytes) with
  | false =>
      rw [RegistrationServerMaterialFrontend.retain_fresh ready before.1 present] at supported
      rw [mem_support_pure_iff] at supported
      cases supported
      exact Or.inr ⟨ready, rfl, rfl⟩
  | true =>
      have replay := RegistrationReplaySchedule.consume_replayed
        (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) before.1.consumed
          (by simpa only [RegistrationServerReferenceRoot.atRoot, RegistrationBoundGate.atRoot] using present)
      simp only [RegistrationServerMaterialFrontend.retain, replay, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl

theorem agreement_server (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n KemSK ProviderState)
    (result : RustM (Option RegistrationServerReferenceRoot.Ready) × State n KemSK ProviderState)
    (supported : result ∈ support
      ((close implementation (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before)) :
    result.2.1 = before.1 := by
  rw [RegistrationNativeProviderAcceptRun.agreement_run, mem_support_bind_iff] at supported
  obtain ⟨collected, _possible, supported⟩ := supported
  cases value : collected.1 with
  | none =>
      simp only [value, mem_support_pure_iff] at supported
      cases supported
      rfl
  | some input =>
      simp only [value, support_map] at supported
      obtain ⟨inner, _possible, equal⟩ := supported
      exact (congrArg (fun output => output.2.1) equal).symm

theorem after (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n KemSK ProviderState)
    (result : RustM (Option Nat) × State n KemSK ProviderState)
    (supported : result ∈ support
      ((close implementation (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationNativeProviderAcceptRun.after_run] at supported
  split at supported
  · rw [mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  · split at supported
    · rw [mem_support_bind_iff] at supported
      obtain ⟨completed, reached, supported⟩ := supported
      have same := agreement_server implementation setup checks packet authenticated before completed reached
      cases completedEq : completed.1 with
      | fail error | div =>
          simp only [completedEq, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl (congrArg (fun server => server.sessions) same)
      | ok value => cases value with
        | none =>
            simp only [completedEq, mem_support_pure_iff] at supported
            cases supported
            exact Or.inl (congrArg (fun server => server.sessions) same)
        | some ready =>
            simp only [completedEq] at supported
            have shape := retain implementation ready completed.2 result supported
            simpa only [same] using shape
    · rw [mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem effect_server (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value)
    (before : State n KemSK ProviderState) (result : Value × State n KemSK ProviderState)
    (supported : result ∈ support
      ((close implementation (StateT.lift (StateT.lift
        (simulateQ RegistrationBeaconReferenceCompiler.effect work)))).run before)) : result.2.1 = before.1 := by
  have normalized : (close implementation (StateT.lift (StateT.lift
      (simulateQ RegistrationBeaconReferenceCompiler.effect work)))).run before =
      (fun output => (output.1, (before.1, (before.2.1, output.2)))) <$>
        (simulateQ implementation (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run before.2.2 := by
    simp only [close, RegistrationNativeProviderLocal.lower, StateT.run, state_lift_apply,
      state_map_apply, simulateQ_map, Functor.map_map, Prod.map_def, id_eq]
  rw [normalized] at supported
  rw [support_map] at supported
  obtain ⟨inner, _possible, equal⟩ := supported
  exact (congrArg (fun output => output.2.1) equal).symm

/-- Mandatory authentication and complete actual acceptance preserve every old session or append exactly the Ready whose index is returned. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : State n KemSK ProviderState)
    (result : RustM (Option Nat) × State n KemSK ProviderState)
    (supported : result ∈ support
      ((close implementation (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before)) :
    Shape before.1.sessions result.1 result.2.1.sessions := by
  rw [RegistrationServerOpenReferenceCompiler.accept, RegistrationNativeProviderAcceptRun.close_bind,
    RegistrationNativeProviderAcceptRun.close_get, pure_bind,
    RegistrationNativeProviderAcceptRun.close_bind, mem_support_bind_iff] at supported
  obtain ⟨checked, reached, supported⟩ := supported
  have same := effect_server implementation
    (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.1.pin packet) before checked reached
  cases value : checked.1 with
  | fail error | div =>
      simp only [value, RegistrationNativeProviderAcceptRun.close_pure, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl (congrArg (fun server => server.sessions) same)
  | ok checkedReply =>
      rcases checkedReply with ⟨events, verdict⟩
      cases verdict <;> simp only [value] at supported
      all_goals try {
        rw [RegistrationNativeProviderAcceptRun.close_pure, mem_support_pure_iff] at supported
        cases supported
        exact Or.inl (congrArg (fun server => server.sessions) same) }
      case Accepted authenticated =>
        have shape := after implementation setup checks packet authenticated checked.2 result supported
        simpa only [same] using shape

end BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.agreement_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.agreement_server
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.after' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.after
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderSessionShape.accept

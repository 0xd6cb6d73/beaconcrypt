-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish

/-! The literal native terminal owner controller retains its same preparation and completion cut under every stateful interpretation of its original local queries. The arbitrary runtime can include the chronological trace and actual shared World; the cut never chooses readiness from an outcome marginal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconFinishController
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK Auxiliary Runtime Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

noncomputable def lower (implementation : QueryImpl (Spec n KemSK) (StateT Runtime ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK)) Value) :
    StateT (EnvState Auxiliary × Runtime) ProbComp Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ implementation (work.run before.1)).run before.2


private theorem lower_run (implementation : QueryImpl (Spec n KemSK) (StateT Runtime ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK)) Value) (before : EnvState Auxiliary × Runtime) :
    (lower implementation work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ implementation (work.run before.1)).run before.2 := rfl

private theorem lower_bind (implementation : QueryImpl (Spec n KemSK) (StateT Runtime ProbComp))
    (work : StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK)) Value)
    (next : Value → StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK)) Next) :
    lower implementation (work >>= next) = (lower implementation work >>= fun value => lower implementation (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower_run, StateT.run_bind, simulateQ_bind, map_bind, bind_map_left]

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := StateT.run_map observe work state

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

attribute [local irreducible] RegistrationBeaconReferenceCompiler.finishPreparation RegistrationBeaconReferenceFinish.complete

/-- Successful actual native finish has its own same-run preparation and completion, retaining an arbitrary complete runtime. -/
theorem finish (implementation : QueryImpl (Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner afterOwner : SelectedOwner source) (application : Pqxdh.Bytes)
    (before after : EnvState Auxiliary × Runtime)
    (supported : ((.ok (some application), afterOwner), after) ∈ support
      ((lower implementation ((RegistrationBeaconReferenceFinish.finish setup source packet).run owner)).run before)) :
    ∃ ready : RegistrationBeaconReferenceRoot.Ready, ∃ preparedOwner : SelectedOwner source, ∃ middle,
      ((.ok (some ready), preparedOwner), middle) ∈ support
        ((lower implementation ((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner)).run before) ∧
      ((.ok (some application), afterOwner), after) ∈ support
        ((lower implementation ((RegistrationBeaconReferenceFinish.complete setup.source owner ready).run preparedOwner)).run middle) := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [phase, lower, StateT.run] at supported
      cases supported
  | initSent pending oneTime =>
      simp only [phase] at supported
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved, lower, StateT.run] at supported
          cases supported
      | ok aborted =>
          simp only [moved, StateT.run_bind, lower_bind, StateT.run_bind, mem_support_bind_iff] at supported
          obtain ⟨prepared, possible, continued⟩ := supported
          cases outcome : prepared.1.1 with
          | fail error | div =>
              simp only [outcome, seqRight_eq_bind, RegistrationBeaconReferenceFinish.abort, bind_pure_comp,
                lower, StateT.run, simulateQ_map, state_map_apply, state_lift_apply, state_bind_apply,
                state_pure_apply, Functor.map_map, support_map] at continued
              obtain ⟨reply, _called, equal⟩ := continued
              cases equal
          | ok result => cases result with
            | none =>
                simp only [outcome, seqRight_eq_bind, RegistrationBeaconReferenceFinish.abort, bind_pure_comp,
                  lower, StateT.run, simulateQ_map, state_map_apply, state_lift_apply, state_bind_apply,
                  state_pure_apply, Functor.map_map, support_map] at continued
                obtain ⟨reply, _called, equal⟩ := continued
                cases equal
            | some ready =>
                refine ⟨ready, prepared.1.2, prepared.2, ?_, ?_⟩
                · have same : prepared = ((.ok (some ready), prepared.1.2), prepared.2) :=
                    Prod.ext (Prod.ext outcome rfl) rfl
                  exact same ▸ possible
                · simpa only [outcome] using continued

end BeaconcryptCore.Computational.RegistrationNativeBeaconFinishController

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconFinishController.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconFinishController.finish

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerPreparation

/-! Every successful actual terminal owner finish comes from its same successful preparation and subsequent completion, retaining both intermediate owner and private states. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordMessage (BeaconReady)
open RegistrationNativeSecretWordInterpreter (State)
open RegistrationNativeSecretWordTargetServerExecution (Auxiliary lower lower_bind)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := StateT.run_map observe work state

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

attribute [local irreducible] RegistrationNativeSecretWordBeaconCompiler.finishPreparation
  RegistrationNativeSecretWordBeaconCompiler.complete

/-- Successful actual finish has its own same-run preparation and completion receipts. -/
theorem finish (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT (State n KemSK) ProbComp))
    (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner afterOwner : SelectedOwner source) (application : Pqxdh.Bytes) (before after : Auxiliary n KemSK)
    (supported : ((.ok (some application), afterOwner), after) ∈ support
      ((lower implementation ((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner)).run before)) :
    ∃ ready : BeaconReady, ∃ preparedOwner : SelectedOwner source, ∃ middle,
      ((.ok (some ready), preparedOwner), middle) ∈ support
        ((lower implementation ((RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet).run owner)).run before) ∧
      ((.ok (some application), afterOwner), after) ∈ support
        ((lower implementation ((RegistrationNativeSecretWordBeaconCompiler.complete setup.source owner ready).run preparedOwner)).run middle) := by
  simp only [RegistrationNativeSecretWordBeaconCompiler.finish, StateT.run_bind, StateT.run_get, pure_bind] at supported
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
              simp only [outcome, seqRight_eq_bind, RegistrationNativeSecretWordBeaconCompiler.abort, bind_pure_comp, lower, StateT.run, simulateQ_map, state_map_apply, state_lift_apply,
                state_bind_apply, state_pure_apply, Functor.map_map, support_map] at continued
              obtain ⟨reply, _called, equal⟩ := continued
              cases equal
          | ok result => cases result with
            | none =>
                simp only [outcome, seqRight_eq_bind, RegistrationNativeSecretWordBeaconCompiler.abort, bind_pure_comp, lower, StateT.run, simulateQ_map, state_map_apply, state_lift_apply,
                  state_bind_apply, state_pure_apply, Functor.map_map, support_map] at continued
                obtain ⟨reply, _called, equal⟩ := continued
                cases equal
            | some ready =>
                refine ⟨ready, prepared.1.2, prepared.2, ?_, ?_⟩
                · have same : prepared = ((.ok (some ready), prepared.1.2), prepared.2) :=
                    Prod.ext (Prod.ext outcome rfl) rfl
                  exact same ▸ possible
                · simpa only [outcome] using continued
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinish.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerFinish.finish

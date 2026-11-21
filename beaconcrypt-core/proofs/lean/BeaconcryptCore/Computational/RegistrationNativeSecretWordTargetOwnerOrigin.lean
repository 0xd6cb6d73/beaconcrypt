-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth

/-! Actual response authentication and ordered Beacon collection return a Ready only after the precise successful checked preparation. The proof retains terminal abort before parsing and the actual supplied reference used by ordinary owners. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrigin
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordTargetServerExecution (lower Auxiliary)
open RegistrationNativeSecretWordBeaconCompiler (agreement collect finishPreparation)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)
  (StateT (State n KemSK) ProbComp))

private theorem lower_bind {Next : Type}
    (first : StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (next : Value → StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Next)
    (before : Auxiliary n KemSK) :
    (lower implementation (first >>= next)).run before = (do
      let reached ← (lower implementation first).run before
      (lower implementation (next reached.1)).run reached.2) := by
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, bind_map_left, map_bind]

private theorem agreement_run (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : Auxiliary n KemSK) :
    (lower implementation (agreement setup owner oneTime authenticated)).run before = (do
      let collected ← (lower implementation (collect setup owner oneTime authenticated)).run before
      match collected.1 with
      | none => pure (.ok none, collected.2)
      | some pending =>
          (fun result => (result.1, (collected.2.1, result.2))) <$>
            (simulateQ implementation (simulateQ RegistrationNativeSecretWordInterface.prepare
              (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run collected.2.2) := by
  simp only [agreement, lower_bind]
  apply bind_congr
  rintro ⟨collected, env, context⟩
  cases collected <;>
    simp only [lower, StateT.run, state_pure_apply, state_lift_apply, state_map_apply, simulateQ_pure, simulateQ_map,
      map_pure, Functor.map_map, Prod.map_def, id_eq]

/-- The actual agreement exposes its same successful collector and root continuation with every intermediate source state retained. -/
theorem agreement (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (ready : BeaconReady)
    (before after : Auxiliary n KemSK)
    (supported : (.ok (some ready), after) ∈ support
      ((lower implementation (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)).run before)) :
    ∃ pending middle,
      (some pending, middle) ∈ support ((lower implementation (collect setup owner oneTime authenticated)).run before) ∧
      (.ok (some ready), after.2) ∈ support
        ((simulateQ implementation (simulateQ RegistrationNativeSecretWordInterface.prepare
          (RegistrationNativeSecretWordBeaconRoot.client authenticated pending))).run middle.2) ∧
      after.1 = middle.1 := by
  rw [agreement_run, mem_support_bind_iff] at supported
  obtain ⟨collected, possible, supported⟩ := supported
  cases formed : collected.1 with
  | none => simp only [formed, mem_support_pure_iff] at supported; cases supported
  | some pending =>
      simp only [formed, support_map] at supported
      obtain ⟨reached, rooted, equal⟩ := supported
      have sameValue := congrArg Prod.fst equal
      have sameState := congrArg (fun result => result.2.2) equal
      have pairEqual : reached = (.ok (some ready), after.2) := Prod.ext sameValue sameState
      rw [pairEqual] at rooted
      exact ⟨pending, collected.2, by simpa only [← formed, Prod.mk.eta] using possible,
        rooted, (congrArg (fun result => result.2.1) equal).symm⟩

attribute [local irreducible] RegistrationResponseExecutor.begin

/-- Successful actual terminal preparation reaches its own original mandatory authentication and collector agreement, retaining the exact supplied packet. -/
theorem preparation (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner afterOwner : SelectedOwner source)
    (ready : BeaconReady) (before after : Auxiliary n KemSK)
    (supported : ((.ok (some ready), afterOwner), after) ∈ support
      ((lower implementation ((finishPreparation setup source packet).run owner)).run before)) :
    ∃ pending oneTime aborted authenticated middle,
      owner.phase = .initSent pending oneTime ∧ pending.aborted_state = .ok aborted ∧
      (.ok (.Ok authenticated), middle) ∈ support
        ((lower implementation (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
          (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
            (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some packet => .Some packet)))))).run before) ∧
      (.ok (some ready), after) ∈ support
        ((lower implementation (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)).run middle) := by
  simp only [finishPreparation, StateT.run_bind, StateT.run_get, pure_bind] at supported
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
          simp only [moved, StateT.run_bind, StateT.run_set, pure_bind, StateT.run_lift, bind_assoc,
            lower_bind, mem_support_bind_iff] at supported
          obtain ⟨accepted, checked, supported⟩ := supported
          cases verdict : accepted.1 with
          | fail error | div =>
              simp only [verdict, lower, StateT.run] at supported
              cases supported
          | ok reply => cases reply with
            | Err error =>
                simp only [verdict, lower, StateT.run] at supported
                cases supported
            | Ok authenticated =>
                simp only [verdict, lower, StateT.run, state_lift_apply, state_map_apply, simulateQ_map,
                  Functor.map_map, support_map] at supported
                obtain ⟨reached, possible, equal⟩ := supported
                refine ⟨pending, oneTime, aborted, authenticated, accepted.2, rfl, moved, ?_, ?_⟩
                · have same : accepted = (.ok (.Ok authenticated), accepted.2) := Prod.ext verdict rfl
                  exact same ▸ checked
                · simp only [lower, StateT.run, support_map]
                  refine ⟨reached, possible, ?_⟩
                  exact Prod.ext (congrArg (fun result => result.1.1) equal) (congrArg (fun result => result.2) equal)
end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrigin.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrigin.agreement
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrigin.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerOrigin.preparation

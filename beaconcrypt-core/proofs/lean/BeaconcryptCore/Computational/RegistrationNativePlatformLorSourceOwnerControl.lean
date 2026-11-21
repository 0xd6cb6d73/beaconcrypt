-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerRoot
import BeaconcryptCore.Computational.RegistrationNativeSecretWordGenericLower
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetOwnerAuth

/-! Actual response authentication and ordered Beacon collection return a Ready only after the precise successful checked preparation. The proof retains terminal abort before parsing and the actual supplied reference used by ordinary owners. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterpreter (Provider State)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeSecretWordGenericLower (lower lower_run Auxiliary)
open RegistrationNativeSecretWordBeaconCompiler (agreement collect finishPreparation)
variable {n : Nat} {ι KemSK Value Private : Type} {base : OracleSpec ι}

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
  (StateT Private ProbComp))

private theorem lower_bind {Next : Type}
    (first : StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (next : Value → StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Next)
    (before : Auxiliary Private) :
    (lower implementation (first >>= next)).run before = (do
      let reached ← (lower implementation first).run before
      (lower implementation (next reached.1)).run reached.2) := by
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, bind_map_left, map_bind]

private theorem agreement_run (setup : Setup base KemSK) {source : RegistrationNativeMldsa.Source}
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (before : Auxiliary Private) :
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
    (before after : Auxiliary Private)
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
    (ready : BeaconReady) (before after : Auxiliary Private)
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

/-- A result of the actual closed local lowering is a possible result of that same original open environment program. -/
theorem output (work : StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK)) Value)
    (before after : Auxiliary Private) (value : Value)
    (supported : (value, after) ∈ support ((lower implementation work).run before)) :
    value ∈ support (work.run' before.1) := by
  rw [lower_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  have possible : reached.1 ∈ support (work.run before.1) := by
    apply support_simulateQ_run'_subset implementation _ before.2
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called
  rw [StateT.run'_eq, support_map]
  exact ⟨reached.1, possible, congrArg Prod.fst equal⟩

/-- Successful actual mandatory authentication retains its caller's exact control, completed binding and supplied packet. -/
theorem packet (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket)
    (authenticated : registration.AuthenticatedResponse) (before after : Auxiliary Private)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((lower implementation (StateT.lift (simulateQ RegistrationNativeSecretWordInterface.effect
        (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
          (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some packet => .Some packet)))))).run before)) :
    ∃ supplied, packet = some supplied ∧
      ∃ (digest : Std.Array Std.U8 64#usize) (completed : session.CompletedRegistrationBinding),
        pending.binding.complete digest = .ok completed ∧
        authenticated = ⟨pending.control, completed, supplied⟩ := by
  have possible := output (Value := RustM RegistrationResponseExecutor.ResponseResult) implementation _ before after (RustM.ok (core.result.Result.Ok authenticated)) supported
  simp only [StateT.run'_eq, StateT.run_lift, bind_pure_comp, Functor.map_map, id_map'] at possible
  have bare := RegistrationNativePublicSourceSupport.simulate_support _ _ _
    (RegistrationNativePublicSourceSupport.simulate_support _ _ _ possible)
  cases packet with
  | none =>
      simp only [RegistrationResponseExecutor.begin_malformed, mem_support_pure_iff] at bare
      cases bare
  | some supplied =>
      exact ⟨supplied, rfl, RegistrationNativeSecretWordTargetOwnerAuth.packet pending supplied authenticated bare⟩
end BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.agreement

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.preparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.output' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.output

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.packet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorSourceOwnerControl.packet

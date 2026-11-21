-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativeBeaconFinishController
import BeaconcryptCore.Computational.RegistrationNativePublicOwners
/-! Successful corrected Beacon finish exposes its own actual preparation and material completion on the same full runtime. Authentication and all failure paths remain in the literal source controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {I KemSK Auxiliary Runtime Value Next : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

theorem factor (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner).run env) =
      match owner.phase with
      | .initSent pending _ => match pending.aborted_state with
        | .fail error => pure ((.fail error, owner), env)
        | .div => pure ((.div, owner), env)
        | .ok _ => do
            let reached ← (((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner).run env)
            (((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner reached.1.1).run reached.1.2).run reached.2)
      | _ => pure ((.ok none, owner), env) := by
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, StateT.run_pure]
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_pure]
      | ok aborted =>
          simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, RegistrationBeaconReferenceCompiler.finishPreparation,
            StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_modify, StateT.run_set,
            StateT.run_lift, bind_pure_comp, bind_map_left, bind_assoc]
          apply bind_congr
          intro accepted
          cases accepted with
          | fail error | div => simp only [StateT.run_pure, pure_bind, RegistrationNativePlatformBeaconContinuation.afterPrepared]
          | ok response => cases response with
            | Err _ => simp only [StateT.run_pure, pure_bind, RegistrationNativePlatformBeaconContinuation.afterPrepared]
            | Ok authenticated =>
                simp only [RegistrationNativePlatformBeaconPhase.phase, StateT.run_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, bind_map_left]

open RegistrationNativeBeaconFinishController (lower)
private theorem factor_state (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) :
    ((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner) =
      match owner.phase with
      | .initSent pending _ => match pending.aborted_state with
        | .fail error => pure (.fail error,owner)
        | .div => pure (.div,owner)
        | .ok _ => do
          let result ← ((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner)
          ((RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner result.1).run result.2)
      | _ => pure (.ok none,owner) := by
  apply StateT.ext
  intro env
  rw [factor]
  cases owner.phase <;> rfl

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

/-- Successful actual native finish has its own same-run preparation and completion, retaining an arbitrary complete runtime. -/
theorem finish (implementation : QueryImpl (Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner afterOwner : SelectedOwner source) (application : Pqxdh.Bytes)
    (before after : EnvState RegistrationServerRoleBackend.State × Runtime)
    (supported : ((.ok (some application), afterOwner), after) ∈ support
      ((lower implementation ((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner)).run before)) :
    ∃ ready : RegistrationBeaconReferenceRoot.Ready, ∃ preparedOwner : SelectedOwner source, ∃ middle,
      ((.ok (some ready), preparedOwner), middle) ∈ support
        ((lower implementation ((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner)).run before) ∧
      ((.ok (some application), afterOwner), after) ∈ support
        ((lower implementation ((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run preparedOwner)).run middle) := by
  rw [factor_state] at supported
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
              simp only [outcome, RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind, RegistrationNativePlatformBeaconMaterialFrontend.abort, bind_pure_comp,
                lower, StateT.run, simulateQ_map, state_map_apply, state_lift_apply, state_bind_apply,
                state_pure_apply, Functor.map_map, support_map] at continued
              obtain ⟨reply, _called, equal⟩ := continued
              cases equal
          | ok result => cases result with
            | none =>
                simp only [outcome, RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind, RegistrationNativePlatformBeaconMaterialFrontend.abort, bind_pure_comp,
                  lower, StateT.run, simulateQ_map, state_map_apply, state_lift_apply, state_bind_apply,
                  state_pure_apply, Functor.map_map, support_map] at continued
                obtain ⟨reply, _called, equal⟩ := continued
                cases equal
            | some ready =>
                refine ⟨ready, prepared.1.2, prepared.2, ?_, ?_⟩
                · have same : prepared = ((.ok (some ready), prepared.1.2), prepared.2) :=
                    Prod.ext (Prod.ext outcome rfl) rfl
                  exact same ▸ possible
                · simpa only [outcome, RegistrationNativePlatformBeaconContinuation.afterPrepared] using continued

private theorem ordinary_effects (setup : Setup base KemSK) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) :
    simulateQ (RegistrationNativePublicOwners.ordinary setup scalar)
      (simulateQ (RegistrationBeaconReferenceCompiler.effect (KemSK := KemSK)) work) =
      simulateQ RegistrationBeaconReferenceCompiler.effect work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativePublicOwners.ordinary setup scalar ∘ₛ RegistrationBeaconReferenceCompiler.effect =
      RegistrationBeaconReferenceCompiler.effect (n := n) (KemSK := KemSK) := by
    funext query
    simp only [QueryImpl.apply_compose,RegistrationBeaconReferenceCompiler.effect,
      simulateQ_spec_query,RegistrationNativePublicOwners.ordinary]
  rw [same]

/-- Optional owner-scalar translation acts before completion; the actual source opening, demand and settlement AST are unchanged. -/
theorem ordinary_complete (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (scalar : PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (env : EnvState Auxiliary) :
    simulateQ (RegistrationNativePublicOwners.ordinary setup scalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete (n := n) setup.source wire.frameWrite
        RegistrationBeaconReferenceCompiler.effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env) =
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete (n := n) setup.source wire.frameWrite
        RegistrationBeaconReferenceCompiler.effect RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete,StateT.run_bind,StateT.run_lift,
    bind_pure_comp,bind_map_left,simulateQ_bind,RegistrationNativePlatformBeaconMaterialInterpreter.demand,
    simulateQ_spec_query,RegistrationNativePublicOwners.ordinary]
  apply bind_congr
  intro choice
  cases choice with
  | none =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort,seqRight_eq_bind,StateT.run_lift,StateT.run_map,
      bind_pure_comp,Functor.map_map,simulateQ_map,RegistrationBeaconReferenceCompiler.effect,
      simulateQ_spec_query,RegistrationNativePublicOwners.ordinary]
  | some choice =>
    exact ordinary_effects setup scalar _

end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut.factor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut.finish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut.ordinary_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut.ordinary_complete

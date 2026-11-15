-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAgreementReplayOrigin
import BeaconcryptCore.Computational.RegistrationWorldRoot

/-! The actual real related-root Server phase is scheduled behind the private native replay lookup. Successful agreement supplies the same authenticated identifier to actual insertion, which precedes every first-record/signing/publication effect and survives all later failures. Root-family history, the complete World, its single cache, primitive costs and signing receipts are retained throughout. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldServerReplay
open PqxdhJointIdentity
variable {n : Nat} {Auxiliary : Type}

/-- Ordinary functional source/primitive contracts retain their exact lower native interfaces. -/
structure Parameters (Auxiliary : Type) where
  source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource
  hmac : PqxdhSecretInputKdf.HmacSha512
  correct : PqxdhSecretInputKdf.SourceRootCorrect source hmac
  joint : Primitives
  dh : PqxdhJointGapDh.DhInterface joint
  domain : PqxdhServerStaticDhSource.PublicDomain joint
  secretOfSeed : IdentitySeed → List.Vector UInt8 64
  wiring : SourceWiring source.crypto joint secretOfSeed
  identity : IdentitySeed
  scalar : PqxdhJointGapDh.ScalarBytes
  native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp)

abbrev Global (n : Nat) (Auxiliary : Type) := RegistrationWorldRoot.FullState n Auxiliary
abbrev State (n : Nat) (Auxiliary : Type) := RegistrationReplaySchedule.State × Global n Auxiliary

noncomputable def agreement (parameters : Parameters Auxiliary) (_control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n Auxiliary) ProbComp (RustM agreement.AgreementEffect) := fun before =>
  if before.1.contains (RegistrationReplaySchedule.identifier authenticated) then
    pure (.ok (.Rejected .None), before)
  else (fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationWorldRoot.stage parameters.source parameters.hmac parameters.joint parameters.dh parameters.domain
      parameters.identity parameters.scalar parameters.native packet authenticated).run before.2

noncomputable def native (parameters : Parameters Auxiliary) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT (RegistrationWorldAgreement.State n Auxiliary) ProbComp) :=
  RegistrationAgreementInterpreter.sourceImpl parameters.joint parameters.identity
    (RegistrationWorldAgreement.agreement parameters.source parameters.native) RegistrationWorldRoot.visit

/-- Forgetting only root-family instrumentation identifies the actual replay-controlled native source execution. -/
theorem agreement_project (parameters : Parameters Auxiliary) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n Auxiliary) :
    Prod.map id (fun state : State n Auxiliary => (state.1, state.2.2)) <$>
      (agreement parameters control packet authenticated).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (simulateQ (native parameters) (RegistrationReplaySchedule.begin control authenticated before.1)).run before.2.2 := by
  rw [RegistrationReplaySchedule.begin_eq]
  by_cases consumed : before.1.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [agreement, StateT.run, consumed, ite_true, map_pure, simulateQ_pure]
    change (pure (RustM.ok (beaconcrypt_core.agreement.AgreementEffect.Rejected .None),
      (before.1, before.2.2)) : ProbComp _) = _
    rfl
  · simp only [agreement, StateT.run, consumed, Bool.false_eq_true, ite_false]
    have projected := RegistrationWorldRoot.stage_project parameters.source parameters.hmac parameters.correct
      parameters.joint parameters.dh parameters.domain parameters.secretOfSeed parameters.wiring parameters.identity
      parameters.scalar parameters.native control packet authenticated before.2
    have mapped := congrArg (fun work => (fun result => (result.1, (before.1, result.2))) <$> work) projected
    simpa only [Functor.map_map, Prod.map, id_eq, native, StateT.run] using mapped

/-- Successful actual root completion proves its own replay freshness and native identifier origin; callers cannot independently assert Fresh. -/
theorem agreement_origin (parameters : Parameters Auxiliary) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : State n Auxiliary) (accepted : agreement.ServerAgreement)
    (supported : (.ok (.ServerComplete accepted), after) ∈ support
      ((agreement parameters control packet authenticated).run before)) :
    after.1 = before.1 ∧ before.1.contains (RegistrationReplaySchedule.identifier authenticated) = false ∧
      absBytes accepted.pending.registration_id.bytes = RegistrationReplaySchedule.identifier authenticated ∧
      accepted.pending.root_key_input.bytes = Std.Array.repeat 192#usize 0#u8 := by
  by_cases consumed : before.1.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [agreement, StateT.run, consumed, ite_true, mem_support_pure_iff, Prod.mk.injEq,
      RustM.ok.injEq, reduceCtorEq, false_and] at supported
  · have fresh : before.1.contains (RegistrationReplaySchedule.identifier authenticated) = false :=
      Bool.eq_false_iff.mpr consumed
    have historyEq : after.1 = before.1 := by
      simp only [agreement, StateT.run, consumed, Bool.false_eq_true, ite_false, support_map] at supported
      obtain ⟨inner, _reached, equal⟩ := supported
      exact (congrArg (fun value => value.2.1) equal).symm
    have projected : (.ok (.ServerComplete accepted), (after.1, after.2.2)) ∈ support
        ((fun result => (result.1, (before.1, result.2))) <$>
          (simulateQ (native parameters) (RegistrationReplaySchedule.begin control authenticated before.1)).run before.2.2) := by
      rw [← agreement_project parameters control packet authenticated before, support_map]
      exact Set.mem_image_of_mem (Prod.map id (fun state : State n Auxiliary => (state.1, state.2.2))) supported
    rw [RegistrationReplaySchedule.begin_eq, fresh] at projected
    simp only [Bool.false_eq_true, ite_false, support_map] at projected
    obtain ⟨inner, reached, equal⟩ := projected
    have first : inner.1 = .ok (.ServerComplete accepted) := congrArg Prod.fst equal
    have nativeReached : (.ok (.ServerComplete accepted), inner.2) ∈ support
        ((simulateQ (native parameters) (RegistrationAgreementExecutor.server control .Fresh authenticated)).run before.2.2) := by
      simpa only [← first, Prod.mk.eta] using reached
    obtain ⟨identifier, cleared⟩ := RegistrationAgreementReplayOrigin.interpreted_server_origin
      (native parameters) before.2.2 inner.2 control .Fresh authenticated accepted nativeReached
    exact ⟨historyEq, fresh, identifier, cleared⟩

/-- The actual insertion point is before post-root services; their complete state is disjoint from the persistent replay set. -/
def afterAgreement {Result : Type}
    (post : peer.ConsumedRegistration → StateT (Global n Auxiliary) ProbComp (RustM Result))
    (value : RustM agreement.AgreementEffect) : StateT (State n Auxiliary) ProbComp (RustM (core.option.Option Result)) :=
  match value with
  | .ok (.ServerComplete accepted) => RegistrationReplaySchedule.consumeThen accepted post
  | .ok _ => pure (.ok .None)
  | .fail error => pure (.fail error)
  | .div => pure .div

/-- Actual membership, real family/native agreement, source insertion, then the complete actual first-record/publication computation. -/
noncomputable def complete {Result : Type} (parameters : Parameters Auxiliary) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (post : peer.ConsumedRegistration → StateT (Global n Auxiliary) ProbComp (RustM Result)) :
    StateT (State n Auxiliary) ProbComp (RustM (core.option.Option Result)) := do
  let accepted ← agreement parameters control packet authenticated
  afterAgreement post accepted

/-- The reached whole native root phase discharges the insertion's freshness condition, and consumes precisely the original lookup identifier before any post-root outcome. -/
theorem reached_consumption {Result : Type} (parameters : Parameters Auxiliary) (control : pqxdh.ServerState)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (post : peer.ConsumedRegistration → StateT (Global n Auxiliary) ProbComp (RustM Result))
    (before after : State n Auxiliary) (accepted : agreement.ServerAgreement)
    (supported : (.ok (.ServerComplete accepted), after) ∈ support
      ((agreement parameters control packet authenticated).run before)) :
    (afterAgreement post (.ok (.ServerComplete accepted))).run after =
      (fun result => (core.option.Option.Some <$> result.1,
        (before.1 ++ [RegistrationReplaySchedule.identifier authenticated], result.2))) <$>
          (post ⟨accepted⟩).run after.2 := by
  obtain ⟨history, fresh, identifier, _cleared⟩ :=
    agreement_origin parameters control packet authenticated before after accepted supported
  have freshNative : after.1.contains (absBytes accepted.pending.registration_id.bytes) = false := by
    rw [history, identifier]
    exact fresh
  change (RegistrationReplaySchedule.consumeThen accepted post).run (after.1, after.2) = _
  rw [RegistrationReplaySchedule.consumeThen_fresh accepted post after.1 after.2 freshNative,
    history, identifier]

end BeaconcryptCore.Computational.RegistrationWorldServerReplay

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerReplay.agreement_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerReplay.agreement_project

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerReplay.agreement_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerReplay.agreement_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerReplay.reached_consumption' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerReplay.reached_consumption

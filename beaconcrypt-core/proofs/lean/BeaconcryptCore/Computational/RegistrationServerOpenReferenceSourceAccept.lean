-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceStage
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept

/-! The literal open native Server frontend closes to the actual replay/reservation and one-use SDK controller. All local state and World coordinates are retained by reconstruction, with private root references evaluated only inside that reconstruction. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceEffects (Callbacks)
open RegistrationServerOpenReferenceSourceStage (callbacks)
variable {n : Nat} {ι KemSK Extra Value : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK Extra : Type) :=
  RegistrationServerMaterialFrontend.State × RegistrationNativeKemReferenceBackend.State n KemSK Extra

def project (before : State n KemSK Extra) : RegistrationServerReferenceSourceRetain.State n :=
  (before.1, RegistrationNativeKemReferenceBackend.project before.2)

noncomputable def close (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) : StateT (State n KemSK Extra) ProbComp Value :=
  fun before => (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativeKemReferencePrefix.lower setup (callbacks setup seed scalar remember services)
      (work.run before.1)).run before.2

private theorem close_run (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (work : RegistrationServerOpenReferenceCompiler.M n KemSK Value) (before : State n KemSK Extra) :
    (close setup seed scalar remember services work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (RegistrationNativeKemReferencePrefix.lower setup (callbacks setup seed scalar remember services)
          (work.run before.1)).run before.2 := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_get_apply {S : Type} {m : Type → Type} [Monad m]
    (state : S) : (get : StateT S m S) state = pure (state, state) := rfl

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun result => (result, state)) <$> work := by
  change (work >>= fun result => pure (result, state)) = _
  rw [bind_pure_comp]

set_option maxHeartbeats 1000000 in

theorem agreement_run (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    (close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        (RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember services packet authenticated).run before.2 := by
  rw [close_run]
  simp only [RegistrationServerOpenReferenceCompiler.agreement,
    RegistrationServerOpenReferenceSourceStage.agreement, RegistrationNativeKemReferencePrefix.lower,
    StateT.run, state_bind_apply, state_lift_apply, state_map_apply,
    simulateQ_bind, bind_map_left, map_bind, Functor.map_map]
  apply bind_congr
  rintro ⟨⟨input, env⟩, current⟩
  cases input <;> simp only [simulateQ_pure, simulateQ_map, state_pure_apply, state_map_apply,
    state_lift_apply, map_pure, Functor.map_map, Prod.map_def, id_eq]

/-- The actual open frontend agreement has the complete source reference-stage result and poststate. -/
theorem agreement_project (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    Prod.map id project <$> (close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before =
      (RegistrationServerReferenceSourceAccept.agree setup checks seed scalar packet authenticated).run (project before) := by
  rw [agreement_run]
  have lowered := congrArg (fun distribution => (fun result => (result.1, (before.1, result.2))) <$> distribution)
    (RegistrationServerOpenReferenceSourceStage.agreement_project setup checks seed scalar remember services packet authenticated before.2)
  simpa only [RegistrationServerReferenceSourceAccept.agree, StateT.run, Functor.map_map, Prod.map,
    id_eq, project] using lowered

theorem close_pure (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (value : Value) (before : State n KemSK Extra) :
    (close setup seed scalar remember services (pure value)).run before = pure (value, before) := by
  rw [close_run]
  simp only [RegistrationNativeKemReferencePrefix.lower, StateT.run, state_pure_apply, simulateQ_pure, state_pure_apply, map_pure]

theorem close_get (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (before : State n KemSK Extra) :
    (close setup seed scalar remember services get).run before = pure (before.1, before) := by
  rw [close_run]
  simp only [RegistrationNativeKemReferencePrefix.lower, StateT.run, state_get_apply, state_pure_apply, simulateQ_pure, map_pure]

theorem close_bind {Result : Type} (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (first : RegistrationServerOpenReferenceCompiler.M n KemSK Value)
    (next : Value → RegistrationServerOpenReferenceCompiler.M n KemSK Result)
    (before : State n KemSK Extra) :
    (close setup seed scalar remember services (first >>= next)).run before = (do
      let result ← (close setup seed scalar remember services first).run before
      (close setup seed scalar remember services (next result.1)).run result.2) := by
  simp only [close_run]
  simp only [RegistrationNativeKemReferencePrefix.lower, StateT.run, state_bind_apply, simulateQ_bind, state_bind_apply, bind_map_left, map_bind, Functor.map_map]

theorem retain_run (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (ready : RegistrationServerReferenceRoot.Ready) (before : State n KemSK Extra) :
    (close setup seed scalar remember services (RegistrationServerOpenReferenceCompiler.retain ready)).run before =
      (fun result => (result.1, (result.2.1, before.2))) <$>
        (RegistrationServerReferenceSourceRetain.retain (n := n) ready).run (project before) := by
  rw [close_run]
  cases retained : RegistrationServerMaterialFrontend.retain ready before.1 <;>
    simp only [RegistrationNativeKemReferencePrefix.lower,
      RegistrationServerOpenReferenceCompiler.retain, retained,
      RegistrationServerReferenceSourceRetain.retain, project, StateT.run, state_pure_apply, simulateQ_pure, state_pure_apply, map_pure]

theorem after_run (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    (close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before =
      (if before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
      else if checks.reserveRegistration then do
        let completed ← (close setup seed scalar remember services
          (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before
        match completed.1 with
        | .fail error => pure (.fail error, completed.2)
        | .div => pure (.div, completed.2)
        | .ok none => pure (.ok none, completed.2)
        | .ok (some ready) => (close setup seed scalar remember services
            (RegistrationServerOpenReferenceCompiler.retain ready)).run completed.2
      else pure (.ok none, before)) := by
  rw [RegistrationServerOpenReferenceCompiler.afterAuthentication, close_bind, close_get, pure_bind]
  split
  · exact close_pure setup seed scalar remember services (RustM.ok (none : Option Nat)) before
  · split
    · rw [close_bind]
      apply bind_congr
      rintro ⟨accepted, current⟩
      cases accepted with
      | fail error => exact close_pure setup seed scalar remember services (RustM.fail error) current
      | div => exact close_pure setup seed scalar remember services (RustM.div : RustM (Option Nat)) current
      | ok accepted =>
          cases accepted with
          | none => exact close_pure setup seed scalar remember services (RustM.ok (none : Option Nat)) current
          | some ready => rfl
    · exact close_pure setup seed scalar remember services (RustM.ok (none : Option Nat)) before

/-- Actual owned replay and allocator checks, successful agreement and one-use retention project to the literal complete source controller. -/
theorem after_project (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    Prod.map id project <$> (close setup seed scalar remember services
      (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before =
      (RegistrationServerReferenceSourceAccept.afterAuthentication setup checks seed scalar packet authenticated).run (project before) := by
  rw [after_run]
  simp only [RegistrationServerReferenceSourceAccept.afterAuthentication,
    StateT.run_bind, StateT.run_get, pure_bind, project]
  by_cases replayed : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ite_true, StateT.run_pure, map_pure]; rfl
  · have fresh : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false :=
      Bool.eq_false_iff.mpr replayed
    simp only [fresh, Bool.false_eq_true, ite_false]
    by_cases reserved : checks.reserveRegistration = true
    · simp only [reserved, ite_true, map_bind, StateT.run_bind]
      have lowered := agreement_project setup checks seed scalar remember services packet authenticated before
      change Prod.map id project <$> _ = (RegistrationServerReferenceSourceAccept.agree setup checks seed scalar packet authenticated).run
        (before.1, RegistrationNativeKemReferenceBackend.project before.2) at lowered
      rw [← lowered, bind_map_left]
      apply bind_congr
      rintro ⟨accepted, current⟩
      cases accepted with
      | fail error => simp only [map_pure]; rfl
      | div => simp only [map_pure]; rfl
      | ok accepted =>
          cases accepted with
          | none => simp only [map_pure]; rfl
          | some ready =>
              change Prod.map id project <$> (close setup seed scalar remember services
                (RegistrationServerOpenReferenceCompiler.retain ready)).run current =
                  (RegistrationServerReferenceSourceRetain.retain ready).run (project current)
              rw [retain_run, Functor.map_map]
              cases retained : RegistrationServerMaterialFrontend.retain ready current.1 <;>
                simp only [RegistrationServerReferenceSourceRetain.retain, project, retained,
                  StateT.run, map_pure, Prod.map_def, id_eq]
    · have refused : checks.reserveRegistration = false := Bool.eq_false_iff.mpr reserved
      simp only [refused, Bool.false_eq_true, ite_false, StateT.run_pure, map_pure]; rfl

/-- Restoring the actual private root and consumed token makes the whole open post-authentication frontend the native SDK source controller. -/
theorem after_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra) (services : Callbacks n KemSK Extra)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    Prod.map id (fun current => RegistrationServerReferenceSourceRetain.project
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)
      (project current)) <$> (close setup created.seed scalar remember services
        (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before =
      (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run
        (RegistrationServerReferenceSourceRetain.project
          (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)
          (project before)) := by
  have source := congrArg (fun distribution => Prod.map id (RegistrationServerReferenceSourceRetain.project
    (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$> distribution)
    (after_project setup checks created.seed scalar remember services packet authenticated before)
  rw [RegistrationServerReferenceSourceAccept.after_native setup checks representation correct created scalar packet authenticated (project before)] at source
  simp only [Functor.map_map, Prod.map_def, id_eq] at source ⊢
  exact source

end BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.agreement_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.agreement_project

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.after_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.after_project
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.after_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.after_native

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.close_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.close_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.close_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.close_get

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.close_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.close_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.agreement_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.agreement_run

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.retain_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.retain_run

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.after_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceSourceAccept.after_run

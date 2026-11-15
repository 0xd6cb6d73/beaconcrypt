-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceRetain

/-! Concrete source interpretation of the reference Server replay/reservation/retain controller. The immutable constructor and roots enter only private reconstruction. Actual native SDK gate order, complete failed poststates and one-use session handles are preserved. The open KEM collector's source law connects to referenceStage separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept
open RegistrationServerReferenceSourceRetain (State project retain)
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

noncomputable def agree (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n) ProbComp (RustM (Option RegistrationServerReferenceRoot.Ready)) := fun before =>
  (fun result => (result.1, (before.1, result.2))) <$>
    (RegistrationServerReferenceSourceStage.referenceStage setup checks seed scalar packet authenticated).run before.2

noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n) ProbComp (RustM (Option Nat)) := do
  let before ← get
  if before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else if checks.reserveRegistration then do
    let accepted ← agree setup checks seed scalar packet authenticated
    match accepted with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok none => pure (.ok none)
    | .ok (some ready) => retain ready
  else pure (.ok none)

/-- The owned replay lookup supplies the Fresh branch used by actual native agreement; no caller-wide simulation premise is needed. -/
theorem agree_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n)
    (fresh : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
        (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar))
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
        (agree setup checks created.seed scalar packet authenticated).run before =
      (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run
        (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  simp only [RegistrationServerNativeSource.agree, StateT.run, RegistrationReplaySchedule.begin_eq,
    project, RegistrationServerReferenceRestore.restore, fresh, Bool.false_eq_true, ite_false]
  have phase := RegistrationServerReferenceSourceStage.reference_native setup checks representation correct
    created.seed scalar before.1.control packet authenticated before.2
  have same := congrArg (fun distribution => (fun result =>
    (result.1, { project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before with
      world := result.2 })) <$> distribution) phase
  simpa only [agree, StateT.run, Functor.map_map, Prod.map, id_eq,
    project, RegistrationServerReferenceRestore.restore] using same

private theorem sdk_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerFrontendCompiler.State n) :
    (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run before =
      (if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
      else if checks.reserveRegistration then do
        let completed ← (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before
        match completed.1 with
        | .fail error => pure (.fail error, completed.2)
        | .div => pure (.div, completed.2)
        | .ok (.ServerComplete accepted) => (RegistrationServerNativeSource.retain created accepted).run completed.2
        | .ok _ => pure (.ok none, completed.2)
      else pure (.ok none, before)) := rfl

/-- The complete concrete post-authentication reference controller is the native SDK controller, including replay and allocation refusal before any primitive work. -/
theorem after_native (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
        (afterAuthentication setup checks created.seed scalar packet authenticated).run before =
      (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run
        (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  change Prod.map id (project roots) <$> _ =
    (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run (project roots before)
  rw [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind, sdk_run]
  have consumed : (project roots before).consumed = before.1.consumed := rfl
  rw [consumed]
  by_cases replayed : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ite_true, StateT.run_pure, map_pure]
    rfl
  · have fresh : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false :=
      Bool.eq_false_iff.mpr replayed
    simp only [fresh, Bool.false_eq_true, ite_false]
    by_cases reserved : checks.reserveRegistration = true
    · simp only [reserved, ite_true, StateT.run_bind, map_bind]
      rw [← agree_native setup checks representation correct created scalar packet authenticated before fresh,
        bind_map_left]
      apply bind_congr
      rintro ⟨accepted, current⟩
      cases accepted with
      | fail error => simp only [StateT.run_pure, map_pure]; rfl
      | div => simp only [StateT.run_pure, map_pure]; rfl
      | ok accepted =>
          cases accepted with
          | none => simp only [StateT.run_pure, map_pure]; rfl
          | some ready => exact RegistrationServerReferenceSourceRetain.retain_native roots ready current created
    · have rejected : checks.reserveRegistration = false := Bool.eq_false_iff.mpr reserved
      simp only [rejected, Bool.false_eq_true, ite_false, StateT.run_pure, map_pure]
      rfl

end BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept.agree_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept.agree_native
/-- info: 'BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept.after_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept.after_native

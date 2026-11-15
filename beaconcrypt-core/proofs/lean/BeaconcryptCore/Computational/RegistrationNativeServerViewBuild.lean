-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeServerViewAccept
import BeaconcryptCore.Computational.RegistrationNativeCompletionView

/-! Actual SDK response construction consumes the same native one-use handle before every later conversion, lookup, size, occupancy or reservation gate. Omitted accounting fields do not affect any of those decisions or the final full native state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerViewBuild
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerMaterialSourceState (nativeView)
open RegistrationStateView (Stable)
open RegistrationNativeServerViewAccept (view_idempotent)
variable {n : Nat} {Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Lifting a local source operation preserves every Server control field. -/
theorem world_input (work : StateT (RegistrationServerRootCompiler.Local n) ProbComp Value)
    (stable : Stable RegistrationServerRecordWorldSource.project work) :
    Stable nativeView (RegistrationServerSdkSource.world work) := by
  intro before
  have law := congrArg (fun distribution => (fun result => (result.1,
    { nativeView before with world := result.2 })) <$> distribution) (stable before.world)
  simpa only [RegistrationServerSdkSource.world, StateT.run, Functor.map_map, Prod.map,
    id_eq, nativeView, Function.comp_def] using law

/-- Publication commits the same native control and optional API reply on every branch. -/
theorem commit_input (result : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)) :
    Stable (nativeView (n := n)) (RegistrationServerSdkSource.commit result) := by
  intro before
  cases result with
  | fail error | div => simp only [RegistrationServerSdkSource.commit, StateT.run, nativeView,
      map_pure, Prod.map, id_eq, RegistrationNativeLocalView.project_idempotent]
  | ok outcome => cases outcome <;> simp only [RegistrationServerSdkSource.commit, StateT.run,
      nativeView, map_pure, Prod.map, id_eq, RegistrationNativeLocalView.project_idempotent]

/-- Actual complete initial-record execution and native publication share the same source view. -/
theorem initial_input (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Stable (nativeView (n := n)) (RegistrationServerSdkSource.fromInitial setup codec sign encode control pending) := by
  unfold RegistrationServerSdkSource.fromInitial
  apply RegistrationStateView.bind_stable
  · exact world_input _ (RegistrationNativeCompletionView.initial_input setup codec sign encode control pending)
  · exact commit_input

/-- The actual selected hash reads the same shared cache and preserves the complete operational source view. -/
theorem adHash_input (pending : registration.ServerAdHash) :
    Stable (nativeView (n := n)) (RegistrationServerSdkSource.adHash pending) := by
  unfold RegistrationServerSdkSource.adHash
  apply world_input
  unfold RegistrationWorldServerCompletion.adHash
  cases pending.request with
  | fail error | div =>
      exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _
  | ok request =>
      apply RegistrationStateView.bind_stable
      · exact RegistrationNativeLocalView.capability_input _
      · intro digest
        exact RegistrationStateView.pure_stable _ RegistrationNativeLocalView.project_idempotent _

/-- Occupancy and the outer peer reservation preserve all actual failure branches before either KDF. -/
theorem after_input (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Stable (nativeView (n := n)) (RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied) := by
  unfold RegistrationServerSdkSource.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact RegistrationStateView.pure_stable _ view_idempotent _
  | ok result => cases result with
    | Err previous => exact RegistrationStateView.pure_stable _ view_idempotent _
    | Ok pending =>
        apply RegistrationStateView.bind_stable
        · exact adHash_input pending
        · intro hashed
          cases hashed with
          | fail error | div => exact RegistrationStateView.pure_stable _ view_idempotent _
          | ok answer => cases answer with
            | Err previous => exact RegistrationStateView.pure_stable _ view_idempotent _
            | Ok initial =>
                dsimp only
                split
                · exact initial_input setup codec sign encode control initial
                · exact RegistrationStateView.pure_stable _ view_idempotent _

private noncomputable def atControl (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (State n) ProbComp (RustM (Option (U64 × Pqxdh.Bytes))) :=
  match peer.begin_completion_lookup control pin token application with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok lookup) => match lookup.request with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok keyId => if RegistrationServerSdkSource.preflight application keyId then do
          let occupied ← RegistrationServerSdkSource.world (RegistrationWorldServerCompletion.capability (.peerPresent keyId))
          RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied
        else pure (.ok none)

private theorem control_input (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Stable (nativeView (n := n)) (atControl setup codec checks sign encode control pin token application) := by
  unfold atControl
  cases peer.begin_completion_lookup control pin token application with
  | fail error | div => exact RegistrationStateView.pure_stable _ view_idempotent _
  | ok result => cases result with
    | Err previous => exact RegistrationStateView.pure_stable _ view_idempotent _
    | Ok lookup =>
      dsimp only
      cases requested : lookup.request with
      | fail error | div =>
          exact RegistrationStateView.pure_stable _ view_idempotent _
      | ok keyId =>
          dsimp only
          split
          · apply RegistrationStateView.bind_stable
            · exact world_input _ (RegistrationNativeLocalView.capability_input _)
            · exact after_input setup codec checks sign encode control lookup
          · exact RegistrationStateView.pure_stable _ view_idempotent _

private theorem control_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) (before : State n) :
    (atControl setup codec checks sign encode before.control before.pin token application).run before =
      (RegistrationServerSdkSource.complete setup codec checks sign encode token application).run before := by
  unfold atControl RegistrationServerSdkSource.complete
  dsimp only [StateT.run]
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok lookup =>
      cases requested : lookup.request with
      | fail error | div => simp only [requested]; rfl
      | ok keyId =>
          cases sized : RegistrationServerSdkSource.preflight application keyId <;>
            simp only [requested, sized, Bool.false_eq_true, ite_false, ite_true] <;> rfl

/-- Actual completion lookup and complete-message preflight read exactly the retained control and full authentication pin. -/
theorem complete_input (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Stable (nativeView (n := n)) (RegistrationServerSdkSource.complete setup codec checks sign encode token application) := by
  intro before
  have law := control_input setup codec checks sign encode before.control before.pin token application before
  rw [control_run] at law
  have projected := control_run setup codec checks sign encode token application (nativeView before)
  change (atControl setup codec checks sign encode before.control before.pin token application).run (nativeView before) = _ at projected
  rw [projected] at law
  exact law

/-- Native moved-handle lookup and consumption commute with the explicit source view. -/
theorem take_view (handle : Nat) (before : State n) :
    RegistrationServerSdkSource.take handle (nativeView before) =
      Prod.map id nativeView (RegistrationServerSdkSource.take handle before) := by
  cases found : before.sessions[handle]? with
  | none => simp only [RegistrationServerSdkSource.take, nativeView, found, Prod.map, id_eq]
  | some token => cases token <;>
      simp only [RegistrationServerSdkSource.take, nativeView, found, Prod.map, id_eq]

/-- The complete native SDK build operation preserves consumption order, actual optional failure and all final operational state. -/
theorem build_input (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) :
    Stable (nativeView (n := n)) (RegistrationServerSdkSource.build setup codec checks sign encode handle application) := by
  intro before
  unfold RegistrationServerSdkSource.build
  dsimp only [StateT.run]
  rw [take_view]
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk token current =>
      cases token with
      | none => simp only [Prod.map, id_eq, map_pure, view_idempotent]
      | some token =>
          cases application with
          | none => simp only [Prod.map, id_eq, map_pure, view_idempotent]
          | some application => exact complete_input setup codec checks sign encode token application current

end BeaconcryptCore.Computational.RegistrationNativeServerViewBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.world_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.world_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.commit_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.commit_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.initial_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.initial_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.after_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.after_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.complete_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.complete_input
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.take_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.take_view
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.build_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.build_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.adHash_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerViewBuild.adHash_input

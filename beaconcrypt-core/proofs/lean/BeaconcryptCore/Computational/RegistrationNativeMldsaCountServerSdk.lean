-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCountServer

/-! The complete original reified SDK Server wrapper obeys the checked private-count normalization laws through moved-token consumption, public lookup/sizing, occupancy/reservation, actual first-record publication and control commit. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsaProgram (Spec liftState)
open RegistrationNativeMldsaCountRules (Correct)
open RegistrationNativeMldsaCountMap (transform)
open RegistrationNativeMldsaCountServer (localProject serverProject)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)

private theorem local_idempotent (before : RegistrationServerRootCompiler.Local n) : localProject (localProject before) = localProject before := by
  simp only [localProject, RegistrationNativeMldsaWorldView.idempotent]
private theorem server_idempotent (before : RegistrationServerFrontendCompiler.State n) : serverProject (serverProject before) = serverProject before := by
  simp only [serverProject, local_idempotent]
private theorem bind_apply {m : Type → Type} [Monad m] {S A B : Type}
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl

/-- The exact original SDK World lens retains both original and normalized continuation equations. -/
theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (OracleComp (Spec source)) Value)
    (good : Correct localProject work) : Correct serverProject (RegistrationNativeMldsaServer.world source work) := by
  constructor
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, { before with world := result.2 })) <$> computation) (good.1 before.world)
    simp only [RegistrationNativeMldsaServer.world, StateT.run, Functor.map_map, Prod.map, id_eq, serverProject] at same ⊢
    exact same
  · intro before
    have same := congrArg (fun computation => (fun result => (result.1, { before with world := result.2 })) <$> computation) (good.2 before.world)
    simp only [RegistrationNativeMldsaServer.world, StateT.run, transform, simulateQ_map, Functor.map_map,
      Prod.map, id_eq, serverProject] at same ⊢
    exact same

private theorem commit_stable (result : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)) :
    RegistrationNativeKemCounterIndependence.Stable (serverProject (n := n)) (RegistrationServerSdkSource.commit result) := by
  cases result with
  | fail error | div =>
      intro before
      simp only [RegistrationServerSdkSource.commit, StateT.run, map_pure, Prod.map, id_eq, server_idempotent]
  | ok result => cases result <;> intro before <;>
      simp only [RegistrationServerSdkSource.commit, StateT.run, map_pure, Prod.map, id_eq, serverProject, local_idempotent]

/-- Committing the actual response changes only the exact SDK control; all reached World state is retained. -/
theorem fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Correct serverProject (RegistrationNativeMldsaServer.fromInitial (n := n) source credential setup codec encode control pending) := by
  unfold RegistrationNativeMldsaServer.fromInitial
  exact RegistrationNativeMldsaCountRules.bind _ _ _
    (world source _ (RegistrationNativeMldsaCountServer.completionFromInitial source credential setup codec encode control pending))
    (fun result => RegistrationNativeMldsaCountRules.closed _ _ (commit_stable result))

private theorem adHash_stable (pending : registration.ServerAdHash) :
    RegistrationNativeKemCounterIndependence.Stable (serverProject (n := n)) (RegistrationServerSdkSource.adHash pending) := by
  intro before
  have same := congrArg (fun computation => (fun result => (result.1, { before with world := result.2 })) <$> computation)
    (RegistrationNativeMldsaCountServer.adHash_stable pending before.world)
  simp only [RegistrationServerSdkSource.adHash, RegistrationServerSdkSource.world, StateT.run,
    Functor.map_map, Prod.map, id_eq, serverProject] at same ⊢
  exact same

/-- Every actual occupancy/reservation branch retains both checked normalization laws, including failure. -/
theorem afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Correct serverProject (RegistrationNativeMldsaServer.afterOccupancy (n := n) source credential setup codec checks encode control lookup occupied) := by
  unfold RegistrationNativeMldsaServer.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _
    | Ok pending =>
        apply RegistrationNativeMldsaCountRules.bind _ _ _
          (RegistrationNativeMldsaCountRules.closed _ _ (adHash_stable pending))
        intro hashed
        cases hashed with
        | fail error | div => exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _
        | ok result => cases result with
          | Err previous => exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _
          | Ok initial =>
              dsimp only
              split
              · exact fromInitial source credential setup codec encode control initial
              · exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _

private def read : StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source))
    (pqxdh.ServerState × session.ServerAuthenticationPin) := fun before => pure ((before.control, before.pin), before)
private theorem read_correct : Correct serverProject (read (n := n) source) := by
  constructor <;> intro before <;>
    simp only [read, StateT.run, transform, simulateQ_pure, map_pure, Prod.map, id_eq, serverProject, local_idempotent]

private noncomputable def completeTail (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (current : pqxdh.ServerState × session.ServerAuthenticationPin) :
    StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) (RustM (Option (U64 × Pqxdh.Bytes))) :=
  match peer.begin_completion_lookup current.1 current.2 token application with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok lookup) => match lookup.request with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok keyId => if RegistrationServerSdkSource.preflight application keyId then do
        let occupied ← RegistrationNativeMldsaServer.world source
          (liftState (RegistrationWorldServerCompletion.capability (.peerPresent keyId)))
        RegistrationNativeMldsaServer.afterOccupancy source credential setup codec checks encode current.1 lookup occupied
      else pure (.ok none)

private theorem complete_shape (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    RegistrationNativeMldsaServer.complete (n := n) source credential setup codec checks encode token application =
      (read source >>= completeTail source credential setup codec checks encode token application) := by
  funext before
  simp only [bind_apply, read, pure_bind, RegistrationNativeMldsaServer.complete, completeTail]
  cases peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div => rfl
  | ok result => cases result with
    | Err previous => rfl
    | Ok lookup =>
        dsimp only
        cases lookup.request with
        | fail error | div => rfl
        | ok keyId =>
            dsimp only
            split <;> rfl

/-- Native completion reads only retained control/pin inputs before its exact size/occupancy/publication sequence. -/
theorem complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Correct serverProject (RegistrationNativeMldsaServer.complete (n := n) source credential setup codec checks encode token application) := by
  rw [complete_shape]
  apply RegistrationNativeMldsaCountRules.bind _ _ _ (read_correct source)
  intro current
  unfold completeTail
  cases peer.begin_completion_lookup current.1 current.2 token application with
  | fail error | div => exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _
    | Ok lookup =>
        dsimp only
        cases lookup.request with
      | fail error | div => exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _
      | ok keyId =>
          dsimp only
          split
          · exact RegistrationNativeMldsaCountRules.bind _ _ _
              (world source _ (RegistrationNativeMldsaCountServer.capability source (.peerPresent keyId)))
              (afterOccupancy source credential setup codec checks encode current.1 lookup)
          · exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) ProbComp (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_stable (handle : Nat) : RegistrationNativeKemCounterIndependence.Stable (serverProject (n := n)) (take handle) := by
  intro before
  cases found : before.sessions[handle]? with
  | none => simp only [take, RegistrationServerSdkSource.take, StateT.run, serverProject, found, map_pure,
      Prod.map, id_eq, local_idempotent]
  | some stored => cases stored with
    | none => simp only [take, RegistrationServerSdkSource.take, StateT.run, serverProject, found, map_pure,
        Prod.map, id_eq, local_idempotent]
    | some token => simp only [take, RegistrationServerSdkSource.take, StateT.run, serverProject, found, map_pure,
        Prod.map, id_eq, local_idempotent]

private theorem build_shape (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) :
    RegistrationNativeMldsaServer.build (n := n) source credential setup codec checks encode handle application = (do
      let token ← liftState (take handle)
      match token, application with
      | some token, some application => RegistrationNativeMldsaServer.complete source credential setup codec checks encode token application
      | _, _ => pure (.ok none)) := by
  funext before
  simp only [StateT.run, bind_apply, RegistrationNativeMldsaServer.build, RegistrationNativeMldsaProgram.liftState, take,
    RegistrationNativeMldsaProgram.lift, simulateQ_pure, pure_bind]
  cases RegistrationServerSdkSource.take handle before with
  | mk token current => cases token <;> cases application <;> rfl

/-- The complete original SDK build retains its moved-handle and failed-state behavior under explicit ML private-count normalization. -/
theorem build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) :
    Correct serverProject (RegistrationNativeMldsaServer.build (n := n) source credential setup codec checks encode handle application) := by
  rw [build_shape]
  apply RegistrationNativeMldsaCountRules.bind _ _ _ (RegistrationNativeMldsaCountRules.closed _ _ (take_stable handle))
  intro token
  cases token <;> cases application
  all_goals first
    | exact complete source credential setup codec checks encode _ _
    | exact RegistrationNativeMldsaCountRules.pure _ server_idempotent _

end BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCountServerSdk.build

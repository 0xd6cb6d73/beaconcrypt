-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaProgram
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! Actual Server response signing is an additive private ML capability. Its complete request and actual owned credential are retained; the reached signature receipt is appended before native resume, encoding or installation can fail. Ordinary hashing, record operations, allocation and moved-handle state remain the original source programs. Evaluation restores the exact original source and its complete shared World and counters. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaServer
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeMldsaProgram (Spec evalState liftState call)
open RegistrationWorldAgreement (State)
variable {n : Nat} {Auxiliary Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source) (credential : RegistrationNativeMldsa.Credential source)

noncomputable def outgoing : QueryImpl RegistrationSigningShared.Spec
    (StateT (RegistrationWorldSigning.State n) (OracleComp (Spec source)))
  | .hash request => liftState (RegistrationWorldSigning.outgoing (RegistrationNativeMldsa.owned source credential) (.hash request))
  | .sign request payload digest => fun before =>
      (fun result => (result.1, (result.2, before.2 ++
        [⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes result.1⟩, digest⟩]))) <$>
      (call .native (.sign credential request)).run before.1

set_option backward.isDefEq.respectTransparency false in
theorem eval_outgoing (query : RegistrationSigningShared.Spec.Domain) :
    evalState (outgoing (n := n) source credential query) =
      RegistrationWorldSigning.outgoing (RegistrationNativeMldsa.owned source credential) query := by
  cases query with
  | hash request => exact RegistrationNativeMldsaProgram.eval_liftState _
  | sign request payload digest =>
      funext before
      change @Eq (ProbComp (RegistrationSigningShared.SignReply × RegistrationWorldSigning.State n)) _ _
      have same := congrArg (fun action : StateT (PqxdhRecordLiftWorld.State n) ProbComp RegistrationSigningShared.SignReply =>
        (fun result => (result.1, (result.2, before.2 ++
          [⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes result.1⟩, digest⟩]))) <$> action.run before.1)
        (RegistrationNativeMldsaProgram.eval_call .native (.sign credential request))
      simp only [evalState, outgoing, RegistrationNativeMldsaProgram.evaluate, StateT.run, simulateQ_map,
        RegistrationNativeMldsaCapability.draw, RegistrationWorldSigning.outgoing] at same ⊢
      exact same

noncomputable def signing (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    StateT (State n Auxiliary) (OracleComp (Spec source)) (RustM (RegistrationWorldServerPublication.Result Encoded)) := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$>
    (simulateQ (outgoing source credential) (RegistrationWorldServerPublication.program encode pending)).run before.world

theorem eval_signing (encode : registration.SignedResponseView → core.option.Option Encoded) (pending : registration.ServerResponseHash) :
    evalState (signing (n := n) (Auxiliary := Auxiliary) source credential encode pending) =
      RegistrationWorldServerCompletion.signing (RegistrationNativeMldsa.owned source credential) encode pending := by
  have queries : (fun query => evalState (outgoing (n := n) source credential query)) =
      RegistrationWorldSigning.outgoing (RegistrationNativeMldsa.owned source credential) := funext (eval_outgoing source credential)
  have same := RegistrationNativeMldsaProgram.eval_simulate (outgoing (n := n) source credential)
    (RegistrationWorldServerPublication.program encode pending)
  rw [queries] at same
  funext before
  have projected := congrArg (fun action : StateT (RegistrationWorldSigning.State n) ProbComp (RustM (RegistrationWorldServerPublication.Result Encoded)) =>
    (fun result => (result.1, { before with world := result.2 })) <$> action.run before.world) same
  simpa only [signing, evalState, RegistrationNativeMldsaProgram.evaluate, StateT.run, simulateQ_map,
    RegistrationWorldServerCompletion.signing] using projected

noncomputable def publish (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    StateT (State n Auxiliary) (OracleComp (Spec source)) (RustM (RegistrationWorldServerCompletion.Result Encoded)) := do
  match ← signing source credential encode pending with
  | .ok (.Ok published) => liftState (RegistrationWorldServerCompletion.install control published)
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

theorem eval_publish (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    evalState (publish (n := n) (Auxiliary := Auxiliary) source credential encode control pending) =
      RegistrationWorldServerCompletion.publish (RegistrationNativeMldsa.owned source credential) encode control pending := by
  simp only [publish, RegistrationNativeMldsaProgram.eval_bind, eval_signing, RegistrationWorldServerCompletion.publish]
  congr 1
  funext result
  cases result with
  | fail error => exact RegistrationNativeMldsaProgram.eval_pure _
  | div => exact RegistrationNativeMldsaProgram.eval_pure _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaProgram.eval_pure _
    | Ok published => exact RegistrationNativeMldsaProgram.eval_liftState _

noncomputable def completionFromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    StateT (State n Auxiliary) (OracleComp (Spec source)) (RustM (RegistrationWorldServerCompletion.Result Encoded)) := do
  match ← liftState (simulateQ (RegistrationWorldRecords.handler setup codec) (RegistrationServerRecordExecutor.fromInitial pending)) with
  | .ok (.Ok pending) => publish source credential encode control pending
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

theorem eval_completionFromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    evalState (completionFromInitial (n := n) (Auxiliary := Auxiliary) source credential setup codec encode control pending) =
      RegistrationWorldServerCompletion.fromInitial setup codec (RegistrationNativeMldsa.owned source credential) encode control pending := by
  simp only [completionFromInitial, RegistrationNativeMldsaProgram.eval_bind, RegistrationNativeMldsaProgram.eval_liftState,
    RegistrationWorldServerCompletion.fromInitial]
  congr 1
  funext result
  cases result with
  | fail error => exact RegistrationNativeMldsaProgram.eval_pure _
  | div => exact RegistrationNativeMldsaProgram.eval_pure _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaProgram.eval_pure _
    | Ok pending => exact eval_publish source credential encode control pending

def world {Value : Type} (work : StateT (RegistrationServerRootCompiler.Local n) (OracleComp (Spec source)) Value) :
    StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) Value := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world

theorem eval_world {Value : Type} (work : StateT (RegistrationServerRootCompiler.Local n) (OracleComp (Spec source)) Value) :
    evalState (world source work) = RegistrationServerSdkSource.world (evalState work) := by
  funext before
  simp only [evalState, world, RegistrationNativeMldsaProgram.evaluate, StateT.run, simulateQ_map,
    RegistrationServerSdkSource.world]

noncomputable def fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) (RustM (Option (U64 × Pqxdh.Bytes))) := do
  let published ← world source (completionFromInitial source credential setup codec encode control pending)
  liftState (RegistrationServerSdkSource.commit published)

theorem eval_fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    evalState (fromInitial (n := n) source credential setup codec encode control pending) =
      RegistrationServerSdkSource.fromInitial setup codec (RegistrationNativeMldsa.owned source credential) encode control pending := by
  simp only [fromInitial, RegistrationNativeMldsaProgram.eval_bind, eval_world, eval_completionFromInitial,
    RegistrationNativeMldsaProgram.eval_liftState, RegistrationServerSdkSource.fromInitial]

noncomputable def afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) (RustM (Option (U64 × Pqxdh.Bytes))) :=
  match lookup.resume occupied with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok pending) => if checks.reservePeer then fromInitial source credential setup codec encode control pending else pure (.ok none)

theorem eval_afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    evalState (afterOccupancy (n := n) source credential setup codec checks encode control lookup occupied) =
      RegistrationServerSdkSource.afterOccupancy setup codec checks (RegistrationNativeMldsa.owned source credential) encode control lookup occupied := by
  unfold afterOccupancy RegistrationServerSdkSource.afterOccupancy
  cases lookup.resume occupied with
  | fail error => exact RegistrationNativeMldsaProgram.eval_pure _
  | div => exact RegistrationNativeMldsaProgram.eval_pure _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaProgram.eval_pure _
    | Ok pending =>
        cases reserved : checks.reservePeer with
        | false => simp only [Bool.false_eq_true, ite_false, RegistrationNativeMldsaProgram.eval_pure]
        | true => simp only [ite_true, eval_fromInitial]

noncomputable def complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) (RustM (Option (U64 × Pqxdh.Bytes))) := fun before =>
  match peer.begin_completion_lookup before.control before.pin token application with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err _) => pure (.ok none, before)
  | .ok (.Ok lookup) => match lookup.request with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok keyId => if RegistrationServerSdkSource.preflight application keyId then do
          let occupied ← (world source (liftState (RegistrationWorldServerCompletion.capability (.peerPresent keyId)))).run before
          (afterOccupancy source credential setup codec checks encode before.control lookup occupied.1).run occupied.2
        else pure (.ok none, before)

private theorem evaluate_bind {Value Next : Type} (work : OracleComp (Spec source) Value)
    (next : Value → OracleComp (Spec source) Next) :
    RegistrationNativeMldsaProgram.evaluate (work >>= next) =
      (RegistrationNativeMldsaProgram.evaluate work >>= fun value => RegistrationNativeMldsaProgram.evaluate (next value)) :=
  simulateQ_bind _ _ _

private theorem evaluate_pure {Value : Type} (value : Value) :
    RegistrationNativeMldsaProgram.evaluate (source := source) (pure value) = pure value := simulateQ_pure _ _

theorem eval_complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    evalState (complete (n := n) source credential setup codec checks encode token application) =
      RegistrationServerSdkSource.complete setup codec checks (RegistrationNativeMldsa.owned source credential) encode token application := by
  funext before
  simp only [evalState, complete, RegistrationServerSdkSource.complete, StateT.run]
  cases peer.begin_completion_lookup before.control before.pin token application with
  | fail error => exact evaluate_pure source _
  | div => exact evaluate_pure source _
  | ok result => cases result with
    | Err previous => exact evaluate_pure source _
    | Ok lookup =>
      simp only
      cases lookup.request with
      | fail error => exact evaluate_pure source _
      | div => exact evaluate_pure source _
      | ok keyId =>
          simp only
          cases admitted : RegistrationServerSdkSource.preflight application keyId with
          | false => simp only [Bool.false_eq_true, ite_false, evaluate_pure]
          | true =>
              simp only [ite_true, evaluate_bind]
              have occupied := congrFun (eval_world source (liftState (RegistrationWorldServerCompletion.capability (n := n) (.peerPresent keyId)))) before
              rw [RegistrationNativeMldsaProgram.eval_liftState] at occupied
              simp only [evalState, StateT.run] at occupied
              rw [occupied]
              apply bind_congr
              intro result
              exact congrFun (eval_afterOccupancy source credential setup codec checks encode before.control lookup result.1) result.2

noncomputable def build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) :
    StateT (RegistrationServerFrontendCompiler.State n) (OracleComp (Spec source)) (RustM (Option (U64 × Pqxdh.Bytes))) := fun before =>
  match RegistrationServerSdkSource.take handle before with
  | (none, current) => pure (.ok none, current)
  | (some token, current) => match application with
      | none => pure (.ok none, current)
      | some application => (complete source credential setup codec checks encode token application).run current

theorem eval_build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) :
    evalState (build (n := n) source credential setup codec checks encode handle application) =
      RegistrationServerSdkSource.build setup codec checks (RegistrationNativeMldsa.owned source credential) encode handle application := by
  funext before
  simp only [evalState, build, RegistrationServerSdkSource.build, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk found current => cases found with
    | none => exact evaluate_pure source _
    | some token => cases application with
      | none => exact evaluate_pure source _
      | some application => exact congrFun (eval_complete source credential setup codec checks encode token application) current

end BeaconcryptCore.Computational.RegistrationNativeMldsaServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_publish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_completionFromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_completionFromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServer.eval_build

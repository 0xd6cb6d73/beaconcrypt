-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaSignMap
import BeaconcryptCore.Computational.RegistrationNativeMldsaServer

/-! The actual Server response program is source-key parametric at its named signing leaf. Every complete request is translated with its owned credential, while all ordinary record, hash, occupancy and publication state stays literal. This is a free-program equality; no equality of the two closed primitive signers is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaMap (Map credential)
open RegistrationNativeMldsaSignMap (transformState transform)
open PqxdhServerAuthExperiment (Setup Codec Checks)
variable {left right : Source} {n : Nat} {Auxiliary Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}

set_option backward.isDefEq.respectTransparency false in
theorem outgoing (mapping : Map left right) (current : Credential left) (query : RegistrationSigningShared.Spec.Domain) :
    transformState mapping (RegistrationNativeMldsaServer.outgoing (n := n) left current query) =
      RegistrationNativeMldsaServer.outgoing right (credential mapping current) query := by
  cases query with
  | hash request =>
      rw [RegistrationNativeMldsaServer.outgoing, RegistrationNativeMldsaSignMap.state_lift]
      rfl
  | sign request payload digest =>
      funext before
      change @Eq (OracleComp (RegistrationNativeMldsaProgram.Spec right)
        (RegistrationSigningShared.SignReply × RegistrationWorldSigning.State n)) _ _
      have same := congrArg (fun action : StateT (PqxdhRecordLiftWorld.State n)
          (OracleComp (RegistrationNativeMldsaProgram.Spec right)) RegistrationSigningShared.SignReply =>
        (fun result => (result.1, (result.2, before.2 ++
          [⟨⟨request.public_key, payload, BeaconcryptCore.Refinement.RegistrationSigningTrace.replyBytes result.1⟩, digest⟩]))) <$> action.run before.1)
        (RegistrationNativeMldsaSignMap.state_sign mapping .native current request)
      simp only [transformState, transform, RegistrationNativeMldsaServer.outgoing, StateT.run, simulateQ_map] at same ⊢
      exact same

theorem signing (mapping : Map left right) (current : Credential left)
    (encode : registration.SignedResponseView → core.option.Option Encoded) (pending : registration.ServerResponseHash) :
    transformState mapping (RegistrationNativeMldsaServer.signing (n := n) (Auxiliary := Auxiliary) left current encode pending) =
      RegistrationNativeMldsaServer.signing right (credential mapping current) encode pending := by
  have queries : (fun query => transformState mapping (RegistrationNativeMldsaServer.outgoing (n := n) left current query)) =
      RegistrationNativeMldsaServer.outgoing right (credential mapping current) := funext (outgoing mapping current)
  have same := RegistrationNativeMldsaSignMap.state_simulate mapping (RegistrationNativeMldsaServer.outgoing (n := n) left current)
    (RegistrationWorldServerPublication.program encode pending)
  rw [queries] at same
  funext before
  have projected := congrArg (fun action : StateT (RegistrationWorldSigning.State n)
      (OracleComp (RegistrationNativeMldsaProgram.Spec right)) (RustM (RegistrationWorldServerPublication.Result Encoded)) =>
    (fun result => (result.1, { before with world := result.2 })) <$> action.run before.world) same
  simpa only [RegistrationNativeMldsaServer.signing, transformState, transform, StateT.run, simulateQ_map] using projected

theorem publish (mapping : Map left right) (current : Credential left)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash) :
    transformState mapping (RegistrationNativeMldsaServer.publish (n := n) (Auxiliary := Auxiliary) left current encode control pending) =
      RegistrationNativeMldsaServer.publish right (credential mapping current) encode control pending := by
  simp only [RegistrationNativeMldsaServer.publish, RegistrationNativeMldsaSignMap.state_bind, signing]
  congr 1
  funext result
  cases result with
  | fail error => exact RegistrationNativeMldsaSignMap.state_pure mapping _
  | div => exact RegistrationNativeMldsaSignMap.state_pure mapping _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaSignMap.state_pure mapping _
    | Ok published => exact RegistrationNativeMldsaSignMap.state_lift mapping _

theorem completionFromInitial (mapping : Map left right) (current : Credential left)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    transformState mapping (RegistrationNativeMldsaServer.completionFromInitial (n := n) (Auxiliary := Auxiliary) left current setup codec encode control pending) =
      RegistrationNativeMldsaServer.completionFromInitial right (credential mapping current) setup codec encode control pending := by
  simp only [RegistrationNativeMldsaServer.completionFromInitial, RegistrationNativeMldsaSignMap.state_bind,
    RegistrationNativeMldsaSignMap.state_lift]
  congr 1
  funext result
  cases result with
  | fail error => exact RegistrationNativeMldsaSignMap.state_pure mapping _
  | div => exact RegistrationNativeMldsaSignMap.state_pure mapping _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaSignMap.state_pure mapping _
    | Ok pending => exact publish mapping current encode control pending

theorem world {Value : Type} (mapping : Map left right)
    (work : StateT (RegistrationServerRootCompiler.Local n) (OracleComp (RegistrationNativeMldsaProgram.Spec left)) Value) :
    transformState mapping (RegistrationNativeMldsaServer.world left work) =
      RegistrationNativeMldsaServer.world right (transformState mapping work) := by
  funext before
  simp only [transformState, transform, RegistrationNativeMldsaServer.world, StateT.run, simulateQ_map]

theorem fromInitial (mapping : Map left right) (current : Credential left)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    transformState mapping (RegistrationNativeMldsaServer.fromInitial (n := n) left current setup codec encode control pending) =
      RegistrationNativeMldsaServer.fromInitial right (credential mapping current) setup codec encode control pending := by
  simp only [RegistrationNativeMldsaServer.fromInitial, RegistrationNativeMldsaSignMap.state_bind, world,
    completionFromInitial, RegistrationNativeMldsaSignMap.state_lift]

theorem afterOccupancy (mapping : Map left right) (current : Credential left)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    transformState mapping (RegistrationNativeMldsaServer.afterOccupancy (n := n) left current setup codec checks encode control lookup occupied) =
      RegistrationNativeMldsaServer.afterOccupancy right (credential mapping current) setup codec checks encode control lookup occupied := by
  unfold RegistrationNativeMldsaServer.afterOccupancy
  cases lookup.resume occupied with
  | fail error => exact RegistrationNativeMldsaSignMap.state_pure mapping _
  | div => exact RegistrationNativeMldsaSignMap.state_pure mapping _
  | ok result => cases result with
    | Err previous => exact RegistrationNativeMldsaSignMap.state_pure mapping _
    | Ok pending =>
        simp only [RegistrationNativeMldsaSignMap.state_bind, RegistrationNativeMldsaServer.adHash,
          RegistrationNativeMldsaSignMap.state_lift]
        congr 1
        funext hashed
        cases hashed with
        | fail error | div => exact RegistrationNativeMldsaSignMap.state_pure mapping _
        | ok result => cases result with
          | Err previous => exact RegistrationNativeMldsaSignMap.state_pure mapping _
          | Ok initial =>
              cases checks.reservePeer with
              | false => simp only [Bool.false_eq_true, ite_false, RegistrationNativeMldsaSignMap.state_pure]
              | true => simp only [ite_true, fromInitial]

private theorem transform_bind {Value Next : Type} (mapping : Map left right)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec left) Value)
    (next : Value → OracleComp (RegistrationNativeMldsaProgram.Spec left) Next) :
    transform mapping (work >>= next) = (transform mapping work >>= fun value => transform mapping (next value)) :=
  simulateQ_bind _ _ _

private theorem transform_pure {Value : Type} (mapping : Map left right) (value : Value) :
    transform mapping (pure value) = pure value := simulateQ_pure _ _

theorem complete (mapping : Map left right) (current : Credential left)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice Std.U8) :
    transformState mapping (RegistrationNativeMldsaServer.complete (n := n) left current setup codec checks encode token application) =
      RegistrationNativeMldsaServer.complete right (credential mapping current) setup codec checks encode token application := by
  funext before
  simp only [transformState, RegistrationNativeMldsaServer.complete, StateT.run]
  cases peer.begin_completion_lookup before.control before.pin token application with
  | fail error => exact transform_pure mapping _
  | div => exact transform_pure mapping _
  | ok result => cases result with
    | Err previous => exact transform_pure mapping _
    | Ok lookup =>
      simp only
      cases lookup.request with
      | fail error => exact transform_pure mapping _
      | div => exact transform_pure mapping _
      | ok keyId =>
          simp only
          cases RegistrationServerSdkSource.preflight application keyId with
          | false => simp only [Bool.false_eq_true, ite_false, transform_pure]
          | true =>
              simp only [ite_true, transform_bind]
              have occupied := congrFun (world mapping (RegistrationNativeMldsaProgram.liftState (RegistrationWorldServerCompletion.capability (n := n) (.peerPresent keyId)))) before
              rw [RegistrationNativeMldsaSignMap.state_lift] at occupied
              simp only [transformState, StateT.run] at occupied
              rw [occupied]
              apply bind_congr
              intro result
              exact congrFun (afterOccupancy mapping current setup codec checks encode before.control lookup result.1) result.2

theorem build (mapping : Map left right) (current : Credential left)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice Std.U8)) :
    transformState mapping (RegistrationNativeMldsaServer.build (n := n) left current setup codec checks encode handle application) =
      RegistrationNativeMldsaServer.build right (credential mapping current) setup codec checks encode handle application := by
  funext before
  simp only [transformState, RegistrationNativeMldsaServer.build, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk found now => cases found with
    | none => exact transform_pure mapping _
    | some token => cases application with
      | none => exact transform_pure mapping _
      | some application => exact congrFun (complete mapping current setup codec checks encode token application) now

end BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.publish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.publish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.completionFromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.completionFromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.world

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.fromInitial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.fromInitial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.afterOccupancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.afterOccupancy

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaServerMap.build

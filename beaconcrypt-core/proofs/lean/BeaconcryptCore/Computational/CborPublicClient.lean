-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborTaggedFinish
import BeaconcryptCore.Computational.CborResponseWriterMap

/-! A public client remembers only the numeric Server pins supplied to successful creation calls. It tags finish inputs and removes the proof prefix from build replies, forwards every other complete-interface query unchanged, and makes at most one query per call. These operational laws do not assert the still-separate native owner pin invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborPublicClient
open PqxdhServerAuthExperiment PqxdhDeploymentInterface
abbrev Pins := Nat → Option Std.U64
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def strip (response : PqxdhServerRegistrationPublication.Response) :
    PqxdhServerRegistrationPublication.Response :=
  { response with serialized := response.serialized.drop 8 }

def handler (next : QueryImpl Spec m) : QueryImpl Spec (StateT Pins m)
  | .inr (.create pin keyId) => do
      let reply ← StateT.lift (next (.inr (.create pin keyId)))
      match reply with
      | none => pure none
      | some index => modify (fun pins => Function.update pins index (some keyId)); pure (some index)
  | .inr (.finish index raw) => do
      let pins ← get
      StateT.lift (next (.inr (.finish index (CborTaggedCodec.tag ((pins index).getD 0#u64) raw))))
  | .inr (.build index payload) => Option.map strip <$> StateT.lift (next (.inr (.build index payload)))
  | query => StateT.lift (next query)

def client : QueryImpl Spec (StateT Pins (OracleComp Spec)) :=
  handler (fun query => Spec.query query)

def fullClient : QueryImpl FullSpec (StateT Pins (OracleComp FullSpec))
  | .inl query => handler (fun query => (FullSpec.query (.inl query) : OracleComp FullSpec _)) query
  | .inr query => StateT.lift (FullSpec.query (.inr query))

theorem strip_tag (sender : Std.U64) (response : PqxdhServerRegistrationPublication.Response) :
    strip (CborResponseWriterMap.response (CborTaggedCodec.tag sender) response) = response := by
  simp [strip, CborResponseWriterMap.response, CborTaggedCodec.tag]

theorem finish_run (next : QueryImpl Spec m) (pins : Pins) (index : Nat) (raw : Pqxdh.Bytes) :
    (handler next (.inr (.finish index raw))).run pins =
      (fun reply => (reply, pins)) <$>
        next (.inr (.finish index (CborTaggedCodec.tag ((pins index).getD 0#u64) raw))) := by
  simp [handler, StateT.run_bind, StateT.run_get]

theorem create_run (next : QueryImpl Spec m) (pins : Pins) (pin : Pqxdh.Bytes) (keyId : Std.U64) :
    (handler next (.inr (.create pin keyId))).run pins =
      (fun reply => (reply, match reply with
        | none => pins
        | some index => Function.update pins index (some keyId))) <$>
      next (.inr (.create pin keyId)) := by
  simp only [handler, StateT.run_bind, StateT.run_lift, map_eq_bind_pure_comp]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  rintro (_ | index)
  all_goals simp [StateT.run_pure, StateT.run_modify]

theorem build_run (next : QueryImpl Spec m) (pins : Pins) (index : Nat) (payload : Option Pqxdh.Bytes) :
    (handler next (.inr (.build index payload))).run pins =
      (fun reply => (Option.map strip reply, pins)) <$> next (.inr (.build index payload)) := by
  simp [handler, StateT.run_map, StateT.run_lift, Functor.map_map]

theorem fullClient_bound (query : FullSpec.Domain) (pins : Pins) :
    ((fullClient query).run pins).IsTotalQueryBound 1 := by
  rcases query with (coin | command) | secrecy
  case inl.inr =>
    cases command
    all_goals simp only [fullClient]
    all_goals simp [handler, StateT.run_bind, StateT.run_lift, StateT.run_get,
      StateT.run_map, IsTotalQueryBound, isQueryBound_query_bind_iff,
      isQueryBound_map_iff]
    case create =>
      rintro (_ | index)
      all_goals simp [StateT.run_pure, StateT.run_map, StateT.run_modify]
  all_goals simp [fullClient, handler, StateT.run_lift, IsTotalQueryBound]

end BeaconcryptCore.Computational.CborPublicClient

/-- info: 'BeaconcryptCore.Computational.CborPublicClient.strip_tag' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborPublicClient.strip_tag
/-- info: 'BeaconcryptCore.Computational.CborPublicClient.finish_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborPublicClient.finish_run
/-- info: 'BeaconcryptCore.Computational.CborPublicClient.create_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborPublicClient.create_run
/-- info: 'BeaconcryptCore.Computational.CborPublicClient.build_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborPublicClient.build_run
/-- info: 'BeaconcryptCore.Computational.CborPublicClient.fullClient_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborPublicClient.fullClient_bound

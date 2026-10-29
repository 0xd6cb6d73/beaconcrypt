-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborSizing
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler
import BeaconcryptCore.Computational.PqxdhRecordLiftBudget

/-!
A public cursor shell filters established-record World requests below the secrecy ledger. It observes only public initialization and capability operands, their public replies, and the record requests themselves. In particular, a missing ciphertext does not prevent an admitted nonempty send from advancing its cursor. Hidden initialization uses the deterministic labeled source constructor, without a seed argument. The transformation preserves arbitrary predicated query budgets because it only forwards an original request once or returns its ordinary refusal.

The reached-shell invariant connecting these cursors to native control is a separate operational obligation. These definitions and budget facts alone do not identify this client with the raw native CBOR game or supply its cryptographic headline.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false

namespace BeaconcryptCore.Computational.CborRecordWorldClient

open PqxdhRecordLiftInterface
open PqxdhRecordLiftWorldCompiler (StoredKernel LabeledKernel)
variable {n : Nat}

structure Cursor where
  sender : Std.U64
  sequence : Nat

structure Server where
  sender : Std.U64
  peers : Std.U64 → Option Nat

structure Shell where
  server : Option Server
  owners : Nat → Option Cursor

def initial : Shell := ⟨none, fun _ => none⟩

/-- Both caller-known control and the deterministic hidden initializer are public operands. -/
noncomputable def initialSequence (role : Role) : KernelRef n → Nat
  | .known kernel => kernel.refined.control.send_sequence.val
  | .hidden slot => (PqxdhRecordLiftWorldCompiler.labeledKernel role slot).control.send_sequence.val

def nextFits (plaintext sequence sender : Nat) : Bool :=
  decide (CborSizing.frameLen (sequence + 1) sender (plaintext + 80) ≤ CborSizing.maxMessageSize)

def advance (plaintext : Pqxdh.Bytes) (sequence : Nat) : Nat :=
  if plaintext.isEmpty then sequence
  else if sequence < core.num.U64.MAX.val then sequence + 1 else sequence

def advanceServer (shell : Shell) (keyId : Std.U64) (plaintext : Pqxdh.Bytes) : Shell :=
  { shell with server := shell.server.map fun server =>
      { server with peers := (Function.update server.peers keyId
        ((server.peers keyId).map (advance plaintext))) } }

def advanceOwner (shell : Shell) (owner : Nat) (plaintext : Pqxdh.Bytes) : Shell :=
  { shell with owners := (Function.update shell.owners owner
      ((shell.owners owner).map fun cursor => { cursor with sequence := advance plaintext cursor.sequence })) }

/-- Failed installation replies leave the shell untouched; no ciphertext reply is used as a progress test. -/
noncomputable def next (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query)
    (shell : Shell) : Shell :=
  match query with
  | .inl created => match shell.server with
      | some _ => shell
      | none => { shell with server := (some
          ⟨created.server.server.metadata.sender, fun keyId =>
            (created.server.server.peers keyId).map fun peer => peer.kernel.refined.control.send_sequence.val⟩) }
  | .inr (.inl (.inr (.installServer keyId _binding ref))) =>
      if (show Bool from reply) then { shell with server := shell.server.map fun server =>
          { server with peers := Function.update server.peers keyId (some (initialSequence .server ref)) } }
      else shell
  | .inr (.inl (.inr (.installBeacon owner metadata ref))) =>
      if (show Bool from reply) then { shell with owners := (Function.update shell.owners owner
          (some ⟨metadata.identityKeyId, initialSequence .beacon ref⟩)) }
      else shell
  | .inr (.inr (.inl (.inl (plaintext, keyId)))) => advanceServer shell keyId plaintext
  | .inr (.inr (.inr (owner, .inl plaintext))) => advanceOwner shell owner plaintext
  | _ => shell

/-- Only an oversized established send is refused here. Registration admission stays in its own environment compiler. -/
def refusal (query : (WorldSpec n).Domain) (shell : Shell) : Option ((WorldSpec n).Range query) :=
  match query with
  | .inr (.inr (.inl (.inl (plaintext, keyId)))) =>
      match shell.server with
      | none => none
      | some server => match server.peers keyId with
          | none => none
          | some sequence => if nextFits plaintext.length sequence server.sender.val then none else some none
  | .inr (.inr (.inr (owner, .inl plaintext))) =>
      match shell.owners owner with
      | none => none
      | some cursor => if nextFits plaintext.length cursor.sequence cursor.sender.val then none else some none
  | _ => none

/-- The forwarded original reply updates public metadata even when it contains no ciphertext. -/
noncomputable def forward (query : (WorldSpec n).Domain) (shell : Shell) :
    OracleComp (WorldSpec n) ((WorldSpec n).Range query × Shell) :=
  (fun reply => (reply, next query reply shell)) <$> (WorldSpec n).query query

noncomputable def handler : QueryImpl (WorldSpec n) (StateT Shell (OracleComp (WorldSpec n))) :=
  fun query shell => match refusal query shell with
  | some reply => pure (reply, shell)
  | none => forward query shell

/-- Wrapping the entire open World program places record admission below every hidden test/fresh draw and ledger update. -/
noncomputable def client {Result : Type} (work : OracleComp (WorldSpec n) Result)
    (shell : Shell := initial) : OracleComp (WorldSpec n) Result :=
  Prod.fst <$> (simulateQ handler work).run shell

/-- The filter forwards at most the original query, with no auxiliary effect. -/
theorem handler_bound (predicate : (WorldSpec n).Domain → Prop) [DecidablePred predicate]
    (query : (WorldSpec n).Domain) (shell : Shell) :
    ((handler query).run shell).IsQueryBoundP predicate (if predicate query then 1 else 0) := by
  cases refused : refusal query shell <;>
    simp +contextual [handler, StateT.run, refused, forward, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- Every predicated budget is preserved, including the joint send/raw counters and each environment effect class. -/
theorem client_bound {Result : Type} (work : OracleComp (WorldSpec n) Result)
    (predicate : (WorldSpec n).Domain → Prop) [DecidablePred predicate] (budget : Nat)
    (bounded : work.IsQueryBoundP predicate budget) (shell : Shell := initial) :
    (client work shell).IsQueryBoundP predicate budget := by
  simpa only [client, isQueryBoundP_map_iff] using bounded.simulateQ_run_of_step
    (fun query selected state => by simpa only [ite_eq_left selected] using handler_bound predicate query state)
    (fun query unselected state => by simpa only [ite_eq_right unselected] using handler_bound predicate query state)
    shell

/-- Ledger-generated sends are filtered without increasing the original adversary's record budget. -/
theorem program_record_bound {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (budget : PqxdhDeploymentInterface.Budget)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (respects : budget.Respects adversary) (kind : PqxdhRecordLiftBudget.RecordKind) :
    (client (program env crypto codec serverKid bounds mode adversary)).IsQueryBoundP
      (PqxdhRecordLiftBudget.WorldRecord kind) (PqxdhRecordLiftBudget.recordBudget budget kind) :=
  client_bound _ _ _
    (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget adversary respects kind)

end BeaconcryptCore.Computational.CborRecordWorldClient

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldClient.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldClient.handler_bound

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldClient.client_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldClient.client_bound

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldClient.program_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldClient.program_record_bound

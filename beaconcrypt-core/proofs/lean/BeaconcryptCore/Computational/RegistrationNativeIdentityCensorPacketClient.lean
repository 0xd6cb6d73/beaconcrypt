-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorBeforeAccept

/-! A literal traversal of the original typed adversary returns only the fixed public stop's selected message and submitted packet. It is exactly the same executable before-accept client after erasing its unused value/final-state coordinates. -/
open OracleComp OracleSpec
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorPublicClient (ClientState Stop)
open PqxdhEd25519EufCma (Ed25519Signature)
variable {S Value : Type}
abbrev Found := Pqxdh.Bytes × beaconcrypt_core.registration.InitPacket
abbrev Spec := RegistrationNativeIdentityCensorOperational.Spec
abbrev Source := RegistrationNativePlatformIdentityCtxCompiler.Spec

def finish (target : Option Pqxdh.Bytes) : Stop → Option Found
  | .published => none
  | .attempted packet _reply => target.map fun message => (message, packet)

def observed (result : Value × (ClientState S × Option Stop)) : Option Found :=
  result.2.2.bind (finish result.2.1.1.2.target)

def candidate (primitives : PqxdhJointIdentity.Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (returned : Option Found) : Option (RegistrationNativeIdentityAdaptiveHashCapture.Candidate primitives identity) :=
  returned.bind fun found => RegistrationNativeIdentityCensorStoppedReduction.packet primitives identity (some found.1) found.2

/-- This packet/message observation retains exactly the verified-field extraction of the frozen executable primitive reduction. -/
theorem extraction (primitives : PqxdhJointIdentity.Primitives) (identity : PqxdhJointIdentity.PublicIdentity)
    (returned : Value × (ClientState S × Option Stop)) :
    RegistrationNativeIdentityCensorStoppedReduction.result primitives identity returned =
      candidate primitives identity (observed returned) := by
  rcases returned with ⟨value, ⟨⟨⟨localState, mode⟩, counter⟩, reason⟩⟩
  cases reason with
  | none => rfl
  | some reason => cases reason with
    | published => rfl
    | attempted packet reply =>
      simp only [RegistrationNativeIdentityCensorStoppedReduction.result, candidate, observed, finish]
      cases mode.target <;> rfl


variable (selected bundle accept : Nat) (placeholder : Ed25519Signature)
variable (frontend : QueryImpl TypedSpec (StateT S (OracleComp Source)))
variable (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
local notation "step" => RegistrationNativeIdentityCensorBeforeAccept.step selected bundle accept placeholder frontend defaults
local notation "freeze" => RegistrationNativeIdentityCensorBeforeAccept.freeze selected bundle accept placeholder frontend defaults
local notation "observe" => RegistrationNativeIdentityCensorPublicClient.observe (S := S) accept

/-- Public branch selection retains precisely the preceding callback state; all primitive work is performed by the unchanged actual step. -/
def visit (work : OracleComp TypedSpec Value) : ClientState S → OracleComp Spec (Option Found) :=
  work.recOn (fun _ _before => pure none)
    (fun query _next continued before => do
      let result ← (step query).run before
      match observe query before result.1 result.2 with
      | none => continued result.1 result.2
      | some reason => pure (finish result.2.1.2.target reason))

private theorem visit_pure (value : Value) (before : ClientState S) :
    visit selected bundle accept placeholder frontend defaults (pure value) before = pure none := rfl
private theorem visit_query (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec Value)
    (before : ClientState S) :
    visit selected bundle accept placeholder frontend defaults (TypedSpec.query query >>= next) before = (do
      let result ← (step query).run before
      match observe query before result.1 result.2 with
      | none => visit selected bundle accept placeholder frontend defaults (next result.1) result.2
      | some reason => pure (finish result.2.1.2.target reason)) := rfl

private theorem bind_apply {m : Type → Type} [Monad m] {X Y State : Type}
    (work : StateT State m X) (next : X → StateT State m Y) (before : State) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl


/-- Erasing unused stopped coordinates from the literal client gives this traversal exactly, before interpreting any private source or hash oracle. -/
theorem source (work : OracleComp TypedSpec Value) (before : ClientState S) :
    observed <$> (simulateQ freeze work).run (before, none) =
      visit selected bundle accept placeholder frontend defaults work before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, visit_pure, observed, Option.bind_none]
  | query_bind query next ih =>
    rw [visit_query]
    simp only [simulateQ_bind, simulateQ_spec_query, bind_apply, RegistrationNativeIdentityCensorBeforeAccept.freeze,
      RegistrationNativeMldsaStop.freeze, RegistrationNativeMldsaStop.monitor, StateT.run, bind_pure_comp, map_bind, bind_map_left,
      Option.orElse_none]
    apply bind_congr
    intro result
    cases selectedReason : observe query before result.1 result.2 with
    | none => exact ih result.1 result.2
    | some reason =>
      obtain ⟨value, stopped⟩ := RegistrationNativeMldsaStop.stopped step observe defaults (next result.1) result.2 reason
      simp only [StateT.run] at stopped
      rw [stopped, map_pure]
      rfl

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient.extraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient.extraction

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPacketClient.source

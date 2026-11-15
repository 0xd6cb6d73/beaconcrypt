-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterRecordRequestMonad
import BeaconcryptCore.AdapterAuthenticationExtraction.Funs

/-! Exact response-authentication primitive requests. Each dynamic occurrence is a separate request, retaining optional hash failure, ordinary verifier rejection, failure/divergence and the complete primitive state. The primitive implementations and their security guarantees remain explicit parameters. -/

open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core

set_option autoImplicit false
set_option warningAsError true

namespace BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad
open AdapterRecordRequestMonad (LiftRust liftRust)

class Operations (m : Type → Type) where
  hash : registration.HashRequest → m (Option (Array Std.U8 64#usize))
  verify : registration.MldsaVerificationRequest → m Bool

instance [ops : beaconcrypt.auth.Operations] : Operations RustM where
  hash := ops.hash
  verify := ops.verify

namespace Lifted
variable {m : Type → Type} [LiftRust m]

def begin (pending : registration.BeaconPending) (packet : Option registration.ResponsePacket) :=
  liftRust (registration.begin_response_authentication pending packet) (m := m)

def branch {Input : Type} (value : core.result.Result Input pqxdh.BeaconAborted) :=
  liftRust (core.result.Result.Insts.CoreOpsTry_traitTry.branch value) (m := m)

def hashRequest (pending : registration.ResponseHash) :=
  liftRust (registration.ResponseHash.request pending) (m := m)

def hashResume (pending : registration.ResponseHash) (digest : Option (Array Std.U8 64#usize)) :=
  liftRust (registration.ResponseHash.resume pending digest) (m := m)

def verifyRequest (pending : registration.ResponseMldsaVerification) :=
  liftRust (registration.ResponseMldsaVerification.request pending) (m := m)

def verifyResume (pending : registration.ResponseMldsaVerification) (verified : Bool) :=
  liftRust (registration.ResponseMldsaVerification.resume pending verified) (m := m)

def adHashRequest (pending : registration.BeaconAdHash) :=
  liftRust (registration.BeaconAdHash.request pending) (m := m)

def adHashResume (pending : registration.BeaconAdHash) (digest : Option (Array Std.U8 64#usize)) :=
  liftRust (registration.BeaconAdHash.resume pending digest) (m := m)

def fromResidual (residual : _) :=
  liftRust (core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
    registration.AuthenticatedResponse (core.convert.From.Blanket pqxdh.BeaconAborted) residual) (m := m)

end Lifted

inductive Request where
  | hash (request : registration.HashRequest)
  | verify (request : registration.MldsaVerificationRequest)

abbrev Response : Request → Type
  | .hash _ => Option (Array Std.U8 64#usize)
  | .verify _ => Bool

abbrev Spec : OracleSpec Request := fun request => RustM (Response request)

structure Program (α : Type) where
  run : OracleComp Spec (RustM α)

namespace Program

def pure {α : Type} (value : α) : Program α := ⟨Pure.pure (.ok value)⟩

def bind {α β : Type} (work : Program α) (next : α → Program β) : Program β :=
  ⟨do
    let result ← work.run
    match result with
    | .ok value => (next value).run
    | .fail error => Pure.pure (.fail error)
    | .div => Pure.pure .div⟩

instance : Monad Program where
  pure := pure
  bind := bind

instance : LiftRust Program where
  liftRust value := ⟨Pure.pure value⟩

def query (request : Request) : Program (Response request) :=
  ⟨OracleComp.lift (Spec.query request)⟩

instance : Operations Program where
  hash request := query (.hash request)
  verify request := query (.verify request)

@[simp] theorem run_pure {α : Type} (value : α) :
    (Pure.pure value : Program α).run = Pure.pure (.ok value) := rfl

@[simp] theorem run_lift {α : Type} (value : RustM α) :
    (liftRust value : Program α).run = Pure.pure value := rfl

@[simp] theorem run_bind {α β : Type} (work : Program α) (next : α → Program β) :
    (work >>= next).run = (do
      let result ← work.run
      match result with
      | .ok value => (next value).run
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) := rfl

theorem ext {α : Type} (left right : Program α) (same : left.run = right.run) : left = right := by
  cases left
  cases right
  cases same
  rfl

instance : LawfulMonad Program := LawfulMonad.mk' Program
  (by
    intro α work
    apply ext
    change (work.run >>= fun result => match result with
      | .ok value => Pure.pure (.ok value)
      | .fail error => Pure.pure (.fail error)
      | .div => Pure.pure .div) = work.run
    have same : (fun result : RustM α => match result with
        | .ok value => Pure.pure (.ok value)
        | .fail error => Pure.pure (.fail error)
        | .div => Pure.pure .div) = (Pure.pure : RustM α → OracleComp Spec (RustM α)) := by
      funext result
      cases result <;> rfl
    rw [same, bind_pure])
  (by intros; rfl)
  (by
    intro α β γ work next last
    apply ext
    simp only [run_bind, bind_assoc]
    refine bind_congr fun result => ?_
    cases result <;> simp only [pure_bind])

end Program

end BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.run_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.run_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.run_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.run_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.run_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.run_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterAuthenticationRequestMonad.Program.ext

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldServerPublication

/-! The actual Core response publication controller sequences an effectful writer after its returned ML signature, at the literal Ready stage. All hash/sign requests, resume gates and publication fields are retained. The writer's optional failure, Rust failure, divergence and shared poststate remain explicit. This is an additive stateful model; the original pure native writer is a compatibility specialization. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication
open RegistrationSigningShared (Spec)
open RegistrationWorldServerPublication (Result)
open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
variable {Encoded : Type} {m : Type → Type} [Monad m]

def continueWith {Input : Type} (action : RustM Input)
    (next : Input → m (RustM (Result Encoded))) : m (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def continueResult {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → m (RustM (Result Encoded))) : m (RustM (Result Encoded)) :=
  match action with
  | .ok (.Ok value) => next value
  | .ok (.Err previous) => pure (.ok (.Err previous))
  | .fail error => pure (.fail error)
  | .div => pure .div

def ready (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseReady) : m (RustM (Result Encoded)) :=
  continueWith pending.message fun view => do
    let encoded ← encode view
    pure (do let value ← encoded; pending.publish value)

def signing (impl : QueryImpl Spec m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) : m (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let signature ← impl (.sign request payload digest)
    continueResult (pending.resume signature) (ready encode)

def program (impl : QueryImpl Spec m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) : m (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let digest ← impl (.hash request)
    continueResult (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest)))
      (signing impl encode ⟨.server, hashBytes request⟩ digest)

attribute [local irreducible] registration.ServerResponseHash.resume registration.ServerResponseSigning.resume

private theorem continueWith_same {Input : Type} (action : RustM Input)
    (left right : Input → OracleComp Spec (RustM (Result Encoded)))
    (same : ∀ value, left value = right value) :
    continueWith action left = RegistrationWorldServerPublication.continueWith action right := by
  cases action <;> simp only [continueWith, RegistrationWorldServerPublication.continueWith, same]

private theorem continueResult_same {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (left right : Input → OracleComp Spec (RustM (Result Encoded)))
    (same : ∀ value, left value = right value) :
    continueResult action left = RegistrationWorldServerPublication.continueResult action right := by
  cases action with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> simp only [continueResult, RegistrationWorldServerPublication.continueResult, same]

/-- The writer sees exactly the actual signed view, and its complete poststate survives every publication outcome. -/
theorem ready_run {State : Type}
    (encode : registration.SignedResponseView → StateT State m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseReady) (before : State) :
    (ready encode pending).run before =
      match pending.message with
      | .ok view => do
          let result ← (encode view).run before
          pure ((do let value ← result.1; pending.publish value), result.2)
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before) := by
  cases message : pending.message <;>
    simp only [ready, continueWith, message, StateT.run_bind, StateT.run_pure]

theorem ready_pure (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseReady) :
    ready (m := OracleComp Spec) (fun view => pure (.ok (encode view))) pending =
      RegistrationWorldServerPublication.ready encode pending := by
  cases message : pending.message <;>
    simp only [ready, continueWith, RegistrationWorldServerPublication.ready,
      RegistrationWorldServerPublication.continueWith, message, pure_bind]
  rfl

theorem signing_pure (encode : registration.SignedResponseView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    signing (m := OracleComp Spec) (fun query => Spec.query query)
      (fun view => pure (.ok (encode view))) payload digest pending =
      RegistrationWorldServerPublication.signing encode payload digest pending := by
  unfold signing RegistrationWorldServerPublication.signing
  apply continueWith_same
  intro request
  apply bind_congr
  intro signature
  apply continueResult_same
  intro next
  exact ready_pure encode next

theorem program_pure (encode : registration.SignedResponseView → core.option.Option Encoded)
    (pending : registration.ServerResponseHash) :
    program (m := OracleComp Spec) (fun query => Spec.query query)
      (fun view => pure (.ok (encode view))) pending =
      RegistrationWorldServerPublication.program encode pending := by
  unfold program RegistrationWorldServerPublication.program
  apply continueWith_same
  intro request
  apply bind_congr
  intro digest
  apply continueResult_same
  intro next
  exact signing_pure encode _ digest next

private theorem continueWith_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) {Input : Type} (action : RustM Input)
    (next : Input → OracleComp base (RustM (Result Encoded))) :
    simulateQ implementation (continueWith action next) =
      continueWith action (fun value => simulateQ implementation (next value)) := by
  cases action <;> rfl

private theorem continueResult_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → OracleComp base (RustM (Result Encoded))) :
    simulateQ implementation (continueResult action next) =
      continueResult action (fun value => simulateQ implementation (next value)) := by
  cases action with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

variable [LawfulMonad m]

theorem ready_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m)
    (encode : registration.SignedResponseView → OracleComp base (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseReady) :
    simulateQ implementation (ready encode pending) =
      ready (fun view => simulateQ implementation (encode view)) pending := by
  cases message : pending.message <;>
    simp only [ready, continueWith, message, simulateQ_bind, simulateQ_pure]

theorem signing_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) (impl : QueryImpl Spec (OracleComp base))
    (encode : registration.SignedResponseView → OracleComp base (RustM (core.option.Option Encoded)))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.ServerResponseSigning) :
    simulateQ implementation (signing impl encode payload digest pending) =
      signing (fun query => simulateQ implementation (impl query))
        (fun view => simulateQ implementation (encode view)) payload digest pending := by
  unfold signing
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind]
  apply bind_congr
  intro signature
  rw [continueResult_interpret]
  apply congrArg (continueResult (pending.resume signature))
  funext next
  exact ready_interpret implementation encode next

theorem program_interpret {ι : Type} {base : OracleSpec ι}
    (implementation : QueryImpl base m) (impl : QueryImpl Spec (OracleComp base))
    (encode : registration.SignedResponseView → OracleComp base (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) :
    simulateQ implementation (program impl encode pending) =
      program (fun query => simulateQ implementation (impl query))
        (fun view => simulateQ implementation (encode view)) pending := by
  unfold program
  rw [continueWith_interpret]
  apply congrArg (continueWith pending.request)
  funext request
  rw [simulateQ_bind]
  apply bind_congr
  intro digest
  rw [continueResult_interpret]
  apply congrArg (continueResult (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))))
  funext next
  exact signing_interpret implementation impl encode _ digest next
end BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.ready_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.ready_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.ready_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.ready_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.signing_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.signing_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.program_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.program_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.ready_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.ready_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.signing_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.signing_interpret

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.program_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPublication.program_interpret

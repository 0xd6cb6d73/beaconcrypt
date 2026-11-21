-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAd
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-! Actual Server AD hashing as a small open primitive program. The callback receives only the selected request, and only the actual owned continuation can produce an initial-record capability. Stateful failure receipts retain the reached primitive state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationServerAdHash

abbrev DigestReply := core.option.Option (Std.Array U8 64#usize)
abbrev Result := RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState)

def runWith {m : Type → Type} [Monad m] (hash : registration.HashRequest → m DigestReply)
    (pending : registration.ServerAdHash) : m Result :=
  match pending.request with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok request => do
    let digest ← hash request
    pure (pending.resume digest)

/-- An actual successful continuation necessarily consumed a present digest. -/
theorem resumed_digest (pending : registration.ServerAdHash) (reply : DigestReply)
    (initial : registration.ServerInitialKdf) (resumed : pending.resume reply = .ok (.Ok initial)) :
    ∃ digest, reply = .Some digest ∧ pending.resume (.Some digest) = .ok (.Ok initial) := by
  cases reply with
  | none => simp [registration.ServerAdHash.resume, pqxdh.server_abort_candidate] at resumed
  | some digest => exact ⟨digest, rfl, resumed⟩

/-- A successful ordinary StateT execution supplies its actual consumed hash reply. -/
theorem receipt {State : Type}
    (hash : registration.HashRequest → StateT State ProbComp DigestReply)
    (pending : registration.ServerAdHash) (before after : State)
    (initial : registration.ServerInitialKdf)
    (supported : (.ok (.Ok initial), after) ∈ support ((runWith hash pending).run before)) :
    ∃ digest, pending.resume (.Some digest) = .ok (.Ok initial) := by
  cases requested : pending.request with
  | fail error | div => simp [runWith, requested, StateT.run_pure] at supported
  | ok request =>
    simp only [runWith, requested, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, _called, returned⟩ := supported
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
    obtain ⟨digest, _, resumed⟩ := resumed_digest pending middle.1 initial returned.1.symm
    exact ⟨digest, resumed⟩

/-- Coordinates preserved by an ordinary hash callback survive every continuation outcome. -/
theorem preserves {State Value : Type}
    (hash : registration.HashRequest → StateT State ProbComp DigestReply)
    (project : State → Value)
    (preserved : ∀ request before reply after,
      (reply, after) ∈ support ((hash request).run before) → project after = project before)
    (pending : registration.ServerAdHash) (before after : State) (reply : Result)
    (supported : (reply, after) ∈ support ((runWith hash pending).run before)) :
    project after = project before := by
  cases requested : pending.request with
  | fail error | div =>
    simp only [runWith, requested, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at supported
    exact congrArg project supported.2
  | ok request =>
    simp only [runWith, requested, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, returned⟩ := supported
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
    exact (congrArg project returned.2).trans (preserved request before middle.1 middle.2 called)

/-- Actual stateful callback support supplies the exact digest receipt; no caller-selected AD or successful-initializer premise is inserted. -/
theorem state_receipt {State Platform : Type}
    (hash : registration.HashRequest → StateT State (StateT Platform ProbComp) DigestReply)
    (pending : registration.ServerAdHash) (before after : State) (previous next : Platform)
    (initial : registration.ServerInitialKdf)
    (supported : ((.ok (.Ok initial), after), next) ∈ support
      (((runWith hash pending).run before).run previous)) :
    ∃ digest, pending.resume (.Some digest) = .ok (.Ok initial) := by
  cases requested : pending.request with
  | fail error => simp [runWith, requested, StateT.run_pure] at supported
  | div => simp [runWith, requested, StateT.run_pure] at supported
  | ok request =>
    simp only [runWith, requested, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, returned⟩ := supported
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
    obtain ⟨digest, _, resumed⟩ := resumed_digest pending middle.1.1 initial returned.1.1.symm
    exact ⟨digest, resumed⟩

/-- A successful stateful hash phase retains the exact reached callback support as well as the owned core resume. -/
theorem state_hash_receipt {State Platform : Type}
    (hash : registration.HashRequest → StateT State (StateT Platform ProbComp) DigestReply)
    (pending : registration.ServerAdHash) (before after : State) (previous next : Platform)
    (initial : registration.ServerInitialKdf)
    (supported : ((.ok (.Ok initial), after), next) ∈ support
      (((runWith hash pending).run before).run previous)) :
    ∃ request digest, pending.request = .ok request ∧
      ((.Some digest, after), next) ∈ support (((hash request).run before).run previous) ∧
      pending.resume (.Some digest) = .ok (.Ok initial) := by
  cases requested : pending.request with
  | fail error | div => simp [runWith, requested, StateT.run_pure] at supported
  | ok request =>
    simp only [runWith, requested, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, returned⟩ := supported
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
    obtain ⟨digest, replyEq, resumed⟩ := resumed_digest pending middle.1.1 initial returned.1.1.symm
    refine ⟨request, digest, rfl, ?_, resumed⟩
    have same : middle = ((.Some digest, after), next) :=
      Prod.ext (Prod.ext replyEq returned.1.2.symm) returned.2.symm
    exact same ▸ called

/-- A state coordinate preserved by the actual hash callback is retained on every outcome of the owned continuation. -/
theorem state_preserves {State Platform Value : Type}
    (hash : registration.HashRequest → StateT State (StateT Platform ProbComp) DigestReply)
    (project : State → Value)
    (preserved : ∀ request before previous reply after next,
      ((reply, after), next) ∈ support (((hash request).run before).run previous) →
        project after = project before)
    (pending : registration.ServerAdHash) (before after : State) (previous next : Platform)
    (reply : Result)
    (supported : ((reply, after), next) ∈ support (((runWith hash pending).run before).run previous)) :
    project after = project before := by
  cases requested : pending.request with
  | fail error | div =>
    simp only [runWith, requested, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq] at supported
    exact congrArg project supported.1.2
  | ok request =>
    simp only [runWith, requested, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, called, returned⟩ := supported
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
    have same := preserved request before previous middle.1.1 middle.1.2 middle.2 called
    exact (congrArg project returned.1.2).trans same

end BeaconcryptCore.Computational.RegistrationServerAdHash
/-- info: 'BeaconcryptCore.Computational.RegistrationServerAdHash.resumed_digest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerAdHash.resumed_digest
/-- info: 'BeaconcryptCore.Computational.RegistrationServerAdHash.state_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerAdHash.state_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationServerAdHash.state_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerAdHash.state_preserves

/-- info: 'BeaconcryptCore.Computational.RegistrationServerAdHash.receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerAdHash.receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationServerAdHash.preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerAdHash.preserves


/-- info: 'BeaconcryptCore.Computational.RegistrationServerAdHash.state_hash_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerAdHash.state_hash_receipt

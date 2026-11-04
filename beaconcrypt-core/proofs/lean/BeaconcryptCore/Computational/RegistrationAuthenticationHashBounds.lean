-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationTermination
import BeaconcryptCore.Computational.RegistrationAuthenticationBounds
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! Actual Init authentication has exactly three possible hash positions: payload, Server fingerprint and Beacon fingerprint. A potential on actual source continuations bounds every failed/optional reply path, independently of the executor's conservative eight callback slots. -/
namespace BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds
open RegistrationAuthenticationExecutor
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow
open BeaconcryptCore.Refinement.RegistrationAuthentication
open BeaconcryptCore.Refinement.RegistrationInbound
open PqxdhRecordLiftInterface (EffectKind effectKind)
variable {Input Result : Type} {n : Nat}

def IsHash : Request → Prop
  | .hash _ => True
  | _ => False
instance : DecidablePred IsHash := fun query => by cases query <;> dsimp [IsHash] <;> infer_instance

def hashRank : registration.InitAuthentication → Nat
  | .HashRequested _ => 3
  | .MldsaVerificationRequested _ | .Ed25519VerificationRequested _ | .ServerFingerprintRequested _ => 2
  | .BeaconFingerprintRequested _ => 1
  | .Accepted _ | .Rejected => 0

def cost : registration.InitAuthentication → Nat
  | .HashRequested _ | .ServerFingerprintRequested _ | .BeaconFingerprintRequested _ => 1
  | _ => 0

private theorem cost_le (state : registration.InitAuthentication) : cost state ≤ hashRank state := by
  cases state <;> simp [cost, hashRank]
private theorem rank_le (state : registration.InitAuthentication) : hashRank state ≤ 3 := by
  cases state <;> simp [hashRank]

theorem step_progress {before after : registration.InitAuthentication} {event : Event}
    (edge : Step before event after) : hashRank after + cost before ≤ hashRank before := by
  cases edge with
  | hash pending reply after run =>
    cases reply with
    | none =>
      have same : after = .Rejected := (RustM.ok.inj run).symm
      rw [same]
      norm_num [hashRank, cost]
    | some digest =>
      obtain ⟨next, resumed, _⟩ := init_hash_success pending digest
      have same := RustM.ok.inj (resumed.symm.trans run)
      cases same
      norm_num [hashRank, cost]
  | mldsa pending verified after run =>
    obtain ⟨actual, resumed, facts⟩ := init_mldsa_exact pending verified
    have same := RustM.ok.inj (resumed.symm.trans run)
    subst actual
    cases after <;> simp only [initMldsaOutcome] at facts
    all_goals norm_num [hashRank, cost]
  | ed25519 pending opened after run =>
    obtain ⟨actual, resumed, facts⟩ := init_ed_resume_refines pending opened
    have same := RustM.ok.inj (resumed.symm.trans run)
    subst actual
    cases after <;> simp only [edProgress] at facts
    all_goals norm_num [hashRank, cost]
  | serverFingerprint pending reply after run =>
    cases reply with
    | none =>
      have same : after = .Rejected := (RustM.ok.inj run).symm
      rw [same]
      norm_num [hashRank, cost]
    | some digest =>
      obtain ⟨next, resumed, _⟩ := init_server_fingerprint_exact pending digest
      have same := RustM.ok.inj (resumed.symm.trans run)
      cases same
      norm_num [hashRank, cost]
  | beaconFingerprint pending reply after run =>
    cases reply with
    | none =>
      have same : after = .Rejected := (RustM.ok.inj run).symm
      rw [same]
      norm_num [hashRank, cost]
    | some digest =>
      obtain ⟨next, resumed, _⟩ := init_beacon_fingerprint_exact pending digest
      have same := RustM.ok.inj (resumed.symm.trans run)
      cases same
      norm_num [hashRank, cost]

private theorem continue_bound (value : RustM Input) (next : Input → OracleComp Spec (RustM Result))
    (cap : Nat) (bounded : ∀ input, (next input).IsQueryBoundP IsHash cap) :
    (continueWith value next).IsQueryBoundP IsHash cap := by
  cases value with
  | ok value => exact bounded value
  | fail error | div => trivial

private theorem step_bound (state : registration.InitAuthentication) : (step state).IsQueryBoundP IsHash (cost state) := by
  cases state <;> simp only [step, cost]
  all_goals first
    | trivial
    | apply continue_bound
      intro request
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨by simp [IsHash], fun _ => by trivial⟩

theorem execute_bound (fuel : Nat) (state : registration.InitAuthentication) :
    (execute fuel state).IsQueryBoundP IsHash (hashRank state) := by
  induction fuel generalizing state with
  | zero => trivial
  | succ fuel ih =>
    rw [execute]
    have tail : ∀ result ∈ support (step state), (continueWith result fun next => match next with
      | none => pure (.ok ([], state))
      | some (event, after) => do
        let rest ← execute fuel after
        continueWith rest fun final => pure (.ok (event :: final.1, final.2))).IsQueryBoundP IsHash (hashRank state - cost state) := by
      intro result present
      cases result with
      | fail error | div => trivial
      | ok selected => cases selected with
        | none => trivial
        | some pair =>
          rcases pair with ⟨event, after⟩
          have progress := step_progress (RegistrationAuthenticationExecutor.step_sound state event after present)
          have afterBound := (ih after).mono (show hashRank after ≤ hashRank state - cost state by omega)
          have finished : ∀ result ∈ support (execute fuel after), (continueWith result fun final =>
              pure (.ok (event :: final.1, final.2))).IsQueryBoundP IsHash 0 := by
            intro result _
            exact continue_bound result _ 0 (fun _ => by trivial)
          simpa only [Nat.add_zero, continueWith] using isQueryBoundP_bind afterBound finished
    have combined := isQueryBoundP_bind (step_bound state) tail
    have sum : cost state + (hashRank state - cost state) = hashRank state := by have := cost_le state; omega
    rw [sum] at combined
    exact combined

attribute [local irreducible] execute registration.begin_init_authentication

theorem begin_bound (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    (begin pin packet).IsQueryBoundP IsHash 3 :=
  continue_bound (registration.begin_init_authentication pin packet) _ 3 (fun state => (execute_bound 8 state).mono (rank_le state))

theorem program_bound (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) (kind : EffectKind) :
    (RegistrationAuthenticationCompiler.program (n := n) crypto verify pin packet).IsQueryBoundP
      (fun query => effectKind query = kind) (if kind = .hash then 3 else 0) := by
  by_cases selected : kind = .hash
  · subst kind
    simp only [ite_true, RegistrationAuthenticationCompiler.program]
    apply RawCtxSourceOpen.simulate_bound _ IsHash _ _ 3 (begin_bound pin packet)
    intro query
    cases query <;> simp [RegistrationAuthenticationCompiler.callbacks, IsHash, isQueryBoundP_query_iff, effectKind]
  · simpa only [ite_eq_right selected] using RegistrationAuthenticationBounds.program_bound (n := n) crypto verify pin packet kind

end BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.step_progress' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.step_progress

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.execute_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.execute_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.begin_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.begin_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds.program_bound

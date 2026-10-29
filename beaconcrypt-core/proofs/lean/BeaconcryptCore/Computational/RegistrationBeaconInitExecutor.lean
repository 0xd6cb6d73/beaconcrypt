-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationSigningShared
import BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence

/-! The complete outgoing Beacon Init executes the actual classical pin gate, three ordered attached-signing continuations, Beacon fingerprint hash, Init transcript hash, ML signing continuation and dynamic signed-view publication. Hashes and ML signing use the existing shared-cache signing interface, with the ML receipt emitted before signature validation or encoding can fail. The independent Ed signing interface preserves its actual request and reply effects. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

open BeaconcryptCore.Refinement.RegistrationInputs (hashBytes)
open BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence (StateCoherent Coherent)

abbrev EdSpec := registration.Ed25519SigningRequest →ₒ RegistrationSigningShared.SignReply
abbrev Spec := RegistrationSigningShared.Spec + EdSpec
abbrev Result (Encoded : Type) := core.result.Result (registration.PublishedBeaconInit Encoded) pqxdh.BeaconFresh
variable {Encoded : Type}

def continueWith {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded))) : OracleComp Spec (RustM (Result Encoded)) :=
  match action with
  | .ok value => next value
  | .fail error => pure (.fail error)
  | .div => pure .div

def ready (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.message fun view => pure (pending.publish (encode view))

def fromSigning (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let signature ← Spec.query (.inl (.sign request payload digest))
    continueWith (pending.resume signature) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .Ready selected => ready encode selected
      | _ => pure .div

def fromHash (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let digest ← Spec.query (.inl (.hash request))
    continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .MldsaSigningRequested selected => fromSigning encode ⟨.beacon, hashBytes request⟩ digest selected
      | _ => pure .div

def fromFingerprint (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let digest ← Spec.query (.inl (.hash request))
    continueWith (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) fun effect =>
      match effect with
      | .Rejected previous => pure (.ok (.Err previous))
      | .HashRequested selected => fromHash encode selected
      | _ => pure .div

def edRank (pending : registration.BeaconEd25519Signing) : Nat :=
  match pending.stage with
  | .PreKey => 3
  | .OneTimeKey => 2
  | .PqKey => 1

theorem ed_rank (pending : registration.BeaconEd25519Signing) (reply : RegistrationSigningShared.SignReply)
    (next : registration.BeaconEd25519Signing)
    (actual : pending.resume reply = .ok (.Ed25519SigningRequested next)) : edRank next < edRank pending := by
  obtain ⟨result, resumed, progress⟩ := BeaconcryptCore.Refinement.RegistrationSigning.ed_resume_refines pending reply
  have same : result = .Ed25519SigningRequested next := RustM.ok.inj (resumed.symm.trans actual)
  subst result
  cases stage : pending.stage
  all_goals simp only [BeaconcryptCore.Refinement.RegistrationSigning.EdReplyTransition, stage] at progress
  · simp only [edRank, progress.2.1, stage]
    decide
  · simp only [edRank, progress.2.1, stage]
    decide
  · exact progress.2.elim

def fromEd (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) : OracleComp Spec (RustM (Result Encoded)) :=
  continueWith pending.request fun request => do
    let reply ← Spec.query (.inr request)
    match _actual : pending.resume reply with
    | .ok (.Rejected previous) => pure (.ok (.Err previous))
    | .ok (.Ed25519SigningRequested next) => fromEd encode next
    | .ok (.FingerprintRequested selected) => fromFingerprint encode selected
    | .ok _ => pure .div
    | .fail error => pure (.fail error)
    | .div => pure .div
termination_by edRank pending
decreasing_by exact ed_rank pending reply next _actual

def begin (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize) :
    OracleComp Spec (RustM (Result Encoded)) :=
  continueWith (registration.begin_beacon_init control inputs coins pin mldsa) fun effect =>
    match effect with
    | .Rejected previous => pure (.ok (.Err previous))
    | .Ed25519SigningRequested selected => fromEd encode selected
    | _ => pure .div

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume

private theorem continueWith_support {Input : Type} (action : RustM Input)
    (next : Input → OracleComp Spec (RustM (Result Encoded))) (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (continueWith action next)) :
    ∃ value, action = .ok value ∧ .ok (.Ok published) ∈ support (next value) := by
  cases action <;> simp_all [continueWith]

theorem ready_coherent (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitReady) (published : registration.PublishedBeaconInit Encoded)
    (coherent : Coherent (.Ready pending)) (supported : .ok (.Ok published) ∈ support (ready encode pending)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  obtain ⟨view, _requested, continued⟩ := continueWith_support pending.message _ published supported
  simp only [support_pure, Set.mem_singleton_iff] at continued
  exact BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.publish_coherent pending (encode view)
    published coherent continued.symm

theorem signing_coherent (encode : registration.SignedInitView → core.option.Option Encoded)
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) (published : registration.PublishedBeaconInit Encoded)
    (coherent : StateCoherent pending.state)
    (supported : .ok (.Ok published) ∈ support (fromSigning encode payload digest pending)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  obtain ⟨request, _requested, called⟩ := continueWith_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨signature, _signed, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continueWith_support (pending.resume signature) _ published continued
  have kept := BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.mldsa_coherent pending signature effect coherent resumed
  cases effect with
  | Ready selected => exact ready_coherent encode selected published kept continued
  | _ => simp at continued

theorem hash_coherent (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconInitHash) (published : registration.PublishedBeaconInit Encoded)
    (coherent : StateCoherent pending.state) (supported : .ok (.Ok published) ∈ support (fromHash encode pending)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  obtain ⟨request, _requested, called⟩ := continueWith_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨digest, _hashed, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continueWith_support
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published continued
  have kept := BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.hash_coherent pending _ effect coherent resumed
  cases effect with
  | MldsaSigningRequested selected => exact signing_coherent encode _ digest selected published kept continued
  | _ => simp at continued

theorem fingerprint_coherent (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconFingerprint) (published : registration.PublishedBeaconInit Encoded)
    (coherent : StateCoherent pending.state) (supported : .ok (.Ok published) ∈ support (fromFingerprint encode pending)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  obtain ⟨request, _requested, called⟩ := continueWith_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨digest, _hashed, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continueWith_support
    (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published continued
  have kept := BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.fingerprint_coherent pending _ effect coherent resumed
  cases effect with
  | HashRequested selected => exact hash_coherent encode selected published kept continued
  | _ => simp at continued

theorem ed_coherent (encode : registration.SignedInitView → core.option.Option Encoded)
    (pending : registration.BeaconEd25519Signing) (published : registration.PublishedBeaconInit Encoded)
    (coherent : StateCoherent pending.state) (supported : .ok (.Ok published) ∈ support (fromEd encode pending)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  rw [fromEd.eq_def] at supported
  obtain ⟨request, _requested, called⟩ := continueWith_support pending.request _ published supported
  simp only [mem_support_bind_iff] at called
  obtain ⟨reply, _signed, continued⟩ := called
  cases actual : pending.resume reply with
  | fail error => rw [actual] at continued; simp at continued
  | div => rw [actual] at continued; simp at continued
  | ok effect =>
      have kept := BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.ed_coherent pending reply effect coherent actual
      cases effect with
      | Ed25519SigningRequested next =>
          rw [actual] at continued
          exact ed_coherent encode next published kept continued
      | FingerprintRequested selected =>
          rw [actual] at continued
          exact fingerprint_coherent encode selected published kept continued
      | _ => rw [actual] at continued; simp at continued
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

/-- Published control/binding coherence is derived from the actual begin gate and all reached native continuations. -/
theorem begin_coherent (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded)
    (supported : .ok (.Ok published) ∈ support (begin encode control inputs coins pin mldsa)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  obtain ⟨effect, actual, continued⟩ := continueWith_support
    (registration.begin_beacon_init control inputs coins pin mldsa) _ published supported
  have kept := BeaconcryptCore.Refinement.RegistrationBeaconInitCoherence.begin_coherent
    control inputs coins pin mldsa effect actual
  cases effect with
  | Ed25519SigningRequested selected => exact ed_coherent encode selected published kept continued
  | _ => simp at continued

theorem simulated_coherent {State : Type} (implementation : QueryImpl Spec (StateT State ProbComp))
    (encode : registration.SignedInitView → core.option.Option Encoded)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array Std.U8 1952#usize)
    (published : registration.PublishedBeaconInit Encoded) (before after : State)
    (supported : (.ok (.Ok published), after) ∈ support
      ((simulateQ implementation (begin encode control inputs coins pin mldsa)).run before)) :
    published.pending.control.expected_server_binding = published.pending.binding.server_pin.binding := by
  apply begin_coherent encode control inputs coins pin mldsa published
  apply OracleComp.support_simulateQ_run'_subset implementation (begin encode control inputs coins pin mldsa) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationBeaconInitExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.ed_rank' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.ed_rank

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.ready_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.ready_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.signing_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.signing_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.hash_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.hash_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.fingerprint_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.fingerprint_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.ed_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.ed_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.begin_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.begin_coherent

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.simulated_coherent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconInitExecutor.simulated_coherent

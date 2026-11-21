-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconPublication
import BeaconcryptCore.Computational.RegistrationNativeInitTupleSource

/-! Successful effectful Init encoding has the same actual preceding Core crypto execution as a pure encoder returning its reached bytes. The replay stops immediately before the actual writer, whose full supported effect and poststate are separately retained. This local source-stage statement requires no writer purity, wire inversion or complete-profile equality. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay
open RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitExecutor (Spec Result)
variable {S Encoded : Type}
attribute [local irreducible] registration.BeaconInitHash.resume
  registration.BeaconEd25519Signing.resume

private theorem continue_support {Input : Type} (action : RustM Input)
    (next : Input → StateT S ProbComp (RustM (Result Encoded)))
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((continueWith action next).run before)) :
    ∃ value, action = .ok value ∧ (.ok (.Ok published), after) ∈ support ((next value).run before) := by
  cases action <;> simp_all [continueWith, StateT.run_pure]

private abbrev EncoderCut (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (published : registration.PublishedBeaconInit Encoded) (before after : S) : Prop :=
  ∃ view, (.ok (.Some published.encoded), after) ∈ support ((encode view).run before)

private theorem ready_replay
    (impl : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitReady) (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((ready encode pending).run before)) :
    ∃ atEncoder,
      (.ok (.Ok published), atEncoder) ∈ support
        ((simulateQ impl (RegistrationBeaconInitExecutor.ready (fun _ => .Some published.encoded) pending)).run before) ∧
      EncoderCut encode published atEncoder after := by
  obtain ⟨view, requested, called⟩ := continue_support pending.message _ published before after supported
  simp only [StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨⟨encoded, current⟩, encodedSupport, returned⟩ := called
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at returned
  have stateEq : current = after := returned.2.symm
  cases encoded with
  | fail error | div => cases returned.1
  | ok optional => cases optional with
    | none =>
      simp only [bind_tc_ok] at returned
      rw [BeaconcryptCore.Refinement.RegistrationSigningContinuations.failed_publication_preserves_fresh] at returned
      cases returned.1
    | some bytes =>
      have publication : pending.publish (.Some bytes) = .ok (.Ok published) := returned.1.symm
      obtain ⟨result, ran, _control, _pin, _hash, _identity, _pre, _one, _pq, output⟩ :=
        BeaconcryptCore.Refinement.RegistrationSigningContinuations.publication_retains_exact_request pending bytes
      have same : result = published := by simpa using ran.symm.trans publication
      subst result
      have bytesEq : bytes = published.encoded := output.symm
      have actualPublication : pending.publish (.Some published.encoded) = .ok (.Ok published) := bytesEq ▸ publication
      refine ⟨before, ?_, view, ?_⟩
      · simp only [RegistrationBeaconInitExecutor.ready, requested, RegistrationBeaconInitExecutor.continueWith,
          simulateQ_pure, StateT.run_pure, actualPublication, support_pure, Set.mem_singleton_iff]
      · simpa only [bytesEq, ← stateEq] using encodedSupport

private theorem hash_replay (impl : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconInitHash) (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((fromHash impl encode pending).run before)) :
    ∃ atEncoder,
      (.ok (.Ok published), atEncoder) ∈ support ((simulateQ impl
        (RegistrationBeaconInitExecutor.fromHash (fun _ => .Some published.encoded) pending)).run before) ∧
      EncoderCut encode published atEncoder after := by
  obtain ⟨request, requested, called⟩ := continue_support pending.request _ published before after supported
  simp only [StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨⟨digest, current⟩, hashed, continued⟩ := called
  obtain ⟨effect, resumed, continued⟩ := continue_support (pending.resume (.Some (RegistrationAuthenticationShared.digestArray digest))) _ published current after continued
  cases effect with
  | Ready selected =>
    obtain ⟨atEncoder, replay, encoded⟩ := ready_replay impl encode selected published current after continued
    refine ⟨atEncoder, ?_, encoded⟩
    simp only [RegistrationBeaconInitExecutor.fromHash, requested, RegistrationBeaconInitExecutor.continueWith,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
    exact ⟨(digest, current), hashed, by simpa only [resumed, RegistrationBeaconInitExecutor.continueWith] using replay⟩
  | _ => simp [StateT.run_pure] at continued

private theorem ed_replay (impl : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (pending : registration.BeaconEd25519Signing) (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((fromEd impl encode pending).run before)) :
    ∃ atEncoder,
      (.ok (.Ok published), atEncoder) ∈ support ((simulateQ impl
        (RegistrationBeaconInitExecutor.fromEd (fun _ => .Some published.encoded) pending)).run before) ∧
      EncoderCut encode published atEncoder after := by
  rw [fromEd.eq_def] at supported
  obtain ⟨request, requested, called⟩ := continue_support pending.request _ published before after supported
  simp only [StateT.run_bind, mem_support_bind_iff] at called
  obtain ⟨⟨reply, current⟩, signed, continued⟩ := called
  cases actual : pending.resume reply with
  | fail error => rw [actual] at continued; simp [StateT.run_pure] at continued
  | div => rw [actual] at continued; simp [StateT.run_pure] at continued
  | ok effect => cases effect with
    | Ed25519SigningRequested next =>
      rw [actual] at continued
      obtain ⟨atEncoder, replay, encoded⟩ := ed_replay impl encode next published current after continued
      refine ⟨atEncoder, ?_, encoded⟩
      rw [RegistrationBeaconInitExecutor.fromEd.eq_def]
      simp only [requested, RegistrationBeaconInitExecutor.continueWith, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, mem_support_bind_iff]
      exact ⟨(reply, current), signed, by dsimp only; rw [actual]; exact replay⟩
    | HashRequested selected =>
      rw [actual] at continued
      obtain ⟨atEncoder, replay, encoded⟩ := hash_replay impl encode selected published current after continued
      refine ⟨atEncoder, ?_, encoded⟩
      rw [RegistrationBeaconInitExecutor.fromEd.eq_def]
      simp only [requested, RegistrationBeaconInitExecutor.continueWith, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, mem_support_bind_iff]
      exact ⟨(reply, current), signed, by dsimp only; rw [actual]; exact replay⟩
    | _ => rw [actual] at continued; simp [StateT.run_pure] at continued
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next actual

/-- Successful effectful encoding retains one exact crypto prefix and the actual subsequent source encoder support, with its full poststate. -/
theorem begin_replay (impl : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((begin impl encode control inputs coins pin).run before)) :
    ∃ atEncoder,
      (.ok (.Ok published), atEncoder) ∈ support ((simulateQ impl
        (RegistrationBeaconInitExecutor.begin (fun _ => .Some published.encoded) control inputs coins pin)).run before) ∧
      ∃ view, (.ok (.Some published.encoded), after) ∈ support ((encode view).run atEncoder) := by
  obtain ⟨effect, actual, continued⟩ := continue_support (registration.begin_beacon_init control inputs coins pin) _ published before after supported
  cases effect with
  | Ed25519SigningRequested selected =>
    obtain ⟨atEncoder, replay, encoded⟩ := ed_replay impl encode selected published before after continued
    refine ⟨atEncoder, ?_, encoded⟩
    simpa only [RegistrationBeaconInitExecutor.begin, actual, RegistrationBeaconInitExecutor.continueWith] using replay
  | _ => simp [StateT.run_pure] at continued


/-- Actual source success retains the original tagged Init tuple and exact hash/sign cuts before its separately retained terminal writer effect. -/
theorem begin_tuple (impl : QueryImpl Spec (StateT S ProbComp))
    (encode : registration.InitView → StateT S ProbComp (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (published : registration.PublishedBeaconInit Encoded) (before after : S)
    (supported : (.ok (.Ok published), after) ∈ support ((begin impl encode control inputs coins pin).run before)) :
    ∃ atEncoder view started pending hashing atHash,
      (.ok (.Some published.encoded), after) ∈ support ((encode view).run atEncoder) ∧
      pqxdh.beacon_start control inputs coins = .ok started ∧
      pqxdh.validate_init_kex started.message = .ok (.Ok {
        beacon_identity_public_key := inputs.identity_public_key,
        beacon_prekey_public_key := inputs.prekey_public_key,
        beacon_one_time_public_key := coins.one_time_public_key,
        beacon_pq_public_key := inputs.pq_public_key }) ∧
      registration.begin_beacon_init control inputs coins pin = .ok (.Ed25519SigningRequested pending) ∧
      RegistrationNativeInitTupleSource.EdLead impl pending before hashing atHash ∧
      RegistrationNativeInitTupleSource.Fixed started pin inputs.identity_public_key hashing.state ∧
      RegistrationNativeInitTupleSource.Attached started hashing.state ∧
      RegistrationNativeInitTupleSource.HashCut impl (fun _ => .Some published.encoded) hashing atHash published atEncoder := by
  obtain ⟨atEncoder, replay, view, encoded⟩ := begin_replay impl encode control inputs coins pin published before after supported
  obtain ⟨started, pending, hashing, atHash, began, validated, requested, leading, fixed, attached, cut⟩ :=
    RegistrationNativeInitTupleSource.begin_receipt impl (fun _ => .Some published.encoded) control inputs coins pin
      published before atEncoder replay
  exact ⟨atEncoder, view, started, pending, hashing, atHash, encoded, began, validated, requested, leading, fixed, attached, cut⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay.begin_replay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay.begin_replay

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay.begin_tuple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicationReplay.begin_tuple

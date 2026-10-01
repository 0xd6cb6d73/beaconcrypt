import BeaconcryptCore.Computational.PqxdhServerAuthNative
import BeaconcryptCore.Computational.RawCtxOwnerProvenance
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds

/-! Concrete Beacon initial-response admission uses the existing complete native owner. The abstraction retains the full callback state and executes preparation, root processing and raw opening before inspecting the actual sequence-one and binding result. It does not infer protocol origin from successful opening or equal bytes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationBeacon
open PqxdhBeaconPhase2Preparation (Bytes State)
open PqxdhBeaconPhase2Publication
variable {I D K X Response A : Type}

/-- A completed source attempt has no retained InitSent owner, whether it published or aborted. -/
def Inactive (state : State I D K) : Prop :=
  ∀ control prekey oneTime kem, state.beacon.phase ≠ .initSent control prekey oneTime kem

/-- Repeated delivery to a consumed owner performs no parser, KDF, decapsulation or opening callback and preserves both complete states. -/
theorem inactive_owner (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (state : State I D K) (inactive : Inactive state) :
    owner (X := X) (Response := Response) decode raw state = pure (none, state) := by
  exact owner_inactive decode raw state inactive

/-- The literal original publication/abort operation consumes InitSent on every staged outcome. -/
theorem finish_inactive (control : pqxdh.BeaconInitSent) (state : State I D K)
    (staged : Option Staged) : Inactive (finish control state staged).2 := by
  exact PqxdhServerAuthExperiment.finish_phase control state staged

/-- Every supported active attempt consumes its private owner after the complete original callback run, retaining the actual optional reply and interpreter poststate. -/
theorem attempt_inactive (handler : QueryImpl (FullSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : D) (kem : K)
    (active : state.beacon.phase = .initSent control prekey oneTime kem)
    (auxiliary : A) (result : (Option Bytes × State I D K) × A)
    (supported : result ∈ support ((simulateQ handler (owner decode raw state)).run auxiliary)) :
    Inactive result.1.2 := by
  have equation := owner_complete handler decode raw state control prekey oneTime kem active auxiliary
    (fun reply => pure reply)
  simp only [bind_pure] at equation
  rw [equation, mem_support_bind_iff] at supported
  obtain ⟨⟨prepared, intermediate⟩, _, supported⟩ := supported
  cases prepared with
  | none =>
      simpa only [eq_of_mem_support_pure _ supported] using finish_inactive control state none
  | some prepared =>
      rw [mem_support_bind_iff] at supported
      obtain ⟨⟨staged, final⟩, _, supported⟩ := supported
      have equal := eq_of_mem_support_pure _ supported
      simpa only [equal] using finish_inactive control state staged

/-- After any actual active attempt, every later raw response is rejected before any callback, with the complete reached owner retained. -/
theorem no_retry (handler : QueryImpl (FullSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw later : Bytes) (state : State I D K)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : D) (kem : K)
    (active : state.beacon.phase = .initSent control prekey oneTime kem)
    (auxiliary : A) (result : (Option Bytes × State I D K) × A)
    (supported : result ∈ support ((simulateQ handler (owner decode raw state)).run auxiliary)) :
    owner (X := X) (Response := Response) decode later result.1.2 = pure (none, result.1.2) := by
  exact inactive_owner decode later result.1.2
    (attempt_inactive handler decode raw state control prekey oneTime kem active auxiliary result supported)

/-- Every failed InitSent attempt installs the exact terminal source abort state; earlier callback effects remain in the actual final interpreter state. -/
theorem active_failure (handler : QueryImpl (FullSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state next : State I D K)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : D) (kem : K)
    (active : state.beacon.phase = .initSent control prekey oneTime kem) (auxiliary final : A)
    (supported : ((none, next), final) ∈ support ((simulateQ handler (owner decode raw state)).run auxiliary)) :
    next = PqxdhBeaconPhase2Preparation.abort control state := by
  simpa only [active] using owner_failure handler decode raw state next auxiliary final supported

/-- The final registration sequence gate uses the same immutable decoded target as the complete raw receiver, after all raw effects have executed. -/
theorem raw_wrong_target (handler : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (auxiliary : A) (received : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) × A)
    (supported : received ∈ support (RawCtxWholeOwner.rawGame handler decode raw (localOwner candidate kernel) auxiliary))
    (wrong : ∀ frame, decode raw = some frame → frame.sequence ≠ 1#u64) :
    afterOpening candidate received.1.2.owner.kernel received.1.1 = none := by
  cases opening : received.1.1 with
  | none => simp only [afterOpening]
  | some message =>
      obtain ⟨frame, decoded, _, _, sequence⟩ :=
        RawCtxOwnerProvenance.raw_success_metadata handler decode raw (localOwner candidate kernel)
          auxiliary received supported message opening
      exact afterOpening_wrong_sequence candidate _ message (sequence ▸ wrong frame decoded)

/-- A successful public reply contains one contiguous actual preparation/root/initialization/app/raw path. No callback state, cache, failed alternative or published kernel is reconstructed from equal public bytes. -/
theorem successful_path (handler : QueryImpl (FullSpec I D K X Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw plaintext : Bytes) (state next : State I D K)
    (auxiliary final : A)
    (supported : ((some plaintext, next), final) ∈ support ((simulateQ handler (owner decode raw state)).run auxiliary)) :
    ∃ control prekey oneTime kem prepared preparedState root rootState initial initialState app appState received staged,
      state.beacon.phase = .initSent control prekey oneTime kem ∧
      (some prepared, preparedState) ∈ support ((simulateQ (fun query => handler (.inl query))
        (PqxdhBeaconPhase2Preparation.prepare control state.beacon.identity prekey oneTime kem raw)).run auxiliary) ∧
      (some root, rootState) ∈ support ((handler (.inr (.inr (.root prepared.candidate.root_key_input)))).run preparedState) ∧
      (initial, initialState) ∈ support ((handler (.inr (.inr (.initial (PqxdhInitialRatchetComplementarity.beaconPending root).request)))).run rootState) ∧
      (some app, appState) ∈ support ((handler (.inr (.inr (.application prepared.response)))).run initialState) ∧
      received ∈ support (RawCtxWholeOwner.rawGame (fun query => handler (.inr (.inl query))) decode app
        (localOwner (clearedCandidate prepared.candidate)
          (normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) initial)) appState) ∧
      received.2 = final ∧
      afterOpening (clearedCandidate prepared.candidate) received.1.2.owner.kernel received.1.1 = some staged ∧
      staged.opened.sequence = 1#u64 ∧ 8 < staged.opened.plaintext.length ∧
      publish state staged = (plaintext, next) := by
  obtain ⟨control, prekey, oneTime, kem, prepared, preparedState, staged,
    active, preparation, tailSupport, _, sequence, length, publication⟩ :=
      owner_success handler decode raw plaintext state next auxiliary final supported
  obtain ⟨root, rootState, rootSupport, afterSupport⟩ :=
    tail_supported (fun query => handler (.inr query)) decode prepared preparedState final staged tailSupport
  obtain ⟨initial, initialState, app, appState, received, initSupport, appSupport,
    rawSupport, finalState, opening⟩ :=
      afterRoot_supported (fun query => handler (.inr query)) decode prepared root rootState final staged afterSupport
  exact ⟨control, prekey, oneTime, kem, prepared, preparedState, root, rootState,
    initial, initialState, app, appState, received, staged, active, preparation, rootSupport,
    initSupport, appSupport, rawSupport, finalState, opening, sequence, length, publication⟩

/-- Pure dispatch on a non-one decoded target retains the entire raw execution and arbitrary complete continuation. Only the subsequent registration decision is simplified to rejection. -/
theorem wrong_target_continuation {Result : Type}
    (handler : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (auxiliary : A) (wrong : ∀ frame, decode raw = some frame → frame.sequence ≠ 1#u64)
    (next : Option Staged → (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) × A → ProbComp Result) :
    (RawCtxWholeOwner.rawGame handler decode raw (localOwner candidate kernel) auxiliary >>= fun received =>
      next (afterOpening candidate received.1.2.owner.kernel received.1.1) received) =
    (RawCtxWholeOwner.rawGame handler decode raw (localOwner candidate kernel) auxiliary >>= fun received =>
      next none received) := by
  apply bind_congr_of_forall_mem_support
  intro received supported
  rw [raw_wrong_target handler decode raw candidate kernel auxiliary received supported wrong]

/-- Actual extracted binding authentication fixes the sender and exact first eight bytes, while leaving the nonempty application suffix unrestricted. -/
theorem opened_binding (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    (staged : Staged) (success : afterOpening candidate kernel reply = some staged) :
    staged.authenticated.candidate = candidate ∧
      staged.opened.keyId = candidate.server_binding.identity_key_id ∧
      staged.opened.plaintext.take 8 = Pqxdh.LE64 candidate.assigned_key_id.val ∧
      staged.opened.plaintext.drop 8 ≠ [] := by
  obtain ⟨_, _, _, _, length, authenticated⟩ := afterOpening_success candidate kernel reply staged success
  obtain ⟨same, sender, binding, bindingEq, bindingBytes⟩ :=
    BeaconcryptCore.Refinement.PqxdhSurface.authenticated_registration_success_shape candidate staged.opened.keyId _ staged.authenticated authenticated
  obtain ⟨expected, expectedEq, bytesEq⟩ :=
    PqxdhRefinement.registration_key_id_binding_abs candidate.assigned_key_id
  have bindingSame : binding = expected := RustM.ok.inj
    ((show pqxdh.registration_key_id_binding candidate.assigned_key_id = ok binding from bindingEq).symm.trans expectedEq)
  subst binding
  refine ⟨same, sender, ?_, ?_⟩
  · exact (BeaconcryptCore.Refinement.ProtocolComposition.plaintextBinding_bytes _ length).symm.trans
      ((congrArg PqxdhRefinement.absBytes bindingBytes).trans bytesEq)
  · intro empty
    have dropped := congrArg List.length empty
    simp only [List.length_drop, List.length_nil] at dropped
    omega

/-- A reached accepted raw result identifies the original decoded sequence-one frame, owning sender and actual committed kernel. -/
theorem raw_success_receipt (handler : QueryImpl RawCtxWholeOwner.PrimitiveSpec (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ratchet.concrete.ConcreteRatchetKernel)
    (auxiliary : A) (received : (core.option.Option RawCtxWholeOwner.Decrypted × RawCtxWholeOwner.OwnerState Unit) × A)
    (supported : received ∈ support (RawCtxWholeOwner.rawGame handler decode raw (localOwner candidate kernel) auxiliary))
    (staged : Staged)
    (accepted : afterOpening candidate received.1.2.owner.kernel received.1.1 = some staged) :
    ∃ frame, decode raw = some frame ∧ frame.sequence = 1#u64 ∧
      staged.opened.keyId = frame.sender ∧ frame.sender = candidate.server_binding.identity_key_id ∧
      staged.kernel = received.1.2.owner.kernel ∧ staged.associatedData = candidate.associated_data := by
  obtain ⟨opened, sequence, actualKernel, ad, _, _⟩ := afterOpening_success candidate _ _ staged accepted
  obtain ⟨frame, decoded, sender, owning, target⟩ :=
    RawCtxOwnerProvenance.raw_success_metadata handler decode raw (localOwner candidate kernel)
      auxiliary received supported staged.opened opened
  exact ⟨frame, decoded, target.symm.trans sequence, sender, sender.symm.trans owning, actualKernel, ad⟩

/-- The complete expanded source retains the prior 69-callback allowance; arbitrary primitive/codec costs are paid by the existing per-callback bound. Inactive delivery has exactly zero such callbacks. -/
theorem native_calls (decode : RawCtxReceive.FrameDecoder) (raw : Bytes) (state : State I D K) :
    (nativeOwner (X := X) (Response := Response) decode raw state).IsTotalQueryBound 69 ∧
      (Inactive state → (nativeOwner (X := X) (Response := Response) decode raw state).IsTotalQueryBound 0) := by
  refine ⟨PqxdhBeaconPhase2Bounds.native_owner_bound decode raw state, ?_⟩
  intro inactive
  simp only [nativeOwner, inactive_owner decode raw state inactive, simulateQ_pure]
  trivial

/-- Successful publication installs the actual raw kernel and the authenticated assigned ID, returning only the unrestricted nonempty suffix after the exact eight-byte prefix. -/
theorem published_shape (candidate : pqxdh.BeaconRegistrationCandidate)
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (reply : core.option.Option RawCtxWholeOwner.Decrypted)
    (staged : Staged) (accepted : afterOpening candidate kernel reply = some staged)
    (state : State I D K) (plaintext : Bytes) (next : State I D K)
    (published : publish state staged = (plaintext, next)) :
    plaintext = staged.opened.plaintext.drop 8 ∧ plaintext ≠ [] ∧
      staged.opened.plaintext.take 8 = Pqxdh.LE64 candidate.assigned_key_id.val ∧
      next.beacon.identityKeyId = candidate.assigned_key_id ∧
      next.beacon.phase = .established ⟨candidate.server_binding, candidate.assigned_key_id⟩
        candidate.associated_data kernel := by
  obtain ⟨same, _, binding, nonempty⟩ := opened_binding candidate kernel reply staged accepted
  obtain ⟨_, _, actualKernel, ad, _, _⟩ := afterOpening_success candidate kernel reply staged accepted
  cases published
  simp only [same, actualKernel, ad, binding, and_self]
  exact ⟨True.intro, nonempty, True.intro⟩

end BeaconcryptCore.Computational.PqxdhRegistrationBeacon

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.inactive_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.inactive_owner
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.finish_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.finish_inactive
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.attempt_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.attempt_inactive
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.no_retry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.no_retry
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.active_failure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.active_failure
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.raw_wrong_target' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.raw_wrong_target
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.successful_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.successful_path
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.wrong_target_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.wrong_target_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.opened_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.opened_binding
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.raw_success_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.raw_success_receipt
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.native_calls' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.native_calls
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationBeacon.published_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationBeacon.published_shape

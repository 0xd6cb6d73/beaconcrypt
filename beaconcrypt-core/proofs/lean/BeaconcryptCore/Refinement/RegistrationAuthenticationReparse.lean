-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.RegistrationAuthenticationParsedIdentity
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
/-! Successful actual authentication derives a repeatable Ed parse receipt for its retained Beacon identity. The selected parser is deterministic and read-only but can reject every invalid input. No key-validity or authentication-success premise is supplied to the native controller. -/
namespace BeaconcryptCore.Refinement.RegistrationAuthenticationReparse
open BeaconcryptCore.Computational
open RegistrationAuthenticationExecutor
open RegistrationAuthenticationFlow (Event Step)
open RegistrationAuthenticationParsedIdentity (Invariant ReplyValid)
variable [primitive : AdapterInitEdPrimitive.Operations]
variable {S : Type}

structure Parser (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp)) where
  parse : Slice U8 → core.result.Result primitive.PublicKey primitive.Error
  source : ∀ bytes, primitive.parse bytes = .ok (parse bytes)
  native : ∀ bytes, native (.inr (.parse bytes)) = pure (parse bytes)

def Parsed {native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp)}
    (parser : Parser native) (key : Std.Array U8 32#usize) : Prop :=
  ∃ publicKey, parser.parse key.to_slice = .Ok publicKey

noncomputable section

theorem opened_admits (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp))
    (parser : Parser native) (request : registration.Ed25519VerificationRequest) (before after : S) (opened : Slice U8)
    (supported : (.Some opened, after) ∈ support
      (((native ∘ₛ AdapterInitAuthenticationStateful.abstractNative) (.ed25519 request)).run before)) :
    Parsed parser request.public_key := by
  rw [QueryImpl.apply_compose] at supported
  simp only [AdapterInitAuthenticationStateful.abstractNative, AdapterInitAuthenticationStateful.opened,
    simulateQ_bind, simulateQ_spec_query, parser.native, pure_bind] at supported
  cases parsed : parser.parse request.public_key.to_slice with
  | Err error =>
      simp only [parsed, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | Ok publicKey => exact ⟨publicKey, parsed⟩

omit primitive in
theorem step_admits (implementation : QueryImpl Spec (StateT S ProbComp))
    (valid : Std.Array U8 32#usize → Prop)
    (admission : ∀ request before after opened,
      (.Some opened, after) ∈ support ((implementation (.ed25519 request)).run before) → valid request.public_key)
    (initial : registration.InitAuthentication) (event : Event) (final : registration.InitAuthentication)
    (before after : S)
    (supported : (.ok (some (event, final)), after) ∈ support
      ((simulateQ implementation (step initial)).run before)) : ReplyValid valid initial event := by
  cases initial with
  | HashRequested _ | MldsaVerificationRequested _ | ServerFingerprintRequested _ | BeaconFingerprintRequested _ | Accepted _ | Rejected => trivial
  | Ed25519VerificationRequested pending =>
    cases event with
    | hash _ | mldsa _ | serverFingerprint _ | beaconFingerprint _ => trivial
    | ed25519 stage opened =>
      cases opened with
      | none => trivial
      | some bytes =>
        simp only [step] at supported
        obtain ⟨request, requested, called⟩ := RegistrationAuthenticationInterpretation.continueWith_support
          implementation pending.request _ _ before after supported
        simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at called
        obtain ⟨⟨reply, middle⟩, answered, finished⟩ := called
        simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq] at finished
        obtain ⟨next, returned, _progress⟩ := RegistrationInbound.init_ed_resume_refines pending reply
        rw [returned] at finished
        cases reply with
        | none =>
          simp only [edge, RustM.ok.injEq, _root_.Option.some.injEq, Prod.mk.injEq, Event.ed25519.injEq, reduceCtorEq] at finished
          exact False.elim finished.1.1.2
        | some opened =>
          obtain ⟨queried, queriedRun, queriedKey, _bytes, _length⟩ := RegistrationAuthentication.init_ed_request_exact pending
          have same : queried = request := RustM.ok.inj (queriedRun.symm.trans requested)
          subst queried
          simpa only [ReplyValid, queriedKey] using admission request before middle opened answered

omit primitive in
private theorem free_step (implementation : QueryImpl Spec (StateT S ProbComp))
    (initial : registration.InitAuthentication) (event : Event) (final : registration.InitAuthentication)
    (before after : S)
    (supported : (.ok (some (event, final)), after) ∈ support
      ((simulateQ implementation (step initial)).run before)) : Step initial event final := by
  apply RegistrationAuthenticationExecutor.step_sound initial event final
  apply OracleComp.support_simulateQ_run'_subset implementation (step initial) before
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst supported

omit primitive in
theorem trace (implementation : QueryImpl Spec (StateT S ProbComp))
    (valid : Std.Array U8 32#usize → Prop)
    (admission : ∀ request before after opened,
      (.Some opened, after) ∈ support ((implementation (.ed25519 request)).run before) → valid request.public_key)
    {initial final : registration.InitAuthentication} {events : List Event} {before after : S}
    (execution : RegistrationAuthenticationInterpretation.Trace implementation initial before events final after) :
    Invariant valid initial → Invariant valid final := by
  induction execution with
  | refl => exact id
  | @cons initial before event next middle events final after first rest ih =>
      intro prior
      apply ih
      exact RegistrationAuthenticationParsedIdentity.progress valid
        (free_step implementation initial event next before middle first) prior
        (step_admits implementation valid admission initial event next before middle first)

-- Use the checked driver interface for elaboration; the entry proof unfolds begin explicitly.
attribute [local irreducible] RegistrationAuthenticationExecutor.execute RegistrationAuthenticationExecutor.begin

omit primitive in
theorem accepted_invariant (implementation : QueryImpl Spec (StateT S ProbComp))
    (valid : Std.Array U8 32#usize → Prop)
    (admission : ∀ request before after opened,
      (.Some opened, after) ∈ support ((implementation (.ed25519 request)).run before) → valid request.public_key)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (authenticated : registration.AuthenticatedInit) (before after : S)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((simulateQ implementation (begin pin packet)).run before)) :
    valid authenticated.binding.beacon_identity_public_key := by
  obtain ⟨phase, started, _packet, _pin, _input⟩ := RegistrationAuthentication.begin_init_exact pin packet
  unfold begin at supported
  rw [started] at supported
  have traced := RegistrationAuthenticationInterpretation.execute_trace implementation 8
    (.HashRequested phase) events (.Accepted authenticated) before after supported
  exact trace implementation valid admission traced True.intro

theorem accepted (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp))
    (parser : Parser native) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (authenticated : registration.AuthenticatedInit) (before after : S)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((simulateQ (native ∘ₛ AdapterInitAuthenticationStateful.abstractNative) (begin pin packet)).run before)) :
    Parsed parser authenticated.binding.beacon_identity_public_key :=
  accepted_invariant _ (Parsed parser) (opened_admits native parser) pin packet events authenticated before after supported

theorem reparse (native : QueryImpl AdapterInitAuthenticationStateful.NativeSpec (StateT S ProbComp))
    (parser : Parser native) (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket)
    (events : List Event) (authenticated : registration.AuthenticatedInit) (before after : S)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((simulateQ (native ∘ₛ AdapterInitAuthenticationStateful.abstractNative) (begin pin packet)).run before)) :
    ∃ publicKey, beaconcrypt_crypto.crypto_sign.PublicKey.from_bytes
      authenticated.binding.beacon_identity_public_key.to_slice = .ok (.Ok publicKey) := by
  obtain ⟨publicKey, parsed⟩ := accepted native parser pin packet events authenticated before after supported
  exact ⟨publicKey, (parser.source _).trans (congrArg RustM.ok parsed)⟩
end
end BeaconcryptCore.Refinement.RegistrationAuthenticationReparse

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.opened_admits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.opened_admits

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.step_admits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.step_admits

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.trace

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.accepted_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.accepted_invariant

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.accepted

/-- info: 'BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.reparse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.RegistrationAuthenticationReparse.reparse

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityHashPair

/-! Actual paired fingerprint continuations emit identical public template markers, even though their retained raw hash addresses differ. The private marker interpreter then performs the real canonical address with the same physical cache, input journal and exact draw reply. No physical address or canonical signature is an executable client input. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair
open BeaconcryptCore.Refinement
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeIdentityCensorOperational (parts)
open RegistrationNativeIdentitySigningPair (stripState)

private theorem leading_same (left right : registration.BeaconInitState) (same : stripState left = stripState right) :
    RegistrationNativeIdentityHashTemplate.leading left = RegistrationNativeIdentityHashTemplate.leading right := by
  simpa only [RegistrationNativeIdentityHashTemplate.leading, stripState] using
    congrArg RegistrationNativeIdentityHashTemplate.leading same

private theorem trailing_same (left right : registration.BeaconInitState) (message : Pqxdh.Bytes)
    (same : stripState left = stripState right) :
    RegistrationNativeIdentityHashTemplate.trailing left message = RegistrationNativeIdentityHashTemplate.trailing right message := by
  simpa only [RegistrationNativeIdentityHashTemplate.trailing, stripState] using
    congrArg (fun state => RegistrationNativeIdentityHashTemplate.trailing state message) same

/-- Actual canonical and placeholder source continuations determine the same framing outside the signature window. -/
theorem source (left right : registration.BeaconFingerprint) (same : stripState left.state = stripState right.state)
    (digest : Std.Array U8 64#usize) (canonical placeholder : Ed25519Signature) (message : Pqxdh.Bytes)
    (attachedLeft : absBytes left.state.one_time_key = canonical.toList ++ message)
    (attachedRight : absBytes right.state.one_time_key = placeholder.toList ++ message) :
    ∃ nextLeft requestLeft nextRight requestRight,
      left.resume (.Some digest) = .ok (.HashRequested nextLeft) ∧ nextLeft.request = .ok requestLeft ∧
      right.resume (.Some digest) = .ok (.HashRequested nextRight) ∧ nextRight.request = .ok requestRight ∧
      parts (RegistrationInputs.hashBytes requestLeft) = parts (RegistrationInputs.hashBytes requestRight) ∧
      RegistrationInputs.hashBytes requestLeft =
        (parts (RegistrationInputs.hashBytes requestRight)).1 ++ canonical.toList ++ (parts (RegistrationInputs.hashBytes requestRight)).2 := by
  obtain ⟨nextLeft, requestLeft, resumedLeft, requestedLeft, framedLeft, literalLeft⟩ :=
    RegistrationNativeIdentityPublicHashTemplate.source left digest canonical message attachedLeft
  obtain ⟨nextRight, requestRight, resumedRight, requestedRight, framedRight, _literalRight⟩ :=
    RegistrationNativeIdentityPublicHashTemplate.source right digest placeholder message attachedRight
  have framing : parts (RegistrationInputs.hashBytes requestLeft) = parts (RegistrationInputs.hashBytes requestRight) := by
    change RegistrationNativeIdentityPublicHashTemplate.parts _ = RegistrationNativeIdentityPublicHashTemplate.parts _
    rw [framedLeft, framedRight, leading_same left.state right.state same, trailing_same left.state right.state message same]
  change RegistrationInputs.hashBytes requestLeft =
    (parts (RegistrationInputs.hashBytes requestLeft)).1 ++ canonical.toList ++ (parts (RegistrationInputs.hashBytes requestLeft)).2 at literalLeft
  rw [framing] at literalLeft
  exact ⟨nextLeft, requestLeft, nextRight, requestRight, resumedLeft, requestedLeft, resumedRight, requestedRight, framing, literalLeft⟩

private theorem requested_route (pending : registration.BeaconInitHash) (request : registration.HashRequest)
    (requested : pending.request = .ok request) : RegistrationNativeIdentityHashRoute.route (RegistrationInputs.hashBytes request) = none := by
  obtain ⟨actual, same, _bytes, routed⟩ := RegistrationNativeIdentityHashRoute.transcript pending
  cases RustM.ok.inj (same.symm.trans requested)
  exact routed

/-- Both actual raw source hash requests compile to the same public marker tree on the selected internal suffix. -/
theorem marker (selected : Nat) (placeholder : Ed25519Signature)
    (left right : registration.BeaconInitHash) (requestLeft requestRight : registration.HashRequest)
    (requestedLeft : left.request = .ok requestLeft) (requestedRight : right.request = .ok requestRight)
    (framing : parts (RegistrationInputs.hashBytes requestLeft) = parts (RegistrationInputs.hashBytes requestRight))
    (before : RegistrationNativeIdentityCensorCompiler.Mode) (active : before.active = true) :
    (simulateQ (r := StateT RegistrationNativeIdentityCensorCompiler.Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec))
      (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
      (RegistrationNativePlatformIdentityCtxCompiler.Spec.query (.inr (RegistrationInputs.hashBytes requestLeft)) :
        OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec (CtxRomAuth.CtxDigest × Nat))).run before =
    (simulateQ (r := StateT RegistrationNativeIdentityCensorCompiler.Mode (OracleComp RegistrationNativeIdentityCensorOperational.Spec))
      (RegistrationNativeIdentityCensorOperational.implementation selected placeholder)
      (RegistrationNativePlatformIdentityCtxCompiler.Spec.query (.inr (RegistrationInputs.hashBytes requestRight)) :
        OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec (CtxRomAuth.CtxDigest × Nat))).run before := by
  have hash_run (bytes : Pqxdh.Bytes) :
      (RegistrationNativeIdentityCensorOperational.implementation selected placeholder (.inr bytes)).run before =
        (match (RegistrationNativeIdentityCensorCompiler.hashInput before bytes).input with
        | some _ => (RegistrationNativeIdentityCensorOperational.promote
            (RegistrationNativeIdentityCensorCompiler.implementation selected placeholder (.inr bytes))).run before
        | none => do
            let reply ← (RegistrationNativeIdentityCensorOperational.Spec.query
              (.inr (.template selected before.target (parts bytes).1 (parts bytes).2)) :
                OracleComp RegistrationNativeIdentityCensorOperational.Spec (CtxRomAuth.CtxDigest × Nat))
            pure (reply, before)) := rfl
  have routedLeft := requested_route left requestLeft requestedLeft
  have routedRight := requested_route right requestRight requestedRight
  rw [simulateQ_spec_query, simulateQ_spec_query, hash_run, hash_run]
  simp only [RegistrationNativeIdentityCensorCompiler.hashInput, active, ite_true, routedLeft, routedRight]
  rw [framing]

/-- The placeholder-side framing realizes the canonical-side actual physical hash, retaining the real queried input and literal draw cost. -/
theorem physical (canonical : Ed25519Signature) (requestLeft requestRight : registration.HashRequest)
    (literal : RegistrationInputs.hashBytes requestLeft =
      (parts (RegistrationInputs.hashBytes requestRight)).1 ++ canonical.toList ++ (parts (RegistrationInputs.hashBytes requestRight)).2)
    (before : RegistrationNativeIdentityCensorSource.State) (stored : before.canonical = some canonical) :
    (RegistrationNativeIdentityCensorSource.template (parts (RegistrationInputs.hashBytes requestRight)).1
      (parts (RegistrationInputs.hashBytes requestRight)).2).run before =
      (fun result => (result.1, { before with
        hash := result.2
        framing := some (parts (RegistrationInputs.hashBytes requestRight)) })) <$>
        (RegistrationNativePlatformCtxBackend.physical (RegistrationInputs.hashBytes requestLeft)).run before.hash := by
  rw [RegistrationNativeIdentityCensorSource.template_source _ _ canonical before stored, ← literal]

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair.marker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair.marker

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair.physical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorTemplatePair.physical

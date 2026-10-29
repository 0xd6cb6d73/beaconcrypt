-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemGetterKey
import BeaconcryptCore.Computational.RegistrationNativeKemAuthenticationReceipt

/-! The literal selected SDK accept exposes its publicly verified PQ coordinate. Authentication, parsed-attempt mutation, replay/reservation checks and retention remain in the actual source; no equality between session handles and attempt selectors is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemSdkGetterKey
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemParsedRouting (Spec source)
open RegistrationNativeKemCut (Cut scan)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret)
variable {ι KemSK Value Result : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def lower : QueryImpl (RegistrationNativeKemServerInterface.Spec n mlSource KemSK)
    (OracleComp (Spec n mlSource KemSK)) :=
  RegistrationNativeKemRouting.route true ∘ₛ RegistrationNativeKemFrontendInterface.lift

private theorem lower_ambient (query : (RegistrationNativeKemServerInterface.Ambient n mlSource).Domain) :
    lower (KemSK := KemSK) (.inl query) =
      ((Spec n mlSource KemSK).query (.inl (.inl (.inl query))) : OracleComp (Spec n mlSource KemSK) _) := rfl

private theorem agreement_program (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    simulateQ (lower (n := n) (mlSource := mlSource))
      (simulateQ (RegistrationNativeKemServerInterface.agreement setup checks) work) =
        simulateQ (RegistrationNativeKemGetterKey.node setup checks) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [lower, QueryImpl.apply_compose, QueryImpl.simulateQ_compose,
    RegistrationNativeKemGetterKey.node]

private theorem pending_bind {S : Type}
    (implementation : QueryImpl (Spec n mlSource KemSK) (StateT S ProbComp))
    (work : OracleComp (Spec n mlSource KemSK) Value)
    (following : Value → OracleComp (Spec n mlSource KemSK) Result) (key : MlKem768PublicKey)
    (first : ∀ actual resume before after,
      (Cut.pending actual resume, after) ∈ support ((scan implementation work 0).run before) → actual = key)
    (last : ∀ value, (following value).AllQueriesSatisfy
      (RegistrationNativeKemCutKey.hasKey (ambient := RegistrationNativeKemParsedRouting.Ambient n mlSource)
        (KemSK := KemSK) key))
    (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) Result)
    (before after : S)
    (supported : (Cut.pending actual resume, after) ∈ support
      ((scan implementation (work >>= following) 0).run before)) : actual = key := by
  rw [RegistrationNativeKemCutKey.scan_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨cut, reached⟩, prefixSupport, tail⟩ := supported
  cases cut with
  | complete value =>
      exact RegistrationNativeKemCutKey.pending_key implementation _ key
        (last value) actual resume reached after tail
  | pending requested next =>
      simp only [StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, Cut.pending.injEq] at tail
      exact tail.1.1.trans (first requested next before reached prefixSupport)

private def continued (result : RustM agreement.AgreementEffect) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.ServerComplete accepted) =>
      (RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.retain accepted))
  | .ok _ => pure (.ok none)

private theorem after_pending_key {S : Type}
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (implementation : QueryImpl (Spec n mlSource KemSK) (StateT S ProbComp))
    (authenticated : registration.AuthenticatedInit) (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)))
    (before after : S)
    (supported : (Cut.pending actual resume, after) ∈ support
      ((scan implementation (simulateQ lower
        (RegistrationNativeKemSdkCompiler.afterAuthentication setup checks authenticated)) 0).run before)) :
    actual = RegistrationRootInput.pqKey authenticated.registration.beacon_pq_public_key := by
  simp only [RegistrationNativeKemSdkCompiler.afterAuthentication, simulateQ_bind,
    RegistrationNativeKemServerInterface.get, simulateQ_spec_query, lower_ambient] at supported
  change (Cut.pending actual resume, after) ∈ support ((scan implementation
    (((Spec n mlSource KemSK).query (.inl (.inl (.inl .get))) :
      OracleComp (Spec n mlSource KemSK) (RegistrationNativeKemServerState.State n mlSource)) >>= _) 0).run before) at supported
  rw [RegistrationNativeKemCut.scan_other, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨state, reached⟩, _prefix, tail⟩ := supported
  split at tail
  · change (Cut.pending actual resume, after) ∈ support
      (pure (Cut.complete (.ok none), reached) : ProbComp (Cut (RegistrationNativeKemParsedRouting.Ambient n mlSource)
        KemSK (RustM (Option Nat)) × S)) at tail
    simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at tail
  · split at tail
    · rw [simulateQ_bind, agreement_program] at tail
      change (Cut.pending actual resume, after) ∈ support ((scan implementation
        (simulateQ (RegistrationNativeKemGetterKey.node setup checks)
          (RegistrationReplaySchedule.begin state.server.control authenticated state.server.consumed) >>=
            fun result => simulateQ lower (continued result)) 0).run reached) at tail
      apply pending_bind implementation _ _ _
        (fun requested next first last support => RegistrationNativeKemGetterKey.agreement_pending_key
          setup checks implementation state.server.control packet authenticated state.server.consumed
          requested next first last support) _ actual resume reached after tail
      intro value
      cases value with
      | fail error | div => exact allQueriesSatisfy_pure _ _
      | ok effect =>
          cases effect <;> simp only [continued, simulateQ_pure, simulateQ_spec_query, lower_ambient,
            allQueriesSatisfy_pure, allQueriesSatisfy_query_iff, RegistrationNativeKemCutKey.hasKey]
    · change (Cut.pending actual resume, after) ∈ support
        (pure (Cut.complete (.ok none), reached) : ProbComp (Cut (RegistrationNativeKemParsedRouting.Ambient n mlSource)
          KemSK (RustM (Option Nat)) × S)) at tail
      simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at tail

private theorem pure_pending_impossible {S : Type}
    (implementation : QueryImpl (Spec n mlSource KemSK) (StateT S ProbComp))
    (value : Value) (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) Value)
    (before after : S)
    (supported : (Cut.pending actual resume, after) ∈ support ((scan implementation (pure value) 0).run before)) : False := by
  change (Cut.pending actual resume, after) ∈ support
    (pure (Cut.complete value, before) : ProbComp (Cut (RegistrationNativeKemParsedRouting.Ambient n mlSource) KemSK Value × S)) at supported
  simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported

attribute [local irreducible] source

/-- The actual source authentication receipt fixes the key of every selected SDK accept suspension, including all failed and replayed branches. -/
theorem accept_pending_key (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (verified : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys)
    (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)))
    (before after : RegistrationNativeKemServerState.State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (supported : (Cut.pending actual resume, after) ∈ support
      ((scan (source setup checks wire route representation created credential)
        (simulateQ lower (RegistrationNativeKemServerInterface.accept setup checks packet)) 0).run before)) :
    actual = keys.2.pqKey := by
  simp only [RegistrationNativeKemServerInterface.accept, simulateQ_bind, simulateQ_spec_query,
    lower_ambient] at supported
  change (Cut.pending actual resume, after) ∈ support ((scan
    (source setup checks wire route representation created credential)
    (((Spec n mlSource KemSK).query (.inl (.inl (.inl (.authenticate packet)))) :
      OracleComp (Spec n mlSource KemSK) _) >>= _) 0).run before) at supported
  rw [RegistrationNativeKemCut.scan_other, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨checked, reached⟩, authenticatedSupport, tail⟩ := supported
  cases checked with
  | fail error | div => exact False.elim (pure_pending_impossible _ _ actual resume reached after tail)
  | ok result =>
      rcases result with ⟨events, result⟩
      cases result with
      | Accepted authenticated =>
          have receipt := RegistrationNativeKemAuthenticationReceipt.accepted setup checks wire route representation
            created credential packet events authenticated before reached authenticatedSupport
          rw [verified] at receipt
          have matching := congrArg (fun tuple => tuple.2.pqKey) (Option.some.inj receipt)
          exact (after_pending_key setup checks packet _ authenticated actual resume reached after tail).trans matching.symm
      | _ => exact False.elim (pure_pending_impossible _ _ actual resume reached after tail)

/-- Advancing the actual parsed-attempt counter before authentication preserves the same verified first-getter key. -/
theorem typed_pending_key (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (packet : registration.InitPacket)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (verified : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys)
    (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)))
    (before after : RegistrationNativeKemServerState.State n mlSource × PqxdhLiveKemBirth.Pool KemSK)
    (supported : (Cut.pending actual resume, after) ∈ support
      ((scan (source setup checks wire route representation created credential)
        (simulateQ lower (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) 0).run before)) :
    actual = keys.2.pqKey := by
  simp only [RegistrationNativeKemServerInterface.typedAccept, RegistrationNativeKemServerInterface.modify,
    RegistrationNativeKemServerInterface.get, RegistrationNativeKemServerInterface.put,
    simulateQ_bind, simulateQ_spec_query, lower_ambient, bind_assoc] at supported
  change (Cut.pending actual resume, after) ∈ support ((scan
    (source setup checks wire route representation created credential)
    (((Spec n mlSource KemSK).query (.inl (.inl (.inl .get))) :
      OracleComp (Spec n mlSource KemSK) _) >>= _) 0).run before) at supported
  rw [RegistrationNativeKemCut.scan_other, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨state, reached⟩, _lookedUp, tail⟩ := supported
  rw [RegistrationNativeKemCut.scan_other, StateT.run_bind, mem_support_bind_iff] at tail
  obtain ⟨⟨ignored, reached⟩, _stored, tail⟩ := tail
  exact accept_pending_key setup checks wire route representation created credential packet keys verified
    actual resume reached after tail

end BeaconcryptCore.Computational.RegistrationNativeKemSdkGetterKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSdkGetterKey.accept_pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSdkGetterKey.accept_pending_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemSdkGetterKey.typed_pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemSdkGetterKey.typed_pending_key

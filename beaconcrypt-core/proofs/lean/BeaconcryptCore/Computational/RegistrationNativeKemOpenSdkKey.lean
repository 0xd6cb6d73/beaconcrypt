-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOptionalKey
import BeaconcryptCore.Computational.RegistrationNativeKemOpenAuthentication

/-! The literal open SDK first getter is fixed by the original publicly verified PQ coordinate under the candidate provider. Actual ML/Ed authentication, replay checks, reservation, parsed mutation and all private source state remain in the operational prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkKey
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemParsedRouting (Spec)
open RegistrationNativeKemCut (Cut scan)
open RegistrationNativeKemOpenProvider (State)
open PqxdhKemIndCca
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

local notation "lower" => RegistrationNativeKemOpenFrame.lower (n := n) (mlSource := mlSource) (KemSK := KemSK) true

private theorem lower_ambient (query : (RegistrationNativeKemServerInterface.Ambient n mlSource).Domain) :
    lower (.inl query) = ((Spec n mlSource KemSK).query (.inl (.inl (.inl query))) : OracleComp (Spec n mlSource KemSK) _) := rfl

private theorem agreement_program (setup : Setup base KemSK) (checks : Checks)
    (work : OracleComp RegistrationAgreementExecutor.Spec Value) :
    simulateQ lower (simulateQ (RegistrationNativeKemServerInterface.agreement setup checks) work) =
      simulateQ (RegistrationNativeKemGetterKey.node setup checks) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [RegistrationNativeKemOpenFrame.lower, QueryImpl.apply_compose,
    QueryImpl.simulateQ_compose, RegistrationNativeKemGetterKey.node]

private def continued (result : RustM agreement.AgreementEffect) :
    OracleComp (RegistrationNativeKemServerInterface.Spec n mlSource KemSK) (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.ServerComplete accepted) => (RegistrationNativeKemServerInterface.Spec n mlSource KemSK).query (.inl (.retain accepted))
  | .ok _ => pure (.ok none)

private theorem pure_pending_impossible {S : Type}
    (implementation : QueryImpl (Spec n mlSource KemSK) (OptionT (StateT S ProbComp)))
    (value : Value) (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) Value)
    (before after : S)
    (supported : (some (Cut.pending actual resume), after) ∈ support
      (((scan implementation (pure value) 0).run).run before)) : False := by
  change (some (Cut.pending actual resume), after) ∈ support
    (pure (some (Cut.complete value), before) : ProbComp _) at supported
  simp only [mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq, reduceCtorEq, false_and] at supported

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (real : Bool)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real
attribute [local irreducible] RegistrationNativeKemOpenProvider.implementation

private theorem after_pending_key (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)))
    (before after : State n mlSource KemSK)
    (supported : (some (Cut.pending actual resume), after) ∈ support
      (((scan provider (simulateQ lower (RegistrationNativeKemSdkCompiler.afterAuthentication setup checks authenticated)) 0).run).run before)) :
    actual = RegistrationRootInput.pqKey authenticated.registration.beacon_pq_public_key := by
  simp only [RegistrationNativeKemSdkCompiler.afterAuthentication, simulateQ_bind,
    RegistrationNativeKemServerInterface.get, simulateQ_spec_query, lower_ambient] at supported
  change (some (Cut.pending actual resume), after) ∈ support
    (((scan provider (((Spec n mlSource KemSK).query (.inl (.inl (.inl .get))) : OracleComp (Spec n mlSource KemSK) _) >>= _) 0).run).run before) at supported
  rw [RegistrationNativeKemCut.scan_other, OptionT.run_bind, Option.elimM, StateT.run_bind,
    RegistrationNativeKemOpenProvider.get_run] at supported
  simp only [pure_bind, Option.elim_some] at supported
  split at supported
  · exact False.elim (pure_pending_impossible provider _ actual resume _ after supported)
  · split at supported
    · rw [simulateQ_bind, agreement_program] at supported
      change (some (Cut.pending actual resume), after) ∈ support
        (((scan provider (simulateQ (RegistrationNativeKemGetterKey.node setup checks)
          (RegistrationReplaySchedule.begin (RegistrationNativeKemServerState.mask before.1.1).server.control
            authenticated (RegistrationNativeKemServerState.mask before.1.1).server.consumed) >>=
              fun result => simulateQ lower (continued result)) 0).run).run _) at supported
      apply RegistrationNativeKemOptionalKey.pending_bind provider _ _ _
        (fun requested next first last support => RegistrationNativeKemOptionalKey.agreement_pending_key setup checks provider
          (RegistrationNativeKemServerState.mask before.1.1).server.control packet authenticated
          (RegistrationNativeKemServerState.mask before.1.1).server.consumed requested next first last support)
        _ actual resume _ after supported
      intro value
      cases value with
      | fail error | div => exact allQueriesSatisfy_pure _ _
      | ok effect =>
          cases effect <;> simp only [continued, simulateQ_pure, simulateQ_spec_query, lower_ambient,
            allQueriesSatisfy_pure, allQueriesSatisfy_query_iff, RegistrationNativeKemCutKey.hasKey]
    · exact False.elim (pure_pending_impossible provider _ actual resume _ after supported)

/-- Actual candidate-provider authentication fixes the literal SDK first-getter key to the original accepted public tuple. -/
theorem accept_pending_key (packet : registration.InitPacket)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (verified : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys)
    (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)))
    (before after : State n mlSource KemSK)
    (supported : (some (Cut.pending actual resume), after) ∈ support
      (((scan provider (simulateQ lower (RegistrationNativeKemServerInterface.accept setup checks packet)) 0).run).run before)) :
    actual = keys.2.pqKey := by
  simp only [RegistrationNativeKemServerInterface.accept, simulateQ_bind, simulateQ_spec_query, lower_ambient] at supported
  change (some (Cut.pending actual resume), after) ∈ support
    (((scan provider
      ((((Spec n mlSource KemSK).query (.inl (.inl (.inl (.authenticate packet))))) :
        OracleComp (Spec n mlSource KemSK) _) >>= _) 0).run).run before) at supported
  rw [RegistrationNativeKemCut.scan_other, OptionT.run_bind, Option.elimM, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨checked, reached⟩, authenticatedSupport, tail⟩ := supported
  cases checked with
  | none =>
      simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
        reduceCtorEq, false_and] at tail
  | some checked =>
      cases checked with
      | fail error | div => exact False.elim (pure_pending_impossible provider _ actual resume reached after tail)
      | ok result =>
          rcases result with ⟨events, result⟩
          cases result with
          | Accepted authenticated =>
              have receipt := RegistrationNativeKemOpenAuthentication.accepted setup checks wire route representation created credential
                selected pairs publicKey real packet events authenticated before reached authenticatedSupport
              rw [verified] at receipt
              have matching := congrArg (fun tuple => tuple.2.pqKey) (Option.some.inj receipt)
              exact (after_pending_key setup checks wire route representation created credential selected pairs publicKey real
                packet authenticated actual resume reached after tail).trans matching.symm
          | _ => exact False.elim (pure_pending_impossible provider _ actual resume reached after tail)

/-- The literal parsed-attempt mutation precedes the same open authenticated first-getter key without changing the verified tuple. -/
theorem typed_pending_key (packet : registration.InitPacket)
    (keys : PqxdhEd25519EufCma.Ed25519PublicKey × PqxdhEd25519EufCma.Phase1KeyTuple)
    (verified : PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate packet) = some keys)
    (actual : MlKem768PublicKey)
    (resume : (MlKem768Ciphertext × MlKemSharedSecret) → OracleComp (Spec n mlSource KemSK) (RustM (Option Nat)))
    (before after : State n mlSource KemSK)
    (supported : (some (Cut.pending actual resume), after) ∈ support
      (((scan provider (simulateQ lower (RegistrationNativeKemServerInterface.typedAccept setup checks packet)) 0).run).run before)) :
    actual = keys.2.pqKey := by
  simp only [RegistrationNativeKemServerInterface.typedAccept, RegistrationNativeKemServerInterface.modify,
    RegistrationNativeKemServerInterface.get, RegistrationNativeKemServerInterface.put,
    simulateQ_bind, simulateQ_spec_query, lower_ambient, bind_assoc] at supported
  change (some (Cut.pending actual resume), after) ∈ support
    (((scan provider (((Spec n mlSource KemSK).query (.inl (.inl (.inl .get))) :
      OracleComp (Spec n mlSource KemSK) _) >>= _) 0).run).run before) at supported
  rw [RegistrationNativeKemCut.scan_other, OptionT.run_bind, Option.elimM, StateT.run_bind,
    RegistrationNativeKemOpenProvider.get_run] at supported
  simp only [pure_bind, Option.elim_some] at supported
  rw [RegistrationNativeKemCut.scan_other, OptionT.run_bind, Option.elimM, StateT.run_bind,
    RegistrationNativeKemOpenProvider.put_run] at supported
  simp only [pure_bind, Option.elim_some] at supported
  exact accept_pending_key setup checks wire route representation created credential selected pairs publicKey real
    packet keys verified actual resume _ after supported

end BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkKey

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkKey.accept_pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkKey.accept_pending_key
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkKey.typed_pending_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenSdkKey.typed_pending_key

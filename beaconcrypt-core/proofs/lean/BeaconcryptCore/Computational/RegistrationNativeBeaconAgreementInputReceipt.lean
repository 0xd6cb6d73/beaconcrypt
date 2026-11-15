-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt
import BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt

/-! The actual lowered Beacon agreement retains its concrete collector and pre-erasure root input. Only the primitive root-query equation is used by the generic cut; the original native source proves that equation directly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationAgreementExecutor
variable {n : Nat} {ι KemSK Value Next Index : Type} {base : OracleSpec ι} {spec : OracleSpec Index}
variable {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationAgreementShared.rootResponse
theorem run {S : Type} (source : FixedHkdfSha512NoSaltSource)
    (implementation : QueryImpl RegistrationAgreementExecutor.Spec (StateT S ProbComp))
    (root : ∀ request before, (implementation (.root request)).run before =
      pure (.Some (RegistrationAgreementShared.rootResponse source.crypto request), before))
    (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (completed : agreement.BeaconAgreement) (before after : S)
    (supported : (.ok (.BeaconComplete completed), after) ∈ support
      ((simulateQ implementation
        (RegistrationAgreementExecutor.beacon authenticated)).run before)) :
    ∃ (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
      (atRoot : S) (original : pqxdh.BeaconRegistrationCandidate),
      (some input, atRoot) ∈ support ((simulateQ implementation
        (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
          (PqxdhBeaconPhase2Preparation.collect () false true () []))).run before) ∧
      RegistrationBeaconRootPreparation.Fields authenticated input ∧
      pqxdh.beacon_prepare_finish authenticated.control input.finishInputs = .ok (.Ok original) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ },
        authenticated.binding, ⟨RegistrationAgreementShared.rootResponse source.crypto
          ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩⟩, authenticated.packet.application⟩ ∧ after = atRoot := by
  rw [RegistrationBeaconAgreementRoot.beacon_normalized authenticated coherent] at supported
  simp only [RegistrationBeaconAgreementRoot.normalized, simulateQ_bind, StateT.run_bind,
    mem_support_bind_iff] at supported
  obtain ⟨⟨input, atRoot⟩, reachedPrefix, tail⟩ := supported
  cases input with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at tail
      cases tail.1
  | some input =>
      change (.ok (.BeaconComplete completed), after) ∈ support
        ((simulateQ implementation
          (RegistrationBeaconAgreementRoot.finish authenticated input)).run atRoot) at tail
      have openPrefix : some input ∈ support
          (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
            (PqxdhBeaconPhase2Preparation.collect () false true () [])) := by
        apply OracleComp.support_simulateQ_run'_subset
          implementation
          (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
            (PqxdhBeaconPhase2Preparation.collect () false true () [])) before
        rw [StateT.run'_eq, support_map]
        exact ⟨(some input, atRoot), reachedPrefix, rfl⟩
      have fields := RegistrationBeaconRootPreparation.collect_fields authenticated input openPrefix
      rw [RegistrationBeaconAgreementRoot.finish,
        RegistrationBeaconRootPreparation.finish_admission authenticated input fields] at tail
      obtain ⟨accepted, actual⟩ := BeaconcryptCore.PanicFreedom.beacon_prepare_finish_ok
        authenticated.control input.finishInputs
      rw [actual] at tail
      cases accepted with
      | Err error =>
          simp only [bind_tc_ok, continueWith, RegistrationBeaconAgreementRoot.rejected,
            drive, step, pure_bind, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at tail
          cases tail.1
      | Ok original =>
          simp only [bind_tc_ok, continueWith] at tail
          have requested : (⟨.Beacon original authenticated.binding authenticated.packet.application⟩ : agreement.RootKdfPending).request =
              .ok ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩ := by
            simp only [agreement.RootKdfPending.request, pqxdh.BeaconRegistrationCandidate.impl.root_key_input,
              pqxdh.RootKeyInput.as_bytes, bind_tc_ok]
          rw [RegistrationBeaconRelatedRoot.root_step_two _ _ requested] at tail
          simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
            root, pure_bind, StateT.run_pure,
            BeaconcryptCore.Refinement.KeyAgreement.root_success_refines, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq,
            agreement.AgreementEffect.BeaconComplete.injEq] at tail
          exact ⟨input, atRoot, original, reachedPrefix, fields, actual, tail.1, tail.2⟩


open RegistrationNativeBeaconFrontend (Owner)
open RegistrationNativeMldsaShared (Local lower)
open RegistrationNativeResponseAuthentication (lower_bind lower_pure)

private theorem lower_simulate (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (implementation : QueryImpl spec (RegistrationNativeBeaconFrontend.M n KemSK mlSource RegistrationServerRoleBackend.State))
    (work : OracleComp spec Value) :
    lower setup checks representation created (simulateQ implementation work) =
      simulateQ (fun query => lower setup checks representation created (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- The original native root callback returns the fixed source derivation and changes no local, World, owner or cache coordinate. -/
theorem root (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (request : agreement.RootKdfRequest) (before : Local n KemSK mlSource) :
    ((lower setup checks representation created (RegistrationNativeBeaconFrontend.agreement setup owner oneTime (.root request))).run before) =
      pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request), before) := by
  have pureRoot : RegistrationNativeBeaconFrontend.agreement (n := n) (Auxiliary := RegistrationServerRoleBackend.State) setup owner oneTime (.root request) =
      pure (.Some (RegistrationAgreementShared.rootResponse setup.source.crypto request)) := by
    simp only [RegistrationNativeBeaconFrontend.agreement, RegistrationWorldAgreement.recorded,
      RegistrationNativeBeaconFrontend.agreementCore, List.append_nil]
    rfl
  rw [pureRoot, lower_pure, StateT.run_pure]

/-- Actual native lowered agreement exposes its exact private inputs before root clearing; no partner, root-equality or whole-game simulation premise is supplied. -/
theorem local_cut (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (owner : Owner mlSource)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (coherent : authenticated.control.expected_server_binding = authenticated.binding.server_pin.binding)
    (completed : agreement.BeaconAgreement) (before after : Local n KemSK mlSource)
    (supported : (.ok (.BeaconComplete completed), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime) (RegistrationAgreementExecutor.beacon authenticated))).run before)) :
    ∃ (input : PqxdhBeaconPhase2Preparation.Inputs registration.AuthenticatedResponse)
      (atRoot : Local n KemSK mlSource) (original : pqxdh.BeaconRegistrationCandidate),
      (some input, atRoot) ∈ support ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.agreement setup owner oneTime)
          (simulateQ (RegistrationBeaconAgreementRoot.callbacks authenticated)
            (PqxdhBeaconPhase2Preparation.collect () false true () [])))).run before) ∧
      RegistrationBeaconRootPreparation.Fields authenticated input ∧
      pqxdh.beacon_prepare_finish authenticated.control input.finishInputs = .ok (.Ok original) ∧
      completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ },
        authenticated.binding, ⟨RegistrationAgreementShared.rootResponse setup.source.crypto
          ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩⟩, authenticated.packet.application⟩ ∧ after = atRoot := by
  rw [lower_simulate] at supported
  obtain ⟨input, atRoot, original, collected, fields, prepared, completedEq, afterEq⟩ :=
    run setup.source (fun query => lower setup checks representation created (RegistrationNativeBeaconFrontend.agreement setup owner oneTime query))
      (root setup checks representation created owner oneTime) authenticated coherent completed before after supported
  rw [← lower_simulate] at collected
  exact ⟨input, atRoot, original, collected, fields, prepared, completedEq, afterEq⟩

end BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt.run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt.root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt.root

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt.local_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBeaconAgreementInputReceipt.local_cut

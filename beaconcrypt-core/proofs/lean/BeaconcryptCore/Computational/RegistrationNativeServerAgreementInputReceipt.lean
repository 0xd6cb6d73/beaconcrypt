-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeAgreementInputReceipt
import BeaconcryptCore.Computational.RegistrationServerNativeSource

/-! A successful actual native Server agreement supplies the original replay-fresh source input receipt. Projection forgets only agreement instrumentation; it retains the actual role state and the shared cache. No matching Beacon or root-equality premise is added. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

namespace BeaconcryptCore.Computational.RegistrationNativeServerAgreementInputReceipt

open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhBeaconPhase2Preparation (Word32)
open RegistrationWorldAgreement (project)

variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}

attribute [local irreducible] RegistrationAgreementShared.rootResponse

/-- The native replay lookup and every native source callback are retained until the private collector and root candidate are extracted. -/
theorem agree (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (completed : agreement.ServerAgreement)
    (before after : RegistrationServerFrontendCompiler.State n)
    (supported : (.ok (.ServerComplete completed), after) ∈ support
      ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)) :
    before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false ∧
      ∃ (input : PqxdhServerRootPreparation.Inputs registration.InitPacket Unit Word32)
        (atRoot : RawCtxSharedPrimitive.SharedState RegistrationServerRoleBackend.State)
        (next : pqxdh.ServerState) (original : pqxdh.PendingServerRegistration),
        (some input, atRoot) ∈ support ((simulateQ (RegistrationAgreementShared.implementation setup.source
          (RegistrationServerRoleBackend.native setup checks representation created.seed))
            (simulateQ RegistrationAgreementRoot.callbacks
              (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated)))).run
                (project before.world)) ∧
        input.verified = RegistrationRootInput.verified packet authenticated ∧
        PqxdhServerRelatedRootInput.accept before.control authenticated.binding.server_pin.binding input = .ok (.Ok (next, original)) ∧
        completed = ⟨{ original with root_key_input := ⟨Array.repeat 192#usize 0#u8⟩ },
          authenticated.binding, ⟨RegistrationAgreementShared.rootResponse setup.source.crypto
            ⟨original.root_key_input.bytes, pqxdh.PQXDH_INFO⟩⟩⟩ ∧
        project after.world = atRoot ∧
        next = before.control ∧
        pqxdh.build_root_key_input (PqxdhServerRelatedRootInput.secrets input) = .ok (.Ok original.root_key_input) ∧
        absBytes original.root_key_input.bytes = Pqxdh.pqxdhIKM
          (absBytes input.first) (absBytes input.second) (absBytes input.third)
          (absBytes input.fourth) (absBytes input.kem) := by
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨inner, executed, equal⟩ := supported
  have valueEq : inner.1 = .ok (.ServerComplete completed) := congrArg Prod.fst equal
  have worldEq : inner.2 = after.world := congrArg (fun result => result.2.world) equal
  have native : (.ok (.ServerComplete completed), inner.2) ∈ support
      ((simulateQ (RegistrationWorldAgreement.agreement setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed))
          (RegistrationReplaySchedule.begin before.control authenticated before.consumed)).run before.world) := by
    simpa only [← valueEq, Prod.mk.eta, StateT.run] using executed
  rw [RegistrationReplaySchedule.begin_eq] at native
  by_cases consumed : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [consumed, ite_true, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at native
    cases native.1
  · have fresh : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false :=
      Bool.eq_false_iff.mpr consumed
    simp only [fresh, Bool.false_eq_true, ite_false] at native
    have actualSource : (.ok (.ServerComplete completed), project inner.2) ∈ support
        ((simulateQ (RegistrationAgreementShared.implementation setup.source
          (RegistrationServerRoleBackend.native setup checks representation created.seed))
            (RegistrationAgreementExecutor.server before.control .Fresh authenticated)).run (project before.world)) := by
      rw [← RegistrationWorldAgreement.agreement_program_project setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed)
          (RegistrationAgreementExecutor.server before.control .Fresh authenticated) before.world,
        support_map]
      exact Set.mem_image_of_mem (Prod.map id project) native
    obtain ⟨input, atRoot, next, original, collected, fields, accepted, completedEq, atRootEq⟩ :=
      RegistrationNativeAgreementInputReceipt.server setup.source
        (RegistrationServerRoleBackend.native setup checks representation created.seed)
        before.control packet authenticated completed (project before.world) (project inner.2) actualSource
    have built := RegistrationNativeAgreementInputReceipt.server_built before.control next
      authenticated.binding.server_pin.binding input original accepted
    have bytes := RegistrationNativeAgreementInputReceipt.server_bytes before.control next
      authenticated.binding.server_pin.binding input original accepted
    exact ⟨fresh, input, atRoot, next, original, collected, fields, accepted, completedEq,
      (congrArg project worldEq).symm.trans atRootEq, built.1, built.2, bytes⟩

end BeaconcryptCore.Computational.RegistrationNativeServerAgreementInputReceipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerAgreementInputReceipt.agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerAgreementInputReceipt.agree

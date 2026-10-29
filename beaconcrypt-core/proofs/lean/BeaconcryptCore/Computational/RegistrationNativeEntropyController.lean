-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeEntropySecrecy

/-! Exact original secrecy-controller transport, with the original private sampler retained below both interfaces. No test bit or fresh message is supplied by an adversary or resampled by the adapter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeEntropyController
open PqxdhDeploymentSecrecy (Ledger)
variable {Reader Response : Type}

/-- The entire original secrecy controller commutes with complete native transcript restoration and the actual ordinary transport. -/
theorem controller (crypto : Pqxdh.Crypto)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (secrecy : PqxdhDeploymentInterface.Secrecy)
    (before : Ledger) :
    (fun result => (result.1, RegistrationNativeEntropyRestore.ledger result.2)) <$>
        ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds (.inr secrecy)).run before) =
      simulateQ RegistrationNativeEntropyCore.compiler
        ((RegistrationNativeLedger.handler crypto codec serverKid bounds (.inr secrecy)).run
          (RegistrationNativeEntropyRestore.ledger before)) := by
  classical
  rw [RegistrationNativeLedger.query_secrecy, simulateQ_map,
    RegistrationNativeEntropySecrecy.legacy_secrecy]
  have test : (RegistrationNativeEntropyRestore.ledger before).ledger.test = before.test := rfl
  have fresh : (RegistrationNativeEntropyRestore.ledger before).ledger.fresh = before.fresh := rfl
  have same : ∀ first second,
      PqxdhDeploymentSecrecy.SameSession crypto codec serverKid
          (RegistrationNativeEntropyRestore.ledger before).ledger.transcript first second ↔
        PqxdhDeploymentSecrecy.SameSession crypto codec serverKid before.transcript first second := by
    intro first second
    rw [RegistrationNativeEntropyRestore.ledger_transcript]
    exact RegistrationNativeEntropyDesignation.sameSession_strip crypto codec serverKid before.transcript first second
  cases secrecy with
  | test handle left right =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run, test]
      by_cases admissible : PqxdhDeploymentSecrecy.Admissible left right
      · simp only [admissible, ite_true]
        cases selected : before.test with
        | none =>
            simp only [map_bind, map_pure]
            apply bind_congr
            intro bit
            apply bind_congr
            intro reply
            exact congrArg pure (congrArg (Prod.mk reply)
              (RegistrationNativeEntropySecrecy.restore_secrecy before (.test handle left right)
                reply (some ⟨bit, handle, 1⟩) before.fresh))
        | some selectedTest =>
            simp only [same]
            by_cases related : PqxdhDeploymentSecrecy.SameSession crypto codec serverKid
                before.transcript selectedTest.first handle
            · simp only [related, ite_true, map_bind, map_pure]
              apply bind_congr
              intro reply
              exact congrArg pure (congrArg (Prod.mk reply)
                (RegistrationNativeEntropySecrecy.restore_secrecy before (.test handle left right)
                  reply (some { selectedTest with count := selectedTest.count + 1 }) before.fresh))
            · simp only [related, ite_false, map_pure]
              exact congrArg pure (congrArg (Prod.mk none)
                (RegistrationNativeEntropySecrecy.restore_secrecy before (.test handle left right)
                  none before.test before.fresh))
      · simp only [admissible, ite_false, map_pure]
        exact congrArg pure (congrArg (Prod.mk none)
          (RegistrationNativeEntropySecrecy.restore_secrecy before (.test handle left right)
            none before.test before.fresh))
  | fresh handle length =>
      simp only [PqxdhDeploymentSecrecy.ledgerImpl, StateT.run]
      by_cases admitted : bounds.min ≤ length ∧ length ≤ bounds.max
      · simp only [admitted, true_and, ite_true, map_bind, map_pure]
        apply bind_congr
        intro message
        apply bind_congr
        intro reply
        have restored := RegistrationNativeEntropySecrecy.restore_secrecy before (.fresh handle length)
          reply before.test (before.fresh ++ [⟨handle, message, reply⟩])
        simpa only [PqxdhDeploymentSecrecy.Ledger.record, test, fresh] using
          congrArg pure (congrArg (Prod.mk reply) restored)
      · simp only [admitted, ite_false, map_pure]
        exact congrArg pure (congrArg (Prod.mk none)
          (RegistrationNativeEntropySecrecy.restore_secrecy before (.fresh handle length)
            none before.test before.fresh))

end BeaconcryptCore.Computational.RegistrationNativeEntropyController

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeEntropyController.controller' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeEntropyController.controller

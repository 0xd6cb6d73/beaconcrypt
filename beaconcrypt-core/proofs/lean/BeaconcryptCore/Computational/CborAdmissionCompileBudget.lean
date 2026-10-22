-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborAdmissionCompiler
import BeaconcryptCore.Computational.CborAdmissionServerCompiler
import BeaconcryptCore.Computational.CborAdmissionCachedBudget
import BeaconcryptCore.Computational.PqxdhDeploymentCompileSecrecy

/-! CBOR admission preserves the existing twelve deployment-command cost classes and fourteen source14 query kinds. Prefetching and caching issue at most one addressed kernel read, while admitted local records issue no second read and at most one commitment hash. The weighted adversary budget therefore stays unchanged, and every compiled adaptive program issues zero identity, KEM, prekey or one-time field reads without needing a client budget or simulation invariant. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborAdmissionCompileBudget
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRegistrationJointRevealCosts (SourceKind sourceKind)
open PqxdhDeploymentCompileBudget (unit commandKind cost)
open CborAdmissionCompiler (Local compileImpl compile)
variable {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}

theorem beacon_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (kind : SourceKind) (index : Nat) (plaintext : Pqxdh.Bytes) (memory : Local) :
    ((CborAdmissionCompiler.beaconSend setup codec index plaintext).run memory).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind)
      (unit kind (.inr 4) + unit kind (.inl 7)) := by
  change (CborAdmissionCompiler.beaconSend setup codec index plaintext memory).IsQueryBoundP _ _
  unfold CborAdmissionCompiler.beaconSend
  by_cases inside : index < memory.copies.log.owners.length
  case pos =>
    rw [ite_eq_left inside]
    refine isQueryBoundP_bind (PqxdhDeploymentCompileBudget.ownerKernel_bound kind memory.copies index)
      fun kernel _ => ?_
    cases kernel
    case some current member =>
      cases viewFound : PqxdhDeploymentCompile.ownerView codec memory.copies.log index
      case some view =>
        dsimp only
        split_ifs
        case pos =>
          rw [isQueryBoundP_map_iff]
          exact CborAdmissionCachedBudget.beacon_cached setup codec kind index (.inl plaintext)
            { memory.copies with owners := Function.update memory.copies.owners index (some current) }
            current (Function.update_self ..)
        case neg => trivial
      case none => trivial
    case none => trivial
  case neg =>
    rw [ite_eq_right inside]
    trivial

theorem step_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (kind : SourceKind)
    (query : PqxdhDeploymentInterface.Spec.Domain) (memory : Local) :
    ((compileImpl setup codec route query).run memory).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = kind) (cost kind (commandKind query)) := by
  cases query
  case inr command =>
    cases command
    case build session payload =>
      simpa only [compileImpl, CborAdmissionCompiler.build, StateT.run, isQueryBoundP_map_iff, commandKind] using
        PqxdhDeploymentCompileBudget.step_bound setup codec route kind
          (.inr (.build session (CborAdmissionCompiler.buildPayload memory.lastId payload))) memory.copies
    case serverSend keyId plaintext =>
      simpa [compileImpl, commandKind, cost] using
        CborAdmissionServerCompiler.source_bound setup codec route kind keyId plaintext memory
    case beaconSend index plaintext =>
      simpa [compileImpl, commandKind, cost] using beacon_bound setup codec kind index plaintext memory
    all_goals simp only [compileImpl, CborAdmissionCompiler.liftExisting, StateT.run, isQueryBoundP_map_iff]
    all_goals exact PqxdhDeploymentCompileBudget.step_bound setup codec route kind _ memory.copies
  case inl coin =>
    simpa only [compileImpl, CborAdmissionCompiler.liftExisting, StateT.run, isQueryBoundP_map_iff] using
      PqxdhDeploymentCompileBudget.step_bound setup codec route kind (.inl coin) memory.copies

theorem compile_bound (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (adversary : OracleComp PqxdhDeploymentInterface.Spec X)
    (budget : Fin 12 → Nat)
    (bounded : ∀ command, adversary.IsQueryBoundP (fun query => commandKind query = command) (budget command))
    (kind : SourceKind) :
    (compile setup codec route adversary).IsQueryBoundP (fun request => sourceKind (KemSK := KemSK) request = kind)
      (∑ command, cost kind command * budget command) :=
  FinitePartitionQueryBounds.weighted_bound commandKind (cost kind) budget (compileImpl setup codec route)
    (fun request => sourceKind (KemSK := KemSK) request = kind) adversary bounded
    (fun query memory => step_bound setup codec route kind query memory) (Local.empty setup.serverKeyId)

theorem compile_unread (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (adversary : OracleComp PqxdhDeploymentInterface.Spec X)
    (field : Fin 5) (notKernel : field ≠ 4) :
    (compile setup codec route adversary).IsQueryBoundP
      (fun request => sourceKind (KemSK := KemSK) request = .inr field) 0 := by
  have zero : ∀ core, cost (.inr field) core = 0 := fun core => by
    fin_cases core <;> simp [cost, unit, notKernel]
  exact PqxdhDeploymentCompileSecrecy.simulate_zero (compileImpl setup codec route) _
    (fun query memory => by simpa only [zero] using step_bound setup codec route (.inr field) query memory)
    adversary (Local.empty setup.serverKeyId)

end BeaconcryptCore.Computational.CborAdmissionCompileBudget

/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileBudget.beacon_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileBudget.beacon_bound
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileBudget.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileBudget.step_bound
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileBudget.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileBudget.compile_bound
/-- info: 'BeaconcryptCore.Computational.CborAdmissionCompileBudget.compile_unread' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborAdmissionCompileBudget.compile_unread

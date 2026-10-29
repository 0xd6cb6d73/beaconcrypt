-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3Common

/-! The complete actual Server common stage has the same semantic receipt/World outcome when its canonical known kernel is replaced by an unused cached hidden reference. The actual record, hash, ML signing, encoding and publication prefix supplies its own supported kernel and preserves the required cache/use receipts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3CommonServer
open RegistrationNativeG3Common (State handler publication view)
variable {n : Nat} {Encoded : Type}

/-- The actual known and hidden whole Server stages agree on complete results, signing receipts and every semantic World coordinate. -/
theorem stage (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (control : pqxdh.ServerState) (slot : PqxdhRecordLiftInterface.Slot n)
    (initial : RegistrationBoundKeySchedule.PublicInitial) (material : PqxdhDeploymentHiddenLayout.Material)
    (seed : PqxdhRecordLiftSeed.Seed) (before : State n)
    (cached : before.2.seeds.1 slot = some seed) (unused : before.2.used slot .server = false) :
    Prod.map id view <$>
      (simulateQ (handler source writer sign) (RegistrationNativePairedServerService.knownStage encode control initial
        (PqxdhDeploymentHiddenLayout.joinOutput material seed))).run before =
      Prod.map id view <$>
        (simulateQ (handler source writer sign) (RegistrationHiddenInstall.stage encode control slot initial
          (PqxdhDeploymentHiddenLayout.joinOutput material seed))).run before := by
  simp only [RegistrationNativePairedServerService.knownStage, RegistrationHiddenInstall.stage, simulateQ_bind,
    RegistrationNativeG3Common.publication_lift, StateT.run_bind, map_bind]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro reached supported
  have keeps := RegistrationNativeG3Common.publication_program_keeps source writer sign _ before reached supported
  have original : reached.1 ∈ support (RegistrationBoundPublication.program encode initial
      (PqxdhDeploymentHiddenLayout.joinOutput material seed)) := by
    apply support_simulateQ_run'_subset (publication source writer sign) _ before
    rw [StateT.run'_eq, support_map]
    exact ⟨reached, supported, rfl⟩
  have cachedAfter : reached.2.2.seeds.1 slot = some seed := by rw [keeps.1]; exact cached
  have unusedAfter : reached.2.2.used slot .server = false := by rw [keeps.2]; exact unused
  have suffix := RegistrationNativeG3ServerInsertion.after_publication encode control slot initial material seed
    reached.1 original reached.2.2 cachedAfter unusedAfter
  have retained := congrArg (fun distribution => (fun result => (result.1, (reached.2.1, result.2))) <$> distribution) suffix
  simpa only [RegistrationNativeG3Common.effect_lift, RegistrationNativeG3Common.effect_program,
    Functor.map_map, Prod.map_def, id_eq, view] using retained

end BeaconcryptCore.Computational.RegistrationNativeG3CommonServer
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3CommonServer.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3CommonServer.stage

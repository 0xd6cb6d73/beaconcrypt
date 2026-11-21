-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3SelectiveService

/-! The direct native flag/108-key interpreter is the known materialization of the actual selective hidden service. Both use the identical full-byte allocator and persistent nonselected cache. The only local capacity condition is at a genuinely fresh selected address; the existing original-ledger prefix bound supplies it in complete executions. No seed or World is stored in the key state. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource
open PqxdhRecordLiftInterface (Slot EnvEffects)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeSelectiveHiddenService (State selected known)
open RegistrationNativeG3SelectiveService (complete fixedKeys direct count)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativePairedChoice (Choice)
open RegistrationNativeRelatedFamily (Message)
variable {n : Nat} {Value : Type}
attribute [local irreducible] PqxdhServerAuthKeySchedule.fromRoot RegistrationNativeRelatedRoot.nativeRoot

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = (fun result => (observe result.1, result.2)) <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]

/-- The actual nonselected cache keeps the identical full108 reply and complete state under fixed material44 completion. -/
theorem known_complete (materials : Slot n → Material) (bytes : Pqxdh.Bytes) (before : State n) :
    Prod.map id (complete materials) <$> (known bytes).run before = (known bytes).run (complete materials before) := by
  cases found : before.2 bytes <;>
    simp only [known, StateT.run, complete, found, map_pure, Functor.map_map, Prod.map_def, id_eq]

/-- Successful descriptor preparation changes precisely the same original flag and leaves both private caches and allocator fields literal. -/
theorem prepare_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : Seeds n)
    (message : Message) (before : State n) :
    Prod.map id (complete materials) <$> (direct source input inside candidate materials seeds (.inr (.prepare message))).run before =
      (RegistrationNativeSelectiveHiddenService.prepare input message).run (complete materials before) := by
  simp only [direct, count, RegistrationNativeG3KeyService.direct, StateT.run, simulateQ_pure,
    map_pure, complete, RegistrationNativeSelectiveHiddenService.prepare, RegistrationNativeSelectiveHiddenService.onHidden,
    RegistrationNativeHiddenService.prepare, Prod.map_def, id_eq] <;> rfl

/-- The actual direct108 material demand equals known materialization of selective44 demand, with full flags, allocations, counters and nonselected cache retained. Capacity is required only if this exact selected address is absent. -/
theorem demand_source (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (materials : Slot n → Material) (seeds : Seeds n)
    (message : Message) (before : State n)
    (room : ∀ bytes, input message = some bytes → selected inside candidate bytes = true →
      before.1.slots bytes = none → before.1.next < n) :
    (fun result => (result.1.map Choice.known, complete materials result.2)) <$>
      (direct source input inside candidate materials seeds (.inr (.demand message))).run before =
      (Option.map (RegistrationNativeG3MaterializedFrontend.materialize seeds) <$>
        RegistrationNativeSelectiveHiddenService.demand source input inside candidate message).run (complete materials before) := by
  cases prepared : before.1.prepared message with
  | false =>
      simp [direct, count, RegistrationNativeG3KeyService.direct, prepared, state_map_apply,
        RegistrationNativeSelectiveHiddenService.demand, RegistrationNativeSelectiveHiddenService.onHidden,
        RegistrationNativeHiddenService.demand, complete, StateT.run, simulateQ_pure] <;> rfl
  | true =>
      cases realized : input message with
      | none =>
          simp [direct, count, RegistrationNativeG3KeyService.direct, prepared, realized, state_map_apply,
            RegistrationNativeSelectiveHiddenService.demand, RegistrationNativeSelectiveHiddenService.onHidden,
            RegistrationNativeHiddenService.demand, complete, StateT.run, simulateQ_pure] <;> rfl
      | some bytes =>
          cases protectedInput : inside bytes with
          | false =>
              simp [direct, count, RegistrationNativeG3KeyService.direct, prepared, realized, protectedInput,
                selected, state_map_apply, RegistrationNativeSelectiveHiddenService.demand,
                RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
                complete, StateT.run, simulateQ_pure, RegistrationNativeG3MaterializedFrontend.materialize] <;> rfl
          | true =>
              cases chosen : selected inside candidate bytes with
              | false =>
                  cases found : before.2 bytes <;>
                    simp [direct, count, RegistrationNativeG3KeyService.direct, prepared, realized, protectedInput,
                      chosen, fixedKeys, known, found, state_map_apply, RegistrationNativeSelectiveHiddenService.demand,
                      complete, StateT.run, simulateQ_map, Functor.map_map, RegistrationNativeG3MaterializedFrontend.materialize] <;> rfl
              | true =>
                  cases found : before.1.slots bytes with
                  | some slot =>
                      simp [direct, count, RegistrationNativeG3KeyService.direct, prepared, realized, protectedInput,
                        chosen, fixedKeys, found, state_map_apply, RegistrationNativeSelectiveHiddenService.demand,
                        RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
                        RegistrationNativeHiddenService.reserve, RegistrationNativeHiddenService.material,
                        complete, StateT.run, simulateQ_map, RegistrationNativeG3MaterializedFrontend.materialize] <;> rfl
                  | none =>
                      have affordable := room bytes realized chosen found
                      simp [direct, count, RegistrationNativeG3KeyService.direct, prepared, realized, protectedInput,
                        chosen, fixedKeys, found, affordable, state_map_apply, RegistrationNativeSelectiveHiddenService.demand,
                        RegistrationNativeSelectiveHiddenService.onHidden, RegistrationNativeHiddenService.demand,
                        RegistrationNativeHiddenService.reserve, RegistrationNativeHiddenService.material,
                        complete, StateT.run, simulateQ_map, RegistrationNativeG3MaterializedFrontend.materialize] <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource.known_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource.known_complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource.prepare_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource.prepare_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource.demand_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3SelectiveServiceSource.demand_source

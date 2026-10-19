import BeaconcryptCore.Computational.PqxdhInitialPendingBuilder
import BeaconcryptCore.Computational.PqxdhInitialBeaconAmbient

/-!
The complete first-send builder commutes with the same shared/private/cache lift as later source operations. Identity checks, allocation, the exact first send, erasure, serialization and publication retain their source order and all optional or Rust failure branches. The result is a literal program equality, with no security or free-ambient-work premise.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient
open PqxdhInitialBeaconAmbient PqxdhInitialGenericBuilder
variable {Kernel M P A N C : Type}

/-- Every source first-send publication callback retains all original shared effects while preserving the extra private state and cache. -/
theorem after_lift
    (calls : RawCtxChainOwner.Calls Kernel (Base A))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : Kernel) (metadata : P)
    (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    PqxdhInitialGenericPublication.afterInitialization (liftCalls (N := N) (C := C) calls)
      (fun query => PqxdhInitialBeaconAmbient.lift (aux query)) candidate authenticated kernel metadata state =
      PqxdhInitialBeaconAmbient.lift (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state) := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, lift_bind, liftCalls]
  apply bind_congr
  rintro ⟨advanced, encrypted⟩
  apply bind_congr
  intro erased
  cases encrypted with
  | none => rfl
  | some encrypted =>
      simp only [lift_bind]
      apply bind_congr
      intro serialized
      cases serialized <;> rfl

/-- All actual admission gates and the first-send tail commute with the same complete ambient lift. -/
theorem candidate_lift
    (calls : RawCtxChainOwner.Calls Kernel (Base A))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (initial : RustM Kernel) (pending : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    candidate (liftCalls (N := N) (C := C) calls) (fun query => PqxdhInitialBeaconAmbient.lift (aux query)) initial pending data metadata state =
      PqxdhInitialBeaconAmbient.lift (candidate calls aux initial pending data metadata state) := by
  simp only [candidate, lift_bind]
  apply bind_congr
  intro valid
  cases valid
  · rfl
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false, lift_bind]
    apply bind_congr
    intro reserved
    cases reserved
    · rfl
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      cases initial with
      | fail error => rfl
      | div => rfl
      | ok kernel =>
          simp only [continueRust]
          split
          · rfl
          · split
            · simp only [lift_bind]
              apply bind_congr
              intro allocated
              cases allocated
              · rfl
              · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                cases binding : pending.key_id_binding with
                | fail error => rfl
                | div => rfl
                | ok binding => simp only [lift_map, after_lift]
            · rfl

/-- The complete original Ready builder executes with the identical shared state and source work under the current protocol's extra private state and initializer cache. -/
theorem ready_lift
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (calls : RawCtxChainOwner.Calls Kernel (Base A))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (initial : RustM Kernel) (binding : pqxdh.ServerBinding) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    readyBuild source (liftCalls (N := N) (C := C) calls) (fun query => PqxdhInitialBeaconAmbient.lift (aux query))
      initial binding ready metadata state =
      PqxdhInitialBeaconAmbient.lift (readyBuild source calls aux initial binding ready metadata state) := by
  unfold readyBuild usedBuild
  cases next : pqxdh.server_next_key_id state.control with
  | fail error => rfl
  | div => rfl
  | ok value =>
      cases value with
      | Err error => rfl
      | Ok key =>
          simp only [continueRust]
          cases preparation : PqxdhRegistrationInputs.prepare state.control
            (PqxdhAcceptedRegistration.usedReady source.crypto binding ready)
            ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => rfl
          | div => rfl
          | ok result =>
              cases result with
              | Err error => rfl
              | Ok candidate => exact candidate_lift calls aux initial candidate ready.application metadata state

end BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient.after_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient.after_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient.candidate_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient.candidate_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient.ready_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient.ready_lift

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate
import BeaconcryptCore.Computational.RawCtxSourceSeal

/-! The actual ordinary seal programme reaches its writer last. Moving the capacity-only reservation after the complete private seal retains every AEAD/hash/writer reply and poststate, including optional failure. No functional or security law for those primitive replies is required by this operational transport. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySealGate
open RegistrationNativePlatformOrdinarySendGate (liftState)
open RegistrationNativePlatformOrdinaryGate (gate)
variable {S Platform E A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

omit [LawfulMonad m] in
private theorem run_liftState (work : StateT S m A) (before : S) :
    (liftState (Platform := Platform) work).run before = StateT.lift (work.run before) := rfl

def implementation (native : QueryImpl RawCtxSourceSeal.SealSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) :
    QueryImpl RawCtxSourceSeal.SealSpec (StateT S (StateT Platform m))
  | .inl input => liftState (native (.inl input))
  | .inr (.inl bytes) => liftState (native (.inr (.inl bytes)))
  | .inr (.inr frame) => do
      let output ← liftState (native (.inr (.inr frame)))
      StateT.lift (gate reserve List.length output)

/-- Source AEAD and commitment failures stop before reservation; a reached writer is followed by precisely its public output-length gate. -/
theorem program (native : QueryImpl RawCtxSourceSeal.SealSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) (input : RawCtxSourceSend.SealInput) :
    simulateQ (implementation native reserve) (RawCtxSourceSeal.sealInput input) = (do
      let output ← liftState (simulateQ native (RawCtxSourceSeal.sealInput input))
      StateT.lift (gate reserve List.length output) : StateT S (StateT Platform m) _) := by
  ext before previous
  simp only [RawCtxSourceSeal.sealInput, simulateQ_bind, simulateQ_spec_query,
    implementation, run_liftState, StateT.run_bind, StateT.run_lift, StateT.run_pure,
    bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨sealed, afterAead⟩
  cases sealed with
  | none => simp only [simulateQ_pure, StateT.run_pure, gate, pure_bind]
  | some pair =>
      rcases pair with ⟨body, tag⟩
      by_cases associated : input.context.associatedData.length = 281
      · by_cases sized : tag.length = 16
        · simp only [associated, sized, ite_true, simulateQ_bind, simulateQ_spec_query, implementation,
            run_liftState, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
          apply bind_congr
          rintro ⟨digest, afterHash⟩
          cases digest with
          | none => simp only [simulateQ_pure, gate, StateT.run_pure, pure_bind]
          | some commitment =>
              simp only [simulateQ_spec_query, implementation, run_liftState, StateT.run_bind,
                StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
              rfl
        · simp only [associated, sized, ite_true, ite_false, simulateQ_pure, gate,
            StateT.run_pure, pure_bind]
      · simp only [associated, ite_false, simulateQ_pure, gate, StateT.run_pure, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySealGate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySealGate.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySealGate.program

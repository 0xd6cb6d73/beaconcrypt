-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate
import BeaconcryptCore.Computational.RawCtxSourceSend

/-! A terminal public reservation gate may follow the complete actual source send while retaining its exact advanced kernel and private primitive state. Empty, exhausted and optional sealing-failure paths invoke no reservation. Rejected publication retains the advanced send state, as the source controller requires. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate
open RawCtxSourceSend
open RegistrationNativePlatformOrdinaryGate (gate)
variable {S Platform E A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Lift the actual primitive state, retaining the common external state. -/
def liftState (work : StateT S m A) : StateT S (StateT Platform m) A := fun before => StateT.lift (work.run before)

omit [LawfulMonad m] in
private theorem run_liftState (work : StateT S m A) (before : S) :
    (liftState (Platform := Platform) work).run before = StateT.lift (work.run before) := rfl

private theorem liftState_pure (value : A) :
    liftState (S := S) (Platform := Platform) (pure value : StateT S m A) = pure value := by
  ext before previous
  simp only [run_liftState, StateT.run_lift, StateT.run_pure, pure_bind]

private theorem liftState_bind (work : StateT S m A) (next : A → StateT S m B) :
    liftState (Platform := Platform) (work >>= next) = (liftState work >>= fun value => liftState (next value)) := by
  ext before previous
  simp only [StateT.run_bind, run_liftState, StateT.run_lift, bind_assoc, pure_bind]

def implementation (native : QueryImpl PrimitiveSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E)) : QueryImpl PrimitiveSpec (StateT S (StateT Platform m))
  | .inl request => liftState (native (.inl request))
  | .inr input => do
      let output ← liftState (native (.inr input))
      StateT.lift (gate reserve List.length output)

/-- Gating follows the complete actual source send; its advanced kernel and every primitive state update are retained when publication fails. -/
theorem program (native : QueryImpl PrimitiveSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E))
    (start : ratchet.concrete.SendStart SealContext) :
    simulateQ (implementation native reserve) (simulateQ adapter (RawCtxSourceSend.program start)) =
      (do
        let result ← liftState (simulateQ native (simulateQ adapter (RawCtxSourceSend.program start)))
        let output ← StateT.lift (gate reserve (fun value : Encrypted => value.ciphertext.length) result.2)
        pure (result.1, output) : StateT S (StateT Platform m) _) := by
  cases start with
  | SendExhausted entry =>
    simp only [RawCtxSourceSend.program, simulateQ_pure]
    ext before previous
    simp only [StateT.run_bind, run_liftState, StateT.run_lift, StateT.run_pure, pure_bind, gate]
  | SendKdfRequested pending =>
    ext before previous
    simp only [RawCtxSourceSend.program, simulateQ_bind, simulateQ_spec_query, adapter, simulateQ_pure,
      implementation, StateT.run_bind, run_liftState, StateT.run_lift, StateT.run_pure]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro response
    apply bind_congr
    intro ciphertext
    rw [RegistrationNativePlatformOrdinaryGate.gate_map]
    simp only [StateT.run_map, bind_map_left]
    rfl

/-- The selected source begin operation retains the same terminal reservation and full state. -/
theorem send (native : QueryImpl PrimitiveSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E))
    (kernel : ratchet.concrete.ConcreteRatchetKernel) (context : SealContext) :
    simulateQ (implementation native reserve) (simulateQ adapter (RawCtxSourceSend.send kernel context)) =
      (do
        let result ← liftState (simulateQ native (simulateQ adapter (RawCtxSourceSend.send kernel context)))
        let output ← StateT.lift (gate reserve (fun value : Encrypted => value.ciphertext.length) result.2)
        pure (result.1, output) : StateT S (StateT Platform m) _) :=
  program native reserve (beginSend kernel context)

/-- Complete owner state advances exactly as in the original source send, even when terminal public reservation rejects the returned ciphertext. -/
theorem sendOwner {Metadata : Type} (native : QueryImpl PrimitiveSpec (StateT S m))
    (reserve : Nat → StateT Platform m (core.result.Result Unit E))
    (senderId : U64) (plaintext : Pqxdh.Bytes) (owner : RawCtxWholeOwner.OwnerState Metadata) :
    simulateQ (implementation native reserve) ((RawCtxSourceSend.sendOwner senderId plaintext).run owner) =
      (do
        let result ← liftState (simulateQ native ((RawCtxSourceSend.sendOwner senderId plaintext).run owner))
        let output ← StateT.lift (gate reserve (fun value : Encrypted => value.ciphertext.length) result.1)
        pure (output, result.2) : StateT S (StateT Platform m) _) := by
  unfold RawCtxSourceSend.sendOwner StateT.run
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, ite_true, simulateQ_pure, liftState_pure, pure_bind, gate]
    ext before previous
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, pure_bind]
  · simp only [empty, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_pure]
    rw [send]
    simp only [liftState_bind, liftState_pure, bind_assoc, pure_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate.send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate.send

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate.sendOwner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySendGate.sendOwner

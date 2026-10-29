-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBoundKeySchedule
import BeaconcryptCore.Computational.RegistrationWorldServerPublication

/-! After the first KDF step, the advanced whole kernel is retained only for eventual installation. The actual raw seal, commitment, response admission, signature preimage and encoder do not inspect it. These commuting equations permit a source compiler to retain a hidden reference instead of exposing seed bytes to its public continuation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open BeaconcryptCore.Refinement.RecordEffects
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace BeaconcryptCore.Computational.RegistrationKernelErasure

def mapCore (kernel : ConcreteRatchetKernel) : RegistrationServerRecordExecutor.Result → RegistrationServerRecordExecutor.Result
  | .Err previous => .Err previous
  | .Ok pending => .Ok { pending with kernel }

def mapResult (kernel : ConcreteRatchetKernel) (result : RustM RegistrationServerRecordExecutor.Result) :
    RustM RegistrationServerRecordExecutor.Result := mapCore kernel <$> result

def selected (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordAead) : registration.ServerRecordAead :=
  { pending with pending := ⟨{ pending.pending.seal with advanced := kernel }⟩ }

/-- Raw source admission returns the supplied whole kernel without using it in any size, transcript or rejection decision. -/
theorem finish_map (kernel : ConcreteRatchetKernel) (state : registration.ServerRecordState)
    (sealing : SendSeal record_effects.SealFrameContext) (written : Option Pqxdh.Bytes) :
    RegistrationRawSealBridge.finish state { sealing with advanced := kernel } written =
      mapResult kernel (RegistrationRawSealBridge.finish state sealing written) := by
  simp only [RegistrationRawSealBridge.finish, registration.ServerRecordWrite.resume,
    pqxdh.server_abort_candidate, seal_write_finish_exact, bind_tc_ok,
    mapResult, ]
  cases writtenBytes : RegistrationAuthenticationShared.openedBytes written <;>
    simp only []
  all_goals try dsimp! +zeta only
  all_goals try simp only [map_bind, ]
  all_goals try simp only [RawCtxMaterialInterpretation.rust_map_ok, mapCore]
  repeat' (
    first | (congr 1; funext result) | split
    all_goals try dsimp! only
    all_goals try simp only [map_bind, mapCore, RawCtxMaterialInterpretation.rust_map_ok])

/-- The exact byte-level raw sealing service retains all primitive effects under whole-kernel replacement. -/
theorem model_map (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordAead) :
    RegistrationRawSealBridge.model (selected kernel pending) =
      mapResult kernel <$> RegistrationRawSealBridge.model pending := by
  simp only [RegistrationRawSealBridge.model, selected, RegistrationRawSealBridge.inputOf, map_bind, map_pure]
  apply bind_congr
  intro written
  exact congrArg pure (finish_map kernel pending.state pending.pending.seal written)

/-- Actual extracted AEAD/hash/raw-writer continuations commute with the private kernel reference, without a callback simulation premise. -/
theorem fromAead_map (kernel : ConcreteRatchetKernel) (pending : registration.ServerRecordAead)
    (raw : pending.pending.seal.context.encoding = .Raw) :
    simulateQ RegistrationRawSealBridge.nativeAdapter (RegistrationServerRecordExecutor.fromAead (selected kernel pending)) =
      mapResult kernel <$> simulateQ RegistrationRawSealBridge.nativeAdapter (RegistrationServerRecordExecutor.fromAead pending) := by
  rw [RegistrationRawSealBridge.model_exact _ (show (selected kernel pending).pending.seal.context.encoding = .Raw from raw),
    RegistrationRawSealBridge.model_exact pending raw]
  exact model_map kernel pending

end BeaconcryptCore.Computational.RegistrationKernelErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationKernelErasure.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationKernelErasure.finish_map

/-- info: 'BeaconcryptCore.Computational.RegistrationKernelErasure.model_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationKernelErasure.model_map

/-- info: 'BeaconcryptCore.Computational.RegistrationKernelErasure.fromAead_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationKernelErasure.fromAead_map

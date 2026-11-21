-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryWorld
import BeaconcryptCore.Computational.CborRawCanonicalBuild

/-! The trusted pure canonical serializer can execute locally before the public reservation decision is observed. This terminal gate returns the original ciphertext only on ordinary reservation success. It does not publish a failed send to the ledger, expose private World state, or identify complete old and corrected profiles. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate
variable {E A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

def gate (reserve : Nat → m (core.result.Result Unit E)) (size : A → Nat) (output : Option A) : m (Option A) :=
  match output with
  | none => pure none
  | some value => do
      let result ← reserve (size value)
      match result with
      | .Err _ => pure none
      | .Ok _ => pure (some value)

omit [LawfulMonad m] in
/-- Exact source writing is a terminal public length gate on the unchanged canonical bytes. -/
theorem writer_late (reserve : Nat → m (core.result.Result Unit E)) (frame : RawCtxReceive.DecodedFrame) :
    RegistrationNativePlatformOrdinaryWriter.write reserve frame =
      gate reserve List.length (CborRawCanonicalBuild.canonicalWriter frame) := by
  unfold RegistrationNativePlatformOrdinaryWriter.write RegistrationNativePlatformOrdinaryWriter.capacity
    CborRawCanonicalBuild.canonicalWriter
  by_cases admitted : CborSizing.frameLen frame.sequence.val frame.sender.val frame.payload.length ≤ 33554432
  · have representable : frame.payload.length < 2 ^ 64 := by
      unfold CborSizing.frameLen CborSizing.byteStringLen at admitted
      omega
    simp only [CborSizing.maxMessageSize, admitted, ite_true, gate]
    rw [CborTransport.render_length frame representable]
    rfl
  · simp only [CborSizing.maxMessageSize, admitted, ite_false, gate]

/-- Wrapping ciphertext metadata preserves the same terminal reservation and optional failure. -/
theorem gate_map (reserve : Nat → m (core.result.Result Unit E)) (size : B → Nat) (wrap : A → B) (output : Option A) :
    gate reserve size (output.map wrap) = Option.map wrap <$> gate reserve (fun value => size (wrap value)) output := by
  cases output with
  | none => simp only [gate, Option.map_none, map_pure]
  | some value =>
      simp only [gate, Option.map_some, map_bind]
      apply bind_congr
      intro result
      cases result <;> simp only [map_pure, Option.map_none, Option.map_some]

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate.writer_late' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate.writer_late

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate.gate_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryGate.gate_map

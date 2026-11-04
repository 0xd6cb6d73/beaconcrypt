-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion
/-! The literal supplied-pending source completion is a typed free tree. Its initializer/ratchet queries, source AEAD/hash/writers, signing and installation run in their unchanged order. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionProgram
variable {n : Nat}
inductive Request (n : Nat) where
  | records (query : RegistrationRecordPrimitives.Spec.Domain)
  | seal (query : record_effects.AeadSealRequest)
  | hash (query : commitment.CommitmentTranscript)
  | write (query : record_effects.RecordWriteRequest)
  | signing (query : RegistrationSigningShared.Spec.Domain)
  | encode (view : registration.SignedResponseView)
  | effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
def Reply : Request n → Type
  | .records query => RegistrationRecordPrimitives.Spec.Range query
  | .seal _ => RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))
  | .hash _ => RegistrationNativePlatformCommitment.HashReply
  | .write _ => RustM (core.option.Option (Slice U8))
  | .signing query => RegistrationSigningShared.Spec.Range query
  | .encode _ => RustM (core.option.Option (alloc.vec.Vec U8))
  | .effect query => (PqxdhRecordLiftInterface.EnvEffects n).Range query
abbrev Spec (n : Nat) : OracleSpec (Request n) := Reply

def record : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Spec n)) := fun query => (Spec n).query (.records query)
def sealed (query : record_effects.AeadSealRequest) : OracleComp (Spec n) (Reply (n := n) (.seal query)) := (Spec n).query (.seal query)
def hashed (query : commitment.CommitmentTranscript) : OracleComp (Spec n) (Reply (n := n) (.hash query)) := (Spec n).query (.hash query)
def written (query : record_effects.RecordWriteRequest) : OracleComp (Spec n) (Reply (n := n) (.write query)) := (Spec n).query (.write query)
def signed : QueryImpl RegistrationSigningShared.Spec (OracleComp (Spec n)) := fun query => (Spec n).query (.signing query)
def encoded (view : registration.SignedResponseView) : OracleComp (Spec n) (Reply (n := n) (.encode view)) := (Spec n).query (.encode view)
def capability : QueryImpl (PqxdhRecordLiftInterface.CapabilitySpec n) (OracleComp (Spec n)) := fun query => (Spec n).query (.effect (.inr query))

def program (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    OracleComp (Spec n) (RustM (RegistrationWorldServerCompletion.Result (alloc.vec.Vec U8))) :=
  RegistrationNativePlatformSourceCompletion.fromInitialSource record sealed hashed written signed capability encoded control pending

variable {m : Type → Type} [Monad m] [LawfulMonad m]
/-- Interpreting the literal completion syntax reconstructs its unchanged source controller under the supplied individual callbacks. -/
theorem interpret (implementation : QueryImpl (Spec n) m)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    simulateQ implementation (program control pending) =
      RegistrationNativePlatformSourceCompletion.fromInitialSource
        (fun query => implementation (.records query)) (fun query => implementation (.seal query))
        (fun query => implementation (.hash query)) (fun query => implementation (.write query))
        (fun query => implementation (.signing query)) (fun query => implementation (.effect (.inr query)))
        (fun current => implementation (.encode current)) control pending := by
  have transported := RegistrationNativePlatformSourceCompletion.fromInitialSource_map (simulateQ_isMonadHom implementation)
    (record (n := n)) sealed hashed written signed capability encoded control pending
  simpa only [program, record, sealed, hashed, written, signed, capability, encoded, simulateQ_spec_query] using transported
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionProgram.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletionProgram.interpret

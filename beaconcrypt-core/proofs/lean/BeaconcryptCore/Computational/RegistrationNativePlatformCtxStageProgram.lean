-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageMap
/-! The complete source supplied-material service is a literal typed free tree. Its marker, sealing, mutable hash, raw writer, ML signature, response writer and installation effects are distinct leaves interpreted on one shared state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageProgram
variable {n : Nat}

inductive Request (n : Nat) where
  | mark
  | seal (query : record_effects.AeadSealRequest)
  | hash (query : commitment.CommitmentTranscript)
  | write (query : record_effects.RecordWriteRequest)
  | signing (query : RegistrationSigningShared.Spec.Domain)
  | encode (view : registration.SignedResponseView)
  | effect (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)

def Reply : Request n → Type
  | .mark => Unit
  | .seal _ => RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))
  | .hash _ => RegistrationNativePlatformCommitment.HashReply
  | .write _ => RustM (core.option.Option (Slice U8))
  | .signing query => RegistrationSigningShared.Spec.Range query
  | .encode _ => RustM (core.option.Option (alloc.vec.Vec U8))
  | .effect query => (PqxdhRecordLiftInterface.EnvEffects n).Range query

abbrev Spec (n : Nat) : OracleSpec (Request n) := Reply

def sealed (query : record_effects.AeadSealRequest) : OracleComp (Spec n) (Reply (n := n) (.seal query)) := (Spec n).query (.seal query)
def hashed (query : commitment.CommitmentTranscript) : OracleComp (Spec n) (Reply (n := n) (.hash query)) := (Spec n).query (.hash query)
def written (query : record_effects.RecordWriteRequest) : OracleComp (Spec n) (Reply (n := n) (.write query)) := (Spec n).query (.write query)
def signed : QueryImpl RegistrationSigningShared.Spec (OracleComp (Spec n)) := fun query => (Spec n).query (.signing query)
def encoded (view : registration.SignedResponseView) : OracleComp (Spec n) (Reply (n := n) (.encode view)) := (Spec n).query (.encode view)
def effect : QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (Spec n)) := fun query => (Spec n).query (.effect query)

def program (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    OracleComp (Spec n) (RustM (RegistrationHiddenInstall.Result (alloc.vec.Vec U8))) := do
  let _ ← (Spec n).query .mark
  RegistrationNativePlatformPairedServerService.knownStage sealed hashed written signed encoded effect control initial output

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The marker and every actual source service leaf occur in their original order, retaining all enclosing outcomes and continuation state. -/
theorem interpret (implementation : QueryImpl (Spec n) m)
    (control : pqxdh.ServerState) (initial : RegistrationBoundKeySchedule.PublicInitial)
    (output : PqxdhServerAuthKeySchedule.Output) :
    simulateQ implementation (program control initial output) = (do
      let _ ← implementation .mark
      RegistrationNativePlatformPairedServerService.knownStage
        (fun query => implementation (.seal query)) (fun query => implementation (.hash query))
        (fun query => implementation (.write query)) (fun query => implementation (.signing query))
        (fun view => implementation (.encode view)) (fun query => implementation (.effect query)) control initial output) := by
  unfold program
  rw [simulateQ_bind, simulateQ_spec_query]
  apply bind_congr
  intro marked
  have transported := RegistrationNativePlatformCtxStageMap.known (simulateQ_isMonadHom implementation)
    (sealed (n := n)) hashed written signed encoded effect control initial output
  simpa only [sealed, hashed, written, signed, encoded, effect, simulateQ_spec_query] using transported
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageProgram.interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxStageProgram.interpret

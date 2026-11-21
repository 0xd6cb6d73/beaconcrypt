-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceRecord
import BeaconcryptCore.Computational.RegistrationNativePlatformBuildInterpret
import BeaconcryptCore.Computational.RegistrationNativePlatformWriter

/-! First-record writing and response publication use their checked extracted request bodies in one common free language. Crypto, capability installation, allocator and serializers share a single interpreter and its complete state. RustM failure/divergence from either source writer is propagated at its literal controller cut. This additive completion does not assume a source codec law or equality to a pure wire function. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion
open RegistrationNativePlatformServerCompletion (continueResult installWith)
open RegistrationWorldServerCompletion (Result)
open PqxdhRecordLiftInterface (CapabilitySpec)
variable {n : Nat} {Encoded : Type} {m : Type → Type} [Monad m]

def fromInitialWith
    (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (sign : QueryImpl RegistrationSigningShared.Spec m)
    (capability : QueryImpl (CapabilitySpec n) m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) : m (RustM (Result Encoded)) := do
  let record ← RegistrationNativePlatformServerRecord.fromInitial record write pending
  continueResult record fun response => do
    let published ← RegistrationNativePlatformServerPublication.program sign encode response
    continueResult published (installWith capability control)

def fromInitialSource
    (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sealing : record_effects.AeadSealRequest → m (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → m RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (sign : QueryImpl RegistrationSigningShared.Spec m)
    (capability : QueryImpl (CapabilitySpec n) m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) : m (RustM (Result Encoded)) := do
  let record ← RegistrationNativePlatformSourceRecord.fromInitialWithHash record sealing hash write pending
  continueResult record fun response => do
    let published ← RegistrationNativePlatformServerPublication.program sign encode response
    continueResult published (installWith capability control)

section Map
variable {left right : Type → Type} [Monad left] [Monad right]
variable {F : ∀ {Value : Type}, left Value → right Value}
variable (hom : Cslib.IsMonadHom left right F)
include hom

private theorem continueResult_map {Input : Type} (action : RustM (core.result.Result Input pqxdh.ServerState))
    (next : Input → left (RustM (Result Encoded))) :
    F (continueResult action next) = continueResult action (fun value => F (next value)) := by
  cases action with
  | ok result => cases result <;> first | rfl | exact hom.map_pure _
  | fail error => exact hom.map_pure _
  | div => exact hom.map_pure _

theorem fromInitialWith_map
    (record : QueryImpl RegistrationRecordPrimitives.Spec left)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (sign : QueryImpl RegistrationSigningShared.Spec left)
    (capability : QueryImpl (CapabilitySpec n) left)
    (encode : registration.SignedResponseView → left (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    F (fromInitialWith record write sign capability encode control pending) =
      fromInitialWith (fun query => F (record query)) (fun request => F (write request))
        (fun query => F (sign query)) (fun query => F (capability query))
        (fun view => F (encode view)) control pending := by
  unfold fromInitialWith
  rw [hom.map_bind, RegistrationNativePlatformServerRecord.fromInitial_map hom]
  apply bind_congr
  intro recorded
  rw [continueResult_map hom]
  apply congrArg (continueResult recorded)
  funext response
  rw [hom.map_bind, RegistrationNativePlatformBuildInterpret.Publication.program hom]
  apply bind_congr
  intro published
  rw [continueResult_map hom]
  apply congrArg (continueResult published)
  funext ready
  exact RegistrationNativePlatformBuildInterpret.Completion.installWith hom capability control ready
theorem fromInitialSource_map
    (record : QueryImpl RegistrationRecordPrimitives.Spec left)
    (sealing : record_effects.AeadSealRequest → left (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → left RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → left (RustM (core.option.Option (Slice U8))))
    (sign : QueryImpl RegistrationSigningShared.Spec left)
    (capability : QueryImpl (CapabilitySpec n) left)
    (encode : registration.SignedResponseView → left (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    F (fromInitialSource record sealing hash write sign capability encode control pending) =
      fromInitialSource (fun query => F (record query)) (fun request => F (sealing request))
        (fun transcript => F (hash transcript)) (fun request => F (write request))
        (fun query => F (sign query)) (fun query => F (capability query))
        (fun view => F (encode view)) control pending := by
  unfold fromInitialSource
  rw [hom.map_bind, RegistrationNativePlatformSourceRecord.fromInitialWithHash_map hom]
  apply bind_congr
  intro recorded
  rw [continueResult_map hom]
  apply congrArg (continueResult recorded)
  funext response
  rw [hom.map_bind, RegistrationNativePlatformBuildInterpret.Publication.program hom]
  apply bind_congr
  intro published
  rw [continueResult_map hom]
  apply congrArg (continueResult published)
  funext ready
  exact RegistrationNativePlatformBuildInterpret.Completion.installWith hom capability control ready

end Map

variable [LawfulMonad m]

theorem fromInitialWith_pure
    (record : QueryImpl RegistrationRecordPrimitives.Spec m)
    (sign : QueryImpl RegistrationSigningShared.Spec m)
    (capability : QueryImpl (CapabilitySpec n) m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    fromInitialWith record (fun request => RustM.ok <$> record (.write request))
      sign capability encode control pending =
      RegistrationNativePlatformServerCompletion.fromInitialWith record sign capability encode control pending := by
  unfold fromInitialWith RegistrationNativePlatformServerCompletion.fromInitialWith
  rw [RegistrationNativePlatformServerRecord.fromInitial_pure]

theorem fromInitialSource_native
    (record : QueryImpl RegistrationRecordPrimitives.Spec m) (erased : commitment.CommitmentTranscript)
    (write : record_effects.RecordWriteRequest → m (RustM (core.option.Option (Slice U8))))
    (sign : QueryImpl RegistrationSigningShared.Spec m)
    (capability : QueryImpl (CapabilitySpec n) m)
    (encode : registration.SignedResponseView → m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    fromInitialSource record (fun request => RustM.ok <$> record (.seal request))
      (fun transcript => (fun reply => RustM.ok (reply, erased)) <$> record (.hash transcript))
      write sign capability encode control pending =
      fromInitialWith record write sign capability encode control pending := by
  unfold fromInitialSource fromInitialWith
  rw [RegistrationNativePlatformSourceRecord.fromInitialWithHash_native,
    RegistrationNativePlatformSourceRecord.fromInitial_pure]

abbrev Spec (E : Type) (n : Nat) := RegistrationRecordPrimitives.Spec +
  (RegistrationSigningShared.Spec + (CapabilitySpec n +
    (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E +
      BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E)))

def recordLift {E : Type} : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp (Spec E n)) :=
  fun query => (Spec E n).query (.inl query)

def signLift {E : Type} : QueryImpl RegistrationSigningShared.Spec (OracleComp (Spec E n)) :=
  fun query => (Spec E n).query (.inr (.inl query))

def capabilityLift {E : Type} : QueryImpl (CapabilitySpec n) (OracleComp (Spec E n)) :=
  fun query => (Spec E n).query (.inr (.inr (.inl query)))

def helperLift {E : Type} : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E)
    (OracleComp (Spec E n)) := fun query => (Spec E n).query (.inr (.inr (.inr (.inl query))))

def writerLift {E : Type} : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E)
    (OracleComp (Spec E n)) := fun query => (Spec E n).query (.inr (.inr (.inr (.inr query))))

def writeWith {E : Type} (implementation :
    QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) m)
    (request : record_effects.RecordWriteRequest) : m (RustM (core.option.Option (Slice U8))) :=
  BeaconcryptCore.Refinement.AdapterRecordNativeWriter.borrow <$>
    simulateQ implementation (BeaconcryptCore.Refinement.AdapterRecordHelperRouting.route
      (E := E) (m := BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program E) request).run

def encodeWith {E : Type} (implementation :
    QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) m)
    (view : registration.SignedResponseView) : m (RustM (core.option.Option (alloc.vec.Vec U8))) :=
  simulateQ implementation (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeResponse
    (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
    (RegistrationNativePlatformWriter.responsePacket view)).run

def program (E : Type) (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    OracleComp (Spec E n) (RustM (Result (alloc.vec.Vec U8))) :=
  fromInitialWith recordLift (writeWith helperLift) signLift capabilityLift (encodeWith writerLift) control pending

private theorem simulate_hom {κ : Type} {spec : OracleSpec.{0, 0} κ}
    (implementation : QueryImpl spec m) :
    Cslib.IsMonadHom (OracleComp spec) m (fun {Value} (work : OracleComp spec Value) =>
      simulateQ implementation work) :=
  .mk' (simulateQ_pure implementation) (simulateQ_bind implementation)

theorem fromInitialSource_interpret {κ : Type} {spec : OracleSpec.{0, 0} κ}
    (implementation : QueryImpl spec m)
    (record : QueryImpl RegistrationRecordPrimitives.Spec (OracleComp spec))
    (sealing : record_effects.AeadSealRequest → OracleComp spec (RustM (core.option.Option (Slice U8 × Std.Array U8 16#usize))))
    (hash : commitment.CommitmentTranscript → OracleComp spec RegistrationNativePlatformCommitment.HashReply)
    (write : record_effects.RecordWriteRequest → OracleComp spec (RustM (core.option.Option (Slice U8))))
    (sign : QueryImpl RegistrationSigningShared.Spec (OracleComp spec))
    (capability : QueryImpl (CapabilitySpec n) (OracleComp spec))
    (encode : registration.SignedResponseView → OracleComp spec (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    simulateQ implementation (fromInitialSource record sealing hash write sign capability encode control pending) =
      fromInitialSource (fun query => simulateQ implementation (record query))
        (fun request => simulateQ implementation (sealing request))
        (fun transcript => simulateQ implementation (hash transcript))
        (fun request => simulateQ implementation (write request))
        (fun query => simulateQ implementation (sign query)) (fun query => simulateQ implementation (capability query))
        (fun view => simulateQ implementation (encode view)) control pending :=
  fromInitialSource_map (simulate_hom implementation) record sealing hash write sign capability encode control pending

theorem writeWith_interpret {E : Type} (implementation : QueryImpl (Spec E n) m)
    (request : record_effects.RecordWriteRequest) :
    simulateQ implementation (writeWith helperLift request) =
      writeWith (fun query => implementation (.inr (.inr (.inr (.inl query))))) request := by
  unfold writeWith
  rw [simulateQ_map, ← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => BeaconcryptCore.Refinement.AdapterRecordNativeWriter.borrow <$>
    simulateQ handler (BeaconcryptCore.Refinement.AdapterRecordHelperRouting.route
      (E := E) (m := BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Program E) request).run)
  funext query
  exact simulateQ_spec_query implementation (.inr (.inr (.inr (.inl query))))

theorem encodeWith_interpret {E : Type} (implementation : QueryImpl (Spec E n) m)
    (view : registration.SignedResponseView) :
    simulateQ implementation (encodeWith writerLift view) =
      encodeWith (fun query => implementation (.inr (.inr (.inr (.inr query))))) view := by
  unfold encodeWith
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => simulateQ handler
    (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestExtraction.encodeResponse
      (E := E) (m := BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Program E)
      (RegistrationNativePlatformWriter.responsePacket view)).run)
  funext query
  exact simulateQ_spec_query implementation (.inr (.inr (.inr (.inr query))))

theorem program_interpret {E : Type} (implementation : QueryImpl (Spec E n) m)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    simulateQ implementation (program E control pending) =
      fromInitialWith (fun query => implementation (.inl query))
        (writeWith (fun query => implementation (.inr (.inr (.inr (.inl query))))))
        (fun query => implementation (.inr (.inl query)))
        (fun query => implementation (.inr (.inr (.inl query))))
        (encodeWith (fun query => implementation (.inr (.inr (.inr (.inr query)))))) control pending := by
  unfold program
  rw [fromInitialWith_map (simulate_hom implementation)]
  simp only [recordLift, signLift, capabilityLift, simulateQ_spec_query,
    writeWith_interpret, encodeWith_interpret]

theorem program_joint {E σ κ : Type} {spec : OracleSpec.{0, 0} κ}
    (implementation : QueryImpl (Spec E n) (StateT σ (OracleComp spec)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) (before : σ) :
    (simulateQ implementation (program E control pending)).run before =
      (fromInitialWith (fun query => implementation (.inl query))
        (writeWith (fun query => implementation (.inr (.inr (.inr (.inl query))))))
        (fun query => implementation (.inr (.inl query)))
        (fun query => implementation (.inr (.inr (.inl query))))
        (encodeWith (fun query => implementation (.inr (.inr (.inr (.inr query)))))) control pending).run before := by
  rw [program_interpret]

theorem program_continuation {E σ κ Output : Type} {spec : OracleSpec.{0, 0} κ}
    (implementation : QueryImpl (Spec E n) (StateT σ (OracleComp spec)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf)
    (next : RustM (Result (alloc.vec.Vec U8)) → StateT σ (OracleComp spec) Output) (before : σ) :
    ((simulateQ implementation (program E control pending) >>= next).run before) = (do
      let result ← (fromInitialWith (fun query => implementation (.inl query))
        (writeWith (fun query => implementation (.inr (.inr (.inr (.inl query))))))
        (fun query => implementation (.inr (.inl query)))
        (fun query => implementation (.inr (.inr (.inl query))))
        (encodeWith (fun query => implementation (.inr (.inr (.inr (.inr query)))))) control pending).run before
      (next result.1).run result.2) := by
  rw [program_interpret, StateT.run_bind]

end BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialWith_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialWith_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialWith_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialWith_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.writeWith_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.writeWith_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.encodeWith_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.encodeWith_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.program_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.program_interpret
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.program_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.program_joint
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.program_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.program_continuation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialSource_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialSource_map
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialSource_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialSource_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialSource_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSourceCompletion.fromInitialSource_interpret

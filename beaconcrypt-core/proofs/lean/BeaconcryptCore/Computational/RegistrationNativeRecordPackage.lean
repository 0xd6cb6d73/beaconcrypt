-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveEntropyStartup
import BeaconcryptCore.Computational.CborRawRecordLiftCrypto

/-! Exact packaging of an actual native World program for the arbitrary-client record reductions. The native transcript is retained alongside its literal original private ledger; no startup, pin hash, callback or failure branch is replaced. The observation contains the complete native result and the existing permitted record view, and has no private interpreter-state argument. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRecordPackage
open PqxdhRecordLiftInterface (WorldSpec)
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeEntropyRun (Outcome)
variable {n : Nat} {E Value Reader Response First Second : Type}
variable {ι KemSK : Type} {base : OracleSpec ι}

abbrev Extra (E : Type) := PqxdhRegistrationJointServerBirth.ClientCreated Unit × List RegistrationNativeInterface.Entry × E

def encode (native : Outcome E Value) : PqxdhRecordLiftLaterWorlds.Outcome (Extra E) Value :=
  native.map fun born => (born.1, (born.2.1.1, born.2.1.2.ledger), (born.1, born.2.1.2.transcript, born.2.2))

def decode (old : PqxdhRecordLiftLaterWorlds.Outcome (Extra E) Value) : Outcome E Value :=
  old.map fun born => (born.2.2.1, (born.2.1.1, ⟨born.2.1.2, born.2.2.2.1⟩), born.2.2.2.2)

theorem decode_encode (native : Outcome E Value) : decode (encode native) = native := by
  cases native <;> rfl

/-- The complete native result and exactly the permitted record observation. -/
structure View (n : Nat) (E Value : Type) where
  result : Outcome E Value
  produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)
  raw : PqxdhRecordLiftWorld.RawCounters
  slots : PqxdhDeploymentInterface.Handle → Option (PqxdhRecordLiftInterface.Slot n)

def view (old : PqxdhRecordLiftIdeal.View n (Extra E) Value) : View n E Value :=
  ⟨old.result.map (fun born =>
    (born.2.2.1, (born.1, ⟨born.2.1, born.2.2.2.1⟩), born.2.2.2.2)), old.produced, old.raw, old.slots⟩

def nativeView (result : Outcome E Value × PqxdhRecordLiftProtocol.Control n)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) : View n E Value :=
  ⟨result.1, produced, PqxdhRecordLiftProtocol.rawCounters result.2, PqxdhRecordLiftIdeal.handleSlot result.2⟩

theorem encoded_view (result : Outcome E Value × PqxdhRecordLiftProtocol.Control n)
    (produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)) :
    view (PqxdhRecordLiftIdeal.viewOf (encode result.1, result.2) produced) = nativeView result produced := by
  rcases result with ⟨_ | born, control⟩ <;> rfl

noncomputable def client (work : OracleComp (WorldSpec n) (Outcome E Value)) :=
  CborRecordWorldClient.client (encode <$> work)

noncomputable def ctx (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (Outcome E Value)) : ProbComp (View n E Value) :=
  (view ∘ PqxdhRecordLiftIdeal.ctxView) <$>
    PqxdhRecordLiftLaterWorlds.ctxRunOf modes id setup codec route (client work)

theorem ctx_source (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (Outcome E Value)) :
    ctx modes setup codec route work =
      (fun result => nativeView (result.1.1.1, result.1.2) result.2.base.produced) <$>
        CborRawRecordOriginFlatten.interpret (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec) codec route work
          CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftIdeal.CtxPrivate.initial := by
  simp only [ctx, PqxdhRecordLiftLaterWorlds.ctxRunOf, client, CborRecordWorldClient.client,
    PqxdhRecordLiftProtocol.schedule, CborRawRecordOriginFlatten.interpret,
    simulateQ_map, StateT.run_map, Functor.map_map]
  congr 1
  funext result
  exact encoded_view (result.1.1.1, result.1.2) result.2.base.produced

theorem ctx_result_source (modes : PqxdhRecordLiftWorldCompiler.Label n → PqxdhRecordLiftIdeal.KeyMode)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) (Outcome E Value)) :
    View.result <$> ctx modes setup codec route work =
      (fun result => result.1.1.1) <$>
        CborRawRecordOriginFlatten.interpret (PqxdhRecordLiftIdeal.ctxInterpreter modes id setup codec) codec route work
          CborRecordWorldClient.initial PqxdhRecordLiftProtocol.initialControl PqxdhRecordLiftIdeal.CtxPrivate.initial := by
  rw [ctx_source, Functor.map_map]
  rfl

noncomputable def actual (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) (Outcome E Value)) :=
  Prod.fst <$> (simulateQ (CborRecordWorldSimulation.guarded setup codec route) work).run PqxdhRecordLiftWorld.initial

/-- The all-real endpoint is the literal complete actual guarded World program; every startup and shared-hash effect is inside it. -/
theorem real_result_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) (Outcome E Value)) :
    (fun result => decode result.1.1) <$>
      PqxdhRecordLiftLaterWorlds.chainsOf (fun _ => false) setup codec route (client work) =
        actual setup codec route work := by
  have source := congrArg (Functor.map (decode ∘ Prod.fst))
    (CborRawRecordLiftCrypto.real_source setup codec route (client work))
  simp only [Functor.map_map, PqxdhRecordLiftProtocol.rejoin, Prod.map_def, id_eq, Function.comp_def] at source
  rw [source]
  simp only [client, RegistrationNativeEntropyProgram.cursor_map,
    simulateQ_map, StateT.run_map, Functor.map_map]
  simp only [decode_encode]
  simpa only [actual, CborRecordWorldCursor.initial_shell.1] using congrArg (Functor.map Prod.fst)
    (CborRecordWorldSimulation.client_simulation setup codec route work PqxdhRecordLiftWorld.initial)

end BeaconcryptCore.Computational.RegistrationNativeRecordPackage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordPackage.decode_encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordPackage.decode_encode

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordPackage.encoded_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordPackage.encoded_view

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordPackage.ctx_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordPackage.ctx_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordPackage.ctx_result_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordPackage.ctx_result_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordPackage.real_result_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordPackage.real_result_source

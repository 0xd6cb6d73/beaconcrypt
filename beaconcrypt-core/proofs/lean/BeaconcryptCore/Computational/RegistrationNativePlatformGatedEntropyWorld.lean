-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyInitial

/-! The original ledger can begin after an effectful public startup in the same CTX World. Flattening retains its actual cursor, control, CTX cache and native state. Random-record hiding is proved at that exact initialized state, so no independent startup cache is substituted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftHiding (Coupled WorldRel ResultRel PrivRel EqRel)
variable {n : Nat} {ι KemSK Reader Response E X Failure : Type} {base : OracleSpec ι}

noncomputable def program (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) :
    OracleComp (WorldSpec n) (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E)) :=
  (fun result => some (PqxdhRegistrationJointServerBirth.encode created, result)) <$>
    (simulateQ (RegistrationNativePlatformGatedRecordInterface.native env reserve) (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (asModeO mode adversary))).run initial

/-- The actual post-startup full ledger has its literal World-level coupling from the reached environment state. -/
theorem program_couple (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (adversary : OracleComp (ModeSpec .P) X)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) :
    Coupled WorldRel ResultRel (program env reserve crypto codec serverKid bounds .P adversary created initial)
      (program env reserve crypto codec serverKid bounds .P adversary created initial) := by
  unfold program
  exact (Coupled.simulateQ_run _ _ Eq
    (fun query first _ same => same ▸ RegistrationNativePlatformGatedRecordInterface.native_couple env reserve query first)
    (PqxdhRecordLiftHiding.wrap_couple crypto codec serverKid bounds adversary) initial initial rfl).map
    fun _ _ related => ⟨rfl, related.1.1, related.1.2, related.2⟩

/-- Flattening the literal initialized World suffix preserves every field except the final public cursor projection. -/
theorem run_flat (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (created : PqxdhLiveServerConstruction.Created Unit)
    (state : CborRawRecordFlat.NativeState n E) :
    RegistrationNativePlatformGatedEntropyInitial.run modes replace setup codec route env reserve serverKid bounds mode adversary created state =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        CborRawRecordOriginFlatten.interpret (ctxInterpreter modes replace setup codec) codec route
          (program env reserve setup.source.crypto codec serverKid bounds mode adversary created state.1.1.1)
          state.1.1.2 state.1.2 state.2 := by
  rcases state with ⟨⟨⟨initial, shell⟩, control⟩, secret⟩
  have represented := RegistrationNativePlatformGatedRecordFlat.native_program (ctxInterpreter modes replace setup codec)
    env reserve codec route (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec serverKid bounds (asModeO mode adversary))
    initial shell control secret
  unfold RegistrationNativePlatformGatedEntropyInitial.run
  simp only [program, CborRawRecordOriginFlatten.interpret, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [PqxdhDeploymentSecrecy.wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT] at represented
  have mapped := congrArg (fun distribution => (fun result : (X × PqxdhDeploymentSecrecy.Ledger) ×
    CborRawRecordOriginService.State n E (CtxPrivate n) =>
      ((some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1.1.1), result.2.1.2), result.2.2)) <$> distribution) represented
  simp only [PqxdhDeploymentSecrecy.wrap, Functor.map_map, CborRawRecordOriginFlatten.interpret, RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl, RegistrationNativePlatformGatedRecordFlat.full, RegistrationNativePlatformGatedRecordFlat.join] at mapped ⊢
  exact mapped

/-- Equal-length plaintext replacement has the same hiding observation from the actual initialized shared CTX state. -/
theorem hiding_replace (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (adversary : OracleComp (ModeSpec .P) X) (created : PqxdhLiveServerConstruction.Created Unit)
    (state : CborRawRecordFlat.NativeState n E) (first second : Pqxdh.Bytes → Pqxdh.Bytes)
    (lengths : ∀ plaintext, (first plaintext).length = (second plaintext).length) :
    (fun result => hidingView (ctxView result)) <$>
      RegistrationNativePlatformGatedEntropyInitial.run (fun _ => .random) first setup codec route env reserve serverKid bounds .P adversary created state =
      (fun result => hidingView (ctxView result)) <$>
        RegistrationNativePlatformGatedEntropyInitial.run (fun _ => .random) second setup codec route env reserve serverKid bounds .P adversary created state := by
  rw [run_flat, run_flat]
  simp only [Functor.map_map]
  have client := CborRawRecordHiding.client_couple
    (program_couple env reserve setup.source.crypto codec serverKid bounds adversary created state.1.1.1) state.1.1.2
  have coupled := Coupled.simulateQ_run _ _ PrivRel
    (PqxdhRecordLiftHiding.interpreter_couple first second lengths setup codec)
    (PqxdhRecordLiftHiding.schedule_couple codec.frameRead route client state.1.2)
    state.2 state.2 ⟨rfl, fun _ => rfl⟩
  have same := coupled.map_eq _ _ fun left right related => PqxdhRecordLiftHiding.hidingView_rel left right related
  simpa only [PqxdhRecordLiftProtocol.schedule, CborRecordWorldClient.client, StateT.run'_eq,
    CborRawRecordOriginFlatten.interpret, simulateQ_map, StateT.run_map, Functor.map_map] using same

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld.program_couple' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld.program_couple

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld.run_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld.run_flat

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld.hiding_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedEntropyWorld.hiding_replace

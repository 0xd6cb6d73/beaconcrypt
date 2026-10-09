-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLedger

/-! Every selected accepted record in the literal initialized source program raises its own execution's marker. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (clientImpl support_run_fst)
open PqxdhRecordLiftProtocolHistory (Safe)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec asModeO)
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginMarkerNative PqxdhRecordFactsOriginMarkerEntry
open PqxdhRecordFactsOriginMarkerLedger
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Actual environment startup with complete marked private state and initially empty source control. -/
noncomputable def startup (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (initial : CtxPrivate n × Bool) :=
  (simulateQ (service target modes replace setup codec)
    ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) (simulateQ coinLift env.start)).run
      PqxdhRecordLiftProtocol.initialControl)).run initial

/-- Literal Server installation with complete marked private state. -/
noncomputable def install (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (control : PqxdhRecordLiftProtocol.Control n)
    (secret : CtxPrivate n × Bool) :=
  (simulateQ (service target modes replace setup codec)
    ((PqxdhRecordLiftProtocol.handler (n := n) codec.frameRead route (.inl created)).run control)).run secret

/-- Exact literal source-program flattening; no call, reply, state field or branch is removed. -/
theorem program_flat (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n × Bool) :
    (simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial =
      startup target modes replace setup codec route env initial >>= fun born =>
        match born.1.1 with
        | none => pure ((none, born.1.2), born.2)
        | some (created, start) =>
            install target modes replace setup codec route created born.1.2 born.2 >>= fun installed =>
              (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created,
                  (result.1, result.2.1), result.2.2.1.1), result.2.2.1.2), result.2.2.2)) <$>
                (simulateQ (fullImpl target modes replace setup codec route env serverKid bounds)
                  (asModeO mode adversary)).run
                  (PqxdhDeploymentSecrecy.Ledger.empty, ((start, installed.1.2), installed.2)) := by
  unfold PqxdhRecordLiftProtocol.program PqxdhRecordLiftProtocol.schedule PqxdhRecordLiftInterface.program
  simp only [simulateQ_bind, StateT.run_bind, startup]
  apply bind_congr
  rintro ⟨⟨born, control⟩, secret⟩
  rcases born with _ | ⟨created, start⟩
  · simp only [simulateQ_pure, StateT.run_pure]
  · simp only [simulateQ_bind, StateT.run_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, install, fullImpl, nativeImpl, clientImpl]
    apply bind_congr
    intro installed
    rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (PqxdhRecordLiftProtocol.handler codec.frameRead route)
      (native env), simulateQ_map, StateT.run_map,
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT (service target modes replace setup codec),
      PqxdhDeploymentSecrecy.wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    simp only [simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    rfl

/-- Actual startup derives source control safety with every service reply and private field retained. -/
theorem startup_safe (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (initial : CtxPrivate n × Bool)
    (result : (Option (PqxdhLiveServerConstruction.Created Unit × E) × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result ∈ support (startup target modes replace setup codec route env initial)) :
    Safe result.1.2 :=
  (PqxdhRecordLiftProtocolHistory.interpreted_schedule (service target modes replace setup codec)
    codec.frameRead route (simulateQ coinLift env.start) PqxdhRecordLiftProtocol.initialControl
    PqxdhRecordLiftProtocolHistory.initial_safe initial result supported).1

/-- Actual Server installation preserves the derived source control safety. -/
theorem install_safe (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (secret : CtxPrivate n × Bool)
    (result : (Unit × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool))
    (supported : result ∈ support (install target modes replace setup codec route created control secret)) :
    Safe result.1.2 :=
  (PqxdhRecordLiftProtocolHistory.handler codec.frameRead route (.inl created) control safe result.1
    (support_run_fst (service target modes replace setup codec) _ secret result supported)).1

/-- Every supported initialized literal source execution supplies selected received-entry facts for its actual final transcript. -/
theorem program_entryFacts (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n × Bool)
    (result : Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript,
      EntryFact target route result.1.2 result.2.2 entry := by
  rw [program_flat, mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := startup_safe target modes replace setup codec route env initial born bornSupported
  cases bornEq : born.1.1 with
  | none =>
      simp only [bornEq] at continued
      obtain rfl := (mem_support_pure_iff _ _).mp continued
      simp
  | some start =>
      rcases start with ⟨created, start⟩
      simp only [bornEq] at continued
      rw [mem_support_bind_iff] at continued
      obtain ⟨installed, installSupported, continued⟩ := continued
      have installedSafe := install_safe target modes replace setup codec route created born.1.2 bornSafe born.2 installed installSupported
      rw [support_map] at continued
      obtain ⟨final, finalSupported, rfl⟩ := continued
      have complete := full_program_invariant target modes replace setup codec route env serverKid bounds
        (asModeO mode adversary) _ (empty_invariant target route _ installedSafe) final finalSupported
      intro value member
      have equal := Option.some.inj member
      subst value
      exact complete.2

/-- Every actual successful final-transcript receive selecting the marked hidden coordinate has raised that same execution's flag, from the literal whole source program. -/
theorem program_received_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n × Bool)
    (result : Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript, ∀ receiver raw opened handle,
      entry.received = some (receiver, raw, .Some opened) → receivingHandle route receiver raw = some handle →
      handleSlot result.1.2 handle = some target.slot → target.direction = !handleDirection handle →
      target.position + 1 = opened.sequence.val → result.2.2 = true := by
  intro value present entry recorded receiver raw opened handle received routed slot direction position
  exact ((program_entryFacts target modes replace setup codec route env serverKid bounds mode adversary initial result supported
    value present entry recorded) receiver raw opened handle received routed).2 slot direction position

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.program_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.program_flat

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.startup_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.startup_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.install_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.install_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.program_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.program_entryFacts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.program_received_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerGlobal.program_received_flag

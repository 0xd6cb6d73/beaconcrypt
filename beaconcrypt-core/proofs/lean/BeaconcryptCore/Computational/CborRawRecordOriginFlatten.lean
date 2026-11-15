-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginService
import BeaconcryptCore.Computational.CborRawRecordOriginProgram

/-! The complete raw cursor, Protocol and private-service interpretation is reassociated onto the actual joint state. The private interpreter is arbitrary, so the same operational flattening applies to the CTX world and its sticky-marker instrumentation. The public cursor remains in state until the final permitted result projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginFlatten
open PqxdhServerAuthExperiment (Codec)
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (Control ServiceSpec initialControl)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds Mode ModeSpec asModeO)
open CborRawRecordOriginService (State native)
variable {n : Nat} {Reader Response E S Result X : Type}

noncomputable def interpret (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Result) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (secret : S) :=
  (simulateQ service ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route)
    ((simulateQ CborRecordWorldClient.handler work).run shell)).run control)).run secret

noncomputable def startup (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (secret : S) :=
  interpret service codec route (simulateQ PqxdhRecordLiftInterface.coinLift env.start)
    CborRecordWorldClient.initial initialControl secret

noncomputable def install (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (secret : S) :=
  (fun result => ((result.1.1.2, result.1.2), result.2)) <$>
    interpret service codec route ((WorldSpec n).query (.inl created)) shell control secret

noncomputable def full (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.Ledger × State n E S) ProbComp) :=
  ((native service env codec route).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds)).flattenStateT

theorem interpret_pure (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (value : Result) (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : S) :
    interpret service codec route (pure value) shell control secret = pure (((value, shell), control), secret) := by
  simp only [interpret, simulateQ_pure, StateT.run_pure]

theorem interpret_bind {Value : Type} (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) Value) (next : Value → OracleComp (WorldSpec n) Result)
    (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : S) :
    interpret service codec route (work >>= next) shell control secret =
      (interpret service codec route work shell control secret >>= fun result =>
        interpret service codec route (next result.1.1.1) result.1.1.2 result.1.2 result.2) := by
  simp only [interpret, simulateQ_bind, StateT.run_bind]

/-- Dropping only the final cursor gives the literal original raw guarded service program. -/
theorem program_interpret (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (secret : S) :
    (simulateQ service (CborRawRecordOriginProgram.program env crypto codec route serverKid bounds mode adversary)).run
      secret =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        interpret service codec route (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary)
          CborRecordWorldClient.initial initialControl secret := by
  simp only [CborRawRecordOriginProgram.program, PqxdhRecordLiftProtocol.schedule, CborRawRecordLiftBounds.client,
    CborRecordWorldClient.client, interpret, simulateQ_map, StateT.run_map]

/-- All adaptive native work has the actual cursor/Protocol/private-service interpretation on its complete joint state. -/
theorem native_program (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp Spec Result) (e : E) (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : S) :
    (simulateQ (native service env codec route) work).run (((e, shell), control), secret) =
      (fun result => (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))) <$>
        interpret service codec route ((simulateQ (PqxdhRecordLiftInterface.native env) work).run e) shell control secret := by
  induction work using OracleComp.inductionOn generalizing e shell control secret with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, interpret, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, CborRawRecordOriginService.source_run,
        interpret, map_bind, bind_map_left]
      apply bind_congr
      intro result
      simpa only [interpret, Functor.map_map] using ih result.1.1.1.1 result.1.1.1.2 result.1.1.2 result.1.2 result.2

/-- The complete actual raw program is startup, actual Server installation and the unchanged full ledger above the cursor-aware native interpreter. -/
theorem program_flat (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (secret : S) :
    (simulateQ service (CborRawRecordOriginProgram.program env crypto codec route serverKid bounds mode adversary)).run
      secret =
      (startup service env codec route secret >>= fun born =>
        match born.1.1.1 with
        | none => pure ((none, born.1.2), born.2)
        | some (created, initial) =>
            install service codec route created born.1.1.2 born.1.2 born.2 >>= fun installed =>
              (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created,
                (result.1, result.2.1), result.2.2.1.1.1), result.2.2.1.2), result.2.2.2)) <$>
                (simulateQ (full service env crypto codec route serverKid bounds) (asModeO mode adversary)).run
                  (PqxdhDeploymentSecrecy.Ledger.empty, (((initial, installed.1.1), installed.1.2), installed.2))) := by
  rw [program_interpret, PqxdhRecordLiftInterface.program, interpret_bind, map_bind]
  apply bind_congr
  intro born
  rcases born with ⟨⟨⟨_ | ⟨created, initial⟩, shell⟩, control⟩, secret⟩
  · rw [interpret_pure, map_pure]
  · rw [interpret_bind, map_bind]
    simp only [install, bind_map_left]
    apply bind_congr
    intro installed
    rw [interpret_bind, map_bind]
    simp only [interpret_pure, map_pure, bind_pure_comp]
    let finish := fun result : (X × PqxdhDeploymentSecrecy.Ledger) × State n E S =>
      ((some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1.1.1), result.2.1.2), result.2.2)
    have represented := congrArg (fun work => finish <$> work)
      (native_program service env codec route
        (PqxdhDeploymentSecrecy.wrap crypto codec serverKid bounds (asModeO mode adversary)) initial
        installed.1.1.2 installed.1.2 installed.2)
    simp only [Functor.map_map] at represented
    refine Eq.trans represented.symm ?_
    rw [PqxdhDeploymentSecrecy.wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    simp only [full, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    rfl

end BeaconcryptCore.Computational.CborRawRecordOriginFlatten

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginFlatten.interpret_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginFlatten.interpret_pure

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginFlatten.interpret_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginFlatten.interpret_bind

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginFlatten.program_interpret' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginFlatten.program_interpret

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginFlatten.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginFlatten.native_program

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginFlatten.program_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginFlatten.program_flat

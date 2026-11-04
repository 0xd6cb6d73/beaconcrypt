-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordInterface
import BeaconcryptCore.Computational.CborRawRecordFlatRun
/-! The actual gated open client is flattened below its unchanged secrecy ledger. Its public environment, cursor, record control and full private interpreter state remain in one joint state; the public post-send service is interpreted after the original private send. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (Control ServiceSpec initialControl)
open PqxdhRecordLiftIdeal (KeyMode CtxPrivate ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Spec FullSpec FreshBounds Mode ModeSpec asModeO)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordOriginFlatten (interpret interpret_bind interpret_pure startup install)
open RegistrationNativePlatformGatedRecordInterface (post)
variable {n : Nat} {Reader Response E S A B X Failure : Type}

abbrev State (n : Nat) (E S : Type) := CborRawRecordOriginService.State n E S

def join (result : ((((A × E) × CborRecordWorldClient.Shell) × Control n) × S)) : A × State n E S :=
  (result.1.1.1.1, (((result.1.1.1.2, result.1.1.2), result.1.2), result.2))

noncomputable def fold (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) A) : StateT (State n E S) ProbComp A := fun before =>
  join <$> interpret service codec route (work.run before.1.1.1) before.1.1.2 before.1.2 before.2

private theorem fold_run (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) A) (before : State n E S) :
    (fold service codec route work).run before =
      join <$> interpret service codec route (work.run before.1.1.1) before.1.1.2 before.1.2 before.2 := rfl

/-- Reassociation preserves the complete stateful bind, including the public platform state chosen by an earlier callback. -/
theorem fold_bind (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : StateT E (OracleComp (WorldSpec n)) A) (next : A → StateT E (OracleComp (WorldSpec n)) B) :
    fold service codec route (work >>= next) = (fold service codec route work >>= fun value => fold service codec route (next value)) := by
  funext before
  change (fold service codec route (work >>= next)).run before =
    ((fold service codec route work >>= fun value => fold service codec route (next value))).run before
  simp only [fold_run, StateT.run_bind, interpret_bind, map_bind, bind_map_left, join]

noncomputable def native (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl Spec (StateT (State n E S) ProbComp) := fun query =>
  fold service codec route (RegistrationNativePlatformGatedRecordInterface.native env reserve query)

noncomputable def full (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (serverKid : U64) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.Ledger × State n E S) ProbComp) :=
  ((native service env reserve codec route).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds)).flattenStateT

/-- The private canonical send is finished before the public post-send allocation code starts. -/
theorem native_split (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (query : Spec.Domain) :
    native service env reserve codec route query =
      (CborRawRecordOriginService.native service env codec route query >>= fun reply =>
        fold service codec route (post reserve query reply)) := by
  rw [native, RegistrationNativePlatformGatedRecordInterface.native, fold_bind]
  have original : fold service codec route (PqxdhRecordLiftInterface.native env query) =
      CborRawRecordOriginService.native service env codec route query := by
    funext before
    change (fold service codec route (PqxdhRecordLiftInterface.native env query)).run before =
      (CborRawRecordOriginService.native service env codec route query).run before
    rw [fold_run, CborRawRecordOriginService.source_run]
    rfl
  rw [original]

/-- Every adaptive continuation is the literal interpretation of the gated World request program on its joint state. -/
theorem native_program (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp Spec A) (e : E) (shell : CborRecordWorldClient.Shell) (control : Control n) (secret : S) :
    (simulateQ (native service env reserve codec route) work).run (((e, shell), control), secret) =
      join <$> interpret service codec route
        ((simulateQ (RegistrationNativePlatformGatedRecordInterface.native env reserve) work).run e) shell control secret := by
  induction work using OracleComp.inductionOn generalizing e shell control secret with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, interpret_pure, map_pure, join]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, native, fold_run, interpret_bind,
        map_bind, bind_map_left]
      apply bind_congr
      intro result
      simpa only [join, Functor.map_map] using
        ih result.1.1.1.1 result.1.1.1.2 result.1.1.2 result.1.2 result.2

/-- Startup and initial installation are unchanged; the actual gated native fold remains beneath every test/fresh ledger continuation. -/
theorem program_flat {ι KemSK : Type} {base : OracleSpec ι}
    (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : U64) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
      (RegistrationNativePlatformGatedRecordInterface.client env reserve setup.source.crypto codec serverKid bounds mode adversary) =
      (startup (ctxInterpreter modes replace setup codec) env codec route CtxPrivate.initial >>= fun born =>
        match born.1.1.1 with
        | none => pure ((none, born.1.2), born.2)
        | some (created, initial) =>
            install (ctxInterpreter modes replace setup codec) codec route created born.1.1.2 born.1.2 born.2 >>= fun installed =>
              (fun result => ((some (PqxdhRegistrationJointServerBirth.encode created,
                (result.1, result.2.1), result.2.2.1.1.1), result.2.2.1.2), result.2.2.2)) <$>
                (simulateQ (full (ctxInterpreter modes replace setup codec) env reserve setup.source.crypto codec route serverKid bounds)
                  (asModeO mode adversary)).run
                  (PqxdhDeploymentSecrecy.Ledger.empty, (((initial, installed.1.1), installed.1.2), installed.2))) := by
  have interpreted : PqxdhRecordLiftLaterWorlds.ctxRunOf modes replace setup codec route
      (RegistrationNativePlatformGatedRecordInterface.client env reserve setup.source.crypto codec serverKid bounds mode adversary) =
      (fun result => ((result.1.1.1, result.1.2), result.2)) <$>
        interpret (ctxInterpreter modes replace setup codec) codec route
          (RegistrationNativePlatformGatedRecordInterface.program env reserve setup.source.crypto codec serverKid bounds mode adversary)
          CborRecordWorldClient.initial initialControl CtxPrivate.initial := by
    simp only [PqxdhRecordLiftLaterWorlds.ctxRunOf, RegistrationNativePlatformGatedRecordInterface.client,
      PqxdhRecordLiftProtocol.schedule, CborRecordWorldClient.client, interpret, simulateQ_map, StateT.run_map]
  rw [interpreted, RegistrationNativePlatformGatedRecordInterface.program, interpret_bind, map_bind]
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
    let finish := fun result : (X × PqxdhDeploymentSecrecy.Ledger) × State n E (CtxPrivate n) =>
      ((some (PqxdhRegistrationJointServerBirth.encode created, result.1, result.2.1.1.1), result.2.1.2), result.2.2)
    have represented := congrArg (fun work => finish <$> work)
      (native_program (ctxInterpreter modes replace setup codec) env reserve codec route
        (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec serverKid bounds (asModeO mode adversary)) initial
        installed.1.1.2 installed.1.2 installed.2)
    simp only [Functor.map_map] at represented
    refine Eq.trans represented.symm ?_
    rw [PqxdhDeploymentSecrecy.wrap, OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    simp only [full, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.fold_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.fold_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.native_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.native_split

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.native_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.native_program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.program_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordFlat.program_flat

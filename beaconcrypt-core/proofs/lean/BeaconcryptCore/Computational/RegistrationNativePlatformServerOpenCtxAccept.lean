-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxProgram
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! The actual corrected OPEN accept controller runs through the explicit CTX dictionary and the real shared public reservation. Source compilation preserves complete public material, Environment, private provider/pool/Extra and platform states. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformCtxRunner (M Full interpret)
open RegistrationNativePlatformServerOpenCtxKernel (Callbacks Transport extended nativeExtended)
attribute [local irreducible] RegistrationNativePlatformServerOpenSyntax.accept
variable {n : Nat} {ι KemSK Extra Platform : Type} {base : OracleSpec ι}

abbrev State (n : Nat) (KemSK Extra : Type) := RegistrationNativePlatformServerOpenControl.State n KemSK Extra
abbrev AstValue := (RustM (Option Nat) × RegistrationServerMaterialFrontend.State) × RegistrationServerReferenceCompiler.Environment

def assemble (result : AstValue × Private n KemSK Extra) : RustM (Option Nat) × State n KemSK Extra :=
  (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))

section
variable {m : Type → Type} [Monad m] [LawfulMonad m]
theorem controller_syntax (handler : QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) (StateT (Private n KemSK Extra) m))
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : State n KemSK Extra) :
    (RegistrationNativePlatformServerOpenControl.close (RegistrationNativePlatformServerOpenControl.accept
      (RegistrationNativePlatformServerOpenSyntax.implementation handler) (handler (.inr ())) setup checks verify packet)).run before =
      assemble <$> (simulateQ handler (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run before.1).run before.2.1)).run before.2.2 := by
  have natural := RegistrationNativePlatformServerOpenSyntax.accept_source handler setup checks verify packet
  have closed := congrArg (fun work => RegistrationNativePlatformServerOpenControl.close (n := n) (KemSK := KemSK) (Extra := Extra) work) natural
  rw [← closed]
  simp only [RegistrationNativePlatformServerOpenControl.close,
    RegistrationNativePlatformServerOpenKernel.closeEnvironment, RegistrationNativePlatformServerOpenSyntax.evaluate,
    StateT.run, Functor.map_map]
  rfl

end

noncomputable def accept (callbacks : Callbacks n KemSK Extra Platform) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) :
    M (State n KemSK Extra) Platform (RustM (Option Nat)) :=
  RegistrationNativePlatformServerOpenControl.close (RegistrationNativePlatformServerOpenControl.accept
    (RegistrationNativePlatformServerOpenCtxKernel.handler callbacks)
    (RegistrationNativePlatformCtxRunner.publicWork reserve) setup checks verify packet)

def realize (before : Full (State n KemSK Extra) Platform) : State n KemSK Extra × Platform :=
  ((before.1.1.1, (before.1.1.2.1, RegistrationNativePlatformServerOpenCtxEffects.replace before.2.1 before.1.1.2.2)), before.1.2)

def privateBefore (before : Full (State n KemSK Extra) Platform) : Full (Private n KemSK Extra) Platform :=
  ((before.1.1.2.2, before.1.2), before.2)

def reassemble (result : AstValue × Full (Private n KemSK Extra) Platform) :
    RustM (Option Nat) × Full (State n KemSK Extra) Platform :=
  (result.1.1.1, (((result.1.1.2, (result.1.2, result.2.1.1)), result.2.1.2), result.2.2))

def nativeReassemble (result : AstValue × (Private n KemSK Extra × Platform)) :
    RustM (Option Nat) × (State n KemSK Extra × Platform) :=
  (result.1.1.1, ((result.1.1.2, (result.1.2, result.2.1)), result.2.2))

theorem syntax_run (callbacks : Callbacks n KemSK Extra Platform) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : State n KemSK Extra) :
    (accept callbacks reserve setup checks verify packet).run before =
      assemble <$> (simulateQ (extended callbacks reserve)
        (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run before.1).run before.2.1)).run before.2.2 := by
  exact controller_syntax (extended callbacks reserve) setup checks verify packet before

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

theorem interpret_syntax (callbacks : Callbacks n KemSK Extra Platform) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : Full (State n KemSK Extra) Platform) :
    (interpret (accept callbacks reserve setup checks verify packet)).run before =
      reassemble <$> (interpret (simulateQ (extended callbacks reserve)
        (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run before.1.1.1).run before.1.1.2.1))).run (privateBefore before) := by
  change (fun result => (result.1.1.1, ((result.1.1.2, result.1.2), result.2))) <$>
    (simulateQ RegistrationNativePlatformCtxBackend.implementation
      (((accept callbacks reserve setup checks verify packet).run before.1.1).run before.1.2)).run before.2 = _
  rw [syntax_run]
  simp only [interpret, simulateQ_map, Functor.map_map,
    StateT.run, state_map_apply, reassemble, privateBefore]
  rfl

theorem physical_source (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (callbacks : Callbacks n KemSK Extra Platform)
    (native : RegistrationNativePlatformServerOpenKernel.Callbacks n KemSK Extra (StateT Platform ProbComp))
    (transport : Transport setup callbacks native) (reserve : StateT Platform ProbComp Bool)
    (before : Full (State n KemSK Extra) Platform) :
    Prod.map id realize <$> (interpret (accept callbacks reserve setup checks verify packet)).run before =
      (RegistrationAgreementNestedState.flatten (RegistrationNativePlatformServerOpenControl.close
        (RegistrationNativePlatformServerOpenControl.accept
          (RegistrationNativePlatformServerOpenKernel.handler RegistrationNativePlatformMldsaProgram.coins setup native)
          (StateT.lift reserve) setup checks verify packet))).run (realize before) := by
  rw [interpret_syntax, Functor.map_map]
  have source := RegistrationNativePlatformServerOpenCtxProgram.accept_program setup checks verify packet callbacks native transport reserve
    before.1.1.1 before.1.1.2.1 (privateBefore before)
  have mapped := congrArg (fun work => nativeReassemble <$> work) source
  have nativeSyntax := controller_syntax (nativeExtended setup native reserve) setup checks verify packet (realize before).1
  have canonical : RegistrationNativePlatformServerOpenSyntax.implementation (nativeExtended setup native reserve) =
      RegistrationNativePlatformServerOpenKernel.handler RegistrationNativePlatformMldsaProgram.coins setup native := by
    funext query
    rfl
  rw [canonical] at nativeSyntax
  dsimp only [nativeExtended] at nativeSyntax
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (((RegistrationNativePlatformServerOpenControl.close (RegistrationNativePlatformServerOpenControl.accept
      (RegistrationNativePlatformServerOpenKernel.handler RegistrationNativePlatformMldsaProgram.coins setup native)
      (StateT.lift reserve) setup checks verify packet)).run (realize before).1).run (realize before).2)
  rw [nativeSyntax]
  simp only [StateT.run_map, Functor.map_map, assemble]
  simpa only [Functor.map_map, RegistrationAgreementNestedState.flatten, StateT.run,
    nativeReassemble, realize, reassemble, privateBefore, RegistrationNativePlatformServerOpenCtxEffects.realize,
    Prod.map_def, id_eq] using mapped

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.controller_syntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.controller_syntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.syntax_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.syntax_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.interpret_syntax' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.interpret_syntax

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.physical_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenCtxAccept.physical_source

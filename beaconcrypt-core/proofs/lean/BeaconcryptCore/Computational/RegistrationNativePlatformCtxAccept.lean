-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptSdk
/-! Literal non-Beacon Context acceptance exposes the actual repeated pin and authentication hashes through the common backend. It retains all Context fields, current KEM pool, complete SDK token state, raw receipt coordinates, physical hash journal, true counters and the same persistent platform state. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformCtxContext (M Full interpret realize)
variable {n : Nat} {I KemSK Reader Response Platform E : Type} {base : OracleSpec I}

def increment (before : Context n KemSK × Platform) : Context n KemSK × Platform :=
  ({before.1 with parsedAccepts := before.1.parsedAccepts + 1}, before.2)

noncomputable def accept (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) : M n KemSK Platform (RustM (Option Nat)) :=
  fun before => (RegistrationNativePlatformCtxBuild.server
    (RegistrationNativePlatformCtxAcceptSdk.accept setup checks reserve verify representation created packet)).run (increment before)

/-- The actual parse-attempt increment and full SDK source accept share one physical backend, preserving the same Context and P. -/
theorem accept_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (accept setup checks reserve verify representation created packet)).run before =
      (RegistrationNativePlatformCtxBuild.nativeServer
        (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup codec checks reserve route verify
          representation created packet)).run (increment (realize before)) := by
  have same := RegistrationNativePlatformCtxBuild.server_source _ _
    (RegistrationNativePlatformCtxAcceptSdk.accept_source setup codec checks reserve route verify representation created packet)
    (increment before.1, before.2)
  simpa only [accept, increment, interpret, realize, RegistrationNativePlatformIdentityCtxAmbient.replace,
    StateT.run] using same

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m] (change : S → S) (before : S) :
    (modify change : StateT S m Unit) before = pure ((), change before) := rfl
private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
variable (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

private theorem handler_accept (packet : registration.InitPacket) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (Sum.inr (RegistrationNativeRawAdapter.Command.accept packet)) = (do
        modify fun before => {before with parsedAccepts := before.parsedAccepts + 1}
        RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformSourceAccept.accept RegistrationNativePlatformMldsaProgram.coins setup
            (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks reserveRegistration
            route source.verify representation created packet)) := by
  rfl

attribute [local irreducible] RegistrationNativePlatformIdentityMainAmbient.command

/-- The exact current-runtime Context accept command is recovered without a public-reference state identification or whole-handler premise. -/
theorem runtime_source (owners : RegistrationNativeIdentityFrontend.State source) (packet : registration.InitPacket)
    (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (accept setup checks reserveRegistration source.verify representation created packet)).run before =
      (RegistrationNativePlatformIdentityMainAmbient.command (n := n) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (RegistrationNativeRawAdapter.Command.accept packet)) owners).run
          (realize before) := by
  have same := accept_source setup
    (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)) checks reserveRegistration
    route source.verify representation created packet before
  apply same.trans
  simp only [RegistrationNativePlatformCtxBuild.nativeServer, increment, RegistrationNativePlatformIdentityMainAmbient.command,
    handler_accept, RegistrationNativePlatformExperiment.server, StateT.run, state_bind_apply, state_pure_apply, state_map_apply,
    state_modify_apply, pure_bind, Functor.map_map, RegistrationNativeIdentityMainOrdinary.attach,
    RegistrationNativeIdentityWorld.project, Prod.map_def, id_eq]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept.accept_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept.runtime_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept.runtime_source

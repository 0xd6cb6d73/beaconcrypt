-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemSdkCompiler

/-! A selected parsed accept opens the actual SDK callback after incrementing the separate parsed-attempt counter. This is an equality of complete reached native states under the explicit uniform-count projection, with the entire generated KEM pool retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemAcceptCompiler
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeKemServerState (State mask)
open RegistrationNativeKemServerCompiler (project)
open RegistrationNativeKemServerInterface (source)
variable {ι KemSK Reader Response : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def increment (state : State n mlSource) : State n mlSource :=
  { state with parsedAccepts := state.parsedAccepts + 1 }

private theorem modify_run (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (change : State n mlSource → State n mlSource) (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    (simulateQ (source setup codec checks route verify representation created)
      (RegistrationNativeKemServerInterface.modify change)).run before =
      pure ((), (mask (change (mask before.1)), before.2)) := by
  simp only [RegistrationNativeKemServerInterface.modify, simulateQ_bind, StateT.run_bind]
  simp only [RegistrationNativeKemServerInterface.get, RegistrationNativeKemServerInterface.put,
    simulateQ_spec_query, source, RegistrationNativeKemInterface.source,
    RegistrationNativeKemServerInterface.other, StateT.run, map_pure, pure_bind]

/-- The selected parsed-attempt increment precedes every actual SDK failure while remaining distinct from the encapsulation-getter index. -/
theorem typed_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n mlSource × PqxdhLiveKemBirth.Pool KemSK) :
    Prod.map id project <$>
        (RegistrationNativeKemSdkCompiler.server
          (RegistrationServerSdkSource.accept setup codec checks route verify representation created packet)).run
            (increment before.1, before.2) =
      (simulateQ (source setup codec checks route verify representation created)
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet)).run (project before) := by
  have law := RegistrationNativeKemSdkCompiler.accept_source setup codec checks route verify representation created packet
    (increment before.1, before.2)
  simp only [RegistrationNativeKemServerInterface.typedAccept, simulateQ_bind, StateT.run_bind]
  rw [modify_run]
  simp only [pure_bind]
  simpa only [project, increment, mask, RegistrationNativeKemServerState.maskServer,
    RegistrationNativeKemWorldUniform.mask_idempotent] using law

def nativeProject (state : RegistrationNativeExperiment.State n KemSK mlSource) :
    State n mlSource × PqxdhLiveKemBirth.Pool KemSK :=
  (RegistrationNativeKemServerState.project state, state.pool)

attribute [local irreducible] RegistrationServerSdkSource.accept

/-- The concrete source dispatcher itself, including its parsed-attempt counter and original failed replies, opens the selected actual SDK getter through the lower service. -/
theorem handler_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (credential : RegistrationNativeMldsa.Credential mlSource) (packet : registration.InitPacket)
    (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    Prod.map id nativeProject <$>
        (RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential
          (.inr (.accept packet))).run before =
      (simulateQ (source setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify representation created)
        (RegistrationNativeKemServerInterface.typedAccept setup checks packet)).run (nativeProject before) := by
  have law := typed_source setup (RegistrationNativeWire.ledgerCodec wire) checks route mlSource.verify representation created packet
    (RegistrationNativeKemServerState.ofNative before, before.pool)
  simp only [RegistrationNativeExperiment.handler, StateT.run_bind, StateT.run_modify, pure_bind]
  simp only [RegistrationNativeExperiment.server, RegistrationNativeKemSdkCompiler.server, StateT.run,
    Functor.map_map, Prod.map, id_eq, nativeProject,
    RegistrationNativeKemServerState.project, RegistrationNativeKemServerState.ofNative, project, increment, mask] at law ⊢
  convert law using 1 <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeKemAcceptCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemAcceptCompiler.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemAcceptCompiler.typed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemAcceptCompiler.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemAcceptCompiler.handler_source

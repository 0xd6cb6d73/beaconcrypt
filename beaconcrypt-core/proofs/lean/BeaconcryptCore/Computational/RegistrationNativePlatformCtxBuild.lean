-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdk
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxContext
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityMainAmbient
/-! The complete source build is exposed as an ordinary Context/platform callback on the same physical CTX backend. Its current native typed callback is recovered with exact returned bytes and full source state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeIdentityWorld (Context)
open RegistrationNativePlatformCtxContext (M Full interpret realize)
variable {n : Nat} {I KemSK Reader Response Platform E A : Type} {base : OracleSpec I}

def server (work : RegistrationNativePlatformCtxRunner.M (RegistrationServerFrontendCompiler.State n) Platform A) :
    M n KemSK Platform A := fun before =>
  (fun result => (result.1.1, ({before.1 with server := result.1.2}, result.2))) <$>
    (work.run before.1.server).run before.2

def nativeServer (work : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) A) :
    StateT (Context n KemSK × Platform) ProbComp A := fun before =>
  (fun result => (result.1.1, ({before.1 with server := result.1.2}, result.2))) <$>
    (work.run before.1.server).run before.2

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The literal SDK source callback retains every Context field and native/platform poststate through the common physical backend. -/
theorem server_source (left : RegistrationNativePlatformCtxRunner.M (RegistrationServerFrontendCompiler.State n) Platform A)
    (right : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) A)
    (coupled : RegistrationNativePlatformCtxSdkCoupling.Coupled left right) (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (server left)).run before = (nativeServer right).run (realize before) := by
  have same := congrArg (fun distribution => (fun result =>
    (result.1, ({(realize before).1 with server := result.2.1}, result.2.2))) <$> distribution)
    (coupled ((before.1.1.server, before.1.2), before.2))
  simpa only [server, nativeServer, interpret, RegistrationNativePlatformCtxRunner.interpret,
    RegistrationNativePlatformPackedState.pack, StateT.run, simulateQ_map, state_map_apply, Functor.map_map,
    realize, RegistrationNativePlatformCtxSdkCoupling.realize, RegistrationNativePlatformCtxSdkCoupling.replace,
    RegistrationNativePlatformIdentityCtxAmbient.replace, RegistrationNativePlatformCtxLocal.attach,
    RegistrationNativePlatformCtxCacheFrame.replace, Prod.map_def, id_eq] using same

def publicResult (result : RustM (Option (U64 × alloc.vec.Vec U8))) : RustM (Option (U64 × Pqxdh.Bytes)) := do
  let optional ← result
  .ok (optional.map fun value => (value.1, TranscriptAuthParts.absSlice value.2))

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (codec : Codec Reader Response)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (erased : commitment.CommitmentTranscript)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def build (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8)) :
    M n KemSK Platform (RustM (Option (U64 × Pqxdh.Bytes))) :=
  publicResult <$> server (RegistrationNativePlatformCtxSdk.build setup codec view failure allocation erased sign helper writer reserve handle application)

/-- The actual source build returns the same public bytes, private KEM pool, native counters and P, with all failed prefixes retained. -/
theorem build_source (reserve : StateT Platform ProbComp Bool) (handle : Nat) (application : Option (Slice U8))
    (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (build setup codec view failure allocation erased sign helper writer reserve handle application)).run before =
      (publicResult <$> nativeServer
        (RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup codec view failure allocation erased reserve sign helper writer handle application)).run (realize before) := by
  have same := congrArg (fun distribution => Prod.map publicResult id <$> distribution)
    (server_source _ _ (RegistrationNativePlatformCtxSdk.build_source setup codec view failure allocation erased sign helper writer reserve handle application) before)
  simpa only [build, interpret, StateT.run, simulateQ_map, state_map_apply, Functor.map_map,
    RegistrationNativePlatformSourceSeal.build, Prod.map_def, id_eq] using same

omit primitive in
private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

omit primitive in
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem handler_build (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (handle : Nat) (application : Option (Slice U8)) :
    RegistrationNativePlatformOrdinaryExperiment.handler (n := n) setup checks wire route representation created source credential
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (Sum.inr (RegistrationNativeRawAdapter.Command.build handle application)) = (do
        let result ← RegistrationNativePlatformExperiment.server
          (RegistrationNativePlatformSourceSeal.build RegistrationNativePlatformMldsaProgram.coins setup
            (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
            view failure allocation erased reservePeer (RegistrationNativeMldsa.owned source credential) helper writer handle application)
        pure (publicResult result)) := by
  rfl

attribute [local irreducible] RegistrationNativePlatformIdentityMainAmbient.command

/-- The exact current-runtime non-Beacon build callback is obtained without public-root-reference or whole-handler premises. -/
theorem runtime_source (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (source : RegistrationNativeMldsa.Source)
    (credential : RegistrationNativeMldsa.Credential source)
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (owners : RegistrationNativeIdentityFrontend.State source)
    (handle : Nat) (application : Option (Slice U8)) (before : Full n KemSK Platform) :
    Prod.map id realize <$> (interpret (build setup
      (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
      view failure allocation erased (RegistrationNativeMldsa.owned source credential) helper writer reservePeer handle application)).run before =
      (RegistrationNativePlatformIdentityMainAmbient.command (n := n) (source := source) setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer (Sum.inr (RegistrationNativeRawAdapter.Command.build handle application)) owners).run (realize before) := by
  have same := build_source setup (RegistrationNativeWire.ledgerCodec (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire))
    view failure allocation erased (RegistrationNativeMldsa.owned source credential) helper writer reservePeer handle application before
  apply same.trans
  simp only [nativeServer, publicResult, RegistrationNativePlatformIdentityMainAmbient.command,
    handler_build,
    RegistrationNativePlatformExperiment.server, StateT.run, state_bind_apply, state_pure_apply, state_map_apply,
    bind_pure_comp, Functor.map_map, RegistrationNativeIdentityMainOrdinary.attach,
    RegistrationNativeIdentityWorld.project, Prod.map_def, id_eq]
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild.server_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild.server_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild.runtime_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxBuild.runtime_source

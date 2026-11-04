-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptFrame
/-! Literal incoming authentication exposes each actual hash address to the common CTX backend. Actual ML/Ed verification operands are retained, while the complete SDK state, original signing receipts and external platform state survive every result. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformCtxRunner (M Full interpret privateWork)
open RegistrationNativePlatformCtxSdkCoupling (Coupled Native replace realize pure_source bind_source)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {I KemSK Reader Response Platform A B : Type} {base : OracleSpec I}

noncomputable def hash (bytes : Pqxdh.Bytes) : M (State n) Platform CtxRomAuth.CtxDigest :=
  RegistrationNativePlatformCtxSdk.world (privateWork (RegistrationNativePlatformCtxLocal.effects (.inr (.hash bytes))))

noncomputable def nativeHash (bytes : Pqxdh.Bytes) : Native n Platform CtxRomAuth.CtxDigest :=
  RegistrationNativePlatformServerSdk.world
    (RegistrationNativePlatformServerCompletion.capability RegistrationNativePlatformMldsaProgram.coins (.hash bytes))

/-- One literal incoming hash has the actual physical source cache/count interpretation. -/
theorem hash_source (bytes : Pqxdh.Bytes) : Coupled (hash (n := n) (Platform := Platform) bytes) (nativeHash bytes) :=
  RegistrationNativePlatformCtxSdk.world_source _ _ (RegistrationNativePlatformCtxPin.capability_source (.hash bytes))

def withWorld (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp A) : Native n Platform A := fun before previous =>
  (fun result => ((result.1, {before with world := {before.world with world := (result.2, before.world.world.2)}}), previous)) <$>
    work.run before.world.world.1

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (do let value ← work; pure (value, before)) := rfl

private theorem world_program {Q : Type} {queries : OracleSpec Q}
    (implementation : QueryImpl queries (StateT (PqxdhRecordLiftWorld.State n) ProbComp))
    (work : OracleComp queries A) :
    simulateQ (fun query => withWorld (Platform := Platform) (implementation query)) work =
      withWorld (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => funext before previous; simp only [simulateQ_pure, withWorld, StateT.run_pure, map_pure]; rfl
  | query_bind query next ih =>
    funext before previous
    simp only [simulateQ_bind, simulateQ_spec_query, ih, withWorld, StateT.run_bind, state_bind_apply,
      bind_map_left, map_bind]

noncomputable def callbacks (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (M (State n) Platform)
  | .hash request => do
      let digest ← hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 crypto request)

noncomputable def nativeCallbacks (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify) :
    QueryImpl RegistrationAuthenticationExecutor.Spec (Native n Platform)
  | .hash request => do
      let digest ← nativeHash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)
      pure (.Some (RegistrationAuthenticationShared.digestArray digest))
  | .mldsa request => pure (RegistrationAuthenticationShared.verifyMldsa verify request)
  | .ed25519 request => pure (RegistrationAuthenticationShared.verifyEd25519 crypto request)

/-- Each real verification leaf either performs its exact shared hash or the literal deterministic ML/Ed check. -/
theorem callback_source (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) :
    Coupled (callbacks (n := n) (Platform := Platform) crypto verify query) (nativeCallbacks crypto verify query) := by
  cases query with
  | hash request => exact bind_source _ _ _ _ (hash_source _) (fun _ => pure_source _)
  | mldsa request | ed25519 request => exact pure_source _

private theorem simulate_source {Q : Type} {queries : OracleSpec Q}
    (left : QueryImpl queries (M (State n) Platform)) (right : QueryImpl queries (Native n Platform))
    (leaves : ∀ query, Coupled (left query) (right query)) (work : OracleComp queries A) :
    Coupled (simulateQ left work) (simulateQ right work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_source _
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact bind_source _ _ _ _ (leaves query) ih

private theorem native_callbacks (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) :
    nativeCallbacks (n := n) (Platform := Platform) setup.source.crypto verify query =
      withWorld (RegistrationWorldAuthentication.implementation setup codec route verify query) := by
  cases query <;> funext before previous
  all_goals simp only [nativeCallbacks, nativeHash, RegistrationWorldAuthentication.implementation,
    QueryImpl.apply_compose, RegistrationWorldAuthentication.callbacks, simulateQ_map, simulateQ_spec_query,
    simulateQ_pure, PqxdhRecordLiftWorld.handler, withWorld, RegistrationNativePlatformServerSdk.world,
    RegistrationNativePlatformServerCompletion.capability, RegistrationNativePlatformServerCompletion.liftNative,
    RegistrationWorldServerCompletion.capability, RegistrationNativePlatformMldsaProgram.lift_coins,
    StateT.run, state_bind_apply, state_pure_apply, state_map_apply, state_lift_apply, bind_pure_comp, Functor.map_map, map_pure, Prod.map_def, id_eq]

  all_goals rfl

noncomputable def authenticate (setup : Setup base KemSK) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) : M (State n) Platform
      (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) :=
  simulateQ (callbacks setup.source.crypto verify) (RegistrationAuthenticationExecutor.begin pin packet)

/-- The complete actual incoming authentication is recovered, retaining the current World and both local and compact receipt coordinates. -/
theorem authenticate_source (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Coupled (authenticate (n := n) (Platform := Platform) setup verify pin packet)
      (RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins setup codec route verify pin packet) := by
  have initial := simulate_source (n := n) (Platform := Platform) (callbacks setup.source.crypto verify) (nativeCallbacks setup.source.crypto verify)
    (callback_source (n := n) (Platform := Platform) setup.source.crypto verify) (RegistrationAuthenticationExecutor.begin pin packet)
  have nativeEquation : simulateQ (nativeCallbacks (n := n) (Platform := Platform) setup.source.crypto verify)
      (RegistrationAuthenticationExecutor.begin pin packet) =
      RegistrationNativePlatformSourceAccept.authenticate RegistrationNativePlatformMldsaProgram.coins setup codec route verify pin packet := by
    have leaves : nativeCallbacks (n := n) (Platform := Platform) setup.source.crypto verify =
        (fun query => withWorld (RegistrationWorldAuthentication.implementation setup codec route verify query)) :=
      funext (native_callbacks setup codec route verify)
    rw [leaves, world_program]
    funext before previous
    simp only [RegistrationWorldAuthentication.implementation, ← QueryImpl.simulateQ_compose,
      RegistrationWorldAuthentication.begin, RegistrationWorldAuthentication.program,
      withWorld, RegistrationNativePlatformSourceAccept.authenticate, StateT.run,
      RegistrationNativePlatformMldsaProgram.lift_coins, state_map_apply, state_lift_apply, bind_pure_comp, Functor.map_map]
    rfl
  exact nativeEquation ▸ initial

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication.hash_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication.hash_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication.callback_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication.callback_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication.authenticate_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptAuthentication.authenticate_source

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAgreement
import BeaconcryptCore.Computational.RegistrationServerReferenceSourceAccept
import BeaconcryptCore.Computational.RegistrationAuthenticationCoinProjection
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The public root-reference accept controller recomputes the actual pin, authenticates, checks owned replay and runs the caller's stateful reservation before its unchanged primitive prefix and root-reference preparation. It stores only public Ready capabilities and retains all shared effects on every failure. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept
open PqxdhServerAuthExperiment (Setup Checks Codec)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationServerReferenceRoot (Ready PrepareSpec)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

abbrev PublicM (m : Type → Type) [Monad m] := StateT RegistrationServerMaterialFrontend.State (StateT Environment m)

def retain (ready : Ready) : PublicM m (RustM (Option Nat)) := fun before =>
  match RegistrationServerMaterialFrontend.retain ready before with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (reply, after) => pure (.ok reply, after)

noncomputable def afterAuthentication (effects : QueryImpl (EnvEffects n) m) (prepare : QueryImpl PrepareSpec m)
    (reserve : m Bool) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : PublicM m (RustM (Option Nat)) := do
  let before ← get
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else do
    let admitted ← StateT.lift (StateT.lift reserve)
    if admitted then do
      let accepted ← RegistrationNativePlatformServerReferencePrefix.agreement effects prepare setup checks packet authenticated
      match accepted with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok none => pure (.ok none)
      | .ok (some ready) => retain ready
    else pure (.ok none)

def hash (effects : QueryImpl (EnvEffects n) m) : QueryImpl RegistrationNativeServerPinRecompute.Spec m := fun request => do
  let digest ← effects (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))
  pure (.ok (.Some (RegistrationAuthenticationShared.digestArray digest)))

def pin (effects : QueryImpl (EnvEffects n) m) (before : session.ServerAuthenticationPin) : m RegistrationNativeServerPinRecompute.PinReply :=
  simulateQ (hash effects) (RegistrationNativeServerPinRecompute.program before.binding before.public_key)

noncomputable def afterPin (effects : QueryImpl (EnvEffects n) m) (prepare : QueryImpl PrepareSpec m) (reserve : m Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (result : RegistrationNativeServerPinRecompute.PinReply) : PublicM m (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok none)
  | .ok (.Some pin) => do
    let checked ← StateT.lift (StateT.lift (simulateQ effects (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)))
    match checked with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok (_events, .Accepted authenticated) => afterAuthentication effects prepare reserve setup checks packet authenticated
    | .ok _ => pure (.ok none)

noncomputable def accept (effects : QueryImpl (EnvEffects n) m) (prepare : QueryImpl PrepareSpec m) (reserve : m Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) : PublicM m (RustM (Option Nat)) := do
  let before ← get
  let current ← StateT.lift (StateT.lift (pin effects before.pin))
  afterPin effects prepare reserve setup checks verify packet current

abbrev State (n : Nat) := RegistrationServerMaterialFrontend.State × RegistrationServerReferenceCompilerNative.Local n

def project (roots : RegistrationServerReferenceRestore.Roots) (before : State n) : RegistrationServerFrontendCompiler.State n :=
  RegistrationServerReferenceRestore.restore roots before.1 (RegistrationWorldAgreementProgramCompiler.project before.2)

def close (work : PublicM (StateT (PqxdhRecordLiftWorld.State n) m) Value) : StateT (State n) m Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativePlatformServerReferencePrefix.closeEnvironment (work.run before.1)).run before.2

theorem close_bind
    (work : PublicM (StateT (PqxdhRecordLiftWorld.State n) m) Value)
    (next : Value → PublicM (StateT (PqxdhRecordLiftWorld.State n) m) Next) :
    close (work >>= next) = (close work >>= fun value => close (next value)) := by
  funext before
  simp only [close, StateT.run, StateT.monad_bind_def, StateT.bind,
    RegistrationNativePlatformServerReferencePrefix.closeEnvironment, map_bind, bind_map_left]

theorem close_pure (value : Value) (before : State n) :
    (close (pure value : PublicM (StateT (PqxdhRecordLiftWorld.State n) m) Value)).run before = pure (value, before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (pure (((value, before.1), before.2.1), before.2.2) : m _)) = _
  simp only [map_pure]

theorem close_get (before : State n) :
    (close (get : PublicM (StateT (PqxdhRecordLiftWorld.State n) m) RegistrationServerMaterialFrontend.State)).run before =
      pure (before.1, before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (pure (((before.1, before.1), before.2.1), before.2.2) : m _)) = _
  simp only [map_pure]


def sourceState (before : State n) : RegistrationServerReferenceSourceRetain.State n :=
  (before.1, RegistrationWorldAgreementProgramCompiler.project before.2)

theorem agree_source (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n) :
    Prod.map id sourceState <$>
      (close (RegistrationNativePlatformServerReferencePrefix.agreement
        (RegistrationNativePlatformServerReferencePrefix.effects coins)
        (RegistrationNativePlatformServerReferenceAgreement.prepareSource setup seed scalar)
        setup checks packet authenticated)).run before =
      simulateQ coins ((RegistrationServerReferenceSourceAccept.agree setup checks seed scalar packet authenticated).run (sourceState before)) := by
  have compared := congrArg (fun work => (fun result => (result.1, (before.1, result.2))) <$> work)
    (RegistrationNativePlatformServerReferenceAgreement.agreement_source coins setup checks seed scalar packet authenticated before.2)
  simpa only [close, sourceState, RegistrationNativePlatformServerReferencePrefix.agreement_factor,
    RegistrationNativePlatformServerReferencePrefix.closeEnvironment, RegistrationServerReferenceSourceAccept.agree,
    StateT.run, StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure,
    map_bind, map_pure, bind_pure_comp, simulateQ_map, Functor.map_map, Prod.map_def, id_eq] using compared


theorem agree_native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n)
    (fresh : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    Prod.map (RegistrationServerReferenceSourceClient.restore
      (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar))
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (RegistrationNativePlatformServerReferencePrefix.agreement
        (RegistrationNativePlatformServerReferencePrefix.effects coins)
        (RegistrationNativePlatformServerReferenceAgreement.prepareSource setup created.seed scalar)
        setup checks packet authenticated)).run before =
    simulateQ coins ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before)) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  have mapped := congrArg (fun work => Prod.map (RegistrationServerReferenceSourceClient.restore roots)
      (RegistrationServerReferenceSourceRetain.project roots) <$> work)
    (agree_source coins setup checks created.seed scalar packet authenticated before)
  have rooted := congrArg (simulateQ coins)
    (RegistrationServerReferenceSourceAccept.agree_native setup checks representation correct created scalar packet authenticated
      (sourceState before) fresh)
  rw [simulateQ_map] at rooted
  have compared := mapped.trans rooted
  simpa only [Functor.map_map, Prod.map_def, id_eq, project, sourceState,
    RegistrationServerReferenceSourceRetain.project, roots] using compared

theorem retain_native (coins : QueryImpl unifSpec m) (roots : RegistrationServerReferenceRestore.Roots)
    (ready : Ready) (before : State n) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) :
    Prod.map id (project roots) <$> (close (retain ready)).run before =
      simulateQ coins ((RegistrationServerNativeSource.retain created
        (RegistrationServerReferenceRoot.atRoot ready (roots ready.reference))).run (project roots before)) := by
  have compared := congrArg (simulateQ coins)
    (RegistrationServerReferenceSourceRetain.retain_native roots ready (sourceState before) created)
  unfold RegistrationServerReferenceSourceRetain.retain at compared
  cases retained : RegistrationServerMaterialFrontend.retain ready before.1 with
  | fail error | div =>
    simpa only [retained, close, retain, RegistrationNativePlatformServerReferencePrefix.closeEnvironment,
      StateT.run, StateT.monad_pure_def, StateT.pure, map_pure, simulateQ_pure,
      project, sourceState, RegistrationServerReferenceSourceRetain.project, Prod.map_def, id_eq] using compared
  | ok pair =>
    rcases pair with ⟨reply, current⟩
    simpa only [retained, close, retain, RegistrationNativePlatformServerReferencePrefix.closeEnvironment,
      StateT.run, StateT.monad_pure_def, StateT.pure, map_pure, simulateQ_pure,
      project, sourceState, RegistrationServerReferenceSourceRetain.project, Prod.map_def, id_eq] using compared


theorem close_reserve (work : m Value) (before : State n) :
    (close (StateT.lift (StateT.lift (StateT.lift work)) : PublicM (StateT (PqxdhRecordLiftWorld.State n) m) Value)).run before =
      (fun value => (value, before)) <$> work := by
  simp only [close, RegistrationNativePlatformServerReferencePrefix.closeEnvironment, StateT.run,
    StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure,
    bind_pure_comp, Functor.map_map]

private theorem sdk_run (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (reserve : m Bool) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerFrontendCompiler.State n) :
    (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated).run before =
      (if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
       else do
         let admitted ← reserve
         if admitted then do
           let completed ← simulateQ coins ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)
           match completed.1 with
           | .fail error => pure (.fail error, completed.2)
           | .div => pure (.div, completed.2)
           | .ok (.ServerComplete accepted) => simulateQ coins ((RegistrationServerNativeSource.retain created accepted).run completed.2)
           | .ok _ => pure (.ok none, completed.2)
         else pure (.ok none, before)) := by
  simp only [RegistrationNativePlatformServerSdk.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · rw [StateT.run_bind, StateT.run_lift]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      rw [StateT.run_bind]
      apply bind_congr
      rintro ⟨completed, current⟩
      cases completed with
      | fail error | div => rfl
      | ok effect => cases effect <;> rfl

theorem after_native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (reserve : m Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (afterAuthentication (RegistrationNativePlatformServerReferencePrefix.effects coins)
        (RegistrationNativePlatformServerReferenceAgreement.prepareSource setup created.seed scalar)
        (StateT.lift reserve) setup checks packet authenticated)).run before =
    (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated).run
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  change Prod.map id (project roots) <$> _ =
    (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve) representation created packet authenticated).run (project roots before)
  unfold afterAuthentication
  rw [close_bind, StateT.run_bind, close_get, pure_bind, sdk_run]
  have consumed : (project roots before).consumed = before.1.consumed := rfl
  rw [consumed]
  by_cases replayed : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ↓reduceIte, close_pure, map_pure]
    rfl
  · have fresh := Bool.eq_false_iff.mpr replayed
    simp only [fresh, Bool.false_eq_true, ↓reduceIte]
    rw [close_bind, StateT.run_bind, close_reserve, map_bind, bind_map_left]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, close_pure, map_pure]; rfl
    | true =>
      simp only [↓reduceIte]
      rw [close_bind, StateT.run_bind, map_bind,
        ← agree_native coins setup checks representation correct created scalar packet authenticated before fresh, bind_map_left]
      apply bind_congr
      rintro ⟨accepted, current⟩
      cases accepted with
      | fail error | div => simp only [close_pure, map_pure, Prod.map_def, id_eq, RegistrationServerReferenceSourceClient.restore, roots]
      | ok accepted => cases accepted with
        | none => simp only [close_pure, map_pure, Prod.map_def, id_eq, RegistrationServerReferenceSourceClient.restore, roots]
        | some ready => exact retain_native coins roots ready current created

end BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_get
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.agree_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.agree_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.agree_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.agree_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.retain_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.retain_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.close_reserve
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.after_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerReferenceAccept.after_native

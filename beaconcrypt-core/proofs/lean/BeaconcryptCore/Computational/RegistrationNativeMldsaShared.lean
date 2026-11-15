-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeExperiment
import BeaconcryptCore.Computational.RegistrationBeaconInitHistory
import BeaconcryptCore.Computational.RegistrationNativeScalarSource

/-! Actual native outgoing Init callbacks preserve the existing Server signing receipts and extend the shared CTX cache only through their request transcript hash. The projection forgets private counters, local phases and Ed histories; it never creates an independent cache or resets the native World. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaShared
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeBeaconFrontend (Owner)
open RegistrationSigningShared (SignReply)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev Local (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeBeaconFrontend.State source ×
    (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State ×
      RegistrationNativeExperiment.State n KemSK source)

def project (before : Local n KemSK source) : RegistrationSigningShared.State :=
  (before.2.1.receipts, before.2.2.server.world.world.1.primitive.2)

noncomputable def lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value) :
    StateT (Local n KemSK source) ProbComp Value := fun before =>
  (fun result => (result.1.1.1, (result.1.1.2, (result.1.2, result.2)))) <$>
    (simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      ((work.run before.1).run before.2.1)).run before.2.2

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl

private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := StateT.run_map observe work state

private theorem state_modify_apply {S : Type} {m : Type → Type} [Monad m]
    (change : S → S) (state : S) : (modify change : StateT S m Unit) state = pure ((), change state) := rfl

private theorem lower_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (value : Value) :
    lower (n := n) (source := source) setup checks representation created (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower, StateT.run, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Next) :
    lower setup checks representation created (work >>= next) =
      (lower setup checks representation created work >>= fun value =>
        lower setup checks representation created (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

noncomputable def edReply (setup : Setup base KemSK) (owner : Owner source)
    (request : registration.Ed25519SigningRequest) : SignReply := by
  classical
  exact if request.public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys owner.identitySeed).ed25519 then
    let message := TranscriptAuthParts.absSlice request.message
    let signature := setup.joint.sign owner.identitySeed message
    RegistrationAuthenticationShared.openedBytes (some (signature.toList ++ message))
  else .None

noncomputable def implementation (setup : Setup base KemSK) (owner : Owner source) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT RegistrationSigningShared.State ProbComp)
  | .inl (.hash request) => RegistrationSigningShared.implementation (fun _ => pure .None) (.hash request)
  | .inl (.sign _ _ _) => pure .None
  | .inr request => pure (edReply setup owner request)

private theorem coin_project (draw : ProbComp Value) (before : PqxdhRecordLiftWorld.State n) :
    (fun result : Value × PqxdhRecordLiftWorld.State n => (result.1, result.2.primitive.2)) <$>
        (simulateQ PqxdhRecordLiftWorld.effects (simulateQ RegistrationWorldCoinCompiler.envCoin draw)).run before =
      (fun value => (value, before.primitive.2)) <$> draw := by
  have erased := congrArg (fun work =>
    (fun result : Value × PqxdhRecordLiftWorld.State n => (result.1, result.2.primitive.2)) <$> work)
    (RegistrationWorldCoinCompiler.coins_erase draw before)
  have coins := congrArg (fun work => (fun value => (value, before.primitive.2)) <$> work)
    (PqxdhRecordLiftWorld.countCoin_forget draw before.primitive.1.uniform)
  simp only [Functor.map_map, Prod.map, id_eq, RegistrationWorldCoinCompiler.eraseCoin,
    PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp] at erased
  simp only [Functor.map_map, StateT.run] at coins
  exact erased.trans coins

/-- The native callback projection retains its literal hash/signature reply and unchanged Server signing history. -/
theorem outgoing (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : Local n KemSK source) :
    Prod.map id project <$>
        (lower setup checks representation created
          (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)).run before =
      (implementation setup owner query).run (project before) := by
  classical
  cases query with
  | inl query => cases query with
    | hash request =>
        have same := congrArg (fun work => (fun result : CtxRomAuth.CtxDigest × RawCtxSharedPrimitive.SharedState Unit =>
          (result.1, (before.2.1.receipts, result.2.2))) <$> work)
          (RegistrationWorldAuthentication.hash_project
            (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before.2.2.server.world.world.1)
        convert same using 1 <;> simp only [lower, RegistrationNativeBeaconFrontend.outgoing,
          RegistrationNativeBeaconFrontend.hash, RegistrationNativeBeaconFrontend.effect,
          state_lift_apply, state_map_apply, simulateQ_map, simulateQ_spec_query,
          RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
          RegistrationNativeExperiment.server, implementation,
          RegistrationSigningShared.implementation, MldsaSharedNative.authentication,
          RegistrationWorldAuthentication.project, project,
          StateT.run, Functor.map_map, Prod.map, id_eq]; rfl
    | sign request payload digest =>
        rw [RegistrationNativeBeaconFrontend.outgoing, lower_pure]
        simp only [implementation, StateT.run, state_pure_apply, map_pure]
        rfl
  | inr request =>
      simp only [RegistrationNativeBeaconFrontend.outgoing, implementation, edReply]
      split <;> simp only [lower, RegistrationNativeBeaconFrontend.logEd,
        StateT.run, state_bind_apply, state_pure_apply, state_modify_apply, pure_bind,
        simulateQ_pure, map_pure, Prod.map, id_eq, project]

private theorem lower_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) :
    lower (n := n) setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner) work) =
      simulateQ (fun query => lower setup checks representation created
        (RegistrationNativeBeaconFrontend.outgoing setup source index owner query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- Complete native Init continuations retain the identical joint ML attempt history and shared cache. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) (before : Local n KemSK source) :
    Prod.map id project <$>
        (lower setup checks representation created
          (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner) work)).run before =
      (simulateQ (implementation setup owner) work).run (project before) := by
  rw [lower_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (outgoing setup checks representation created index owner) work before

/-- Every actual callback preserves earlier Server signing receipts; no Beacon signing leaf exists. -/
private theorem query_cached (setup : Setup base KemSK) (owner : Owner source)
    (query : RegistrationBeaconInitExecutor.Spec.Domain) (before : RegistrationSigningShared.State)
    (cached : RegistrationSigningShared.Cached before)
    (result : RegistrationBeaconInitExecutor.Spec.Range query × RegistrationSigningShared.State)
    (supported : result ∈ support ((implementation setup owner query).run before)) :
    RegistrationSigningShared.Cached result.2 := by
  cases query with
  | inl shared => cases shared with
    | hash request => exact RegistrationSigningShared.hash_cached_state (fun _ => pure .None) request before cached result supported
    | sign request payload digest =>
        simp only [implementation, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact cached
  | inr request =>
      simp only [implementation, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact cached

private theorem program_cached (setup : Setup base KemSK) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value) (before : RegistrationSigningShared.State)
    (cached : RegistrationSigningShared.Cached before)
    (result : Value × RegistrationSigningShared.State)
    (supported : result ∈ support ((simulateQ (implementation setup owner) work).run before)) :
    RegistrationSigningShared.Cached result.2 := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query (implementation setup owner)
    RegistrationSigningShared.Cached (query_cached setup owner) work before cached result supported

/-- Native Init execution preserves validity of every chronological ML receipt, including failed replies and failed publication. -/
theorem begin_cached (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (encode : registration.InitView → core.option.Option Value)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (before : Local n KemSK source) (cached : RegistrationSigningShared.Cached (project before))
    (result : RustM (RegistrationBeaconInitExecutor.Result Value) × Local n KemSK source)
    (supported : result ∈ support ((lower setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin encode control inputs coins pin))).run before)) :
    RegistrationSigningShared.Cached (project result.2) := by
  have projected : (result.1, project result.2) ∈ support
      ((simulateQ (implementation setup owner)
        (RegistrationBeaconInitExecutor.begin encode control inputs coins pin)).run (project before)) := by
    rw [← program setup checks representation created index owner _ before, support_map]
    exact ⟨result, supported, rfl⟩
  exact program_cached setup owner _ (project before) cached _ projected

def nativeProject (before : RegistrationNativeExperiment.State n KemSK source) : RegistrationSigningShared.State :=
  (before.server.world.world.2, before.server.world.world.1.primitive.2)

def close (before : Local n KemSK source) : RegistrationNativeExperiment.State n KemSK source :=
  { before.2.2 with beacons := before.1, server := { before.2.2.server with
      world := RegistrationWorldAgreementCompiler.join before.2.1 before.2.2.server.world.world.1 } }

private theorem source_lower (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    (RegistrationNativeExperiment.beacon setup checks representation created work).run before =
      Prod.map id close <$> (lower setup checks representation created work).run
        (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) := by
  simp only [RegistrationNativeExperiment.beacon, lower, StateT.run,
    bind_pure_comp, Functor.map_map, Prod.map, id_eq, close]

/-- The original native wrapper of outgoing Init uses the same cache/history projection after restoring its entire local state. -/
theorem source_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (work : OracleComp RegistrationBeaconInitExecutor.Spec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    Prod.map id nativeProject <$>
        (RegistrationNativeExperiment.beacon setup checks representation created
          (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner) work)).run before =
      (simulateQ (implementation setup owner) work).run (nativeProject before) := by
  rw [source_lower, Functor.map_map]
  convert program setup checks representation created index owner work
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) using 1 <;>
    simp only [nativeProject, close, project, RegistrationWorldAgreementCompiler.join,
      RegistrationWorldAgreementCompiler.erase, Prod.map, id_eq]
  rfl

/-- Every actual native Init outcome preserves the chronological digest receipts under the original source wrapper. -/
theorem source_begin_cached (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (index : Nat) (owner : Owner source)
    (encode : registration.InitView → core.option.Option Value)
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (cached : RegistrationSigningShared.Cached (nativeProject before))
    (result : RustM (RegistrationBeaconInitExecutor.Result Value) × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.beacon setup checks representation created
      (simulateQ (RegistrationNativeBeaconFrontend.outgoing setup source index owner)
        (RegistrationBeaconInitExecutor.begin encode control inputs coins pin))).run before)) :
    RegistrationSigningShared.Cached (nativeProject result.2) := by
  rw [source_lower, support_map] at supported
  obtain ⟨observed, possible, same⟩ := supported
  have valid := begin_cached setup checks representation created index owner encode control inputs coins pin
    (before.beacons, (RegistrationWorldAgreementCompiler.erase before.server.world, before)) cached observed possible
  have equal : project observed.2 = nativeProject result.2 := by
    rw [← same]
    rfl
  exact equal ▸ valid

end BeaconcryptCore.Computational.RegistrationNativeMldsaShared

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaShared.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaShared.outgoing
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaShared.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaShared.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaShared.begin_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaShared.begin_cached
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaShared.source_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaShared.source_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaShared.source_begin_cached' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaShared.source_begin_cached

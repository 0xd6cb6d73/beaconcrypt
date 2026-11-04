-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeWorldCache
import BeaconcryptCore.Computational.RegistrationResponseExecutor

/-! The actual incoming Beacon signature controller reads and extends the existing global CTX cache. Its projection keeps the literal chronological signing receipts, with no independent authentication world or reset. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaShared (Local lower project)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (state : S) :
    (work >>= next) state = (do let result ← work state; next result.1 result.2) := rfl
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl
private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) :
    (observe <$> work) state = Prod.map observe id <$> work state := StateT.run_map observe work state

theorem lower_bind (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Value)
    (next : Value → RegistrationNativeBeaconFrontend.M n KemSK source RegistrationServerRoleBackend.State Next) :
    lower setup checks representation created (work >>= next) =
      (lower setup checks representation created work >>= fun value =>
        lower setup checks representation created (next value)) := by
  apply StateT.ext
  intro before
  simp only [lower, StateT.run, state_bind_apply, simulateQ_bind, map_bind, bind_map_left]

theorem lower_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (value : Value) :
    lower (n := n) (source := source) setup checks representation created (pure value) = pure value := by
  apply StateT.ext
  intro before
  simp only [lower, StateT.run, state_pure_apply, simulateQ_pure, map_pure]

private theorem lower_program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) :
    lower (n := n) setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work) =
      simulateQ (fun query => lower setup checks representation created
        (RegistrationNativeBeaconFrontend.authentication setup source query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, lower_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, lower_bind, ih]

/-- Every actual native authentication callback uses its current global cache and literal verification operands. -/
theorem query (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (selected : RegistrationAuthenticationExecutor.Spec.Domain) (before : Local n KemSK source) :
    Prod.map id project <$>
      (lower setup checks representation created
        (RegistrationNativeBeaconFrontend.authentication setup source selected)).run before =
      (RegistrationAuthenticationShared.implementation setup.source.crypto source.verify wire.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source) selected).run (project before) := by
  cases selected with
  | hash request =>
      rw [RegistrationAuthenticationShared.hash_exact]
      have same := congrArg (fun work => (fun result : CtxRomAuth.CtxDigest × RawCtxSharedPrimitive.SharedState Unit =>
        (core.option.Option.Some (RegistrationAuthenticationShared.digestArray result.1),
          (before.2.1.receipts, result.2.2))) <$> work)
        (RegistrationWorldAuthentication.hash_project
          (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request) before.2.2.server.world.world.1)
      convert same using 1 <;> simp only [RegistrationNativeBeaconFrontend.authentication,
        RegistrationNativeBeaconFrontend.hash, RegistrationNativeBeaconFrontend.effect,
        lower, StateT.run, state_bind_apply, state_lift_apply, state_pure_apply, state_map_apply,
        simulateQ_map, simulateQ_spec_query,
        bind_pure_comp, RegistrationNativeExperiment.trusted, RegistrationNativeExperiment.world,
        RegistrationNativeExperiment.server, RegistrationWorldAuthentication.project, project, Functor.map_map, Prod.map, id_eq]; rfl
  | mldsa request | ed25519 request => rfl

/-- The complete native response controller projects to the same mandatory source controller and the same reached cache. -/
theorem program (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (work : OracleComp RegistrationAuthenticationExecutor.Spec Value) (before : Local n KemSK source) :
    Prod.map id project <$>
      (lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source) work)).run before =
      (simulateQ (RegistrationAuthenticationShared.implementation setup.source.crypto source.verify wire.frameWrite
        (RawCtxSourceHkdf.kdfImpl setup.source)) work).run (project before) := by
  rw [lower_program]
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query setup checks representation created wire) work before

/-- Native response success supplies the accepted ML trial at its actual shared-cache cut. -/
theorem accepted (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (before after : Local n KemSK source) (authenticated : registration.AuthenticatedResponse)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (.Some packet)))).run before))
    (protectedKey : Bool) (honest : protectedKey = true) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash (project after).2) source.verify
      (RegistrationResponseExecutor.trial protectedKey pending packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
          (project before))) := by
  apply RegistrationResponseExecutor.accepted_trial setup.source.crypto source.verify wire.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) pending packet (project before) (project after) authenticated
    ?_ protectedKey honest _
  rw [RegistrationResponseExecutor.execute, ← program setup checks representation created wire, support_map]
  exact Set.mem_image_of_mem (Prod.map id project) supported

/-- The actual native response cut gives a fresh-message ML forgery or a collision between reached cache queries. -/
theorem origin_split (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (before after : Local n KemSK source) (authenticated : registration.AuthenticatedResponse)
    (supported : (.ok (.Ok authenticated), after) ∈ support
      ((lower setup checks representation created
        (simulateQ (RegistrationNativeBeaconFrontend.authentication setup source)
          (RegistrationResponseExecutor.begin pending (.Some packet)))).run before))
    (protectedKey : Bool) (honest : protectedKey = true)
    (cached : RegistrationSigningShared.Cached (project before))
    (absent : ¬ MldsaTranscriptAuth.Issued (RegistrationResponseExecutor.trial protectedKey pending packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
        (project before)))) :
    MldsaTranscriptAuth.WeakForgery (MldsaSharedAuthentication.cacheHash (project after).2) source.verify
      (RegistrationResponseExecutor.trial protectedKey pending packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes pending.binding.server_pin.public_key)
          (project before))) ∨ CacheHasCollision (project after).2 := by
  apply RegistrationResponseExecutor.origin_split setup.source.crypto source.verify wire.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) pending packet (project before) (project after) authenticated
    ?_ protectedKey honest _ ?_ absent
  · rw [RegistrationResponseExecutor.execute, ← program setup checks representation created wire, support_map]
    exact Set.mem_image_of_mem (Prod.map id project) supported
  · exact RegistrationSigningShared.history_cached _ _ cached

end BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.lower_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.lower_bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.lower_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.lower_pure
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.accepted
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.origin_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseAuthentication.origin_split

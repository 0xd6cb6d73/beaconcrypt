import BeaconcryptCore.Computational.RawCtxSelectedRoleCompiler

/-!
The same original finite Server/Beacon family uses the checked key-free selected CTX role compiler and the unchanged real public HKDF. Public coins and commitment lookups reach the ordinary selected challenger's actual shared cache. The compiled family keeps exact indexed role publication and a separate selected-nonce stopping outcome; it does not substitute a conclusion about arbitrary native clients.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageKdf
open RawCtxSelectedMessageDriver (privateTable)
open RawCtxSelectedReceiveCompiler (State project evaluated)
open RawCtxSelectedOwnerCompiler (Kernel Base calls originalCalls)
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily
variable {A M P I D K : Type} {S B : Nat}
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem state_map_apply {X Y σ : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT σ m X) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  change (f <$> work).run state = _
  rw [StateT.run_map]
  rfl

private theorem state_lift_apply {X σ : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (work : m X) (state : σ) :
    (monadLift work : StateT σ m X) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

noncomputable def publicWork (source : FixedHkdfSha512NoSaltSource) : QueryImpl RawCtxServerServices.PublicSpec Base
  | .inl coin => AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inl coin)))
  | .inr (.inl bytes) => (fun digest : CtxRomAuth.CtxDigest => some digest.toList) <$>
      AdaptiveCtxDynamicKnownKeys.Spec.query (.inl (.inl (.inr (.inl ((), bytes)))))
  | .inr (.inr request) => pure (request.project (PqxdhJointKdf.productionStream source.crypto request.address))

noncomputable def publicCalls (source : FixedHkdfSha512NoSaltSource) : QueryImpl RawCtxServerServices.PublicSpec (OptionT Base) :=
  fun query => OptionT.mk (some <$> publicWork source query)

noncomputable def originalPublic (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :=
  RawCtxFunctionalFamily.backend (A := A) source writer prior ∘ₛ RawCtxServerServices.publicLift

/-- Public operations always bypass the private selected table and retain the original fixed HKDF, hash cache and explicit caller coins. -/
theorem original_public (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior) :
    originalPublic (A := A) source writer prior = RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift := by
  funext query
  rcases query with coin | (bytes | request)
  all_goals simp only [originalPublic, RawCtxFunctionalFamily.backend, QueryImpl.compose,
    RawCtxServerServices.publicLift, RawCtxSelectiveKdfFamily.compiler, simulateQ_spec_query, RawCtxRetainedTable.viewImpl]

/-- The actual public reply and complete source cache are unchanged by the key-free CTX public service. In particular, public HKDF remains the real fixed source function. -/
theorem public_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (key : RootOutput) (read : RawCtxReceive.FrameDecoder) (query : RawCtxServerServices.PublicSpec.Domain) (state : State A) :
    Prod.map id project <$> (evaluated source key read (publicWork source query)).run state =
      (originalPublic source writer prior query).run (project state) := by
  rw [original_public]
  rcases query with coin | (bytes | request)
  · rw [RawCtxProtocolBackend.backend, RawCtxServerServices.public_coin]
    simp [publicWork, evaluated, AdaptiveCtxDynamicKnownKeys.sourceImpl,
      AdaptiveCtxSharedModes.localImpl, AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.hashImpl,
      StateT.run, state_map_apply, state_lift_apply, project, Prod.map_def]
  · rw [RawCtxProtocolBackend.backend, RawCtxServerServices.public_hash]
    simp [publicWork, evaluated, AdaptiveCtxDynamicKnownKeys.sourceImpl,
      AdaptiveCtxSharedModes.localImpl, AdaptiveCtxSharedHash.localImpl, AdaptiveCtxSharedHash.hashImpl,
      StateT.run, state_map_apply, project, Prod.map_def]
  · rw [RawCtxProtocolBackend.public_hkdf]
    rfl


noncomputable def family (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles Kernel M P I D K S B) :
    Base (Option ((RawCtxProtocolRoles.SourceSpec S B).Range query × Roles Kernel M P I D K S B)) :=
  ((RawCtxGenericFamilyFrontend.impl (calls source writer prior parent target nonce next read) (publicCalls source)
    sender route read query).run before).run

noncomputable def Stops (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles Kernel M P I D K S B)
    (state : AdaptiveCtxDynamicKnownKeys.SourceState) : Prop :=
  match query with
  | .inl ⟨index, request⟩ => RawCtxSelectedRoleCompiler.ServerStops prior parent target nonce next sender request (before.1 index) state
  | .inr (.inl ⟨index, request⟩) => RawCtxSelectedRoleCompiler.BeaconStops prior parent target nonce next request (before.2 index) state
  | .inr (.inr _) => False

noncomputable def originalFrontend (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :=
  RawCtxGenericFamilyFrontend.impl (originalCalls (A := A) source writer prior parent key target nonce next)
    (originalPublic source writer (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)))
    sender route read (PeerMetadata := P) (Identity := I) (DhPair := D) (KemPair := K) (serverCount := S) (beaconCount := B)

/-- The exact indexed family dispatcher publishes only the selected original role and returns its actual optional API value; public services preserve all roles. -/
theorem family_cases (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles Kernel M P I D K S B) :
    family source writer prior parent target nonce next sender route read query before =
      match query with
      | .inl ⟨index, request⟩ =>
          Option.map (fun result => (result.1, (Function.update before.1 index result.2, before.2))) <$>
            RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read request (before.1 index)
      | .inr (.inl ⟨index, request⟩) =>
          Option.map (fun result => (result.1, (before.1, Function.update before.2 index result.2))) <$>
            RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read request (before.2 index)
      | .inr (.inr request) => (fun reply => some (reply, before)) <$> publicWork source request := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  all_goals simp only [family, RawCtxGenericFamilyFrontend.impl, StateT.run, RawCtxSelectedRoleCompiler.server,
    RawCtxSelectedRoleCompiler.beacon, publicCalls, bind_pure_comp, OptionT.run_map, OptionT.run_mk,
    Functor.map_map, Option.map_some]
  all_goals rfl

/-- Every original finite-family API query preserves its complete optional source result, all indexed roles and shared state. No honest-role or nonce-freshness premise replaces the explicitly retained stop. -/
theorem family_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles Kernel M P I D K S B) (state : State A) :
    Prod.map id project <$> (evaluated source key read
      (family source writer prior parent target nonce next sender route read query before)).run state =
      if Stops prior parent target nonce next sender query before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        ((originalFrontend source writer prior parent key target nonce next sender route read query).run before).run (project state) := by
  rw [family_cases]
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · have same := RawCtxSelectedRoleCompiler.mapped_source source key read
      (fun result => (result.1, (Function.update before.1 index result.2, before.2)))
      (RawCtxSelectedRoleCompiler.server source writer prior parent target nonce next sender route read request (before.1 index))
      ((RawCtxGenericServer.serverImpl (originalCalls source writer prior parent key target nonce next) sender route read request).run (before.1 index))
      state (RawCtxSelectedRoleCompiler.ServerStops prior parent target nonce next sender request (before.1 index) state.2)
      (RawCtxSelectedRoleCompiler.server_source source writer prior parent key target nonce next sender route read request (before.1 index) state)
    simp only [Stops, originalFrontend, RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at same ⊢
    convert same using 1
    rfl
  · have same := RawCtxSelectedRoleCompiler.mapped_source source key read
      (fun result => (result.1, (before.1, Function.update before.2 index result.2)))
      (RawCtxSelectedRoleCompiler.beacon source writer prior parent target nonce next read request (before.2 index))
      ((RawCtxGenericBeacon.impl (originalCalls source writer prior parent key target nonce next) read request).run (before.2 index))
      state (RawCtxSelectedRoleCompiler.BeaconStops prior parent target nonce next request (before.2 index) state.2)
      (RawCtxSelectedRoleCompiler.beacon_source source writer prior parent key target nonce next read request (before.2 index) state)
    simp only [Stops, originalFrontend, RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at same ⊢
    convert same using 1
    rfl
  · have clear : ¬ Stops prior parent target nonce next sender (.inr (.inr request)) before state.2 := by simp only [Stops, not_false_eq_true]
    rw [ite_eq_right (fun h => (clear h).elim)]
    rw [RawCtxSelectedReceiveCompiler.evaluated_map, StateT.run_map]
    have same := congrArg (fun work => (fun result => (some (result.1, before), result.2)) <$> work)
      (public_source source writer (privateTable prior parent target (RawCtxSelectedMessageKdf.response key nonce next)) key read request state)
    simp only [Functor.map_map, Prod.map_def, id_eq, originalFrontend, RawCtxGenericFamilyFrontend.impl,
      StateT.run, bind_pure_comp, state_map_apply] at same ⊢
    convert same using 1


/-- Native interpretation recovers the original complete finite role API and every indexed native state, using the already checked source driver rather than an ambient realization premise. -/
theorem original_native (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles Kernel M P I D K S B) :
    simulateQ (RawCtxFunctionalFamily.backend (A := A) source writer (privateTable prior parent target (response key nonce next)))
      ((RawCtxProtocolRoles.protocolImpl S B sender route read query).run
        (nativeRoles (RawCtxSelectedMessageReveals.nativeKernel key) before)) =
      Prod.map id (nativeRoles (RawCtxSelectedMessageReveals.nativeKernel key)) <$>
        (originalFrontend source writer prior parent key target nonce next sender route read query).run before :=
  RawCtxSelectedMessageFamily.frontend_source source writer prior parent key target nonce next sender route read query before

/-- The actual native finite-family experiment has an executable selected-key-free record/public step with the same complete native roles, optional API value and source cache until its explicit selected nonce stop. -/
theorem native_family (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles Kernel M P I D K S B) (state : State A) :
    (fun result => (Option.map (Prod.map id (nativeRoles (RawCtxSelectedMessageReveals.nativeKernel key))) result.1, project result.2)) <$>
      (evaluated source key read (family source writer prior parent target nonce next sender route read query before)).run state =
      if Stops prior parent target nonce next sender query before state.2 then pure (none, project state)
      else (fun result => (some result.1, result.2)) <$>
        (simulateQ (RawCtxFunctionalFamily.backend source writer (privateTable prior parent target (response key nonce next)))
          ((RawCtxProtocolRoles.protocolImpl S B sender route read query).run
            (nativeRoles (RawCtxSelectedMessageReveals.nativeKernel key) before))).run (project state) := by
  rw [original_native]
  have mapped := congrArg (fun work => (fun result =>
    (Option.map (Prod.map id (nativeRoles (RawCtxSelectedMessageReveals.nativeKernel key))) result.1, result.2)) <$> work)
      (family_source source writer prior parent key target nonce next sender route read query before state)
  simp only [StateT.run_map, Functor.map_map, Prod.map_def, id_eq, apply_ite, map_pure, Option.map_none, Option.map_some] at mapped ⊢
  convert mapped using 1

/-- A public service issues at most one actual component call; its public HKDF branch is the fixed local source function. -/
theorem public_queries (source : FixedHkdfSha512NoSaltSource) (query : RawCtxServerServices.PublicSpec.Domain) :
    (publicWork source query).IsTotalQueryBound 1 := by
  rcases query with coin | (bytes | request)
  all_goals simp [publicWork, IsTotalQueryBound]

/-- Every complete finite-family record/public API request has at most one dynamic component call, regardless of session or peer selection and rejection. -/
theorem family_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain) (before : Roles Kernel M P I D K S B) :
    (family source writer prior parent target nonce next sender route read query before).IsTotalQueryBound 1 := by
  rw [family_cases]
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectedRoleCompiler.server_queries source writer prior parent target nonce next sender route read request (before.1 index)
  · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      RawCtxSelectedRoleCompiler.beacon_queries source writer prior parent target nonce next read request (before.2 index)
  · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using public_queries source request

end BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.original_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.original_public

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.public_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.public_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.family_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.family_cases

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.family_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.family_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.original_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.original_native

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.native_family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.native_family

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.public_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.public_queries

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.family_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedFamilyCompiler.family_queries

import BeaconcryptCore.Computational.PqxdhServerAuthCtxBuildSettlement

/-! The complete source registration builder preserves a map between two private kernel representations. Actual auxiliary callbacks and their enclosing monad remain unchanged. Its concrete material sender and final known-slot settlement discharge the representation conditions. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthBuildMap
open PqxdhServerRegistrationPublication (AuxSpec Response registrationWitness)
open PqxdhInitialGenericPublication (State)

variable {K L Metadata PeerMetadata Consumed : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Only the private kernel representation changes; every peer identity, metadata field, consumed registration and allocation field remains. -/
def mapState (f : K → L) (state : State K Metadata PeerMetadata Consumed) :
    State L Metadata PeerMetadata Consumed :=
  ⟨⟨state.server.identity, fun kid => (state.server.peers kid).map
      (fun peer => ⟨peer.identity, f peer.kernel, peer.metadata⟩), state.server.metadata⟩,
    state.identityKeyId, state.control, state.consumed⟩

/-- Actual successful publication commutes with the private representation map, retaining every unrelated peer. -/
theorem publish_map (f : K → L) (state : State K Metadata PeerMetadata Consumed)
    (candidate : pqxdh.ServerRegistrationCandidate) (kernel : K) (metadata : PeerMetadata) :
    mapState f (PqxdhInitialGenericPublication.publish state candidate kernel metadata) =
      PqxdhInitialGenericPublication.publish (mapState f state) candidate (f kernel) metadata := by
  simp only [mapState, PqxdhInitialGenericPublication.publish]
  congr 1
  congr 1
  funext kid
  by_cases same : kid = candidate.key_id
  · subst kid
    simp only [Function.update_self, Option.map_some]
  · simp only [Function.update_of_ne same]

/-- The literal first-send, erase, optional writer and publication sequence preserves the complete mapped state under the displayed send equation. -/
theorem after_map (f : K → L) (left : RawCtxChainOwner.Calls K m) (right : RawCtxChainOwner.Calls L m)
    (aux : QueryImpl AuxSpec m)
    (sendMap : ∀ kernel context, right.send (f kernel) context =
      (fun result => (f result.1, result.2)) <$> left.send kernel context)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : K) (metadata : PeerMetadata) (state : State K Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.afterInitialization right aux candidate authenticated (f kernel) metadata
        (mapState f state) =
      Prod.map id (mapState f) <$>
        PqxdhInitialGenericPublication.afterInitialization left aux candidate authenticated kernel metadata state := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, sendMap, bind_map_left, map_bind]
  refine bind_congr fun ⟨advanced, encrypted⟩ => bind_congr fun _ => ?_
  cases encrypted <;> simp only [map_pure, Prod.map_apply, id_eq, map_bind]
  refine bind_congr fun written => ?_
  cases written <;> simp only [map_pure, Prod.map_apply, id_eq, publish_map]

/-- Candidate validation, both allocation gates and the exact registration binding prefix precede the same complete mapped first send. -/
theorem candidate_map (f : K → L) (left : RawCtxChainOwner.Calls K m) (right : RawCtxChainOwner.Calls L m)
    (aux : QueryImpl AuxSpec m)
    (sendMap : ∀ kernel context, right.send (f kernel) context =
      (fun result => (f result.1, result.2)) <$> left.send kernel context)
    (initial : RustM K) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State K Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericBuilder.candidate right aux (f <$> initial) candidate data metadata (mapState f state) =
      Functor.map (Prod.map id (mapState f)) <$>
        PqxdhInitialGenericBuilder.candidate left aux initial candidate data metadata state := by
  simp only [PqxdhInitialGenericBuilder.candidate, map_bind]
  refine bind_congr fun valid => ?_
  cases valid <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq, map_bind]
  refine bind_congr fun reserved => ?_
  cases reserved <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
    map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
  cases initial <;> simp only [PqxdhInitialGenericBuilder.continueRust, map_pure,
    RawCtxMaterialInterpretation.rust_map_ok]
  case true.true.ok kernel =>
    by_cases empty : (data.getD registrationWitness).isEmpty = true
    all_goals simp only [empty, Bool.false_eq_true, ite_true, ite_false, map_pure,
      RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
    by_cases fits : 8 + (data.getD registrationWitness).length ≤ Usize.max
    all_goals simp only [fits, ite_true, ite_false, map_bind, map_pure,
      RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
    refine bind_congr fun allocated => ?_
    cases allocated <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false,
      map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
    cases candidate.key_id_binding <;> simp only [map_pure,
      after_map f left right aux sendMap, Functor.map_map]
    all_goals rfl
  all_goals rfl

/-- The complete actual builder preserves the representation map through every identity, allocation, consumed-registration and peer-publication branch. -/
theorem build_map (f : K → L) (left : RawCtxChainOwner.Calls K m) (right : RawCtxChainOwner.Calls L m)
    (aux : QueryImpl AuxSpec m)
    (sendMap : ∀ kernel context, right.send (f kernel) context =
      (fun result => (f result.1, result.2)) <$> left.send kernel context)
    (initial : RustM K) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (state : State K Metadata PeerMetadata Consumed) :
    PqxdhServerAuthSendFactor.genericBuild right aux (f <$> initial) pending data metadata (mapState f state) =
      Functor.map (Prod.map id (mapState f)) <$>
        PqxdhServerAuthSendFactor.genericBuild left aux initial pending data metadata state := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  change PqxdhInitialGenericBuilder.continueRust (pqxdh.server_next_key_id state.control) _ = _
  cases next : pqxdh.server_next_key_id state.control <;>
    simp only [PqxdhInitialGenericBuilder.continueRust, map_pure]
  case ok value =>
    cases value <;> simp only [map_pure, RawCtxMaterialInterpretation.rust_map_ok, Prod.map_apply, id_eq]
    simp only [mapState, Option.isSome_map]
    rename_i key
    cases prepared : pqxdh.server_prepare_commit state.control pending
        ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers key).isSome then .Occupied else .Available) <;>
      simp only [map_pure]
    case ok value =>
      cases value <;> simp only [map_pure]
      case Err _ => rfl
      case Ok candidate => exact candidate_map f left right aux sendMap initial candidate data metadata state
    all_goals rfl
  all_goals rfl

/-- The complete native projection composes with the intermediate private kernel map. -/
theorem native_map (f : K → L) (g : L → ConcreteRatchetKernel)
    (state : State K Metadata PeerMetadata Consumed) :
    PqxdhInitialGenericPublication.native g (mapState f state) =
      PqxdhInitialGenericPublication.native (g ∘ f) state := by
  simp only [PqxdhInitialGenericPublication.native, mapState, RawCtxGenericRoleStorage.nativeServer,
    Option.map_map, Function.comp_def]

/-- The actual known-peer embedding supplies the intermediate material map without excluding byte aliases. -/
theorem embed_map (key : PqxdhSecretInputKdf.RootOutput)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    mapState (PqxdhServerAuthCtxCalls.interpret key) (PqxdhServerAuthCtxBuildSettlement.embed state) =
      PqxdhServerAuthSendFactor.embed state := by
  rcases state with ⟨⟨identity, peers, metadata⟩, keyId, control, consumed⟩
  simp only [mapState, PqxdhServerAuthCtxBuildSettlement.embed, PqxdhServerAuthSendFactor.embed,
    Option.map_map, Function.comp_def, PqxdhServerAuthCtxBuildSettlement.known,
    PqxdhServerAuthCtxCalls.interpret, RawCtxSelectedMessageKey.known_kernel]

open PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhServerAuthCtxCalls (Chain Material Kernel Residual step interpret)

/-- Mathematical material interpretation feeds the original seal adapter in its unchanged monad. The actual executable CTX sealer will remove this key argument. -/
noncomputable def materialSealer (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (key : RootOutput) (pending : PqxdhServerAuthCtxSend.Pending) : m (Option RawCtxSourceSend.Encrypted) :=
  (prim ∘ₛ RawCtxSourceSend.adapter) (.inr (RawCtxInterpretedSend.nativeSeal
    (RawCtxInterpretedSend.mapSeal (RawCtxSelectedMessageKey.interpret key)
      (PqxdhServerAuthCtxSend.sealing pending))))

/-- The actual factor-side sender is exactly the material-marker sender in any lawful monad, including the complete seal log. No functional or security premise is added. -/
theorem material_send (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (key : RootOutput) (rest : Residual)
    (entry : Kernel) (context : RawCtxSourceSend.SealContext) :
    simulateQ (PqxdhServerAuthSendFactor.primLabels prim source
      (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)).1)
        (RawCtxChainSend.execute (interpret key entry) context) =
      (fun result => (interpret key result.1, result.2)) <$>
        simulateQ (PqxdhServerAuthCtxBuildSettlement.labels source rest (materialSealer prim key))
          (RawCtxChainSend.execute entry context) := by
  apply RawCtxChainMaterialMap.send_execute (RawCtxSelectedMessageKey.interpret key)
  · intro chain
    simp only [PqxdhServerAuthSendFactor.primLabels, PqxdhServerAuthCtxBuildSettlement.labels,
      map_pure, PqxdhServerAuthCtxCalls.step_source]
  · intro pending
    simp only [PqxdhServerAuthSendFactor.primLabels, PqxdhServerAuthCtxBuildSettlement.labels, materialSealer]
    rfl

/-- The material-marker source continuation retains the original primitive and auxiliary effects, resolving only the proved known final material slots. -/
noncomputable def materialBuild (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (aux : QueryImpl AuxSpec m) (key : RootOutput) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    m (RustM (Option Response × PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed)) :=
  Functor.map (Prod.map id (PqxdhInitialGenericPublication.native PqxdhServerAuthCtxBuildSettlement.resolve)) <$>
    PqxdhServerAuthSendFactor.genericBuild
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None))
        source rest (materialSealer prim key)) aux
      (PqxdhServerAuthCtxCalls.initial false rest.2.2) pending data metadata
      (PqxdhServerAuthCtxBuildSettlement.embed state)

/-- The actual complete logged-factor builder is the material-marker builder after its concrete constructor, sender and settlement equations. No callback or no-alias hypothesis remains. -/
theorem material_build (prim : QueryImpl RawCtxSourceSend.PrimitiveSpec m)
    (source : FixedHkdfSha512NoSaltSource) (aux : QueryImpl AuxSpec m) (key : RootOutput) (rest : Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes) (metadata : PeerMetadata)
    (state : PqxdhServerRegistrationPublication.State Metadata PeerMetadata Consumed) :
    PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None)) prim source aux
      (PqxdhServerAuthCtxMaterial.factor (PqxdhServerAuthCtxMaterial.output key rest)) pending data metadata state =
      materialBuild prim source aux key rest pending data metadata state := by
  unfold PqxdhServerAuthLoggedSendFactor.factored materialBuild
  rw [PqxdhServerAuthCtxCalls.initial_source false _ key, ← embed_map key state,
    build_map (interpret key)
      (PqxdhServerAuthCtxBuildSettlement.calls (fun entry _ _ => pure (entry, .None))
        source rest (materialSealer prim key)) _ aux (material_send prim source key rest)]
  simp only [Functor.map_map, Prod.map_def, id_eq, native_map]
  exact PqxdhServerAuthCtxBuildSettlement.build_settled _ source rest (materialSealer prim key)
    aux key rest.2.2 pending data metadata state

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse A : Type}
open PqxdhServerAuthExperiment (Setup Codec Checks)

/-- The concrete unlogged primitive callback is the unchanged source seal and optional writer on the full shared state. -/
theorem material_native (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (key : RootOutput) (pending : PqxdhServerAuthCtxSend.Pending) :
    materialSealer (m := StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)
        (fun query => PqxdhServerAuthExperiment.nativeTail setup codec checks (.inl query)) key pending =
      PqxdhServerAuthCtxSend.sourceSealing setup.source codec.frameWrite key pending := by
  simp only [materialSealer, PqxdhServerAuthCtxSend.sourceSealing, QueryImpl.apply_compose,
    RawCtxSourceSend.adapter, simulateQ_map, simulateQ_spec_query, bind_pure_comp,
    PqxdhServerAuthExperiment.nativeTail, PqxdhServerRegistrationPublication.nativeAdapter,
    RawCtxSourceSeal.nativeAdapter]
  congr 1
  simp only [← QueryImpl.simulateQ_compose]
  congr 1

/-- The actual logged callback appends the original context exactly when the inner frame writer succeeds. A cryptographic seal followed by writer failure adds no source log entry. -/
theorem material_logged (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
    (key : RootOutput) (pending : PqxdhServerAuthCtxSend.Pending) :
    materialSealer (PqxdhServerAuthLoggedSendFactor.loggedPrim setup codec checks) key pending = (do
      let sealed ← PqxdhServerAuthCtxSend.sourceSealing setup.source codec.frameWrite key pending
      if sealed.isSome then modify fun state => (state.1 ++ [pending.context], state.2)
      pure sealed) := by
  rw [← material_native setup codec checks key pending]
  simp only [materialSealer, QueryImpl.apply_compose, RawCtxSourceSend.adapter, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, PqxdhServerAuthLoggedSendFactor.loggedPrim,
    PqxdhServerAuthExperiment.tailImpl, map_bind, bind_map_left]
  refine bind_congr fun sealed => ?_
  cases sealed <;> simp only [Option.map_none, Option.map_some, Option.isSome_none, Option.isSome_some,
    Bool.false_eq_true, ite_false, ite_true, map_pure]
  all_goals rfl

end BeaconcryptCore.Computational.PqxdhServerAuthBuildMap

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.publish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.publish_map

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.after_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.after_map

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.candidate_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.candidate_map

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.build_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.build_map

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.native_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.native_map

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.embed_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.embed_map

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_send

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_build

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_native

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBuildMap.material_logged

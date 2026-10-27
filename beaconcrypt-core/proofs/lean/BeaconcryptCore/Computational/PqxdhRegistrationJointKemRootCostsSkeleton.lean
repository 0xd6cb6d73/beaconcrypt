import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCostsLayers
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactorNative

/-!
# The random draws of the skeleton (item 2, stage S8, skeleton)

Every native step of the services skeleton of stage S1b, run on the exposed encapsulation interface with the table oracles, costs at most a fixed weight of its request (`skelImpl_cost`, weights `wG` through the service classes `wKind`): a forwarded private-pool request its pool weight (`wPool_le`), a Beacon tail callback 64 (one shared-cache commitment or one direct table read), a raw accept `96 + encapsCost` (the scalar, the exposed encapsulation and the root's direct table read; `clientPrefix_cost`, `ncost_acceptTail`), a build 64 (one sealing commitment), a public HMAC 64 (one direct table read), a hash 64 (one BLAKE2b miss), a reveal nothing, and a grouped Beacon finish 128 (one direct table read or a hidden read, and one opening commitment of the continuation). The hidden-entry services must cost at most 64 per build and per continuation (`ServiceBills`); the native and the factored services do (`nativeServices_bills`, `factoredServices_bills`, from the Server-authentication resource lemmas `generic_build_uniform`, `generic_raw_uniform` and the factor equalities of stage S3b).

The Server's resumption (the open bill of stage D) costs at most 64 (`resume_cost`): its candidate-free suffix after the encapsulation draws nothing (`after_free`, `compiled_cost`: two conversions and four DH calls), and its private tail reads its root at most once (`tail_cost`, from `PqxdhRegistrationJointKemOpaqueCosts.client_root`), 64 bytes for a direct table read and nothing for a hidden read (`resumeImpl_cost`).

These are resource bounds; they make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthSourceCosts (KemCaps KemBound serverClass serverUniformCost)
open PqxdhRegistrationJointKemPostSkeleton
open PqxdhRegistrationJointBeaconFinishOnce (liftComp_inl)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-! ### The exposed encapsulation interface without the table oracles -/

section Enc

/-- The exposed encapsulation interface: pool weights, and `encapsCost` per encapsulation. -/
def wEncBase (caps : KemCaps) : (Enc KemSK).Domain → ℕ
  | .inl query => wPool (KemSK := KemSK) caps query
  | .inr _ => caps.encapsCost

/-- Local work whose coins go to the private pool's coin channel costs its coins. -/
theorem forwardCoins_cost (caps : KemCaps) {α : Type} (work : ProbComp α) {n : ℕ} (bounded : work.IsTotalQueryBound n) :
    WBound (simulateQ PqxdhRegistrationJointKemEncapsulation.forward
      (PqxdhLiveKemBirth.coins (KemSK := KemSK) work)) (wEncBase caps) n := by
  unfold PqxdhLiveKemBirth.coins
  rw [← QueryImpl.simulateQ_compose]
  refine wBound_simulate _ (fun _ => 1) (wEncBase caps) (fun coin => ?_) (wBound_of_total bounded)
  rw [QueryImpl.apply_compose, simulateQ_spec_query]
  exact (wBound_query _ _ _).mpr le_rfl

/-- Each native callback of the Server's prefix draws at most its source class allowance. -/
theorem serverAux_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (PqxdhRegistrationJointServerPrefix.AuxSpec Reader).Domain) (consumed : List Pqxdh.Bytes) :
    ((serverAux setup codec checks query).run consumed).IsTotalQueryBound (serverUniformCost caps (serverClass query)) := by
  cases query <;> first | trivial | skip
  · change (generateEphemeral setup >>= fun value => pure (value, consumed)).IsTotalQueryBound 32
    rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact PqxdhServerAuthSourceCosts.generate_uniform setup
  · change (encapsulate setup _ >>= fun value => pure (value, consumed)).IsTotalQueryBound caps.encapsCost
    rw [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff]
    exact PqxdhServerAuthSourceCosts.encaps_uniform setup caps bounded _

/-- Each compiled callback of the Server's prefix with only the encapsulation exposed costs at most its source class allowance. -/
theorem prefixStep_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (query : (PqxdhRegistrationJointServerPrefix.NativeSpec Reader).Domain) (consumed : List Pqxdh.Bytes) :
    WBound ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.compiler (KemSK := KemSK) identityIndex query)).run consumed)
      (wEncBase caps) (serverUniformCost caps (serverClass query)) := by
  cases query
  case staticDh point =>
    simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_map, simulateQ_spec_query, StateT.run_map]
    refine wBound_map _ (wBound_map _ ?_)
    simp only [PqxdhRegistrationJointKemEncapsulation.forward]
    exact wBound_map _ ((wBound_query _ _ _).mpr (by simp [wEncBase, wPool, PqxdhDynamicIdentityPool.IsCreate,
      PqxdhDynamicIdentityPool.IsUniform, serverUniformCost, serverClass]))
  case encapsulate key =>
    simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_spec_query,
      PqxdhRegistrationJointKemEncapsulation.prefixImpl]
    exact wBound_map _ ((wBound_query _ _ _).mpr (by simp [wEncBase, serverUniformCost, serverClass]))
  all_goals simp only [PqxdhRegistrationJointServerPrefix.compiler, simulateQ_spec_query,
    PqxdhRegistrationJointKemEncapsulation.prefixImpl]
  all_goals exact forwardCoins_cost caps _ (serverAux_total setup codec checks caps bounded _ consumed)

/-- The whole raw prefix with only the encapsulation exposed costs at most `32 + encapsCost`. -/
theorem clientPrefix_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (consumed : List Pqxdh.Bytes) :
    WBound ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
      (PqxdhRegistrationJointServerPrefix.clientPrefix (KemSK := KemSK) identityIndex raw)).run consumed)
      (wEncBase caps) (32 + caps.encapsCost) := by
  rw [PqxdhRegistrationJointServerPrefix.clientPrefix, ← QueryImpl.simulateQ_compose]
  have kinds := wBound_kinds (serverClass (Reader := Reader) (E := PqxdhJointGapDh.ScalarBytes))
    (serverUniformCost caps) PqxdhServerAuthSourceCosts.serverCap
    (PqxdhServerAuthSourceCosts.server_callbacks (Shared := PqxdhBeaconPhase2Preparation.Word32) raw)
  rw [PqxdhServerAuthSourceCosts.server_bill] at kinds
  exact wBound_run _ _ _ (fun query state => by
    rw [QueryImpl.apply_compose]
    exact prefixStep_cost setup codec checks caps bounded identityIndex raw query state) kinds consumed

end Enc

/-! ### The hidden-entry services -/

section Services

/-- The hidden-entry services cost at most one 64-byte commitment per build and per continuation. -/
structure ServiceBills (services : Services V Response) : Prop where
  build : ∀ value token payload server state,
    (((services.hidden value).hiddenBuild token payload server).run state).IsTotalQueryBound 64
  after : ∀ value pending state, (((services.hidden value).hiddenAfter pending).run state).IsTotalQueryBound 64

/-- The factored build of stage S3b costs at most one sealing commitment. -/
theorem factoredBuild_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (value : PqxdhServerAuthKeySchedule.Output) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (server : PqxdhServerAuthEntryFactor.ServerState)
    (state : PqxdhServerAuthEntryFactor.SealState) :
    (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenBuild token payload
      server).run state).IsTotalQueryBound 64 := by
  simp only [PqxdhRegistrationJointKemEntryFactor.factoredHidden, PqxdhServerAuthLoggedSendFactor.factored,
    StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
  exact PqxdhServerAuthEntryFactor.generic_build_uniform _ _ 64
    (PqxdhServerAuthEntryFactor.factored_send_uniform setup codec checks _)
    (PqxdhServerAuthEntryFactor.logged_aux_uniform setup codec checks) _ token.pending payload () _ state

/-- The factored Beacon continuation of stage S3b costs at most one opening commitment. -/
theorem factoredAfter_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (value : PqxdhServerAuthKeySchedule.Output) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (state : RawCtxSharedPrimitive.SharedState Unit) :
    (((PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks value).hiddenAfter pending).run
      state).IsTotalQueryBound 64 := by
  simp only [PqxdhRegistrationJointKemEntryFactor.factoredHidden, PqxdhServerAuthBeaconFactor.factored, pure_bind]
  cases app : codec.application (PqxdhPhase2DhRootConsumer.cleared pending).response with
  | none => trivial
  | some raw =>
      simp only [bind_pure_comp, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
      exact PqxdhServerAuthEntryFactor.generic_raw_uniform _ 64
        (PqxdhServerAuthEntryFactor.factored_receive_uniform setup codec _) _ raw _ state

theorem factoredServices_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    ServiceBills (PqxdhRegistrationJointKemEntryFactor.factoredServices setup codec checks) :=
  ⟨fun value token payload server state => factoredBuild_total setup codec checks value token payload server state,
    fun value pending state => factoredAfter_total setup codec checks value pending state⟩

/-- The native response tail costs at most one sealing commitment. -/
theorem nativeResponse_total (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) (state : PqxdhServerAuthEntryFactor.SealState) :
    ((nativeResponse setup codec checks token payload server).run state).IsTotalQueryBound 64 := by
  rw [PqxdhRegistrationJointKemEntryFactor.hiddenBuild_factor setup codec checks token token rfl]
  exact factoredBuild_total setup codec checks _ token payload server state

theorem nativeServices_bills (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    ServiceBills (nativeServices setup codec checks) := by
  refine ⟨fun root token payload server state => nativeResponse_total setup codec checks token payload server state,
    fun root pending state => ?_⟩
  change (((nativeHidden setup codec checks root).hiddenAfter pending).run state).IsTotalQueryBound 64
  rw [PqxdhRegistrationJointKemEntryFactor.hiddenAfter_factor]
  exact factoredAfter_total setup codec checks _ pending state

end Services

/-! ### The native layer -/

section Native

/-- A game-state computation of the source costs its coins. -/
theorem gameStep_cost {α : Type} (work : StateT (GameState KemSK) ProbComp α) (n : ℕ)
    (bounded : ∀ game, (work.run game).IsTotalQueryBound n) (state : SkelState KemSK V) :
    WBound ((gameStep (V := V) work).run state) (wSkel (V := V)) n := by
  rw [gameStep_run]
  exact wBound_map _ (wBound_liftComp_inl (fun _ => 1) _ (fun _ => rfl) (wBound_of_total (bounded _)))

theorem ctxGame_total {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) (n : ℕ)
    (bounded : ∀ state, (work.run state).IsTotalQueryBound n) (game : GameState KemSK) :
    ((ctxGame work).run game).IsTotalQueryBound n := by
  change ((fun result => (result.1, { game with ctx := result.2.2 })) <$> work.run ((), game.ctx)).IsTotalQueryBound n
  rw [IsTotalQueryBound, isQueryBound_map_iff]
  exact bounded _

theorem tableRead_cost (point : Pqxdh.Bytes) (state : SkelState KemSK V) :
    WBound ((tableRead (KemSK := KemSK) (V := V) point).run state) (wSkel (V := V)) 64 := by
  rw [tableRead_eq]
  exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)

theorem valueRead_cost (point : PqxdhCorrelatedExtractFamily.Message) (state : SkelState KemSK V) :
    WBound ((valueRead (KemSK := KemSK) (V := V) point).run state) (wSkel (V := V)) 0 := by
  rw [valueRead_eq]
  exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)

/-- A Beacon tail callback costs at most one commitment or one direct table read. -/
theorem tailStep_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) (state : SkelState KemSK V) :
    WBound ((tailStep (V := V) setup codec query).run state) (wSkel (V := V)) 64 := by
  rcases query with query | (input | request | response)
  · refine gameStep_cost _ 64 (ctxGame_total _ 64 fun current => ?_) state
    exact (RawCtxSharedPrimitive.native_uniform_step setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source)
      0 (RawCtxSourceHkdf.kdf_uniform setup.source) query current).mono
      (show (if query.isLeft then 0 else if RawCtxSourceOpen.openingPredicate Sum.isLeft query then 64 else 0) ≤ 64 by
        split_ifs <;> omega)
  · change WBound ((tableRead _ >>= fun block => pure _ : NGame KemSK V _).run state) _ 64
    rw [StateT.run_bind]
    simpa using wBound_bind (b := 0) (tableRead_cost _ state) fun _ _ => wBound_pure _ _ _
  · refine gameStep_cost _ 64 (ctxGame_total _ 64 fun current => ?_) state
    simp only [beaconNative]
    trivial
  · refine gameStep_cost _ 64 (ctxGame_total _ 64 fun current => ?_) state
    simp only [beaconNative]
    trivial

/-- A native-layer program of the skeleton costs at most `n` from every state. -/
def NCost {α : Type} (work : NGame KemSK V α) (n : ℕ) : Prop := ∀ state, WBound (work.run state) (wSkel (V := V)) n

theorem ncost_pure {α : Type} (value : α) : NCost (pure value : NGame KemSK V α) 0 := fun _ => trivial

theorem ncost_bind {α β : Type} {work : NGame KemSK V α} {next : α → NGame KemSK V β} {a b : ℕ}
    (first : NCost work a) (rest : ∀ value, NCost (next value) b) : NCost (work >>= next) (a + b) := by
  intro state
  rw [StateT.run_bind]
  exact wBound_bind (first state) fun result _ => rest result.1 result.2

theorem ncost_mono {α : Type} {work : NGame KemSK V α} {a b : ℕ} (cost : NCost work a) (le : a ≤ b) :
    NCost work b := fun state => wBound_mono (cost state) le

theorem ncost_map {α β : Type} (f : α → β) {work : NGame KemSK V α} {n : ℕ} (cost : NCost work n) :
    NCost (f <$> work) n := by
  intro state
  rw [StateT.run_map]
  exact wBound_map _ (cost state)

theorem ncost_game {α : Type} (work : StateT (GameState KemSK) ProbComp α) (n : ℕ)
    (bounded : ∀ game, (work.run game).IsTotalQueryBound n) : NCost (gameStep (V := V) work) n :=
  fun state => gameStep_cost work n bounded state

theorem ncost_table (point : Pqxdh.Bytes) : NCost (tableRead (KemSK := KemSK) (V := V) point) 64 :=
  fun state => tableRead_cost point state

theorem ncost_value (point : PqxdhCorrelatedExtractFamily.Message) :
    NCost (valueRead (KemSK := KemSK) (V := V) point) 0 :=
  fun state => valueRead_cost point state

/-- The Server's core acceptance reads its root once. -/
theorem ncost_client (hmac : PqxdhSecretInputKdf.HmacSha512) (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    NCost (clientStep (KemSK := KemSK) (V := V) hmac control binding input) 64 := by
  unfold clientStep
  split
  · exact ncost_mono (ncost_pure _) (Nat.zero_le _)
  · exact ncost_mono (ncost_pure _) (Nat.zero_le _)
  · exact ncost_mono (ncost_pure _) (Nat.zero_le _)
  · exact ncost_bind (a := 64) (b := 0) (ncost_map _ (ncost_table _)) fun _ =>
      ncost_bind (a := 0) (b := 0) (fun _ => trivial) fun _ => ncost_pure _

/-- The Server's accept tail reads its root once. -/
theorem ncost_acceptTail (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity) (before : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    NCost (acceptTail (V := V) setup publicIdentity before collected) 64 := by
  unfold acceptTail
  dsimp only
  refine ncost_mono (ncost_bind (a := 0) (b := 64) (fun _ => trivial) fun _ => ?_) (by omega)
  rcases collected with ⟨_ | input, consumed⟩
  · exact ncost_mono (ncost_pure _) (Nat.zero_le _)
  · refine ncost_bind (a := 64) (b := 0) (ncost_client _ _ _ _) fun returned => ?_
    split
    · exact ncost_bind (a := 0) (b := 0) (fun _ => trivial) fun _ => ncost_pure _
    · exact ncost_pure _

/-- A build costs at most one sealing commitment. -/
theorem ncost_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (services : Services V Response) (bills : ServiceBills services) (session : Nat) (payload : Option Pqxdh.Bytes) :
    NCost (buildStep (KemSK := KemSK) setup codec checks services session payload) 64 := by
  intro state
  change WBound (match state.1.pending session with
    | none => pure (none, state)
    | some token => _ : OracleComp (SkelSpec V) _) _ 64
  split
  · trivial
  · rename_i token found
    refine wBound_mono (wBound_bind (a := 64) (b := 0) ?_ fun _ _ => wBound_pure _ _ _) (by omega)
    refine wBound_liftComp_inl (fun _ => 1) _ (fun _ => rfl) (wBound_of_total ?_)
    unfold buildService
    rcases state with ⟨game, _ | ⟨index, value⟩⟩
    · exact nativeResponse_total setup codec checks _ _ _ _
    · dsimp only
      by_cases same : index = session
      · simp only [same, ite_true]
        exact bills.build _ _ _ _ _
      · simp only [same, ite_false]
        exact nativeResponse_total setup codec checks _ _ _ _

/-- The adversary's public HMAC reads the table at most once. -/
theorem ncost_hmac (setup : Setup baseSpec KemSK) (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    NCost (hmacStep (KemSK := KemSK) (V := V) setup key message) 64 := by
  unfold hmacStep
  split
  · exact ncost_table _
  · exact ncost_mono (ncost_pure _) (Nat.zero_le _)

/-- A public BLAKE2b request draws at most one 64-byte digest. -/
theorem ncost_hash (bytes : Pqxdh.Bytes) : NCost (gameStep (V := V) (hashGame (KemSK := KemSK) bytes)) 64 := by
  refine ncost_game _ 64 fun game => ?_
  change ((fun result => (result.1, { game with ctx := result.2 })) <$>
    (CtxRomAuth.ctxRandomOracle ((), bytes)).run game.ctx).IsTotalQueryBound 64
  rw [IsTotalQueryBound, isQueryBound_map_iff]
  exact CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) game.ctx

/-- A grouped Beacon finish reads its root (from the table or as a hidden value) and runs its continuation. -/
theorem ncost_group (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (services : Services V Response) (bills : ServiceBills services)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) :
    NCost (groupStep (KemSK := KemSK) setup codec services pending) 128 := by
  unfold groupStep
  split
  · split
    · exact ncost_mono (ncost_bind (a := 0) (b := 64) (ncost_value _) fun value =>
        ncost_game _ 64 (ctxGame_total _ 64 fun state => bills.after value _ state)) (by omega)
    · refine ncost_bind (a := 64) (b := 64) (ncost_table _) fun block => ncost_game _ 64
        (ctxGame_total _ 64 fun state => ?_)
      have := (nativeServices_bills setup codec checks).after
        (PqxdhSecretInputKdf.expandRoot setup.hmac block) (embed pending) state
      rw [PqxdhRegistrationJointKemPostSkeleton.afterRoot_embed]
      exact this
  · exact ncost_mono (ncost_pure _) (Nat.zero_le _)

end Native

/-! ### The grouped interface -/

section Grouped

open PqxdhRegistrationJointServiceCosts (Kind classify poolClass)

/-- The weight of a service class of the source's command interface: an identity creation 32, a KEM decapsulation `decapsCost`, an explicit coin and an other pool request 1, a Beacon tail callback 64, a raw accept `96 + encapsCost`, a build, a public HMAC and a hash 64, and nothing for signing, static DH, KEM creation and reveals. -/
def wKind (caps : KemCaps) : Kind → ℕ
  | .identityCreate => 32
  | .decapsulate => caps.decapsCost
  | .uniform => 1
  | .other => 1
  | .tail => 64
  | .accept => 96 + caps.encapsCost
  | .build => 64
  | .hmac => 64
  | .hash => 64
  | .signing => 0
  | .staticDh => 0
  | .kemCreate => 0
  | .read => 0

/-- The grouped interface: a source command its class weight, a grouped Beacon finish 128. -/
def wG (caps : KemCaps) : (GSpec KemSK Response).Domain → ℕ
  | .inl query => wKind caps (classify (KemSK := KemSK) (Response := Response) query)
  | .inr _ => 128

theorem wPool_le (caps : KemCaps) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) :
    wPool caps query ≤ wKind caps (poolClass query) := by
  rcases query with (coin | request) | (coin | request)
  · simp [wPool, poolClass, wKind, PqxdhDynamicIdentityPool.IsCreate, PqxdhDynamicIdentityPool.IsUniform]
  · rcases request with _ | ⟨_, _ | _⟩ | _ <;>
      simp [wPool, poolClass, wKind, PqxdhDynamicIdentityPool.IsCreate, PqxdhDynamicIdentityPool.IsUniform]
  · simp [wPool, poolClass, wKind]
  · rcases request with _ | ⟨_, _⟩ | _ <;> simp [wPool, poolClass, wKind, PqxdhDynamicKemBounds.IsDecapsulation]

/-- Every native step of the skeleton on the grouped interface costs at most the weight of its request. -/
theorem skelImpl_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (services : Services V Response) (bills : ServiceBills services)
    (query : (GSpec KemSK Response).Domain) (state : SkelState KemSK V) :
    WBound ((skelImpl setup codec checks identityIndex publicIdentity services query).run state) (wEnc (V := V) caps)
      (wG caps query) := by
  rcases query with ((pool | tail) | shared) | pending
  · change WBound ((fun reply => (reply, state)) <$> encLift (V := V) (.inl pool)) _ _
    exact wBound_map _ ((wBound_query _ _ _).mpr (wPool_le caps pool))
  · exact wBound_mono (liftT_cost caps _ state (tailStep_cost setup codec tail state)) (by simp [wG, classify, wKind])
  · cases shared with
    | accept raw =>
        change WBound ((acceptStep (V := V) setup codec checks identityIndex publicIdentity raw).run state) _ _
        unfold acceptStep
        rw [StateT.run_bind]
        refine wBound_mono (wBound_bind (a := 0) (b := 32 + caps.encapsCost + 64) (wBound_pure _ _ _) fun first _ => ?_)
          (by simp [wG, classify, wKind]; omega)
        rw [StateT.run_bind]
        refine wBound_bind (a := 32 + caps.encapsCost) (b := 64) ?_ fun second _ =>
          liftT_cost caps _ _ (ncost_acceptTail setup publicIdentity _ _ _)
        change WBound ((fun result => (result, first.2)) <$> simulateQ (encLift (V := V)) _) _ _
        refine wBound_map _ (wBound_simulate _ (wEncBase caps) _ (fun query => ?_)
          (clientPrefix_cost setup codec checks caps bounded identityIndex raw _))
        rcases query with pool | request
        · exact (wBound_query _ _ _).mpr le_rfl
        · exact (wBound_query _ _ _).mpr le_rfl
    | build session payload =>
        exact wBound_mono (liftT_cost caps _ state (ncost_build setup codec checks services bills session payload state))
          (by simp [wG, classify, wKind])
    | hmac key message =>
        exact wBound_mono (liftT_cost caps _ state (ncost_hmac setup key message state)) (by simp [wG, classify, wKind])
    | hash bytes =>
        exact wBound_mono (liftT_cost caps _ state (ncost_hash bytes state)) (by simp [wG, classify, wKind])
    | reveal keyId =>
        exact wBound_mono (liftT_cost caps _ state (ncost_game (fun game => pure (revealKernel keyId game, game)) 0
          (fun _ => trivial) state)) (Nat.zero_le _)
  · exact liftT_cost caps _ state (ncost_group setup codec checks services bills pending state)

end Grouped

/-! ### The Server's resumption -/

section Resume

open PqxdhRegistrationJointKemOpaqueResume (prefixLift tailLift)

/-- The Server's private tail: 64 for its root request, nothing for the auxiliary and bookkeeping requests. -/
def wTail : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain → ℕ
  | .inl (.inl _) => 64
  | _ => 0

/-- The resumption's interface: the exposed encapsulation interface and the private tail. -/
def wResume (caps : KemCaps) : (PqxdhRegistrationJointKemOpaqueResume.Spec Reader KemSK).Domain → ℕ
  | .inl query => wEncBase (KemSK := KemSK) caps query
  | .inr query => wTail query

/-- Every native step of the resumption costs at most the weight of its request. -/
theorem resumeImpl_cost (caps : KemCaps) (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (services : Services V Response) (query : (PqxdhRegistrationJointKemOpaqueResume.Spec Reader KemSK).Domain)
    (state : SkelState KemSK V) :
    WBound ((resumeImpl hmac index services query).run state) (wEnc (V := V) caps) (wResume caps query) := by
  rcases query with query | ((input | aux) | mutation)
  · change WBound ((fun reply => (reply, state)) <$> encLift (V := V) query) _ _
    refine wBound_map _ ((wBound_query _ _ _).mpr ?_)
    rcases query with _ | _ <;> exact le_rfl
  · refine liftT_cost caps _ state ?_
    show WBound _ _ 64
    simp only [resumeTail]
    split
    · refine ncost_mono (ncost_bind (a := 0) (b := 0) (ncost_value _) fun value => ?_) (Nat.zero_le _) state
      exact ncost_bind (a := 0) (b := 0) (fun current => wBound_pure _ _ _) fun _ => ncost_pure _
    · exact ncost_bind (a := 64) (b := 0) (ncost_table _) (fun _ => ncost_pure _) state
  · refine liftT_cost caps _ state ?_
    cases aux with
    | eraseShared => trivial
    | eraseInput => trivial
    | consume rid => trivial
  · refine liftT_cost caps _ state ?_
    cases mutation with
    | install game => trivial
    | publish slot token => trivial

/-- The source suffix after the encapsulation samples nothing: its callbacks are two conversions and four DH calls. -/
theorem after_free (caps : KemCaps) (verified : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (reply : Option (PqxdhBeaconPhase2Preparation.Ciphertext × PqxdhBeaconPhase2Preparation.Word32)) :
    WBound (PqxdhRegistrationJointKemCollected.afterEncapsulation (Shared := PqxdhBeaconPhase2Preparation.Word32)
      verified ephemeral reply) (fun query => serverUniformCost caps (serverClass query)) 0 := by
  unfold PqxdhRegistrationJointKemCollected.afterEncapsulation
  rcases reply with _ | encapsulated
  all_goals simp only [OptionT.run_bind, OptionT.run_mk, OptionT.run_monadLift, Option.elimM, bind_map_left, pure_bind]
  repeat' first
    | trivial
    | (rw [wBound_query_bind]; refine ⟨by simp [serverClass, serverUniformCost], ?_⟩)
    | (fail_if_no_progress simp only [Option.elim, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM,
        Bool.not_true, Bool.false_eq_true, ite_false])
    | intro answer; cases answer

/-- The candidate-free suffix after the encapsulation draws nothing. -/
theorem compiled_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (verified : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token)
    (consumed : List Pqxdh.Bytes) :
    WBound ((PqxdhRegistrationJointKemOpaqueSuffix.compiled setup codec checks identityIndex raw verified ephemeral
      ciphertext token).run consumed) (wEncBase caps) 0 := by
  unfold PqxdhRegistrationJointKemOpaqueSuffix.compiled
  refine wBound_run _ (fun query => serverUniformCost caps (serverClass query)) _ (fun query state => ?_) ?_ consumed
  · rw [PqxdhRegistrationJointKemSourceSuffix.handler, QueryImpl.apply_compose]
    exact prefixStep_cost setup codec checks caps bounded identityIndex raw query state
  · unfold PqxdhRegistrationJointKemOpaqueSuffix.program
    exact wBound_map _ (after_free caps verified ephemeral _)

/-- The Server's private tail reads its root at most once (`PqxdhRegistrationJointKemOpaqueCosts.client_root`). -/
theorem tail_cost (serverKeyId : U64) (publicIdentity : PublicIdentity) (state : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    WBound (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)
      (wTail (Reader := Reader) (KemSK := KemSK)) 64 := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail
  rw [← Nat.zero_add 64]
  refine wBound_bind ((wBound_query _ _ _).mpr le_rfl) fun _ _ => ?_
  rcases collected with ⟨_ | input, consumed⟩
  · exact wBound_pure _ _ _
  · refine wBound_bind (a := 64) (b := 0) ?_ fun returned _ => ?_
    · refine wBound_simulate _ (fun query => if PqxdhRegistrationJointKemOpaqueCosts.IsRoot query then 64 else 0) _
        (fun query => ?_) ?_
      · rcases query with input | aux
        · exact (wBound_query _ _ _).mpr (by simp [PqxdhRegistrationJointKemOpaqueCosts.IsRoot, wTail])
        · exact (wBound_query _ _ _).mpr (by simp [PqxdhRegistrationJointKemOpaqueCosts.IsRoot, wTail])
      · simpa using wBound_of_isQueryBoundP _ 64 (PqxdhRegistrationJointKemOpaqueCosts.client_root _ _ input)
    · split
      · exact wBound_bind (a := 0) (b := 0) ((wBound_query _ _ _).mpr le_rfl) fun _ _ => wBound_pure _ _ _
      · exact wBound_pure _ _ _

/-- The Server's resumption draws nothing but its root: its suffix after the encapsulation samples nothing. -/
theorem resume_cost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (raw : Pqxdh.Bytes) (verified : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token)
    (state : GameState KemSK) (consumed : List Pqxdh.Bytes) :
    WBound (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw verified
      ephemeral ciphertext token state consumed) (wResume caps) 64 := by
  unfold PqxdhRegistrationJointKemOpaqueResume.resume
  rw [← Nat.zero_add 64]
  refine wBound_bind (wBound_simulate (prefixLift (Reader := Reader)) (wEncBase caps) (wResume caps)
    (fun query => (wBound_query _ _ _).mpr le_rfl)
    (compiled_cost setup codec checks caps bounded identityIndex raw verified ephemeral ciphertext token consumed))
    fun collected _ => ?_
  exact wBound_simulate (tailLift (KemSK := KemSK)) wTail (wResume caps) (fun query => (wBound_query _ _ _).mpr le_rfl)
    (tail_cost setup.serverKeyId publicIdentity state collected)

end Resume

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.forwardCoins_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.forwardCoins_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.serverAux_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.serverAux_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.prefixStep_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.prefixStep_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.clientPrefix_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.clientPrefix_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.factoredBuild_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.factoredBuild_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.factoredAfter_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.factoredAfter_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.factoredServices_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.factoredServices_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.nativeResponse_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.nativeResponse_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.nativeServices_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.nativeServices_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.gameStep_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.gameStep_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ctxGame_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ctxGame_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.tableRead_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.tableRead_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.valueRead_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.valueRead_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.tailStep_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.tailStep_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_table

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_value

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_client

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_acceptTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_acceptTail

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_build

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_hmac

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_group' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.ncost_group

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wPool_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.wPool_le

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.skelImpl_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.skelImpl_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.resumeImpl_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.resumeImpl_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.after_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.after_free

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.compiled_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.compiled_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.tail_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.tail_cost

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.resume_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCosts.resume_cost

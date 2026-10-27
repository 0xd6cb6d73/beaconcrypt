import BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead
import BeaconcryptCore.Computational.PqxdhPhase2SourceAux
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Bounds

/-!
The actual native Phase2 auxiliary callbacks run through the live joint identity and indexed KEM services. Codecs and private DH-pair operations retain their ordinary optional source callbacks and complete local state. Static identity DH uses its original joint seed; other-key decapsulation uses its current indexed creation slot. No selected KEM secret or candidate argument is supplied to this compiler.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLivePhase2Aux
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhKemIndCca PqxdhJointIdentity PqxdhJointKdfGame
open PqxdhBeaconPhase2Routed (AuxSpec)
open PqxdhPhase2JointIdentity (Converted)
open PqxdhLiveKemRouting (Handle)
open PqxdhLiveKemBirth (Spec)
open PqxdhRootTableInitialization (rootArray)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK D Response A : Type}

abbrev Identity := Nat × PublicIdentity

/-- Only original local codec, point conversion and privately owned DH-pair callbacks. No selected-secret, identity-seed or root callback occurs in this interface. -/
inductive LocalQuery (D Response : Type) where
  | decode : Bytes → LocalQuery D Response
  | ciphertext : Response → LocalQuery D Response
  | ephemeral : Response → LocalQuery D Response
  | serverIdentity : Response → LocalQuery D Response
  | publicConversion : Word32 → LocalQuery D Response
  | dhPair : D → Word32 → LocalQuery D Response
  | assignedId : Response → LocalQuery D Response
  | application : Response → LocalQuery D Response

abbrev LocalSpec (D Response : Type) : OracleSpec (LocalQuery D Response)
  | .decode _ => Option Response
  | .ciphertext _ => Option Ciphertext
  | .ephemeral _ | .serverIdentity _ | .publicConversion _ | .dhPair _ _ => Option Word32
  | .assignedId _ => Std.U64
  | .application _ => Option Bytes

abbrev NativeAux (D Response : Type) := AuxSpec Identity D Handle Converted Response
abbrev SharedState (A : Type) := RawCtxSharedPrimitive.SharedState A

/-- Original local state and cache survive each local callback; all random work remains explicit source coins. -/
def localCall (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (LocalSpec D Response).Domain) : StateT (SharedState A) (OracleComp (Spec KemSK)) ((LocalSpec D Response).Range query) :=
  fun state => PqxdhLiveKemBirth.coins
    ((fun result => (result.1, (result.2, state.2))) <$> (callbacks query).run state.1)

/-- The concrete auxiliary compiler keeps the original source callback order and routes correlated identity and KEM operations through their actual private services. -/
noncomputable def aux (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp)) :
    QueryImpl (NativeAux D Response) (StateT (SharedState A) (OracleComp (Spec KemSK)))
  | .decode raw => localCall callbacks (.decode raw)
  | .ciphertext response => localCall callbacks (.ciphertext response)
  | .ephemeral response => localCall callbacks (.ephemeral response)
  | .serverIdentity response => localCall callbacks (.serverIdentity response)
  | .publicConversion value => localCall callbacks (.publicConversion value)
  | .privateConversion identity => pure (some ⟨identity.1, identity.2⟩)
  | .dhPair pair value => localCall callbacks (.dhPair pair value)
  | .dhIdentity converted peer => fun state =>
      (fun reply => (Option.map rootArray reply.join, state)) <$>
        ((Spec KemSK).query (.inl (PqxdhPhase2JointIdentity.request converted (PqxdhPhase2InputBytes.word peer))))
  | .assignedId response => localCall callbacks (.assignedId response)
  | .localDecapsulation ciphertext handle => fun state =>
      (fun reply => (Option.map rootArray reply, state)) <$>
        ((Spec KemSK).query (.inr (.inr (.decapsulate handle.2 (PqxdhPhase2InputBytes.ciphertext ciphertext)))))
  | .initial request => pure (RawCtxSourceHkdf.initialResponse source.crypto request)
  | .application response => localCall callbacks (.application response)
  | .raw query => fun state => PqxdhLiveKemBirth.coins
      ((RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run state)

set_option backward.isDefEq.respectTransparency false in
/-- Complete local callback effects retain the shared cache and both live private service states; all local randomness remains the original program. -/
theorem local_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (LocalSpec D Response).Domain) (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem) ((localCall callbacks query).run auxiliary)).run state =
      (fun result => ((result.1, (result.2, auxiliary.2)), state)) <$> (callbacks query).run auxiliary.1 := by
  simpa only [localCall, StateT.run, Functor.map_map] using
    PqxdhLiveKemBirth.coins_complete baseImpl primitives kem
      ((fun result => (result.1, (result.2, auxiliary.2))) <$> (callbacks query).run auxiliary.1) state

set_option backward.isDefEq.respectTransparency false in
/-- Static DH uses the actual indexed joint seed, preserving missing-index and invalid-peer rejection and the entire joint request/reply history. -/
theorem dh_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (converted : Converted) (peer : Word32) (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((aux source callbacks (.dhIdentity converted peer)).run auxiliary)).run state =
      let reply := state.1.seeds[converted.index]?.map (fun seed => primitives.staticDh seed (PqxdhPhase2InputBytes.word peer))
      pure ((Option.map rootArray reply.join, auxiliary),
        (PqxdhDynamicIdentityPool.record (PqxdhPhase2JointIdentity.request converted (PqxdhPhase2InputBytes.word peer)) reply state.1, state.2)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Indexed native KEM use executes the original optional private-pool callback and retains its complete history, with no public-byte ownership comparison. -/
theorem kem_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (ciphertext : Ciphertext) (handle : Handle) (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((aux source callbacks (.localDecapsulation ciphertext handle)).run auxiliary)).run state =
      (fun result => ((Option.map rootArray result.1, auxiliary), (state.1, result.2))) <$>
        (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate handle.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))).run state.2 := by
  change (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
    ((fun reply => (Option.map rootArray reply, auxiliary)) <$>
      ((Spec KemSK).query (.inr (.inr (.decapsulate handle.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))))))).run state = _
  rw [simulateQ_map, StateT.run_map, simulateQ_spec_query]
  simp only [PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]


set_option backward.isDefEq.respectTransparency false in
/-- Actual raw source evaluation retains its complete shared CTX cache and leaves both live private services unchanged. -/
theorem raw_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : RawCtxSourceOpen.NativeSpec.Domain) (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((aux source callbacks (.raw query)).run auxiliary)).run state =
      (fun result => (result, state)) <$>
        (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run auxiliary := by
  exact PqxdhLiveKemBirth.coins_complete baseImpl primitives kem _ state

/-- The direct local source callback retains the live private state and exact cache. -/
def directLocal (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (LocalSpec D Response).Domain) : StateT (SharedState A × PqxdhLiveKemBirth.State KemSK) ProbComp ((LocalSpec D Response).Range query) :=
  fun state => (fun result => (result.1, ((result.2, state.1.2), state.2))) <$> (callbacks query).run state.1.1

/-- Direct source callbacks expose the exact indexed optional operations and retain every private poststate. -/
noncomputable def direct (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp)) :
    QueryImpl (NativeAux D Response) (StateT (SharedState A × PqxdhLiveKemBirth.State KemSK) ProbComp)
  | .decode raw => directLocal callbacks (.decode raw)
  | .ciphertext response => directLocal callbacks (.ciphertext response)
  | .ephemeral response => directLocal callbacks (.ephemeral response)
  | .serverIdentity response => directLocal callbacks (.serverIdentity response)
  | .publicConversion value => directLocal callbacks (.publicConversion value)
  | .privateConversion identity => pure (some ⟨identity.1, identity.2⟩)
  | .dhPair pair value => directLocal callbacks (.dhPair pair value)
  | .dhIdentity converted peer => fun state =>
      let reply := state.2.1.seeds[converted.index]?.map (fun seed => primitives.staticDh seed (PqxdhPhase2InputBytes.word peer))
      pure (Option.map rootArray reply.join, (state.1,
        (PqxdhDynamicIdentityPool.record (PqxdhPhase2JointIdentity.request converted (PqxdhPhase2InputBytes.word peer)) reply state.2.1, state.2.2)))
  | .assignedId response => directLocal callbacks (.assignedId response)
  | .localDecapsulation ciphertext handle => fun state =>
      (fun result => (Option.map rootArray result.1, (state.1, (state.2.1, result.2)))) <$>
        (PqxdhLiveKemBirth.poolImpl baseImpl kem (.decapsulate handle.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))).run state.2.2
  | .initial request => pure (RawCtxSourceHkdf.initialResponse source.crypto request)
  | .application response => directLocal callbacks (.application response)
  | .raw query => fun state =>
      (fun result => (result.1, (result.2, state.2))) <$>
        (RawCtxSharedPrimitive.nativeImpl source.crypto (RawCtxSourceHkdf.kdfImpl source) query).run state.1

set_option backward.isDefEq.respectTransparency false in
/-- Every optional source callback equals its live-service compilation with complete local, cache, identity and KEM state retained. -/
theorem step_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (NativeAux D Response).Domain) (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem) ((aux source callbacks query).run auxiliary)).run state =
        (direct baseImpl primitives kem source callbacks query).run (auxiliary, state) := by
  cases query with
  | dhIdentity converted peer => rw [dh_source]; rfl
  | localDecapsulation ciphertext handle =>
    rw [kem_source]
    simp only [direct, StateT.run, Functor.map_map]
  | privateConversion identity => rfl
  | initial request => rfl
  | raw query =>
    rw [raw_source]
    simp only [direct, StateT.run, Functor.map_map]
  | _ =>
    simp only [aux]
    rw [local_source]
    simp only [direct, directLocal, StateT.run, Functor.map_map]


set_option backward.isDefEq.respectTransparency false in
/-- The complete original adaptive auxiliary program has the same result and every complete private poststate under live-service execution. This is a syntactic program equality, not only equality of marginal replies. -/
theorem program_source {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (client : OracleComp (NativeAux D Response) Result) (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((simulateQ (aux source callbacks) client).run auxiliary)).run state =
        (fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (direct baseImpl primitives kem source callbacks) client).run (auxiliary, state) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have equal : ((PqxdhLiveKemBirth.impl baseImpl primitives kem).mapStateTBase (aux source callbacks)).flattenStateT =
      direct baseImpl primitives kem source callbacks := by
    funext query before
    exact step_source baseImpl primitives kem source callbacks query before.1 before.2
  rw [equal]


/-- Native dispatch keeps the original preparation, root, raw-receive and finish callback order. Legal fixed-source root HKDF remains real; logical erasure has no primitive response. -/
noncomputable def dispatch {m : Type → Type} [Monad m]
    (source : FixedHkdfSha512NoSaltSource) (handler : QueryImpl (NativeAux D Response) m) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Identity D Handle Converted Response) m
  | .inl (.decode raw) => handler (.decode raw)
  | .inl (.ciphertext response) => handler (.ciphertext response)
  | .inl (.ephemeral response) => handler (.ephemeral response)
  | .inl (.serverIdentity response) => handler (.serverIdentity response)
  | .inl (.publicConversion value) => handler (.publicConversion value)
  | .inl (.privateConversion identity) => handler (.privateConversion identity)
  | .inl (.decapsulate value handle) => handler (.localDecapsulation value handle)
  | .inl (.dhPair pair value) => handler (.dhPair pair value)
  | .inl (.dhIdentity identity value) => handler (.dhIdentity identity value)
  | .inl (.assignedId response) => handler (.assignedId response)
  | .inl (.eraseShared _) => pure ()
  | .inr (.inl query) => handler (.raw query)
  | .inr (.inr (.root input)) => pure (some (RawCtxSourceHkdf.rootResponse source.crypto input))
  | .inr (.inr (.initial request)) => handler (.initial request)
  | .inr (.inr (.application response)) => handler (.application response)

set_option backward.isDefEq.respectTransparency false in
/-- The actual native dispatcher preserves every source callback and complete poststate, including rejection, root evaluation and successful or failed raw opening. -/
theorem native_step_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (PqxdhBeaconPhase2Publication.NativeSpec Identity D Handle Converted Response).Domain)
    (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
        ((dispatch source (aux source callbacks) query).run auxiliary)).run state =
          (dispatch source (direct baseImpl primitives kem source callbacks) query).run (auxiliary, state) := by
  rcases query with preparation | (raw | tail)
  · cases preparation with
    | decode raw => exact step_source baseImpl primitives kem source callbacks (.decode raw) auxiliary state
    | ciphertext response => exact step_source baseImpl primitives kem source callbacks (.ciphertext response) auxiliary state
    | ephemeral response => exact step_source baseImpl primitives kem source callbacks (.ephemeral response) auxiliary state
    | serverIdentity response => exact step_source baseImpl primitives kem source callbacks (.serverIdentity response) auxiliary state
    | publicConversion value => exact step_source baseImpl primitives kem source callbacks (.publicConversion value) auxiliary state
    | privateConversion identity => exact step_source baseImpl primitives kem source callbacks (.privateConversion identity) auxiliary state
    | decapsulate value handle => exact step_source baseImpl primitives kem source callbacks (.localDecapsulation value handle) auxiliary state
    | dhPair pair value => exact step_source baseImpl primitives kem source callbacks (.dhPair pair value) auxiliary state
    | dhIdentity identity value => exact step_source baseImpl primitives kem source callbacks (.dhIdentity identity value) auxiliary state
    | assignedId response => exact step_source baseImpl primitives kem source callbacks (.assignedId response) auxiliary state
    | eraseShared shared => rfl
  · exact step_source baseImpl primitives kem source callbacks (.raw raw) auxiliary state
  · cases tail with
    | root input => rfl
    | initial request => exact step_source baseImpl primitives kem source callbacks (.initial request) auxiliary state
    | application response => exact step_source baseImpl primitives kem source callbacks (.application response) auxiliary state


set_option backward.isDefEq.respectTransparency false in
/-- Every native source continuation preserves the exact full source result and private service state, not just its public marginal. -/
theorem native_program_source {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (client : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec Identity D Handle Converted Response) Result)
    (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((simulateQ (dispatch source (aux source callbacks)) client).run auxiliary)).run state =
        (fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (dispatch source (direct baseImpl primitives kem source callbacks)) client).run (auxiliary, state) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT]
  have equal : ((PqxdhLiveKemBirth.impl baseImpl primitives kem).mapStateTBase (dispatch source (aux source callbacks))).flattenStateT =
      dispatch source (direct baseImpl primitives kem source callbacks) := by
    funext query before
    exact native_step_source baseImpl primitives kem source callbacks query before.1 before.2
  rw [equal]

/-- The actual native Phase2 owner uses those same live identity/KEM services through raw receive, sequence-one and registration binding checks, and complete owner finish. All optional failures and the reached cache remain in the result. -/
theorem owner_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State Identity D Handle)
    (auxiliary : SharedState A) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      ((simulateQ (dispatch source (aux source callbacks))
        (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run auxiliary)).run state =
        (fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (dispatch source (direct baseImpl primitives kem source callbacks))
            (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run (auxiliary, state) :=
  native_program_source baseImpl primitives kem source callbacks _ auxiliary state


/-- Exact nonuniform service cost: one actual indexed static-DH or decapsulation request when that request belongs to the chosen class. -/
def serviceBill (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate] :
    (NativeAux D Response).Domain → Nat
  | .dhIdentity converted peer =>
      if predicate (.inl (PqxdhPhase2JointIdentity.request converted (PqxdhPhase2InputBytes.word peer))) then 1 else 0
  | .localDecapsulation ciphertext handle =>
      if predicate (.inr (.inr (.decapsulate handle.2 (PqxdhPhase2InputBytes.ciphertext ciphertext)))) then 1 else 0
  | _ => 0

set_option backward.isDefEq.respectTransparency false in
/-- Every concrete auxiliary callback pays its exact service request. Arbitrary local source work is confined to, and later charged on, the uniform channel. -/
theorem service_queries (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate]
    (noCoins : ∀ coin, ¬ predicate (.inr (.inl coin)))
    (query : (NativeAux D Response).Domain) (state : SharedState A) :
    ((aux (KemSK := KemSK) source callbacks query).run state).IsQueryBoundP predicate (serviceBill (KemSK := KemSK) predicate query) := by
  have excluded {Result : Type} (work : ProbComp Result) :
      (PqxdhLiveKemBirth.coins (KemSK := KemSK) work).IsQueryBoundP predicate 0 := by
    rw [PqxdhLiveKemBirth.coins_class]
    simpa only [noCoins] using isQueryBoundP_false work 0
  cases query with
  | dhIdentity converted peer =>
    simp only [aux, StateT.run, serviceBill, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    split_ifs <;> simp_all
  | localDecapsulation ciphertext handle =>
    simp only [aux, StateT.run, serviceBill, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    split_ifs <;> simp_all
  | privateConversion identity => trivial
  | initial request => trivial
  | _ => exact excluded _


set_option backward.isDefEq.respectTransparency false in
/-- Original local callbacks pay their full supplied source-coin bound and the actual raw commitment path pays its existing 64-byte allowance. Static DH and KEM service requests retain separate primitive bills after interpretation. -/
theorem uniform_queries (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (query : (NativeAux D Response).Domain) (state : SharedState A) :
    ((aux (KemSK := KemSK) source callbacks query).run state).IsQueryBoundP
      (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) (max qLocal 64) := by
  have coins {Result : Type} (work : ProbComp Result) (q : Nat) (bounded : work.IsTotalQueryBound q) :
      (PqxdhLiveKemBirth.coins (KemSK := KemSK) work).IsQueryBoundP
        (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) q := by
    rw [PqxdhLiveKemBirth.coins_class]
    simpa only [PqxdhDynamicKemJointBounds.IsUniform, isQueryBoundP_true_iff] using bounded
  have localBudget (request : (LocalSpec D Response).Domain) :
      ((localCall (KemSK := KemSK) callbacks request).run state).IsQueryBoundP
        (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) (max qLocal 64) := by
    apply coins
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using
      (localBound request state.1).mono (Nat.le_max_left qLocal 64)
  cases query with
  | dhIdentity converted peer =>
    simp only [aux, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
      PqxdhDynamicKemJointBounds.IsUniform, PqxdhPhase2JointIdentity.request]
    simp
  | localDecapsulation ciphertext handle =>
    simp only [aux, StateT.run, isQueryBoundP_map_iff, isQueryBoundP_query_iff,
      PqxdhDynamicKemJointBounds.IsUniform]
    simp
  | privateConversion identity => trivial
  | initial request => trivial
  | raw request =>
    exact (coins _ 64 (PqxdhPhase2SourceAux.raw_uniform source request state)).mono (Nat.le_max_right qLocal 64)
  | _ => exact localBudget _


/-- Creation or direct private-key disclosure in either indexed service. -/
def IsAllocationOrReveal : (Spec KemSK).Domain → Prop
  | .inl (.inr .create) | .inl (.inr (.reveal _)) => True
  | .inr (.inr .create) | .inr (.inr (.reveal _)) => True
  | _ => False

instance : DecidablePred (IsAllocationOrReveal (KemSK := KemSK)) := fun query => by
  rcases query with (coin | joint) | (coin | kem)
  · exact inferInstanceAs (Decidable False)
  · cases joint <;> simp only [IsAllocationOrReveal] <;> infer_instance
  · exact inferInstanceAs (Decidable False)
  · cases kem <;> simp only [IsAllocationOrReveal] <;> infer_instance

/-- Actual auxiliary execution neither creates nor directly reveals an indexed private key. It requests at most one indexed decapsulation per callback. -/
theorem auxiliary_service_caps (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (query : (NativeAux D Response).Domain) (state : SharedState A) :
    let run := (aux (KemSK := KemSK) source callbacks query).run state
    run.IsQueryBoundP (IsAllocationOrReveal (KemSK := KemSK)) 0 ∧
      run.IsQueryBoundP (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK)) 0 ∧
      run.IsQueryBoundP (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK)) 1 := by
  have allocations := service_queries source callbacks (IsAllocationOrReveal (KemSK := KemSK)) (fun _ => by simp [IsAllocationOrReveal]) query state
  have creates := service_queries source callbacks (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK))
    (fun _ => by simp [PqxdhDynamicKemJointBounds.IsIdentityCreate]) query state
  have decaps := service_queries source callbacks (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK))
    (fun _ => by simp [PqxdhDynamicKemJointBounds.IsDecapsulation]) query state
  constructor
  · cases query <;> simpa [serviceBill, IsAllocationOrReveal, PqxdhPhase2JointIdentity.request] using allocations
  constructor
  · cases query <;> simpa [serviceBill, PqxdhDynamicKemJointBounds.IsIdentityCreate,
      PqxdhDynamicIdentityPool.IsCreate, PqxdhPhase2JointIdentity.request] using creates
  · apply decaps.mono
    cases query <;> simp [serviceBill, PqxdhDynamicKemJointBounds.IsDecapsulation, PqxdhDynamicKemBounds.IsDecapsulation]

/-- Pure root/erasure callbacks add no underlying service request; every other native operation forwards the original auxiliary bill. -/
theorem dispatch_queries {σ κ : Type} {spec : OracleSpec κ}
    (source : FixedHkdfSha512NoSaltSource)
    (handler : QueryImpl (NativeAux D Response) (StateT σ (OracleComp spec)))
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (bound : Nat)
    (bounded : ∀ query state, ((handler query).run state).IsQueryBoundP predicate bound)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec Identity D Handle Converted Response).Domain) (state : σ) :
    ((dispatch source handler query).run state).IsQueryBoundP predicate bound := by
  rcases query with preparation | (raw | tail)
  · cases preparation <;> simp only [dispatch] <;> first | apply bounded | trivial
  · exact bounded (.raw raw) state
  · cases tail <;> simp only [dispatch] <;> first | apply bounded | trivial


/-- Every actual native attempt pays its original 69-callback allowance, including aborting work. No key is allocated or directly revealed; local uniforms and indexed decapsulations stay separate. -/
theorem owner_query_caps (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (qLocal : Nat) (localBound : ∀ query state, ((callbacks query).run state).IsTotalQueryBound qLocal)
    (decode : RawCtxReceive.FrameDecoder) (raw : Bytes)
    (owner : PqxdhBeaconPhase2Preparation.State Identity D Handle) (auxiliary : SharedState A) :
    let run := (simulateQ (dispatch source (aux (KemSK := KemSK) source callbacks))
      (PqxdhBeaconPhase2Publication.nativeOwner decode raw owner)).run auxiliary
    run.IsQueryBoundP (IsAllocationOrReveal (KemSK := KemSK)) 0 ∧
      run.IsQueryBoundP (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK)) 0 ∧
      run.IsQueryBoundP (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK)) 69 ∧
      run.IsQueryBoundP (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) (69 * max qLocal 64) := by
  constructor
  · simpa only [Nat.mul_zero] using PqxdhBeaconPhase2Bounds.native_interpreted_bound
      (dispatch source (aux source callbacks)) (IsAllocationOrReveal (KemSK := KemSK)) 0
      (dispatch_queries source _ _ 0 (fun query state => (auxiliary_service_caps source callbacks query state).1))
      decode raw owner auxiliary
  constructor
  · simpa only [Nat.mul_zero] using PqxdhBeaconPhase2Bounds.native_interpreted_bound
      (dispatch source (aux source callbacks)) (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK)) 0
      (dispatch_queries source _ _ 0 (fun query state => (auxiliary_service_caps source callbacks query state).2.1))
      decode raw owner auxiliary
  constructor
  · simpa only [Nat.mul_one] using PqxdhBeaconPhase2Bounds.native_interpreted_bound
      (dispatch source (aux source callbacks)) (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK)) 1
      (dispatch_queries source _ _ 1 (fun query state => (auxiliary_service_caps source callbacks query state).2.2))
      decode raw owner auxiliary
  · exact PqxdhBeaconPhase2Bounds.native_interpreted_bound
      (dispatch source (aux source callbacks)) (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) (max qLocal 64)
      (dispatch_queries source _ _ _ (uniform_queries source callbacks qLocal localBound))
      decode raw owner auxiliary


end BeaconcryptCore.Computational.PqxdhLivePhase2Aux

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.local_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.local_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.dh_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.dh_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.kem_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.kem_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.raw_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.raw_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.step_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.native_step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.native_step_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.native_program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.native_program_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.owner_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.owner_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.service_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.service_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.uniform_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.uniform_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.auxiliary_service_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.auxiliary_service_caps
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.dispatch_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.dispatch_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase2Aux.owner_query_caps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase2Aux.owner_query_caps

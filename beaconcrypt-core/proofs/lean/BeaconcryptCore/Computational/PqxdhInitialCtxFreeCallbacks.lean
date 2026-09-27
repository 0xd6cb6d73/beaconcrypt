import BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon

/-!
Actual Beacon preparation and application callbacks cannot inspect or change the common CTX cache. This is derived from the existing source interpreter, retaining all local and joint-identity state effects and all rejected decapsulation outcomes. Raw callbacks are deliberately excluded: they use that cache. The cache-free program is the original callback evaluated at the empty cache, with only its cache component projected out.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhPrivateKemSource PqxdhInitializerSecrecy
open PqxdhCorrelatedExpandHybrid PqxdhInitialRootFreeCallbacks
variable {ι I D K X Response A KemSK Result : Type} {baseSpec : OracleSpec ι}

abbrev Cache := CtxRomAuth.CtxRO.QueryCache

def replace (cache : Cache) {count : Nat} (state : SharedState A × BareState count) :
    SharedState A × BareState count := ((state.1.1, cache), state.2)

def reply (cache : Cache) {count : Nat} (result : Result × (SharedState A × BareState count)) :
    Result × (SharedState A × BareState count) := (result.1, replace cache result.2)

def auxiliarySafe : (PqxdhPhase2SourceAux.Spec I D K X Response).Domain → Prop
  | .raw _ => False
  | _ => True

set_option backward.isDefEq.respectTransparency false in
/-- Every actual non-raw auxiliary callback retains the incoming common cache and has exactly the same result, local poststate and joint-identity poststate for every cache. -/
theorem direct_cache
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (PqxdhPhase2SourceAux.Spec I D K X Response).Domain) (safe : auxiliarySafe query)
    (state : SharedState A × BareState count) (cache : Cache) :
    (directAux attachedVerify primitives count fixed localImpl query).run (replace cache state) =
      reply cache <$> (directAux attachedVerify primitives count fixed localImpl query).run state := by
  cases query with
  | privateConversion identity =>
      cases identity <;> simp only [directAux, localRun, replace, reply, StateT.run_mk,
        StateT.run_pure, map_pure, Functor.map_map]
  | dhIdentity identity peer =>
      cases identity <;> simp only [directAux, localRun, replace, reply, StateT.run_mk,
        Functor.map_map]
  | raw query => exact False.elim safe
  | _ => simp only [directAux, localRun, replace, reply, StateT.run_mk,
      StateT.run_pure, map_pure, Functor.map_map]

/-- Public forwarding and ordinary interpretation retain the entire actual auxiliary callback. -/
theorem auxiliary_evaluated
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhPhase2SourceAux.Spec I D K X Response).Domain) (state : SharedState A × BareState count) :
    simulateQ (publicOnly baseImpl kem secret challenge)
      ((PqxdhBeaconPhase2Routed.sharedAux (borrowedAux attachedVerify primitives count fixed localImpl) query).run state) =
        (directAux attachedVerify primitives count fixed localImpl query).run state := by
  have forwarding : publicOnly baseImpl kem secret challenge ∘ₛ PqxdhBeaconPhase2Routed.publicLift =
      PqxdhPhase2PostSource.interpretation baseImpl kem secret challenge := by
    funext query
    exact simulateQ_spec_query (publicOnly baseImpl kem secret challenge) (.inl query)
  change simulateQ (publicOnly baseImpl kem secret challenge)
    (simulateQ PqxdhBeaconPhase2Routed.publicLift
      ((borrowedAux attachedVerify primitives count fixed localImpl query).run state)) = _
  rw [← QueryImpl.simulateQ_compose, forwarding]
  exact PqxdhPhase2PostSource.auxiliary_step attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query state

def fullSafe : (PqxdhBeaconPhase2Shared.FullSpec (PqxdhGeneratedBeaconState.IdentityHandle I) D (Option K)
    (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain → Prop
  | .inr (.inl _) => False
  | _ => True

set_option backward.isDefEq.respectTransparency false in
/-- The actual routed non-raw callbacks preserve and cannot inspect the CTX cache, including blocked selected-key decapsulation and root routing. -/
theorem routed_cache
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhBeaconPhase2Shared.FullSpec (PqxdhGeneratedBeaconState.IdentityHandle I) D (Option K)
      (X ⊕ PqxdhPhase2JointIdentity.Converted) Response PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (safe : fullSafe query) (state : SharedState A × BareState count) (cache : Cache) :
    simulateQ (publicOnly baseImpl kem secret challenge)
      ((PqxdhBeaconPhase2Routed.handles fixed challenge
        (borrowedAux attachedVerify primitives count fixed localImpl) query).run (replace cache state)) =
      reply cache <$> simulateQ (publicOnly baseImpl kem secret challenge)
        ((PqxdhBeaconPhase2Routed.handles fixed challenge
          (borrowedAux attachedVerify primitives count fixed localImpl) query).run state) := by
  rcases query with (query | (query | query))
  · cases query with
    | decapsulate value key =>
        cases key with
        | none =>
            simp only [PqxdhBeaconPhase2Routed.handles, liftM, MonadLiftT.monadLift,
              MonadLift.monadLift, StateT.lift, StateT.run, bind_pure_comp]
            change simulateQ (publicOnly baseImpl kem secret challenge)
              ((fun result => (result, replace cache state)) <$> PqxdhPhase2InputBytes.decapCall challenge value) =
                reply cache <$> simulateQ (publicOnly baseImpl kem secret challenge)
                  ((fun result => (result, state)) <$> PqxdhPhase2InputBytes.decapCall challenge value)
            simp only [simulateQ_map, Functor.map_map, reply, replace]
        | some key =>
            simp only [PqxdhBeaconPhase2Routed.handles, StateT.run_map, simulateQ_map,
              auxiliary_evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge]
            rw [direct_cache attachedVerify primitives count fixed localImpl (.localDecapsulation value key) (by trivial) state cache]
            simp only [Functor.map_map, reply, replace]
    | eraseShared secrets =>
        simp only [PqxdhBeaconPhase2Routed.handles, StateT.run_pure, simulateQ_pure, map_pure, reply, replace]
    | _ =>
        simp only [PqxdhBeaconPhase2Routed.handles, auxiliary_evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge]
        apply direct_cache attachedVerify primitives count fixed localImpl
        trivial
  · exact False.elim safe
  · cases query with
    | root secrets =>
        simp only [PqxdhBeaconPhase2Routed.handles, liftM, MonadLiftT.monadLift,
          MonadLift.monadLift, StateT.lift, StateT.run, bind_pure_comp]
        change simulateQ (publicOnly baseImpl kem secret challenge)
          ((fun result => (result, replace cache state)) <$> PqxdhPhase2InputBytes.rootCall fixed challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4) =
            reply cache <$> simulateQ (publicOnly baseImpl kem secret challenge)
              ((fun result => (result, state)) <$> PqxdhPhase2InputBytes.rootCall fixed challenge secrets.shared secrets.dh1 secrets.dh2 secrets.dh3 secrets.dh4)
        simp only [simulateQ_map, Functor.map_map, reply, replace]
    | _ =>
        simp only [PqxdhBeaconPhase2Routed.handles, auxiliary_evaluated attachedVerify primitives count fixed localImpl baseImpl kem secret challenge]
        apply direct_cache attachedVerify primitives count fixed localImpl
        trivial

def baseSafe : (ActualBaseSpec I D K X Response).Domain → Prop
  | .inr (.inl _) => False
  | _ => True

set_option backward.isDefEq.respectTransparency false in
/-- The actual preparation/application interpreter is independent of the common CTX cache. This is proved from its complete original callback program, rather than assumed for an arbitrary callback. -/
theorem interpreted_cache
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (ActualBaseSpec I D K X Response).Domain) (safe : baseSafe query)
    (state : SharedState A × BareState count) (cache : Cache) :
    (interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run (replace cache state) =
      reply cache <$> (interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state := by
  change simulateQ (publicOnly baseImpl kem secret challenge)
    (work attachedVerify primitives count fixed localImpl challenge query (replace cache state)) =
      reply cache <$> simulateQ (publicOnly baseImpl kem secret challenge)
        (work attachedVerify primitives count fixed localImpl challenge query state)
  rcases query with (query | (query | response))
  · cases query
    all_goals
      simp only [work, original, simulateQ_spec_query, PqxdhPhase2PostScheduler.handles,
        QueryImpl.compose, PqxdhPhase2SharedKemHandles.full, PqxdhPhase2SharedKemHandles.preparation,
        PqxdhBeaconPhase2Shared.preLift]
      apply routed_cache attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      trivial
  · exact False.elim safe
  · simp only [work, original, simulateQ_spec_query, PqxdhPhase2PostScheduler.handles,
      QueryImpl.compose, PqxdhPhase2SharedKemHandles.full]
    apply routed_cache attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
    trivial

/-- This executable callback uses the same original interpreter, evaluated at an empty CTX cache and with only that cache component projected out. -/
noncomputable def cacheFree
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (ActualBaseSpec I D K X Response) (StateT (A × BareState count) ProbComp) :=
  fun query state => (fun result => (result.1, (result.2.1.1, result.2.2))) <$>
    (interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run ((state.1, ∅), state.2)

set_option backward.isDefEq.respectTransparency false in
/-- Restoring the unchanged actual cache after the concrete local callback reproduces the entire original preparation/application distribution and complete poststate. -/
theorem interpreted_local
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (ActualBaseSpec I D K X Response).Domain) (safe : baseSafe query)
    (state : SharedState A × BareState count) :
    (interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state =
      (fun result => (result.1, ((result.2.1, state.1.2), result.2.2))) <$>
        (cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run (state.1.1, state.2) := by
  rcases state with ⟨⟨localState, cache⟩, identityState⟩
  have result := interpreted_cache attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query safe
    ((localState, ∅), identityState) cache
  unfold reply replace at result
  simpa only [cacheFree, StateT.run, Functor.map_map] using result

/-- The literal current Beacon preparation callback runs the concrete cache-free computation and retains both the actual CTX cache and the complete root cache. -/
theorem preparation_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (PqxdhBeaconPhase2Shared.Spec (PqxdhGeneratedBeaconState.IdentityHandle I) D
      (PqxdhGeneratedBeaconState.KemHandle K) (X ⊕ PqxdhPhase2JointIdentity.Converted) Response
      PqxdhPhase2DecapsulationRouting.Shared).Domain)
    (state : SharedState A × BareState count) (roots : PqxdhCorrelatedExpand.RootOracle.QueryCache) :
    PqxdhInitialCurrentBeacon.preparation attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query state roots =
      (fun result => ((result.1, ((result.2.1, state.1.2), result.2.2)), roots)) <$>
        (cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query)).run (state.1.1, state.2) := by
  change (fun result => (result, roots)) <$>
    (interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query)).run state = _
  rw [interpreted_local attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inl query) (by trivial)]
  simp only [Functor.map_map]

/-- The literal current application getter retains its true optional bytes and both caches while running its original local and joint-state callback. -/
theorem application_source
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (response : Response)
    (state : SharedState A × BareState count) (roots : PqxdhCorrelatedExpand.RootOracle.QueryCache) :
    PqxdhInitialCurrentBeacon.application attachedVerify primitives count fixed localImpl baseImpl kem secret challenge response state roots =
      (fun result => ((result.1, ((result.2.1, state.1.2), result.2.2)), roots)) <$>
        (cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inr response))).run (state.1.1, state.2) := by
  change (fun result => (result, roots)) <$>
    (interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inr response))).run state = _
  rw [interpreted_local attachedVerify primitives count fixed localImpl baseImpl kem secret challenge (.inr (.inr response)) (by trivial)]
  simp only [Functor.map_map]

/-- Cache independence removes no actual callback work: the complete uniform-query bound is equivalent to the original source callback's bound at the reached state. -/
theorem cacheFree_uniform
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext)
    (query : (ActualBaseSpec I D K X Response).Domain) (safe : baseSafe query)
    (state : SharedState A × BareState count) (qUniform : Nat) :
    ((cacheFree attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run
      (state.1.1, state.2)).IsTotalQueryBound qUniform ↔
        ((interpreted attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query).run state).IsTotalQueryBound qUniform := by
  rw [interpreted_local attachedVerify primitives count fixed localImpl baseImpl kem secret challenge query safe]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]

end BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.direct_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.direct_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.auxiliary_evaluated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.auxiliary_evaluated

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.routed_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.routed_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.interpreted_cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.interpreted_cache

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.interpreted_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.interpreted_local

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.preparation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.preparation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.application_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.application_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.cacheFree_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialCtxFreeCallbacks.cacheFree_uniform

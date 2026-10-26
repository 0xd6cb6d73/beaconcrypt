import BeaconcryptCore.Computational.PqxdhDynamicKemLiveRead
import BeaconcryptCore.Computational.PqxdhLiveIndexedCreation
import BeaconcryptCore.Computational.PqxdhDynamicKemJointStopping
import BeaconcryptCore.Computational.PqxdhDynamicKemJointBounds

/-!
The compromise adapter reads only the actual currently retained native KEM field. Its stable creation index selects the private pool slot; disposed fields make no pool request. Exact optional replies and full joint/private histories are retained. This is a concrete exposure boundary, not a claim that chain-only freshness already forbids KEM compromise.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead
open PqxdhKemIndCca PqxdhLiveKemRouting
open PqxdhLiveKemBirth (Pool Spec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK I D : Type}

/-- Lift the actual retained-field getter to the complete joint identity/local/KEM source. -/
def read (owner : RawCtxBeaconLifecycle.State I D Handle) : OracleComp (Spec KemSK) (Option KemSK) :=
  simulateQ (fun query => (Spec KemSK).query (.inr (.inr query)))
    (PqxdhDynamicKemLiveRead.read owner)

/-- Native ownership derived from construction identifies the exact retained private slot, regardless of public-key aliases. -/
theorem retained_known (pool : Pool KemSK) (owner : RawCtxBeaconLifecycle.State I D Handle)
    (owned : PqxdhLiveKemOwnership.Owner pool owner) (prekey : D) (handle : Handle)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, handle)) :
    Known pool handle := by
  cases phase : owner.beacon.phase <;>
    simp only [PqxdhLivePhase1State.privateKeys, phase] at retained
  all_goals cases retained
  all_goals simpa only [PqxdhLiveKemOwnership.Owner, phase, PqxdhPhase2KemProvenance.Phase] using owned

/-- The exact native read either has no retained field or records the optional value at that field's original creation index. -/
def observed (pool : Pool KemSK) (owner : RawCtxBeaconLifecycle.State I D Handle) : Option KemSK × Pool KemSK :=
  match PqxdhLivePhase1State.privateKeys owner with
  | none => (none, pool)
  | some pair =>
    let reply := (pool.keys[pair.2.2]?).map Prod.snd
    (reply, PqxdhLiveKemBirth.record (.reveal pair.2.2) reply pool)

set_option backward.isDefEq.respectTransparency false in
/-- The concrete native compromise read has the exact original source reply and full private poststate; all joint identity state is preserved. -/
theorem source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (owner : RawCtxBeaconLifecycle.State I D Handle) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem) (read owner)).run state =
      pure ((observed state.2 owner).1, (state.1, (observed state.2 owner).2)) := by
  unfold read PqxdhDynamicKemLiveRead.read observed
  cases retained : PqxdhLivePhase1State.privateKeys owner with
  | none => rfl
  | some pair =>
    simp only [simulateQ_spec_query, PqxdhLiveKemBirth.impl, PqxdhLiveKemBirth.poolImpl, StateT.run, map_pure]

/-- On an actually owned retained field, compromise returns that slot's real secret and records exactly the successful disclosure. There is no rejection or replacement-secret premise. -/
theorem owned_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (owner : RawCtxBeaconLifecycle.State I D Handle) (state : PqxdhLiveKemBirth.State KemSK)
    (owned : PqxdhLiveKemOwnership.Owner state.2 owner) (prekey : D) (handle : Handle)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, handle)) :
    ∃ secret, state.2.keys[handle.2]? = some (handle.1, secret) ∧
      (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem) (read owner)).run state =
        pure (some secret, (state.1, PqxdhLiveKemBirth.record (.reveal handle.2) (some secret) state.2)) := by
  obtain ⟨secret, lookup⟩ := retained_known state.2 owner owned prekey handle retained
  refine ⟨secret, lookup, ?_⟩
  rw [source]
  simp only [observed, retained, lookup, Option.map_some]

/-- An absent native field rejects before the combined service is consulted, preserving both entire private histories. -/
theorem absent (owner : RawCtxBeaconLifecycle.State I D Handle)
    (missing : PqxdhLivePhase1State.privateKeys owner = none) :
    read (KemSK := KemSK) owner = pure none := by
  simp only [read, PqxdhDynamicKemLiveRead.absent owner missing, simulateQ_pure]

/-- Actual Phase2 finish erases the retained KEM field on success and on terminal rejection; a later compromise makes no private-pool request. -/
theorem finished (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (owner : RawCtxBeaconLifecycle.State I D Handle) (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    read (KemSK := KemSK) (PqxdhBeaconPhase2Publication.finish control owner staged).2 = pure none := by
  apply absent
  cases staged with
  | none => rfl
  | some staged =>
    simp only [PqxdhBeaconPhase2Publication.finish]
    split_ifs <;> rfl

/-- A currently retained native handle is the only way this adapter requests a private-pool reveal. -/
theorem present (owner : RawCtxBeaconLifecycle.State I D Handle) (prekey : D) (handle : Handle)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, handle)) :
    read (KemSK := KemSK) owner = (Spec KemSK).query (.inr (.inr (.reveal handle.2))) := by
  rw [read, PqxdhDynamicKemLiveRead.present owner prekey handle retained]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary monitored source really returns the selected retained secret and records the successful disclosure, without stopping its future continuation. -/
theorem selected_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (owner : RawCtxBeaconLifecycle.State I D Handle) (state : PqxdhDynamicKemJointSource.State KemSK)
    (prekey : D) (target : MlKem768PublicKey) (secret : KemSK)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, (target, selected)))
    (lookup : (pairs.take state.2.created)[selected]? = some (target, secret)) :
    (((simulateQ (PqxdhDynamicKemJointSource.normal baseImpl primitives kem selected pairs)
      (read owner)).run).run state) =
      pure (some (some secret), (state.1,
        PqxdhDynamicKemRouter.record (.reveal selected) (some secret) { state.2 with forbiddenReveal := true })) := by
  rw [present owner prekey (target, selected) retained]
  simp only [simulateQ_spec_query, PqxdhDynamicKemJointSource.normal, OptionT.run_mk, StateT.run,
    PqxdhDynamicKemStopping.normal, lookup, ite_true, map_pure]

set_option backward.isDefEq.respectTransparency false in
/-- The actual selected retained-field read is exactly where the prechallenge reduction stops before supplying its unavailable secret. -/
theorem selected_pre (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (owner : RawCtxBeaconLifecycle.State I D Handle) (state : PqxdhDynamicKemJointSource.State KemSK)
    (prekey : D) (target : MlKem768PublicKey) (slot : PqxdhDynamicKemRouter.Slot KemSK)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, (target, selected)))
    (lookup : PqxdhDynamicKemRouter.lookup reservation state.2 selected = some slot) :
    (((simulateQ (PqxdhDynamicKemJointRouter.pre primitives kem selected reservation)
      (read owner)).run).run state) = pure (none, (state.1, { state.2 with forbiddenReveal := true })) := by
  rw [present owner prekey (target, selected) retained]
  simp only [simulateQ_spec_query, PqxdhDynamicKemJointRouter.pre, PqxdhDynamicKemJointRouter.combine,
    OptionT.run_mk, StateT.run, PqxdhDynamicKemRouter.pre, PqxdhDynamicKemRouter.router, lookup, ite_true, map_pure]

set_option backward.isDefEq.respectTransparency false in
/-- Postchallenge uses the identical native reveal stop; challenge-ciphertext routing does not change compromise semantics. -/
theorem selected_post (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (selected : Nat) (reservation : PqxdhDynamicKemRouter.Reservation KemSK)
    (challenge : MlKem768Ciphertext) (candidate : MlKemSharedSecret)
    (owner : RawCtxBeaconLifecycle.State I D Handle) (state : PqxdhDynamicKemJointSource.State KemSK)
    (prekey : D) (target : MlKem768PublicKey) (slot : PqxdhDynamicKemRouter.Slot KemSK)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, (target, selected)))
    (lookup : PqxdhDynamicKemRouter.lookup reservation state.2 selected = some slot) :
    (((simulateQ (PqxdhDynamicKemJointRouter.post primitives kem selected reservation challenge candidate)
      (read owner)).run).run state) = pure (none, (state.1, { state.2 with forbiddenReveal := true })) := by
  rw [present owner prekey (target, selected) retained]
  simp only [simulateQ_spec_query, PqxdhDynamicKemJointRouter.post, PqxdhDynamicKemJointRouter.combine,
    OptionT.run_mk, StateT.run, PqxdhDynamicKemRouter.post, PqxdhDynamicKemRouter.router, lookup, ite_true, map_pure]

/-- The adversary supplies only a native-owner index. The interpreter selects the actual installed owner before reading its current field. -/
def indexed (owners : List (RawCtxBeaconLifecycle.State I D Handle)) (index : Nat) :
    OracleComp (Spec KemSK) (Option KemSK) :=
  match owners[index]? with
  | none => pure none
  | some owner => read owner

/-- A missing owner rejects before looking up any private service index. -/
theorem indexed_missing (owners : List (RawCtxBeaconLifecycle.State I D Handle)) (index : Nat)
    (missing : owners[index]? = none) : indexed (KemSK := KemSK) owners index = pure none := by
  simp only [indexed, missing]

/-- The installed owner index and private KEM creation index remain distinct: the exact constructor reply resolves to its newly installed field. -/
theorem allocated (primitives : PqxdhJointIdentity.Primitives) (state : PqxdhLiveKemBirth.State KemSK)
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (value : PqxdhLiveBeaconBirth.Created setup KemSK) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : PqxdhLiveOwnerCreation.Owners setup Nat) :
    indexed (KemSK := KemSK)
      (PqxdhLiveOwnerCreation.install binding
        (some (PqxdhLiveKemBirth.handle primitives state.1.seeds.length state.2.keys.length value)) owners).2 owners.length =
      (Spec KemSK).query (.inr (.inr (.reveal state.2.keys.length))) := by
  rw [indexed, (PqxdhLiveIndexedCreation.allocated_lookup primitives state value binding owners).2]
  exact present _ (.inl value.before) (value.target, state.2.keys.length) rfl

set_option backward.isDefEq.respectTransparency false in
/-- Reading the exact newly allocated source owner returns its actual generated secret, retaining all earlier owners and complete joint/private creation histories. -/
theorem allocated_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : PqxdhJointIdentity.Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (state : PqxdhLiveKemBirth.State KemSK)
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (value : PqxdhLiveBeaconBirth.Created setup KemSK) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (owners : PqxdhLiveOwnerCreation.Owners setup Nat) :
    (simulateQ (PqxdhLiveKemBirth.impl baseImpl primitives kem)
      (indexed (PqxdhLiveOwnerCreation.install binding
        (some (PqxdhLiveKemBirth.handle primitives state.1.seeds.length state.2.keys.length value)) owners).2 owners.length)).run
      ((PqxdhDynamicIdentityPool.createdReply primitives state.1 value.seed).2,
        (PqxdhLiveKemBirth.created state.2 (value.target, value.secret)).2) =
      pure (some value.secret,
        ((PqxdhDynamicIdentityPool.createdReply primitives state.1 value.seed).2,
          PqxdhLiveKemBirth.record (.reveal state.2.keys.length) (some value.secret)
            (PqxdhLiveKemBirth.created state.2 (value.target, value.secret)).2)) := by
  rw [allocated]
  simp only [simulateQ_spec_query, PqxdhLiveKemBirth.impl, PqxdhLiveKemBirth.poolImpl, StateT.run,
    (PqxdhLiveKemBirth.created_lookup state.2 (value.target, value.secret)).2, Option.map_some, map_pure]

set_option backward.isDefEq.respectTransparency false in
/-- Native compromise makes at most one private reveal request and no identity-creation, explicit-coin or decapsulation request. Source lookup computation is not a claimed running-time bound. -/
theorem read_queries (owner : RawCtxBeaconLifecycle.State I D Handle) :
    (read (KemSK := KemSK) owner).IsTotalQueryBound 1 ∧
    (read (KemSK := KemSK) owner).IsQueryBoundP (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK)) 0 ∧
    (read (KemSK := KemSK) owner).IsQueryBoundP (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) 0 ∧
    (read (KemSK := KemSK) owner).IsQueryBoundP (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK)) 0 := by
  cases retained : PqxdhLivePhase1State.privateKeys owner with
  | none => rw [absent owner retained]; trivial
  | some pair =>
    rw [present owner pair.1 pair.2 retained]
    refine ⟨⟨Nat.zero_lt_succ 0, fun _ => trivial⟩, ?_, ?_, ?_⟩
    all_goals simp only [isQueryBoundP_query_iff, PqxdhDynamicKemJointBounds.IsIdentityCreate,
      PqxdhDynamicKemJointBounds.IsUniform, PqxdhDynamicKemJointBounds.IsDecapsulation,
      PqxdhDynamicKemBounds.IsDecapsulation, false_implies]

/-- Public native-owner selection preserves the getter's private-request cap and all three complete joint source resource classes, including missing owners. -/
theorem indexed_queries (owners : List (RawCtxBeaconLifecycle.State I D Handle)) (index : Nat) :
    (indexed (KemSK := KemSK) owners index).IsTotalQueryBound 1 ∧
    (indexed (KemSK := KemSK) owners index).IsQueryBoundP (PqxdhDynamicKemJointBounds.IsIdentityCreate (KemSK := KemSK)) 0 ∧
    (indexed (KemSK := KemSK) owners index).IsQueryBoundP (PqxdhDynamicKemJointBounds.IsUniform (KemSK := KemSK)) 0 ∧
    (indexed (KemSK := KemSK) owners index).IsQueryBoundP (PqxdhDynamicKemJointBounds.IsDecapsulation (KemSK := KemSK)) 0 := by
  cases found : owners[index]? with
  | none => rw [indexed_missing owners index found]; trivial
  | some owner => simpa only [indexed, found] using read_queries (KemSK := KemSK) owner

/-- The original source history records a successful selected native compromise; a disclosure-based KEM freshness policy must reject this event independently of any final adversary decision. -/
theorem selected_disclosed (pool : Pool KemSK) (owner : RawCtxBeaconLifecycle.State I D Handle)
    (owned : PqxdhLiveKemOwnership.Owner pool owner) (prekey : D) (target : MlKem768PublicKey) (selected : Nat)
    (retained : PqxdhLivePhase1State.privateKeys owner = some (prekey, (target, selected))) :
    (observed pool owner).2.transcript.any (PqxdhDynamicKemStopping.disclosed selected) = true := by
  obtain ⟨secret, lookup⟩ := retained_known pool owner owned prekey (target, selected) retained
  simp [observed, retained, lookup, PqxdhLiveKemBirth.record, PqxdhDynamicKemStopping.disclosed]

/-- Explicit native disposal prevents a new private reveal while preserving every earlier recorded disclosure. It cannot restore disclosure freshness. -/
theorem disposed (pool : Pool KemSK) (owner : RawCtxBeaconLifecycle.State I D Handle) :
    observed pool (PqxdhLivePhase1State.deleteKem owner) = (none, pool) := by
  simp only [observed, PqxdhLivePhase1State.deleteKem_privateKeys]

end BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead

/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.retained_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.retained_known
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.owned_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.owned_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.absent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.absent
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.finished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.finished
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.present
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_pre' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_pre
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_post
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.indexed_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.indexed_missing
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.allocated' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.allocated
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.allocated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.allocated_source
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.read_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.read_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.indexed_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.indexed_queries
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_disclosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.selected_disclosed
/-- info: 'BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.disposed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDynamicKemNativeRead.disposed

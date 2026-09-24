import BeaconcryptCore.Computational.PqxdhLiveOwnerCreation
import BeaconcryptCore.Computational.PqxdhPhase2KemHandles

/-!
The live constructor receives an indexed KEM handle while its actual generated secret remains inside the private KEM interpreter. The source identity, prekey and KEM generators keep their original order. Public-key byte equality never selects the private owner. Complete creation results retain both private services and every earlier observation; this operational representation alone is not an IND-CCA bound or a selected-target freshness proof.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveKemBirth
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhStatefulPhase1EufCma PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

inductive Query where
  | create
  | decapsulate (handle : Nat) (ciphertext : MlKem768Ciphertext)
  | reveal (handle : Nat)

def Range (KemSK : Type) : Query → Type
  | .create => Nat × MlKem768PublicKey
  | .decapsulate _ _ => Option MlKemSharedSecret
  | .reveal _ => Option KemSK

abbrev PoolSpec (KemSK : Type) : OracleSpec Query := Range KemSK
abbrev Observation (KemSK : Type) := (query : Query) × Range KemSK query

structure Pool (KemSK : Type) where
  keys : List (MlKem768PublicKey × KemSK)
  transcript : List (Observation KemSK)

def empty : Pool KemSK := ⟨[], []⟩

def record (query : Query) (answer : Range KemSK query) (pool : Pool KemSK) : Pool KemSK :=
  { pool with transcript := pool.transcript ++ [⟨query, answer⟩] }

def created (pool : Pool KemSK) (pair : MlKem768PublicKey × KemSK) :
    (Nat × MlKem768PublicKey) × Pool KemSK :=
  let reply := (pool.keys.length, pair.1)
  (reply, record .create reply { pool with keys := pool.keys ++ [pair] })

/-- The actual KEM pair is available only to this private service; clients receive its creation index and public bytes. -/
def poolImpl (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    QueryImpl (PoolSpec KemSK) (StateT (Pool KemSK) ProbComp) := fun query pool =>
  match query with
  | .create => created pool <$> simulateQ (kemAmbientImpl baseImpl) kem.keygen
  | .decapsulate handle ciphertext => do
    let answer ← match pool.keys[handle]? with
      | none => pure none
      | some pair => simulateQ (kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)
    pure (answer, record (.decapsulate handle ciphertext) answer pool)
  | .reveal handle =>
    let answer := (pool.keys[handle]?).map Prod.snd
    pure (answer, record (.reveal handle) answer pool)

abbrev Spec (KemSK : Type) := DynamicSpec + (unifSpec + PoolSpec KemSK)
abbrev State (KemSK : Type) := SourceState × Pool KemSK

def impl (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) :
    QueryImpl (Spec KemSK) (StateT (State KemSK) ProbComp) := fun query state =>
  match query with
  | .inl query => (fun result => (result.1, (result.2, state.2))) <$> (lazyImpl primitives query).run state.1
  | .inr (.inl query) => (fun result => (result, state)) <$> (unifSpec.query query : ProbComp _)
  | .inr (.inr query) => (fun result => (result.1, (state.1, result.2))) <$> (poolImpl baseImpl kem query).run state.2

def coins {Result : Type} (work : ProbComp Result) : OracleComp (Spec KemSK) Result :=
  simulateQ (fun query => (Spec KemSK).query (.inr (.inl query))) work

/-- The original prekey generator precedes the private KEM creation request. No later one-time draw is moved into construction. -/
def afterIdentity (baseImpl : QueryImpl baseSpec ProbComp)
    (setup : StatefulPhase1Setup baseSpec) (identity : Nat × PublicIdentity) :
    OracleComp (Spec KemSK) (PqxdhLiveJointBirth.Created setup Nat) := do
  let before ← coins (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity.2.ed25519))
  let pair ← (Spec KemSK).query (.inr (.inr .create))
  pure ⟨identity.1, identity.2, before, pair.2, pair.1⟩

def create (baseImpl : QueryImpl baseSpec ProbComp) (setup : StatefulPhase1Setup baseSpec) :
    OracleComp (Spec KemSK) (Option (PqxdhLiveJointBirth.Created setup Nat)) := do
  let identity ← (Spec KemSK).query (.inl (.inr .create))
  match identity with
  | none => pure none
  | some identity => some <$> afterIdentity baseImpl setup identity

set_option backward.isDefEq.respectTransparency false in
/-- Every local generator query leaves both complete private services and their histories unchanged. -/
theorem coins_complete {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (work : ProbComp Result) (state : State KemSK) :
    (simulateQ (impl baseImpl primitives kem) (coins work)).run state =
      (fun result => (result, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    change ((unifSpec.query query : ProbComp _) >>= fun reply =>
      (simulateQ (impl baseImpl primitives kem) (coins (next reply))).run state) = _
    simp only [ih, map_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Source prekey generation then actual private KEM generation retain both entire service states and previous histories. -/
theorem afterIdentity_complete (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (identity : Nat × PublicIdentity) (state : State KemSK) :
    (simulateQ (impl baseImpl primitives kem) (afterIdentity baseImpl setup identity)).run state = (do
      let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity.2.ed25519)
      let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
      pure (⟨identity.1, identity.2, before, pair.1, state.2.keys.length⟩,
        (state.1, (created state.2 pair).2))) := by
  simp only [afterIdentity, simulateQ_bind, simulateQ_pure,
    simulateQ_spec_query, StateT.run_bind, StateT.run_pure]
  rw [coins_complete]
  simp only [bind_map_left, impl, poolImpl, StateT.run, created]

/-- Joint requests affect exactly their original private service; the whole KEM pool and its history are retained. -/
theorem joint_step (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (query : DynamicSpec.Domain) (state : State KemSK) :
    (impl baseImpl primitives kem (.inl query)).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (lazyImpl primitives query).run state.1 := rfl

/-- A creation reply records the actual joint public identity and the separate private KEM-service index. -/
def handle (primitives : Primitives) (identityIndex kemIndex : Nat) {setup : StatefulPhase1Setup baseSpec}
    (value : PqxdhLiveBeaconBirth.Created setup KemSK) : PqxdhLiveJointBirth.Created setup Nat :=
  ⟨identityIndex, primitives.publicKeys value.seed, value.before, value.target, kemIndex⟩

set_option backward.isDefEq.respectTransparency false in
/-- The full key-free constructor is the literal source identity/prekey/KEM execution, retaining both private services and every prior history in the same result. -/
theorem create_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (state : State KemSK) :
    (simulateQ (impl baseImpl primitives kem) (create baseImpl setup)).run state = (do
      let value ← PqxdhLiveBeaconBirth.create baseImpl primitives kem setup
      pure (some (handle primitives state.1.seeds.length state.2.keys.length value),
        ((createdReply primitives state.1 value.seed).2,
          (created state.2 (value.target, value.secret)).2))) := by
  simp only [create, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [joint_step, lazyImpl_create]
  simp only [bind_map_left, createdReply, simulateQ_map, StateT.run_map, afterIdentity_complete,
    PqxdhLiveBeaconBirth.create, handle, bind_assoc, pure_bind, map_bind, map_pure]

/-- The complete subsequent computation sees the same generated private states, public handles and all earlier histories. This is not merely equality of marginal key distributions. -/
theorem create_continuation {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (state : State KemSK)
    (next : (Option (PqxdhLiveJointBirth.Created setup Nat) × State KemSK) → ProbComp Result) :
    (simulateQ (impl baseImpl primitives kem) (create baseImpl setup)).run state >>= next = (do
      let value ← PqxdhLiveBeaconBirth.create baseImpl primitives kem setup
      next (some (handle primitives state.1.seeds.length state.2.keys.length value),
        ((createdReply primitives state.1 value.seed).2,
          (created state.2 (value.target, value.secret)).2))) := by
  rw [create_source]
  simp only [bind_assoc, pure_bind]

/-- The returned index resolves to the exact generated pair, independently of equality with any earlier public key bytes. -/
theorem created_lookup (pool : Pool KemSK) (pair : MlKem768PublicKey × KemSK) :
    (created pool pair).1 = (pool.keys.length, pair.1) ∧
      (created pool pair).2.keys[pool.keys.length]? = some pair := by
  simp [created, record]

/-- Later creation never replaces an earlier private owner, even for equal public key encodings. -/
theorem created_prior (pool : Pool KemSK) (pair : MlKem768PublicKey × KemSK)
    (index : Nat) (prior : index < pool.keys.length) :
    (created pool pair).2.keys[index]? = pool.keys[index]? := by
  simp only [created, record, List.getElem?_append_left prior]

/-- Decapsulation uses the exact private pair at the requested creation index and records the actual optional reply. -/
theorem decapsulate_present (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : Pool KemSK) (index : Nat) (pair : MlKem768PublicKey × KemSK)
    (present : pool.keys[index]? = some pair) (ciphertext : MlKem768Ciphertext) :
    (poolImpl baseImpl kem (.decapsulate index ciphertext)).run pool = (do
      let reply ← simulateQ (kemAmbientImpl baseImpl) (kem.decaps pair.2 ciphertext)
      pure (reply, record (.decapsulate index ciphertext) reply pool)) := by
  simp only [poolImpl, StateT.run, present]

/-- An uncreated handle rejects without invoking a primitive, while retaining the rejected attempt in the same history. -/
theorem decapsulate_missing (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : Pool KemSK) (index : Nat) (missing : pool.keys[index]? = none)
    (ciphertext : MlKem768Ciphertext) :
    (poolImpl baseImpl kem (.decapsulate index ciphertext)).run pool =
      pure (none, record (.decapsulate index ciphertext) none pool) := by
  simp only [poolImpl, StateT.run, missing, pure_bind]
  rfl

/-- A KEM reveal returns the actual indexed secret or rejection and records that exact disclosure. Freshness must consume this history; this service does not silently forbid compromise. -/
theorem reveal_step (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (pool : Pool KemSK) (index : Nat) :
    (poolImpl baseImpl kem (.reveal index)).run pool =
      pure ((pool.keys[index]?).map Prod.snd,
        record (.reveal index) ((pool.keys[index]?).map Prod.snd) pool) := rfl

/-- The installed native Fresh owner retains every binding/prekey field, replacing only private identity and KEM representations by their actual separate service handles. -/
theorem fresh_source (primitives : Primitives) (identityIndex kemIndex : Nat)
    {setup : StatefulPhase1Setup baseSpec} (value : PqxdhLiveBeaconBirth.Created setup KemSK)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) :
    PqxdhBeaconPhase1Publication.mapState (fun seed => (identityIndex, primitives.publicKeys seed))
      (fun pair : MlKem768PublicKey × KemSK => (pair.1, kemIndex))
      (PqxdhLiveBeaconBirth.fresh value binding) =
        PqxdhLiveJointBirth.fresh (handle primitives identityIndex kemIndex value) binding := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete constructor pays all source samplers and every interpreted prekey/KEM ambient random query. The two private-service calls do not erase those costs. -/
theorem create_uniform (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (state : State KemSK) (qPrekey qKeygen : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen) :
    ((simulateQ (impl baseImpl primitives kem) (create baseImpl setup)).run state).IsTotalQueryBound
      (32 + (qPrekey + qKeygen)) := by
  rw [create_source]
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhLiveBeaconBirth.create_uniform baseImpl primitives kem setup qPrekey qKeygen prekeyBound keygenBound

set_option backward.isDefEq.respectTransparency false in
/-- Every indexed decapsulation pays its actual interpreted primitive bill; the missing-handle branch still counts as an attempted service request and makes no random draws. -/
theorem decapsulate_uniform (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : Pool KemSK) (index : Nat) (ciphertext : MlKem768Ciphertext) (qDecap : Nat)
    (bounded : ∀ secret,
      (simulateQ (kemAmbientImpl baseImpl) (kem.decaps secret ciphertext)).IsTotalQueryBound qDecap) :
    ((poolImpl baseImpl kem (.decapsulate index ciphertext)).run pool).IsTotalQueryBound qDecap := by
  cases found : pool.keys[index]? with
  | none =>
      rw [decapsulate_missing baseImpl kem pool index found]
      trivial
  | some pair =>
      rw [decapsulate_present baseImpl kem pool index pair found]
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using bounded pair.2

set_option backward.isDefEq.respectTransparency false in
/-- Local randomness is forwarded one-for-one in its own query class, without generating service observations. -/
theorem coins_class {Result : Type} (work : ProbComp Result) (predicate : (Spec KemSK).Domain → Prop)
    [DecidablePred predicate] (bound : Nat) :
    (coins (KemSK := KemSK) work).IsQueryBoundP predicate bound ↔
      work.IsQueryBoundP (fun query => predicate (.inr (.inl query))) bound := by
  induction work using OracleComp.inductionOn generalizing bound with
  | pure value => simp [coins]
  | query_bind query next ih =>
      simp only [coins, simulateQ_bind, simulateQ_spec_query, isQueryBoundP_query_bind_iff]
      exact and_congr Iff.rfl (forall_congr' fun reply => ih reply _)

inductive Kind where
  | joint
  | localUniform
  | kem
  deriving DecidableEq

def IsKind (kind : Kind) : (Spec KemSK).Domain → Prop
  | .inl _ => kind = .joint
  | .inr (.inl _) => kind = .localUniform
  | .inr (.inr _) => kind = .kem

instance (kind : Kind) : DecidablePred (IsKind (KemSK := KemSK) kind) := fun query => by
  rcases query with query | (query | query) <;> simp only [IsKind] <;> infer_instance

/-- Only the local-uniform class is charged by local generation; every actual random query remains counted. -/
theorem coins_bills {Result : Type} (work : ProbComp Result) (q : Nat)
    (bounded : work.IsTotalQueryBound q) (kind : Kind) :
    (coins (KemSK := KemSK) work).IsQueryBoundP (IsKind (KemSK := KemSK) kind)
      (if kind = .localUniform then q else 0) := by
  rw [coins_class]
  cases kind <;> simp_all [IsKind, isQueryBoundP_true_iff]

/-- After joint creation, the source pays its local prekey bill and one private KEM creation request in distinct classes. -/
theorem afterIdentity_bills (baseImpl : QueryImpl baseSpec ProbComp)
    (setup : StatefulPhase1Setup baseSpec) (identity : Nat × PublicIdentity) (qPrekey : Nat)
    (prekeyBound : (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity.2.ed25519)).IsTotalQueryBound qPrekey)
    (kind : Kind) :
    (afterIdentity (KemSK := KemSK) baseImpl setup identity).IsQueryBoundP (IsKind (KemSK := KemSK) kind)
      ((if kind = .localUniform then qPrekey else 0) + (if kind = .kem then 1 else 0)) := by
  apply isQueryBoundP_bind (coins_bills _ qPrekey prekeyBound kind)
  intro before _
  simp only [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff, IsKind]
  cases kind <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- One constructor makes at most one joint creation, one KEM creation and qPrekey local uniform requests. Evaluation additionally charges the full identity/KEM sampler bills above. -/
theorem create_bills (baseImpl : QueryImpl baseSpec ProbComp)
    (setup : StatefulPhase1Setup baseSpec) (qPrekey : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (kind : Kind) :
    (create (KemSK := KemSK) baseImpl setup).IsQueryBoundP (IsKind (KemSK := KemSK) kind)
      ((if kind = .joint then 1 else 0) +
        ((if kind = .localUniform then qPrekey else 0) + (if kind = .kem then 1 else 0))) := by
  unfold create
  apply isQueryBoundP_bind
  · cases kind <;> simp [isQueryBoundP_query_iff, IsKind]
  · intro identity _
    cases identity with
    | none => simp
    | some identity =>
      simpa only [isQueryBoundP_map_iff] using afterIdentity_bills baseImpl setup identity qPrekey (prekeyBound _) kind

end BeaconcryptCore.Computational.PqxdhLiveKemBirth

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.coins_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.coins_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.afterIdentity_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.afterIdentity_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.joint_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.joint_step

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.created_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.created_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.created_prior' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.created_prior

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.decapsulate_present' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.decapsulate_present

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.decapsulate_missing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.decapsulate_missing

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.reveal_step' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.reveal_step

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.fresh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.fresh_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.decapsulate_uniform' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.decapsulate_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.coins_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.coins_class

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.coins_bills' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.coins_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.afterIdentity_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.afterIdentity_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveKemBirth.create_bills

import BeaconcryptCore.Computational.PqxdhLiveBeaconBirth
import BeaconcryptCore.Computational.PqxdhDynamicIdentityPool

/-!
The live constructor asks the existing joint identity service to allocate its seed, then generates the prekey and KEM pair locally in source order. The client receives only the stable index and correlated public identity. Its complete interpretation retains the actual seed inside the joint service and every previous observation. Local primitive randomness is a separate counted interface and does not enter the public joint transcript.
-/

open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveJointBirth
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhPrivateKemSource PqxdhStatefulPhase1EufCma PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

abbrev Spec := DynamicSpec + unifSpec

structure Created (setup : StatefulPhase1Setup baseSpec) (KemSK : Type) where
  index : Nat
  publicIdentity : PublicIdentity
  before : PrivatePrekey setup.PrivatePre
  target : TargetKemPublicKey
  secret : KemSK

def coins {A : Type} (work : ProbComp A) : OracleComp Spec A :=
  simulateQ (fun query => (Spec.query (.inr query) : OracleComp Spec _)) work

def impl (primitives : Primitives) : QueryImpl Spec (StateT SourceState ProbComp) :=
  fun query state => match query with
  | .inl request => (lazyImpl primitives request).run state
  | .inr request => do
      let reply ← unifSpec.query request
      pure (reply, state)

def afterIdentity (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (identity : Nat × PublicIdentity) :
    OracleComp Spec (Created setup KemSK) := do
  let before ← coins (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity.2.ed25519))
  let pair ← coins (simulateQ (kemAmbientImpl baseImpl) kem.keygen)
  pure ⟨identity.1, identity.2, before, pair.1, pair.2⟩

def create (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) : OracleComp Spec (Option (Created setup KemSK)) := do
  let identity ← Spec.query (.inl (.inr .create))
  match identity with
  | none => pure none
  | some identity => some <$> afterIdentity baseImpl kem setup identity

set_option backward.isDefEq.respectTransparency false in
/-- Local generation samples retain the entire joint identity state; they are not extra identity-service observations. -/
theorem coins_complete {A : Type} (primitives : Primitives) (work : ProbComp A) (state : SourceState) :
    (simulateQ (impl primitives) (coins work)).run state = (fun result => (result, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
    change ((unifSpec.query query : ProbComp _) >>= fun reply =>
      (simulateQ (impl primitives) (coins (next reply))).run state) = _
    simp only [ih, map_bind]

set_option backward.isDefEq.respectTransparency false in
/-- Both local generators run after the joint public reply and retain the complete identity-service state. -/
theorem afterIdentity_complete (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (identity : Nat × PublicIdentity) (state : SourceState) :
    (simulateQ (impl primitives) (afterIdentity baseImpl kem setup identity)).run state = (do
      let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity.2.ed25519)
      let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
      pure (⟨identity.1, identity.2, before, pair.1, pair.2⟩, state)) := by
  simp only [afterIdentity, simulateQ_bind, simulateQ_pure, StateT.run_bind, coins_complete,
    StateT.run_pure, bind_map_left]

/-- The joint branch uses the existing lazy service without reading its private seed in the constructor client. -/
theorem joint_complete (primitives : Primitives) (request : DynamicSpec.Domain) (state : SourceState) :
    (impl primitives (.inl request)).run state = (lazyImpl primitives request).run state := rfl

def handle (primitives : Primitives) (index : Nat) {setup : StatefulPhase1Setup baseSpec}
    (created : PqxdhLiveBeaconBirth.Created setup KemSK) : Created setup KemSK :=
  ⟨index, primitives.publicKeys created.seed, created.before, created.target, created.secret⟩

set_option backward.isDefEq.respectTransparency false in
/-- The key-free constructor is the actual source constructor with its seed retained only in the complete joint service state. No generator is exchanged with a continuation. -/
theorem create_complete (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (state : SourceState) :
    (simulateQ (impl primitives) (create baseImpl kem setup)).run state = (do
      let created ← PqxdhLiveBeaconBirth.create baseImpl primitives kem setup
      pure (some (handle primitives state.seeds.length created),
        (createdReply primitives state created.seed).2)) := by
  simp only [create, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    joint_complete, lazyImpl_create, bind_map_left, createdReply, simulateQ_map,
    StateT.run_map, afterIdentity_complete, PqxdhLiveBeaconBirth.create, bind_assoc, pure_bind,
    map_bind, map_pure, handle]

/-- Every later decision sees the same full generated values, prior transcript and retained private seed. -/
theorem create_continuation {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp)
    (primitives : Primitives) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (state : SourceState)
    (next : (Option (Created setup KemSK) × SourceState) → ProbComp Result) :
    (simulateQ (impl primitives) (create baseImpl kem setup)).run state >>= next = (do
      let created ← PqxdhLiveBeaconBirth.create baseImpl primitives kem setup
      next (some (handle primitives state.seeds.length created),
        (createdReply primitives state created.seed).2)) := by
  rw [create_complete]
  simp only [bind_assoc, pure_bind]

/-- The returned stable index refers to the actual newly generated seed inside the joint interpreter. -/
theorem created_seed (primitives : Primitives) (state : SourceState) (seed : IdentitySeed) :
    (createdReply primitives state seed).2.seeds[state.seeds.length]? = some seed := by
  simp [createdReply, record]

/-- Earlier joint identity indices keep their actual seeds; creation never relabels an existing owner. -/
theorem created_prior (primitives : Primitives) (state : SourceState) (seed : IdentitySeed)
    (index : Nat) (prior : index < state.seeds.length) :
    (createdReply primitives state seed).2.seeds[index]? = state.seeds[index]? := by
  simp [createdReply, record, List.getElem?_append_left prior]

abbrev Beacon (setup : StatefulPhase1Setup baseSpec) (KemSK : Type) :=
  RawCtxBeaconLifecycle.State (Nat × PublicIdentity) (PqxdhGeneratedBeaconState.DhPair setup)
    (TargetKemPublicKey × KemSK)

def fresh {setup : StatefulPhase1Setup baseSpec} (created : Created setup KemSK)
    (binding : beaconcrypt_core.pqxdh.ServerBinding) : Beacon setup KemSK :=
  ⟨⟨(created.index, created.publicIdentity), binding.identity_key_id, binding.identity_public_key,
    .fresh ⟨binding⟩ (.inl created.before) (created.target, created.secret)⟩, 0⟩

/-- Installing the public identity handle preserves the entire original native Fresh role, including its actual private prekey/KEM pair and pinned server binding. -/
theorem fresh_source (primitives : Primitives) (index : Nat) {setup : StatefulPhase1Setup baseSpec}
    (created : PqxdhLiveBeaconBirth.Created setup KemSK) (binding : beaconcrypt_core.pqxdh.ServerBinding) :
    PqxdhBeaconPhase1Publication.mapState (fun seed => (index, primitives.publicKeys seed)) id
      (PqxdhLiveBeaconBirth.fresh created binding) = fresh (handle primitives index created) binding := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every local sampling request is retained in its own exact query class. -/
theorem coins_class {A : Type} (work : ProbComp A) (predicate : Spec.Domain → Prop)
    [DecidablePred predicate] (bound : Nat) :
    (coins work).IsQueryBoundP predicate bound ↔
      work.IsQueryBoundP (fun query => predicate (.inr query)) bound := by
  induction work using OracleComp.inductionOn generalizing bound with
  | pure value => simp [coins]
  | query_bind query next ih =>
    simp only [coins, simulateQ_bind, simulateQ_spec_query, isQueryBoundP_query_bind_iff]
    exact and_congr Iff.rfl (forall_congr' fun reply => ih reply _)

inductive Kind where
  | joint
  | localUniform
  deriving DecidableEq

def IsKind (kind : Kind) : Spec.Domain → Prop
  | .inl _ => kind = .joint
  | .inr _ => kind = Kind.localUniform

instance (kind : Kind) : DecidablePred (IsKind kind) := fun query => by
  cases query <;> simp only [IsKind] <;> infer_instance

/-- Local callback work charges all of its uniform queries and makes no joint identity request. -/
theorem coins_bills {A : Type} (work : ProbComp A) (q : Nat) (bounded : work.IsTotalQueryBound q)
    (kind : Kind) : (coins work).IsQueryBoundP (IsKind kind)
      (if kind = Kind.localUniform then q else 0) := by
  rw [coins_class]
  cases kind <;> simp_all [IsKind, isQueryBoundP_true_iff]

/-- Both locally evaluated primitive callbacks are counted, including every ambient uniform query. -/
theorem afterIdentity_bills (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (identity : Nat × PublicIdentity)
    (qPrekey qKeygen : Nat)
    (prekeyBound : (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity.2.ed25519)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (kind : Kind) :
    (afterIdentity baseImpl kem setup identity).IsQueryBoundP (IsKind kind)
      (if kind = Kind.localUniform then qPrekey + qKeygen else 0) := by
  have nextBound (before : PrivatePrekey setup.PrivatePre) :
      (do let pair ← coins (simulateQ (kemAmbientImpl baseImpl) kem.keygen)
          pure (⟨identity.1, identity.2, before, pair.1, pair.2⟩ : Created setup KemSK)).IsQueryBoundP
        (IsKind kind) (if kind = Kind.localUniform then qKeygen else 0) := by
    simpa only [bind_pure_comp, isQueryBoundP_map_iff] using coins_bills _ qKeygen keygenBound kind
  have total := isQueryBoundP_bind (coins_bills _ qPrekey prekeyBound kind) (fun before _ => nextBound before)
  cases kind <;> simpa only [afterIdentity, bind_pure_comp, reduceCtorEq, if_true, if_false, Nat.zero_add] using total

set_option backward.isDefEq.respectTransparency false in
/-- One live creation makes one joint create request and charges both local primitive samplers, including optional service rejection. -/
theorem create_bills (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (qPrekey qKeygen : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (kind : Kind) :
    (create baseImpl kem setup).IsQueryBoundP (IsKind kind)
      ((if kind = .joint then 1 else 0) + (if kind = Kind.localUniform then qPrekey + qKeygen else 0)) := by
  cases kind <;> simp only [create, IsKind, reduceCtorEq, if_true, if_false, Nat.add_zero, Nat.zero_add,
    isQueryBoundP_query_bind_iff]
  all_goals simp only [not_true_eq_false, false_or, Nat.zero_lt_succ, true_and, not_false_eq_true, true_or, Nat.sub_self]
  all_goals rintro (_ | identity)
  all_goals simp only [isQueryBoundP_pure, isQueryBoundP_map_iff]
  all_goals first
    | exact afterIdentity_bills baseImpl kem setup identity qPrekey qKeygen (prekeyBound _) keygenBound .joint
    | exact afterIdentity_bills baseImpl kem setup identity qPrekey qKeygen (prekeyBound _) keygenBound .localUniform

/-- Evaluating the actual joint creation also pays the challenger's 32 seed bytes; local prekey/KEM callback sampling is additional. -/
theorem create_uniform (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (state : SourceState) (qPrekey qKeygen : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen) :
    ((simulateQ (impl primitives) (create baseImpl kem setup)).run state).IsTotalQueryBound
      (32 + (qPrekey + qKeygen)) := by
  rw [create_complete]
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhLiveBeaconBirth.create_uniform baseImpl primitives kem setup qPrekey qKeygen prekeyBound keygenBound

end BeaconcryptCore.Computational.PqxdhLiveJointBirth

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.coins_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.coins_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.afterIdentity_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.afterIdentity_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.joint_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.joint_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.created_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.created_seed
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.created_prior' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.created_prior
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.fresh_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.fresh_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.coins_class' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.coins_class
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.coins_bills' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.coins_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.afterIdentity_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.afterIdentity_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_bills
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointBirth.create_uniform

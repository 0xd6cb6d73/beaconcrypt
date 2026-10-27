import BeaconcryptCore.Computational.PqxdhGeneratedBeaconState
import BeaconcryptCore.Computational.PqxdhPrivateRootGameBudgets

/-!
The live native constructor ends after identity, prekey and KEM generation. It does not generate the registration one-time pair. The complete private result can therefore be installed before an arbitrary later source continuation. Only an adjacent subsequent one-time generation is identified with the earlier atomic Phase1 generator; no interleaving is moved across a random draw.

This is the normal-return, validated-binding constructor interface. Primitive generation, conversion and the native binding parser keep their functional contracts. No public request receives the private constructor result. The later dynamic owner, compromise and registration interpreters must consume this private state; this module alone supplies no global secrecy or replication theorem.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveBeaconBirth
open PqxdhJointIdentity PqxdhPrivateKemSource PqxdhStatefulPhase1EufCma PqxdhKemIndCca
open PqxdhInitializerSecrecy (kemAmbientImpl)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The constructor retains exactly the three generated private values. There is no one-time pair yet. -/
structure Created (setup : StatefulPhase1Setup baseSpec) (KemSK : Type) where
  seed : IdentitySeed
  before : PrivatePrekey setup.PrivatePre
  target : TargetKemPublicKey
  secret : KemSK

/-- Native `try_new` generation order after initialization and server-binding validation have succeeded. -/
def create (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) : ProbComp (Created setup KemSK) := do
  let seed ← sampleSeed
  let before ← simulateQ (kemAmbientImpl baseImpl) (setup.prekey (primitives.publicKeys seed).ed25519)
  let pair ← simulateQ (kemAmbientImpl baseImpl) kem.keygen
  pure ⟨seed, before, pair.1, pair.2⟩

/-- When a Fresh owner later requests its bundle, the source draws the one-time pair at that call. -/
def complete (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (created : Created setup KemSK) :
    ProbComp (Generated setup KemSK) := do
  let after ← simulateQ (kemAmbientImpl baseImpl)
    (setup.oneTime (primitives.publicKeys created.seed).ed25519 created.before created.target)
  pure ⟨created.before, created.target, created.secret, after⟩

/-- The ordinary native role owns the actual private representations; it is not an adversary observation. -/
abbrev Beacon (setup : StatefulPhase1Setup baseSpec) (KemSK : Type) :=
  RawCtxBeaconLifecycle.State IdentitySeed (PqxdhGeneratedBeaconState.DhPair setup)
    (TargetKemPublicKey × KemSK)

def fresh {setup : StatefulPhase1Setup baseSpec}
    (created : Created setup KemSK) (binding : pqxdh.ServerBinding) : Beacon setup KemSK :=
  ⟨⟨created.seed, binding.identity_key_id, binding.identity_public_key,
    .fresh ⟨binding⟩ (.inl created.before) (created.target, created.secret)⟩, 0⟩

/-- Constructor and immediately following bundle generation retain the old generator's entire continuation, without any exchange of source operations. -/
theorem adjacent_complete {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (next : IdentitySeed → Generated setup KemSK → ProbComp Result) :
    (do let created ← create baseImpl primitives kem setup
        let generated ← complete baseImpl primitives setup created
        next created.seed generated) =
      (do let seed ← sampleSeed
          let generated ← generate baseImpl kem setup (primitives.publicKeys seed).ed25519
          next seed generated) := by
  simp only [create, complete, generate, bind_assoc, pure_bind]

/-- Creation is charged before any later registration request, including all ambient sampling used by the primitive callbacks. -/
theorem create_uniform
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (qPrekey qKeygen : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen) :
    (create baseImpl primitives kem setup).IsTotalQueryBound (32 + (qPrekey + qKeygen)) := by
  unfold create
  apply isTotalQueryBound_bind sampleSeed_uniform_bound
  intro seed
  apply isTotalQueryBound_bind (prekeyBound _)
  intro before
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using keygenBound

/-- The later one-time draw has its own bill and uses the actual retained prekey and KEM public key. -/
theorem complete_uniform
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (setup : StatefulPhase1Setup baseSpec) (qOneTime : Nat)
    (oneTimeBound : ∀ identity before target,
      (simulateQ (kemAmbientImpl baseImpl) (setup.oneTime identity before target)).IsTotalQueryBound qOneTime)
    (created : Created setup KemSK) :
    (complete baseImpl primitives setup created).IsTotalQueryBound qOneTime := by
  simpa only [complete, bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    oneTimeBound (primitives.publicKeys created.seed).ed25519 created.before created.target

/-- Membership concerns the actual locally generated pair, without imposing any condition on an adversary's later selected key. -/
theorem create_key_support
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (created : Created setup KemSK)
    (actual : created ∈ support (create baseImpl primitives kem setup)) :
    (created.target, created.secret) ∈ support (simulateQ (kemAmbientImpl baseImpl) kem.keygen) := by
  simp only [create, mem_support_bind_iff] at actual
  obtain ⟨seed, _, before, _, pair, present, finished⟩ := actual
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
  exact present

/-- Every native constructor field comes from the validated binding or the retained private generation. -/
theorem fresh_fields {setup : StatefulPhase1Setup baseSpec}
    (created : Created setup KemSK) (binding : pqxdh.ServerBinding) :
    (fresh created binding).beacon.identity = created.seed ∧
    (fresh created binding).beacon.identityKeyId = binding.identity_key_id ∧
    (fresh created binding).beacon.serverIdentity = binding.identity_public_key ∧
    (fresh created binding).beacon.phase =
      .fresh ⟨binding⟩ (.inl created.before) (created.target, created.secret) ∧
    (fresh created binding).rawAttempts = 0 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Replacing private identity/KEM representations by their generated handles preserves the entire original Fresh object, independently of any later one-time sample. -/
theorem fresh_handles {I K : Type} {setup : StatefulPhase1Setup baseSpec}
    (primitives : Primitives) (created : Created setup KemSK) (binding : pqxdh.ServerBinding)
    (index : Nat) (after : PrivateOneTime setup.PrivateOne) :
    PqxdhBeaconPhase1Publication.mapState
      (fun seed => (PqxdhGeneratedBeaconState.IdentityHandle.generated index (primitives.publicKeys seed) :
        PqxdhGeneratedBeaconState.IdentityHandle I))
      (fun pair => (PqxdhGeneratedBeaconState.KemHandle.generated index pair.1 :
        PqxdhGeneratedBeaconState.KemHandle K)) (fresh created binding) =
      PqxdhGeneratedBeaconState.fresh setup index (primitives.publicKeys created.seed)
        ⟨created.before, created.target, (), after⟩ binding := rfl

/-- A dynamic family retains stable native indices; only the private family stores the generated secrets. -/
abbrev Pool (setup : StatefulPhase1Setup baseSpec) (KemSK : Type) := List (Beacon setup KemSK)

def install {setup : StatefulPhase1Setup baseSpec}
    (binding : pqxdh.ServerBinding) (created : Created setup KemSK) (pool : Pool setup KemSK) :
    Nat × Pool setup KemSK :=
  (pool.length, pool ++ [fresh created binding])

/-- Successful native construction publishes a new handle while retaining every earlier live owner. -/
def allocate (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : pqxdh.ServerBinding) :
    StateT (Pool setup KemSK) ProbComp Nat := fun pool =>
  (fun created => install binding created pool) <$> create baseImpl primitives kem setup

/-- No later API operation is commuted before creation; the arbitrary continuation sees the installed full state. -/
theorem allocate_continuation {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec) (binding : pqxdh.ServerBinding) (pool : Pool setup KemSK)
    (next : Nat × Pool setup KemSK → ProbComp Result) :
    (allocate baseImpl primitives kem setup binding).run pool >>= next =
      (do let created ← create baseImpl primitives kem setup
          next (install binding created pool)) := by
  simp only [allocate, StateT.run, bind_map_left]

/-- Allocation does not renumber or overwrite an existing owner. -/
theorem install_prior {setup : StatefulPhase1Setup baseSpec}
    (binding : pqxdh.ServerBinding) (created : Created setup KemSK) (pool : Pool setup KemSK)
    (index : Nat) (present : index < pool.length) :
    (install binding created pool).2[index]? = pool[index]? := by
  simp [install, List.getElem?_append_left present]

/-- The returned handle selects the complete fresh object, with one additional owner and no collision with a prior index. -/
theorem install_new {setup : StatefulPhase1Setup baseSpec}
    (binding : pqxdh.ServerBinding) (created : Created setup KemSK) (pool : Pool setup KemSK) :
    (install binding created pool).1 = pool.length ∧
    (install binding created pool).2.length = pool.length + 1 ∧
    (install binding created pool).2[(install binding created pool).1]? = some (fresh created binding) := by
  simp [install]

variable {κ A : Type} {localSpec : OracleSpec κ}

/-- Creation returns only a stable index; every subsequent capability remains the original selected-owner request. -/
inductive Request (localSpec : OracleSpec κ) where
  | create (binding : pqxdh.ServerBinding)
  | owner (index : Nat) (request : localSpec.Domain)

def Reply (localSpec : OracleSpec κ) : Request localSpec → Type
  | .create _ => Nat
  | .owner _ request => Option (localSpec.Range request)

abbrev Spec (localSpec : OracleSpec κ) : OracleSpec (Request localSpec) := Reply localSpec

/-- Dynamic birth and live owner calls share one private pool and one primitive/application state. Missing indices reject before calling an owner. -/
def impl (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp)) :
    QueryImpl (Spec localSpec) (StateT (Pool setup KemSK × A) ProbComp) := fun request state =>
  match request with
  | .create binding => do
      let created ← create baseImpl primitives kem setup
      let installed := install binding created state.1
      pure (installed.1, (installed.2, state.2))
  | .owner index request =>
      match state.1[index]? with
      | none => pure (none, state)
      | some beacon => do
          let result ← (owner request).run (beacon, state.2)
          pure (some result.1, (state.1.set index result.2.1, result.2.2))

/-- A request at an uncreated index has no primitive side effect and exposes no placeholder owner. -/
theorem owner_missing (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp))
    (index : Nat) (request : localSpec.Domain) (state : Pool setup KemSK × A)
    (missing : state.1[index]? = none) :
    (impl baseImpl primitives kem setup owner (.owner index request)).run state =
      pure (none, state) := by
  simp only [impl, StateT.run, missing]
  rfl

/-- An existing owner is called with the original request and actual common state; its full returned owner is reinstalled before continuation. -/
theorem owner_present (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp))
    (index : Nat) (request : localSpec.Domain) (state : Pool setup KemSK × A)
    (beacon : Beacon setup KemSK) (present : state.1[index]? = some beacon) :
    (impl baseImpl primitives kem setup owner (.owner index request)).run state =
      (do let result ← (owner request).run (beacon, state.2)
          pure (some result.1, (state.1.set index result.2.1, result.2.2))) := by
  simp only [impl, StateT.run, present]

/-- Birth and live owner calls are separate source query classes. -/
def IsBirth : (Spec localSpec).Domain → Prop
  | .create _ => True
  | .owner _ _ => False

instance : DecidablePred (IsBirth (localSpec := localSpec)) := fun request => by
  cases request <;> simp only [IsBirth] <;> infer_instance

/-- Birth pays all three source generators; a live call pays its actual selected-owner implementation. Missing indices use no random draw. -/
theorem step_uniform
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp))
    (qPrekey qKeygen qOwner : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (ownerBound : ∀ request state, ((owner request).run state).IsTotalQueryBound qOwner)
    (request : (Spec localSpec).Domain) (state : Pool setup KemSK × A) :
    ((impl baseImpl primitives kem setup owner request).run state).IsTotalQueryBound
      (if IsBirth request then 32 + (qPrekey + qKeygen) else qOwner) := by
  cases request with
  | create binding =>
    have birth : IsBirth (Request.create binding : Request localSpec) := True.intro
    simpa only [impl, StateT.run, ite_eq_left birth, bind_pure_comp,
      IsTotalQueryBound, isQueryBound_map_iff] using
      create_uniform baseImpl primitives kem setup qPrekey qKeygen prekeyBound keygenBound
  | owner index request =>
    have noBirth : ¬ IsBirth (Request.owner index request : Request localSpec) := id
    simp only [impl, StateT.run, ite_eq_right noBirth]
    cases present : state.1[index]? with
    | none => trivial
    | some beacon =>
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff, StateT.run] using
        ownerBound request (beacon, state.2)

/-- All finite adaptive creation/owner schedules pay the original creation and service bills, with no cost attributed to nonexistent future owners. -/
theorem schedule_uniform {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp))
    (qPrekey qKeygen qOwner : Nat)
    (prekeyBound : ∀ identity,
      (simulateQ (kemAmbientImpl baseImpl) (setup.prekey identity)).IsTotalQueryBound qPrekey)
    (keygenBound : (simulateQ (kemAmbientImpl baseImpl) kem.keygen).IsTotalQueryBound qKeygen)
    (ownerBound : ∀ request state, ((owner request).run state).IsTotalQueryBound qOwner)
    (client : OracleComp (Spec localSpec) Result) (qBirth qCall : Nat)
    (births : client.IsQueryBoundP IsBirth qBirth)
    (calls : client.IsQueryBoundP (fun request => ¬ IsBirth request) qCall)
    (state : Pool setup KemSK × A) :
    ((simulateQ (impl baseImpl primitives kem setup owner) client).run state).IsTotalQueryBound
      ((32 + (qPrekey + qKeygen)) * qBirth + qOwner * qCall) := by
  induction client using OracleComp.inductionOn generalizing qBirth qCall state with
  | pure value => trivial
  | query_bind request next ih =>
    rw [isQueryBoundP_query_bind_iff] at births calls
    simp only [simulateQ_query_bind, OracleQuery.input_query, StateT.run_bind]
    have total := isTotalQueryBound_bind
      (step_uniform baseImpl primitives kem setup owner qPrekey qKeygen qOwner
        prekeyBound keygenBound ownerBound request state)
      (fun result => ih result.1 _ _ (births.2 result.1) (calls.2 result.1) result.2)
    apply total.mono
    have b := births.1
    have c := calls.1
    have predecessor : ∀ cost n : Nat, 0 < n → cost * (n - 1) + cost = cost * n := by
      intro cost n positive
      rw [← Nat.mul_succ]
      congr 1
      omega
    cases request with
    | create binding =>
      have birth : IsBirth (Request.create binding : Request localSpec) := True.intro
      have noCall : ¬ ¬ IsBirth (Request.create binding : Request localSpec) :=
        not_not_intro birth
      simp only [ite_eq_left birth, ite_eq_right noCall]
      simp only [IsBirth, not_true_eq_false, false_or] at b
      have exactBill := predecessor (32 + (qPrekey + qKeygen)) qBirth (by tauto)
      omega
    | owner index request =>
      have noBirth : ¬ IsBirth (Request.owner index request : Request localSpec) := id
      simp only [ite_eq_right noBirth, ite_eq_left noBirth]
      simp only [IsBirth, not_false_eq_true] at c
      have exactBill := predecessor qOwner qCall (by tauto)
      omega

/-- Only actual construction extends the private owner family; service calls keep its length even when rejected. -/
theorem step_length
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp))
    (request : (Spec localSpec).Domain) (state : Pool setup KemSK × A)
    (result : (Spec localSpec).Range request × (Pool setup KemSK × A))
    (actual : result ∈ support ((impl baseImpl primitives kem setup owner request).run state)) :
    result.2.1.length = state.1.length + if IsBirth request then 1 else 0 := by
  cases request with
  | create binding =>
    simp only [impl, StateT.run, mem_support_bind_iff] at actual
    obtain ⟨created, _, finished⟩ := actual
    obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
    simp [install, IsBirth]
  | owner index request =>
    simp only [impl, StateT.run] at actual
    cases present : state.1[index]? with
    | none =>
      rw [present] at actual
      obtain rfl := OracleComp.eq_of_mem_support_pure _ actual
      simp [IsBirth]
    | some beacon =>
      rw [present, mem_support_bind_iff] at actual
      obtain ⟨called, _, finished⟩ := actual
      obtain rfl := OracleComp.eq_of_mem_support_pure _ finished
      simp [IsBirth]

/-- A bounded adaptive creation schedule admits a finite native-owner catalogue derived from actual births, not from a premise about selected owner honesty. -/
theorem schedule_length {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp))
    (client : OracleComp (Spec localSpec) Result) (qBirth : Nat)
    (births : client.IsQueryBoundP IsBirth qBirth) (state : Pool setup KemSK × A)
    (result : Result × (Pool setup KemSK × A))
    (actual : result ∈ support ((simulateQ (impl baseImpl primitives kem setup owner) client).run state)) :
    state.1.length ≤ result.2.1.length ∧ result.2.1.length ≤ state.1.length + qBirth := by
  induction client using OracleComp.inductionOn generalizing qBirth state result with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at actual
    subst result
    change state.1.length ≤ state.1.length ∧ state.1.length ≤ state.1.length + qBirth
    omega
  | query_bind request next ih =>
    rw [isQueryBoundP_query_bind_iff] at births
    rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at actual
    obtain ⟨called, first, later⟩ := actual
    have step := step_length baseImpl primitives kem setup owner request state called first
    have rest := ih called.1 _ (births.2 called.1) called.2 result later
    by_cases hit : IsBirth request
    · have positive := births.1.resolve_left (not_not_intro hit)
      rw [ite_eq_left hit] at step rest
      omega
    · rw [ite_eq_right hit] at step rest
      omega

/-- Any actually present owner selected after the schedule lies in its derived finite catalogue. Public-key collisions are irrelevant to index allocation and are not excluded. -/
theorem selected_index {Result : Type}
    (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (setup : StatefulPhase1Setup baseSpec)
    (owner : QueryImpl localSpec (StateT (Beacon setup KemSK × A) ProbComp))
    (client : OracleComp (Spec localSpec) Result) (qBirth : Nat)
    (births : client.IsQueryBoundP IsBirth qBirth) (state : Pool setup KemSK × A)
    (result : Result × (Pool setup KemSK × A))
    (actual : result ∈ support ((simulateQ (impl baseImpl primitives kem setup owner) client).run state))
    (index : Nat) (beacon : Beacon setup KemSK) (present : result.2.1[index]? = some beacon) :
    index < state.1.length + qBirth := by
  have bound := (schedule_length baseImpl primitives kem setup owner client qBirth births state result actual).2
  have inRange : index < result.2.1.length := by
    by_contra outside
    have absent : result.2.1[index]? = none := List.getElem?_eq_none (by omega)
    rw [absent] at present
    cases present
  omega

end BeaconcryptCore.Computational.PqxdhLiveBeaconBirth

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.adjacent_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.adjacent_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.create_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.create_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.complete_uniform' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.complete_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.create_key_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.create_key_support

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.fresh_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.fresh_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.fresh_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.fresh_handles

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.allocate_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.allocate_continuation

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.install_prior' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.install_prior

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.install_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.install_new

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.owner_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.owner_missing

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.owner_present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.owner_present

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.step_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.step_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.schedule_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.step_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.step_length

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.schedule_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.schedule_length

/--
info: 'BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.selected_index' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveBeaconBirth.selected_index

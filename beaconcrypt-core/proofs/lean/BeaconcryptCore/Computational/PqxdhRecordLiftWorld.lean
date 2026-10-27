-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftBeacon
import BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable

/-! An executable probabilistic interpreter of the frozen capability boundary. Dynamic records use the existing source programs and one actual CTX cache. The analysis state records every primitive call and underlying uniform query. Registration/source erasure, installation shell correspondence and security remain separate obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftWorld
open Classical
open PqxdhRecordLiftInterface
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds FrameTag)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}

abbrev SeedSpec (n : Nat) := Slot n →ₒ PqxdhRecordLiftSeed.Seed

/-- Count actual uniform queries, native primitives and every EnvEffects request: startup/adversary/ledger coins, public hashes, and env coins/hash/administrative requests, including refusals. Effects are not env-only totals. -/
structure Counts where
  uniform : Nat
  native : RawCtxMixedOwner.CallKind → Nat
  effects : EffectKind → Nat

def Counts.empty : Counts := ⟨0, fun _ => 0, fun _ => 0⟩

abbrev Primitive := Counts × CtxRomAuth.CtxRO.QueryCache

/-- The immutable outer sender is distinct from each assigned peer handle. -/
structure Server where
  sender : Std.U64
  records : RawCtxServerRouting.State Unit Unit

/-- Only record-relevant Beacon fields are retained. The raw counter map distinguishes absent handles from existing inactive owners. -/
structure State (n : Nat) where
  server : Option Server
  owners : List PqxdhRecordLiftBeacon.Phase
  ownerRaw : Nat → Nat
  produced : List (FrameTag × PqxdhDeploymentNative.Frame)
  primitive : Primitive
  seeds : PqxdhRecordLiftLazyTable.State (SeedSpec n)
  used : Slot n → Role → Bool

def initial : State n := ⟨none, [], fun _ => 0, [], (Counts.empty, ∅),
  PqxdhRecordLiftLazyTable.initial, fun _ _ => false⟩

/-- Forward each actual uniform query unchanged and count it, including seed and CTX cache misses. -/
def countCoin : QueryImpl unifSpec (StateT Nat ProbComp) := fun query count =>
  (fun reply => (reply, count + 1)) <$> (unifSpec.query query : ProbComp _)

/-- Instrument an existing probabilistic computation without replacing its sampler. -/
def sampled {Y : Type} (work : ProbComp Y) : StateT (State n) ProbComp Y := fun state => do
  let result ← (simulateQ countCoin work).run state.primitive.1.uniform
  pure (result.1, { state with primitive :=
    ({ state.primitive.1 with uniform := result.2 }, state.primitive.2) })

/-- The exact native real-HKDF/AEAD/ROM/writer interpreter, with every call and underlying draw instrumented. -/
noncomputable def primitives (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT Primitive ProbComp) := fun query state => do
  let result ← (simulateQ countCoin
    ((PqxdhDeploymentNative.primitives setup codec query).run ((), state.2))).run state.1.uniform
  let kind := RawCtxMixedOwner.callKind query
  pure (result.1.1, ({ state.1 with
    uniform := result.2
    native := Function.update state.1.native kind (state.1.native kind + 1) }, result.1.2.2))

/-- Full source constructor data is private; retain precisely its native record coordinates. Duplicate private initialization cannot reset the world. -/
def initializeServer (created : PqxdhLiveServerConstruction.Created Unit) : StateT (State n) ProbComp Unit :=
  fun state => match state.server with
  | some _ => pure ((), state)
  | none => pure ((), { state with server := some ⟨created.server.server.metadata.sender,
        ⟨⟨created.server.server.identity, created.server.server.peers, ()⟩, 0⟩⟩ })

/-- CE administrative phase edges. Refused or same-state source commands require no transition. -/
def LegalAdvance : InactivePhase → InactivePhase → Prop
  | .fresh, .initSent | .freshWithCoins, .initSent | .initSent, .aborted => True
  | _, _ => False

instance (before after : InactivePhase) : Decidable (LegalAdvance before after) := by
  cases before <;> cases after <;> unfold LegalAdvance <;> infer_instance

/-- C2b: the world admits a hidden role only while its slot/role marker is unused. Known kernels do not consume a hidden slot. -/
def Unused (state : State n) (role : Role) : KernelRef n → Prop
  | .known _ => True
  | .hidden slot => state.used slot role = false

instance (state : State n) (role : Role) (ref : KernelRef n) : Decidable (Unused state role ref) := by
  cases ref <;> unfold Unused <;> infer_instance

/-- C2b: Server installation requires an initialized Server and a vacant assigned handle. -/
def ServerVacant (state : State n) (keyId : Std.U64) : Prop :=
  ∃ server, state.server = some server ∧ server.records.server.peers keyId = none

/-- C2b: successful Beacon publication can replace only an existing initSent phase. -/
def BeaconReady (state : State n) (owner : Nat) : Prop :=
  state.owners[owner]? = some (.inactive .initSent)

/-- C2b: later computations preserve all previously cached seeds. -/
def SeedsPersist (before after : State n) : Prop := before.seeds.1 ≤ after.seeds.1

/-- C2b: used slot/role markers cannot be cleared. -/
def UsesPersist (before after : State n) : Prop :=
  ∀ slot role, before.used slot role = true → after.used slot role = true

/-- The two persistent private coordinates that no later world request may reset. -/
def Persistent (before after : State n) : Prop := SeedsPersist before after ∧ UsesPersist before after

/-- Mark precisely the hidden role that was installed. -/
def markUsed (state : State n) (role : Role) : KernelRef n → State n
  | .known _ => state
  | .hidden slot => { state with used := Function.update state.used slot (Function.update (state.used slot) role true) }

/-- Seed kernel constructors are total; no seed-dependent refusal or fabricated fallback kernel exists. -/
theorem hiddenKernel_total (role : Role) (seed : PqxdhRecordLiftSeed.Seed) :
    ∃ kernel, hiddenKernel role seed = RustM.ok kernel := by
  cases role
  · exact PqxdhRecordLiftSeed.serverKernel_total seed
  · exact PqxdhRecordLiftSeed.beaconKernel_total seed

noncomputable def kernel (role : Role) (seed : PqxdhRecordLiftSeed.Seed) : ConcreteRatchetKernel :=
  (hiddenKernel_total role seed).choose

/-- A hidden admitted install queries the same persistent lazy table in either role. -/
noncomputable def resolve (role : Role) : KernelRef n → StateT (State n) ProbComp ConcreteRatchetKernel
  | .known known => pure known
  | .hidden slot => fun state => do
      let result ← (sampled ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)).run state
      pure (kernel role result.1.1, { result.2 with seeds := result.1.2 })

/-- All administrative validation precedes hidden resolution, so rejected installs neither sample nor consume a slot. -/
noncomputable def installServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) : StateT (State n) ProbComp Bool := fun state =>
  match state.server with
  | none => pure (false, state)
  | some server =>
      if server.records.server.peers keyId = none ∧ Unused state .server ref then do
        let resolved ← (resolve .server ref).run state
        let next := markUsed resolved.2 .server ref
        let peers := Function.update server.records.server.peers keyId (some ⟨identity, resolved.1, ()⟩)
        pure (true, { next with server := some { server with records :=
          { server.records with server := { server.records.server with peers := peers } } } })
      else pure (false, state)

/-- Existing inactive raw counters survive installation. Outer sender and assigned control ID stay separate in the supplied exact shell. -/
noncomputable def installBeacon (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) :
    StateT (State n) ProbComp Bool := fun state =>
  if BeaconReady state owner ∧ Unused state .beacon ref then do
    let resolved ← (resolve .beacon ref).run state
    let next := markUsed resolved.2 .beacon ref
    pure (true, { next with owners := state.owners.set owner (.established shell resolved.1) })
  else pure (false, state)

/-- Private registration metadata is env-owned and irrelevant to inactive record dispatch. The frozen API permits any inactive birth tag; CE's create correspondence supplies fresh. -/
noncomputable def capability : QueryImpl (CapabilitySpec n) (StateT (State n) ProbComp)
  | .peerPresent keyId => fun state => pure
      ((state.server.bind fun server => server.records.server.peers keyId).isSome, state)
  | .ownerPresent owner => fun state => pure ((state.owners[owner]?).isSome, state)
  | .appendOwner _ _ phase => fun state => pure
      (state.owners.length, { state with owners := state.owners ++ [.inactive phase] })
  | .advanceOwner owner phase => fun state =>
      match state.owners[owner]? with
      | some (.inactive before) =>
          if LegalAdvance before phase then
            pure (true, { state with owners := state.owners.set owner (.inactive phase) })
          else pure (false, state)
      | _ => pure (false, state)
  | .installServer keyId identity ref => installServer keyId identity ref
  | .installBeacon owner shell ref => installBeacon owner shell ref
  | .hash bytes => fun state => do
      let result ← (sampled ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2)).run state
      pure (result.1.1, { result.2 with primitive := (result.2.primitive.1, result.1.2) })

def chargeEffect (query : (EnvEffects n).Domain) (state : State n) : State n :=
  let kind := effectKind query
  let charged := Function.update state.primitive.1.effects kind (state.primitive.1.effects kind + 1)
  { state with primitive := ({ state.primitive.1 with effects := charged }, state.primitive.2) }

/-- Count every direct effect, including refused administrative attempts, before answering it. -/
noncomputable def effects : QueryImpl (EnvEffects n) (StateT (State n) ProbComp) := fun query state =>
  match query with
  | .inl coin => (sampled (unifSpec.query coin : ProbComp _)).run (chargeEffect query state)
  | .inr request => (capability request).run (chargeEffect query state)

def produce (tag : FrameTag) (frames : List PqxdhDeploymentNative.Frame) (state : State n) : State n :=
  { state with produced := state.produced ++ frames.map fun frame => (tag, frame) }

/-- Source Server routing, whole-kernel updates and writer-failure logs are retained verbatim. -/
noncomputable def serverStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain) :
    StateT (State n) ProbComp (RawCtxServerMixed.SourceSpec.Range query) := fun state =>
  match state.server with
  | none => match query with
      | .inl _ => pure (none, state)
      | .inr _ => pure (.None, state)
  | some server => do
      let result ← (simulateQ (primitives setup codec) (PqxdhDeploymentNative.logged
        ((RawCtxServerMixed.serverImpl (fun _ => server.sender) route codec.frameRead query).run
          server.records))).run state.primitive
      pure (result.1.1.1, produce (PqxdhDeploymentNative.serverTag query) result.1.2
        { state with server := some { server with records := result.1.1.2 }, primitive := result.2 })

/-- Absent owners have no ghost increment; existing inactive owners execute the exact source rejection and raw increment. -/
noncomputable def beaconStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) :
    StateT (State n) ProbComp (RawCtxMixedOwner.SourceSpec.Range query) := fun state =>
  match state.owners[owner]? with
  | none => pure (PqxdhDeploymentNative.absent query, state)
  | some phase => do
      let result ← (simulateQ (primitives setup codec) (PqxdhDeploymentNative.logged
        ((PqxdhRecordLiftBeacon.handler codec.frameRead query).run ⟨phase, state.ownerRaw owner⟩))).run state.primitive
      pure (result.1.1.1, produce (PqxdhDeploymentNative.beaconTag owner) result.1.2
        { state with
          owners := state.owners.set owner result.1.1.2.phase
          ownerRaw := Function.update state.ownerRaw owner result.1.1.2.rawAttempts
          primitive := result.2 })

/-- Concrete interpretation of all private and public world requests. No operation reads the secrecy ledger. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (WorldSpec n) (StateT (State n) ProbComp)
  | .inl created => initializeServer created
  | .inr (.inl query) => effects query
  | .inr (.inr (.inl (.inl query))) => serverStep setup codec route (.inl query)
  | .inr (.inr (.inl (.inr raw))) => serverStep setup codec route (.inr raw)
  | .inr (.inr (.inr (owner, .inl plaintext))) => beaconStep setup codec owner (.inl plaintext)
  | .inr (.inr (.inr (owner, .inr raw))) => beaconStep setup codec owner (.inr raw)

/-- Run the exact frozen open program. The full returned analysis state includes produced frames, raw counters, cache and hidden seeds; none is returned to the adversary or environment during execution. -/
noncomputable def run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  (simulateQ (handler setup codec route)
    (program env setup.source.crypto codec serverKid bounds mode adversary)).run initial

/-- The C1 target projection retains the exact CE ledger (including test/fresh and transcript) and native produced log. Constructor failure remains none. No equality with the CE game is claimed here. -/
def observed (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n) :
    Option (X × PqxdhDeploymentSecrecy.Ledger × List (FrameTag × PqxdhDeploymentNative.Frame)) :=
  result.1.map fun value => (value.2.1.1, value.2.1.2, result.2.produced)

/-- Raw API attempt ghosts for integrity analysis, independent of the private seed/cache coordinates. -/
structure RawCounters where
  server : Nat
  owners : Nat → Nat

def rawCounters (state : State n) : RawCounters :=
  ⟨(state.server.map fun server => server.records.rawAttempts).getD 0, state.ownerRaw⟩

/-- A permitted analysis projection. Arbitrary predicates over the private result of run are not record-security events. -/
def analysis (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n) :=
  result.1.map fun value => (value.2.1.1, value.2.1.2, result.2.produced, rawCounters result.2)

/-- The CE-shaped observable game. Its ledger is an analysis output, not a public mode-P transcript; raw plaintexts/test/fresh remain subject to the eventual event definition. -/
noncomputable def game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :=
  observed <$> run setup codec route env serverKid bounds mode adversary

/-- Discarding the uniform counter restores the original probabilistic computation exactly. -/
theorem countCoin_forget {Y : Type} (work : ProbComp Y) (count : Nat) :
    Prod.fst <$> (simulateQ countCoin work).run count = work := by
  induction work using OracleComp.inductionOn generalizing count with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [StateT.run] at ih
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      simp only [countCoin, StateT.run, bind_map_left, ih]

/-- Erasing just instrumentation gives the exact native reply and shared cache. No primitive is replaced or supplied for free. -/
theorem primitives_forget (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : Primitive) :
    Prod.map id Prod.snd <$> (primitives setup codec query).run state =
      Prod.map id Prod.snd <$>
        (PqxdhDeploymentNative.primitives setup codec query).run ((), state.2) := by
  have same := congrArg (fun work => Prod.map id Prod.snd <$> work)
    (countCoin_forget ((PqxdhDeploymentNative.primitives setup codec query).run ((), state.2)) state.1.uniform)
  simpa only [primitives, StateT.run, bind_pure_comp, Functor.map_map, Prod.map, id_eq] using same

/-- The total chosen kernel is exactly the frozen role-directed source constructor. -/
theorem kernel_exact (role : Role) (seed : PqxdhRecordLiftSeed.Seed) :
    hiddenKernel role seed = RustM.ok (kernel role seed) :=
  (hiddenKernel_total role seed).choose_spec

/-- Every hidden lookup keeps previous seeds and all role/registration/log fields; only the lazy table and actual uniform counter can change. -/
theorem resolve_hidden_facts (role : Role) (slot : Slot n) (state : State n)
    (result : ConcreteRatchetKernel × State n)
    (supported : result ∈ support ((resolve role (.hidden slot)).run state)) :
    ∃ seed, result.1 = kernel role seed ∧ result.2.seeds.1 slot = some seed ∧
      SeedsPersist state result.2 ∧ result.2.used = state.used ∧
      result.2.server = state.server ∧ result.2.owners = state.owners ∧
      result.2.ownerRaw = state.ownerRaw ∧ result.2.produced = state.produced ∧
      result.2.primitive.2 = state.primitive.2 ∧
      result.2.primitive.1.native = state.primitive.1.native ∧
      result.2.primitive.1.effects = state.primitive.1.effects := by
  simp only [resolve, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds) := by
    rw [← countCoin_forget ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)
      state.primitive.1.uniform, support_map]
    exact ⟨inner, member, rfl⟩
  exact ⟨inner.1.1, rfl,
    (PqxdhRecordLiftLazyTable.step_facts slot state.seeds inner.1 original).1,
    (PqxdhRecordLiftLazyTable.step_facts slot state.seeds inner.1 original).2.1,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A first hidden lookup uses the actual seed sampler, caches that exact seed and changes only the lazy-table counters and the instrumented uniform counter. -/
theorem resolve_miss (role : Role) (slot : Slot n) (state : State n)
    (missing : state.seeds.1 slot = none) :
    (resolve role (.hidden slot)).run state =
      (fun result => (kernel role result.1, { state with
        seeds := (state.seeds.1.cacheQuery slot result.1,
          ⟨state.seeds.2.lookups + 1, state.seeds.2.draws + 1⟩)
        primitive := ({ state.primitive.1 with uniform := result.2 }, state.primitive.2) })) <$>
          (simulateQ countCoin ($ᵗ PqxdhRecordLiftSeed.Seed)).run state.primitive.1.uniform := by
  have miss := PqxdhRecordLiftLazyTable.run_miss (spec := SeedSpec n) slot state.seeds missing
  simp only [StateT.run] at miss
  simp only [resolve, sampled, StateT.run, miss, simulateQ_map,
    bind_pure_comp, Functor.map_map]
  have mapped := StateT.run_map
    (fun seed : PqxdhRecordLiftSeed.Seed => (seed, (state.seeds.1.cacheQuery slot seed,
      (⟨state.seeds.2.lookups + 1, state.seeds.2.draws + 1⟩ : PqxdhRecordLiftLazyTable.Counts))))
    (simulateQ countCoin ($ᵗ PqxdhRecordLiftSeed.Seed)) state.primitive.1.uniform
  simp only [StateT.run] at mapped
  rw [mapped, Functor.map_map]

/-- Forgetting the private poststate gives exactly the source kernel of one uniformly sampled seed. -/
theorem resolve_miss_kernel (role : Role) (slot : Slot n) (state : State n)
    (missing : state.seeds.1 slot = none) :
    Prod.fst <$> (resolve role (.hidden slot)).run state =
      (fun seed => kernel role seed) <$> ($ᵗ PqxdhRecordLiftSeed.Seed) := by
  rw [resolve_miss role slot state missing]
  have forget := congrArg (fun work => (fun seed => kernel role seed) <$> work)
    (countCoin_forget ($ᵗ PqxdhRecordLiftSeed.Seed) state.primitive.1.uniform)
  simpa only [Functor.map_map] using forget

/-- The other role's lookup reuses the exact cached seed and makes no additional uniform query. -/
theorem resolve_hit (role : Role) (slot : Slot n) (state : State n) (seed : PqxdhRecordLiftSeed.Seed)
    (cached : state.seeds.1 slot = some seed) :
    (resolve role (.hidden slot)).run state = pure (kernel role seed,
      { state with seeds := (state.seeds.1, ⟨state.seeds.2.lookups + 1, state.seeds.2.draws⟩) }) := by
  have hit := PqxdhRecordLiftLazyTable.run_hit slot state.seeds seed cached
  simp only [StateT.run] at hit
  simp [resolve, sampled, StateT.run, hit]
  rfl

/-- Refused Server admission is a pure rejection before resolution or any state update. -/
theorem installServer_refused (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n)
    (refused : ¬ (ServerVacant state keyId ∧ Unused state .server ref)) :
    (installServer keyId identity ref).run state = pure (false, state) := by
  cases hs : state.server <;> simp only [installServer, StateT.run, hs]
  case some server => exact ite_eq_right (fun h => refused ⟨⟨server, hs, h.1⟩, h.2⟩)

/-- Wrong-phase, missing-owner and already-used Beacon installs all reject before sampling. -/
theorem installBeacon_refused (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) (state : State n)
    (refused : ¬ (BeaconReady state owner ∧ Unused state .beacon ref)) :
    (installBeacon owner shell ref).run state = pure (false, state) := by
  simp only [installBeacon, StateT.run, ite_eq_right refused]

/-- Every successful Server installation had a vacant target and unused hidden role at admission. -/
theorem installServer_admitted (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state after : State n)
    (supported : (true, after) ∈ support ((installServer keyId identity ref).run state)) :
    ServerVacant state keyId ∧ Unused state .server ref := by
  by_contra refused
  simp [installServer_refused keyId identity ref state refused] at supported

/-- Every successful Beacon installation had an existing initSent owner and unused hidden role. -/
theorem installBeacon_admitted (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) (state after : State n)
    (supported : (true, after) ∈ support ((installBeacon owner shell ref).run state)) :
    BeaconReady state owner ∧ Unused state .beacon ref := by
  by_contra refused
  simp [installBeacon_refused owner shell ref state refused] at supported

/-- Marking one role cannot clear a previously used slot/role pair. -/
theorem markUsed_persists (state : State n) (role : Role) (ref : KernelRef n) :
    UsesPersist state (markUsed state role ref) := by
  cases ref with
  | known _ => exact fun _ _ used => used
  | hidden slot =>
      intro other role' used
      simp only [markUsed, Function.update_apply]
      split_ifs <;> simp_all [Function.update_apply]

theorem persistent_refl (state : State n) : Persistent state state :=
  ⟨le_refl _, fun _ _ used => used⟩

theorem persistent_trans (first second third : State n)
    (left : Persistent first second) (right : Persistent second third) : Persistent first third :=
  ⟨left.1.trans right.1, fun slot role used => right.2 slot role (left.2 slot role used)⟩

/-- Known and hidden resolution both retain the persistent private coordinates. -/
theorem resolve_persists (role : Role) (ref : KernelRef n) (state : State n)
    (result : ConcreteRatchetKernel × State n)
    (supported : result ∈ support ((resolve role ref).run state)) : Persistent state result.2 := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact persistent_refl state
  | hidden slot =>
      obtain ⟨seed, facts⟩ := resolve_hidden_facts role slot state result supported
      exact ⟨facts.2.2.1, fun slot role used => by simpa only [facts.2.2.2.1] using used⟩

theorem markUsed_store (state : State n) (role : Role) (ref : KernelRef n) :
    Persistent state (markUsed state role ref) := by
  refine ⟨?_, markUsed_persists state role ref⟩
  cases ref <;> exact le_refl _

/-- Server installation cannot erase cached seeds or clear any used marker. -/
theorem installServer_persists (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) :
    Persistent state result.2 := by
  cases hs : state.server with
  | none =>
      simp only [installServer, StateT.run, hs, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact persistent_refl state
  | some server =>
      simp only [installServer, StateT.run, hs] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact persistent_trans state inner.2 (markUsed inner.2 .server ref)
          (resolve_persists .server ref state inner member) (markUsed_store inner.2 .server ref)
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact persistent_refl state

/-- Beacon installation cannot erase cached seeds or clear any used marker. -/
theorem installBeacon_persists (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    Persistent state result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact persistent_trans state inner.2 (markUsed inner.2 .beacon ref)
      (resolve_persists .beacon ref state inner member) (markUsed_store inner.2 .beacon ref)
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact persistent_refl state

theorem sampled_persists {Y : Type} (work : ProbComp Y) (state : State n) (result : Y × State n)
    (supported : result ∈ support ((sampled work).run state)) : Persistent state result.2 := by
  simp only [sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact persistent_refl state

/-- Every restricted capability preserves the persistent seed table and used-role markers. -/
theorem capability_persists (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : Persistent state result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_persists keyId identity ref state result supported
  | installBeacon owner shell ref => exact installBeacon_persists owner shell ref state result supported
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact persistent_refl state
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact persistent_refl state
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact persistent_refl state
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact persistent_refl state
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      split at supported
      · split_ifs at supported <;>
          simp only [support_pure, Set.mem_singleton_iff] at supported <;>
          subst result <;> exact persistent_refl state
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact persistent_refl state

theorem effects_persists (query : (EnvEffects n).Domain) (state : State n)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) : Persistent state result.2 := by
  cases query with
  | inl coin => exact sampled_persists (unifSpec.query coin) (chargeEffect (.inl coin) state) result supported
  | inr request => exact capability_persists request (chargeEffect (.inr request) state) result supported

theorem serverStep_persists (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State n) (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep setup codec route query).run state)) :
    Persistent state result.2 := by
  cases hs : state.server with
  | none =>
      cases query <;> simp only [serverStep, StateT.run, hs, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact persistent_refl state
  | some server =>
      simp only [serverStep, StateT.run, hs, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact persistent_refl state

theorem beaconStep_persists (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State n) (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep setup codec owner query).run state)) :
    Persistent state result.2 := by
  cases found : state.owners[owner]? with
  | none =>
      simp only [beaconStep, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact persistent_refl state
  | some phase =>
      simp only [beaconStep, StateT.run, found, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact persistent_refl state

/-- Every private or public world request preserves earlier seeds and used-role markers. -/
theorem handler_persists (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler setup codec route query).run state)) :
    Persistent state result.2 := by
  cases query with
  | inl created =>
      cases hs : state.server <;>
        simp only [handler, initializeServer, StateT.run, hs, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact persistent_refl state
  | inr outer =>
      cases outer with
      | inl effect => exact effects_persists effect state result supported
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact serverStep_persists setup codec route (.inl send) state result supported
              | inr raw => exact serverStep_persists setup codec route (.inr raw) state result supported
          | inr ownerQuery =>
              rcases ownerQuery with ⟨owner, query⟩
              cases query with
              | inl plaintext => exact beaconStep_persists setup codec owner (.inl plaintext) state result supported
              | inr raw => exact beaconStep_persists setup codec owner (.inr raw) state result supported

/-- Persistent seeds and one-install markers survive every adaptive continuation, including rejected operations. -/
theorem schedule_persists {Y : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (work : OracleComp (WorldSpec n) Y)
    (state : State n) (result : Y × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route) work).run state)) :
    Persistent state result.2 :=
  simulateQ_run_preservesInv (handler setup codec route) (Persistent state)
    (fun query current before after member => persistent_trans state current after.2 before
      (handler_persists setup codec route query current after member))
    work state (persistent_refl state) result supported

/-- A successful hidden Server installation consumes exactly the operation's slot/role marker. -/
theorem installServer_marks (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (slot : Slot n) (state after : State n)
    (supported : (true, after) ∈ support ((installServer keyId identity (.hidden slot)).run state)) :
    after.used slot .server = true := by
  obtain ⟨⟨server, hs, vacant⟩, unused⟩ := installServer_admitted keyId identity (.hidden slot) state after supported
  simp only [installServer, StateT.run, hs, ite_eq_left (And.intro vacant unused),
    bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, equal⟩ := supported
  simpa [markUsed] using (congrArg (fun result => result.2.used slot .server) equal).symm

/-- A successful hidden Beacon installation consumes exactly the operation's slot/role marker. -/
theorem installBeacon_marks (owner : Nat) (shell : BeaconShell) (slot : Slot n) (state after : State n)
    (supported : (true, after) ∈ support ((installBeacon owner shell (.hidden slot)).run state)) :
    after.used slot .beacon = true := by
  have admitted := installBeacon_admitted owner shell (.hidden slot) state after supported
  simp only [installBeacon, StateT.run, ite_eq_left admitted, bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, equal⟩ := supported
  simpa [markUsed] using (congrArg (fun result => result.2.used slot .beacon) equal).symm

/-- Once marked, another Server installation for this slot rejects even at a different vacant handle. -/
theorem usedServer_refuses (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (slot : Slot n) (state : State n) (used : state.used slot .server = true) :
    (installServer keyId identity (.hidden slot)).run state = pure (false, state) :=
  installServer_refused keyId identity (.hidden slot) state (by simp [Unused, used])

/-- Once marked, another Beacon installation for this slot rejects even at a different initSent owner. -/
theorem usedBeacon_refuses (owner : Nat) (shell : BeaconShell) (slot : Slot n) (state : State n)
    (used : state.used slot .beacon = true) :
    (installBeacon owner shell (.hidden slot)).run state = pure (false, state) :=
  installBeacon_refused owner shell (.hidden slot) state (by simp [Unused, used])

end BeaconcryptCore.Computational.PqxdhRecordLiftWorld

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.hiddenKernel_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.hiddenKernel_total
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.countCoin_forget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.countCoin_forget
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.primitives_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.primitives_forget
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.kernel_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.kernel_exact
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_hidden_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_hidden_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_miss_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_miss_kernel

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_hit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_hit
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_refused
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_refused
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_admitted
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_admitted
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.markUsed_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.markUsed_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.persistent_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.persistent_refl
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.persistent_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.persistent_trans
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.resolve_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.markUsed_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.markUsed_store
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.sampled_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.sampled_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.capability_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.capability_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.effects_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.effects_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.serverStep_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.serverStep_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.beaconStep_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.beaconStep_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.handler_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.handler_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.schedule_persists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.schedule_persists
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installServer_marks
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_marks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.installBeacon_marks
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.usedServer_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.usedServer_refuses
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorld.usedBeacon_refuses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorld.usedBeacon_refuses

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftOrigins
import BeaconcryptCore.Computational.PqxdhRecordLiftChainCompiler
import BeaconcryptCore.Computational.PqxdhRecordLiftChainCoordinates
import BeaconcryptCore.Computational.PqxdhRecordLiftNativeAdapters
import BeaconcryptCore.Computational.PqxdhRecordLiftLoggedAdapters
import BeaconcryptCore.Computational.PqxdhRecordLiftTableScope

/-! The actual dynamic record world executes caller-known concrete kernels and private labeled kernels. Complete all-real source simulation retains every optional reply, native field, counter and failed-writer frame through arbitrary adaptive WorldSpec continuations. Operational invariants are derived from the actual empty state. Private state is not a security observation; mixed-policy, global provenance/orientation, masked-client and security-event joins remain separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler
open PqxdhRecordLiftInterface
open PqxdhRecordLiftChainState (Coordinate)
variable {n : Nat}

abbrev Label (n : Nat) := Coordinate (Slot n)
abbrev LabeledKernel (n : Nat) := PqxdhRecordLiftChainState.Kernel (Slot n) (Label n)

/-- Hidden record storage has only its installation origin and logical source state. -/
inductive StoredKernel (n : Nat) where
  | known (kernel : ConcreteRatchetKernel)
  | hidden (slot : Slot n) (kernel : LabeledKernel n)

def StoredKernel.origin : StoredKernel n → Option (Slot n)
  | .known _ => none
  | .hidden slot _ => some slot

/-- A representation map is an internal proof parameter, not an environment capability or an independently sampled family. Its concrete cached-seed/table interpretation is supplied by the source simulation. -/
abbrev Interpretation (n : Nat) := Slot n → LabeledKernel n → ConcreteRatchetKernel

def StoredKernel.erase (interpret : Interpretation n) : StoredKernel n → ConcreteRatchetKernel
  | .known kernel => kernel
  | .hidden slot kernel => interpret slot kernel

structure Peer (n : Nat) where
  identity : RawCtxServerRouting.Identity
  kernel : StoredKernel n

structure Server (n : Nat) where
  sender : Std.U64
  identity : RawCtxServerRouting.Identity
  peers : Std.U64 → Option (Peer n)
  rawAttempts : Nat

inductive Phase (n : Nat) where
  | inactive (phase : InactivePhase)
  | established (shell : BeaconShell) (kernel : StoredKernel n)

def Peer.erase (interpret : Interpretation n) (peer : Peer n) : RawCtxServerRouting.Peer Unit :=
  ⟨peer.identity, peer.kernel.erase interpret, ()⟩

def Server.erase (interpret : Interpretation n) (server : Server n) : PqxdhRecordLiftWorld.Server :=
  ⟨server.sender, ⟨⟨server.identity, fun keyId => (server.peers keyId).map (Peer.erase interpret), ()⟩,
    server.rawAttempts⟩⟩

def Phase.erase (interpret : Interpretation n) : Phase n → PqxdhRecordLiftBeacon.Phase
  | .inactive phase => .inactive phase
  | .established shell kernel => .established shell (kernel.erase interpret)

def Phase.origin : Phase n → Option (Slot n)
  | .inactive _ => none
  | .established _ kernel => kernel.origin

/-- Every original non-record World field is retained. The persistent complete-output table is additional private compiler state; actual costs remain in the retained primitive counters. -/
structure State (n : Nat) where
  server : Option (Server n)
  owners : List (Phase n)
  ownerRaw : Nat → Nat
  produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)
  primitive : PqxdhRecordLiftWorld.Primitive
  seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)
  used : Slot n → Role → Bool
  chain : PqxdhRecordLiftChainTable.Table (Slot n)

/-- Installation provenance is read directly from actual stored record objects. -/
def origins (state : State n) : PqxdhRecordLiftOrigins.Origins n :=
  ⟨fun keyId => state.server.bind fun server => (server.peers keyId).bind fun peer => peer.kernel.origin,
    fun owner => (state.owners[owner]?).bind Phase.origin⟩

/-- Structural full-state erasure; the separate chain table is interpreted through the supplied map, never exposed as a public observation. -/
def erase (interpret : Interpretation n) (state : State n) : PqxdhRecordLiftOrigins.State n :=
  (⟨state.server.map (Server.erase interpret), state.owners.map (Phase.erase interpret),
    state.ownerRaw, state.produced, state.primitive, state.seeds, state.used⟩, origins state)

def initial : State n :=
  ⟨none, [], fun _ => 0, [], (PqxdhRecordLiftWorld.Counts.empty, ∅),
    PqxdhRecordLiftLazyTable.initial, fun _ _ => false, ∅⟩

/-- Initial erasure needs no seed interpretation or populated table. -/
theorem initial_erasure (interpret : Interpretation n) :
    erase interpret initial = PqxdhRecordLiftOrigins.initial := rfl

/-- The source observation frame and all native accounting remain literal fields of this state. -/
theorem erase_fields (interpret : Interpretation n) (state : State n) :
    (erase interpret state).1.ownerRaw = state.ownerRaw ∧
      (erase interpret state).1.produced = state.produced ∧
      (erase interpret state).1.primitive = state.primitive ∧
      (erase interpret state).1.seeds = state.seeds ∧
      (erase interpret state).1.used = state.used := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A hidden-origin tag is carried only by an actual labeled kernel. -/
theorem origin_hidden (stored : StoredKernel n) (slot : Slot n) :
    stored.origin = some slot ↔ ∃ kernel, stored = .hidden slot kernel := by
  cases stored <;> simp [StoredKernel.origin, eq_comm]

/-- A tagged Server handle necessarily names an actual stored labeled peer. -/
theorem peer_origin_exists (state : State n) (keyId : Std.U64) (slot : Slot n)
    (tagged : (origins state).peers keyId = some slot) :
    ∃ server peer kernel, state.server = some server ∧ server.peers keyId = some peer ∧
      peer.kernel = .hidden slot kernel := by
  obtain ⟨server, serverFound, peerFound⟩ := Option.bind_eq_some_iff.mp tagged
  obtain ⟨peer, found, hidden⟩ := Option.bind_eq_some_iff.mp peerFound
  obtain ⟨kernel, same⟩ := (origin_hidden peer.kernel slot).mp hidden
  exact ⟨server, peer, kernel, serverFound, found, same⟩

/-- A tagged Beacon handle necessarily names an established stored labeled owner. -/
theorem owner_origin_exists (state : State n) (owner : Nat) (slot : Slot n)
    (tagged : (origins state).owners owner = some slot) :
    ∃ shell kernel, state.owners[owner]? = some (.established shell (.hidden slot kernel)) := by
  obtain ⟨phase, found, hidden⟩ := Option.bind_eq_some_iff.mp tagged
  cases phase with
  | inactive phase => simp only [Phase.origin, reduceCtorEq] at hidden
  | established shell stored =>
      obtain ⟨kernel, same⟩ := (origin_hidden stored slot).mp hidden
      exact ⟨shell, kernel, same ▸ found⟩

/-- Full-state erasure retains the actual peer named by each hidden provenance tag. -/
theorem erase_peer_exists (interpret : Interpretation n) (state : State n)
    (keyId : Std.U64) (slot : Slot n) (tagged : (origins state).peers keyId = some slot) :
    ∃ server peer, (erase interpret state).1.server = some server ∧
      server.records.server.peers keyId = some peer := by
  obtain ⟨server, peer, kernel, serverFound, found, _⟩ := peer_origin_exists state keyId slot tagged
  exact ⟨server.erase interpret, peer.erase interpret,
    by simp [erase, serverFound], by simp [Server.erase, found]⟩

/-- Full-state erasure retains the exact established shell at every hidden Beacon tag. -/
theorem erase_owner_exists (interpret : Interpretation n) (state : State n)
    (owner : Nat) (slot : Slot n) (tagged : (origins state).owners owner = some slot) :
    ∃ shell kernel, (erase interpret state).1.owners[owner]? =
      some (.established shell (interpret slot kernel)) := by
  obtain ⟨shell, kernel, found⟩ := owner_origin_exists state owner slot tagged
  exact ⟨shell, kernel, by simp [erase, List.getElem?_map, found, Phase.erase, StoredKernel.erase]⟩

/-- A total seed interpretation agrees with the actual partial lazy cache wherever it is populated. This relation describes representation, not a sampled family or security assumption. -/
def SeedExtension (state : State n) (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n)) : Prop :=
  ∀ slot seed, state.seeds.1 slot = some seed → seeds slot = seed

def SeedPresent (state : State n) (slot : Slot n) : Prop :=
  ∃ seed, state.seeds.1 slot = some seed

/-- Every actual cache admits a total mathematical interpretation; no such extension is stored or sampled by the executable World. -/
theorem seedExtension_exists (state : State n) :
    ∃ seeds, SeedExtension state seeds := by
  classical
  refine ⟨fun slot => (state.seeds.1 slot).getD (Classical.choice inferInstance), ?_⟩
  intro slot seed found
  simp only [found, Option.getD_some]

/-- The interpretation choice is irrelevant at every populated installation slot. -/
theorem seedExtension_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (slot : Slot n) (present : SeedPresent state slot) : left slot = right slot := by
  obtain ⟨seed, found⟩ := present
  exact (hleft slot seed found).trans (hright slot seed found).symm

/-- A chain coordinate reads only its own slot's seed, and otherwise the same persistent predecessor reply. -/
theorem chain_seed_congr (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (coordinate : Label n)
    (same : left coordinate.slot = right coordinate.slot) :
    PqxdhRecordLiftChainTable.chain left table coordinate =
      PqxdhRecordLiftChainTable.chain right table coordinate := by
  simp only [PqxdhRecordLiftChainTable.chain, same]

/-- For a populated installation slot, changing a total extension outside the actual cache cannot change chain interpretation. -/
theorem chain_extension_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (coordinate : Label n) (present : SeedPresent state coordinate.slot) :
    PqxdhRecordLiftChainTable.chain left state.chain coordinate =
      PqxdhRecordLiftChainTable.chain right state.chain coordinate :=
  chain_seed_congr left right state.chain coordinate
    (seedExtension_agrees state left right hleft hright coordinate.slot present)

/-- Private constructor peers supplied by the environment are caller-known source kernels. -/
def Peer.fromKnown (peer : RawCtxServerRouting.Peer Unit) : Peer n :=
  ⟨peer.identity, .known peer.kernel⟩

def Server.fromKnown (server : PqxdhRecordLiftWorld.Server) : Server n :=
  ⟨server.sender, server.records.server.identity,
    fun keyId => (server.records.server.peers keyId).map Peer.fromKnown, server.records.rawAttempts⟩

/-- Importing a known peer neither changes nor invents any native field. -/
theorem known_peer_erasure (interpret : Interpretation n) (peer : RawCtxServerRouting.Peer Unit) :
    Peer.erase interpret (Peer.fromKnown peer) = peer := by
  cases peer with
  | mk identity kernel metadata => cases metadata; rfl

/-- The complete constructor-supplied Server map, outer sender and raw counter survive known import. -/
theorem known_server_erasure (interpret : Interpretation n) (server : PqxdhRecordLiftWorld.Server) :
    Server.erase interpret (Server.fromKnown server) = server := by
  have peers : (fun keyId => ((server.records.server.peers keyId).map Peer.fromKnown).map
      (Peer.erase interpret)) = server.records.server.peers := by
    funext keyId
    cases found : server.records.server.peers keyId <;> simp [known_peer_erasure]
  cases server with
  | mk sender records =>
      cases records with
      | mk server raw =>
          cases server with
          | mk identity entries metadata =>
              cases metadata
              exact congrArg (fun mapped => (⟨sender, ⟨⟨identity, mapped, ()⟩, raw⟩⟩ :
                PqxdhRecordLiftWorld.Server)) peers

/-- Known constructor peers acquire no hidden provenance, even if their bytes equal some hidden value. -/
theorem known_server_origins (server : PqxdhRecordLiftWorld.Server) (keyId : Std.U64) :
    ((Server.fromKnown (n := n) server).peers keyId).bind (fun peer => peer.kernel.origin) = none := by
  cases found : server.records.server.peers keyId <;>
    simp [Server.fromKnown, found, Peer.fromKnown, StoredKernel.origin]

/-- The same private constructor handoff, importing its existing source peers as caller-known kernels. Duplicate initialization cannot reset any field. -/
def initializeServer (created : PqxdhLiveServerConstruction.Created Unit) :
    StateT (State n) ProbComp Unit := fun state => match state.server with
  | some _ => pure ((), state)
  | none => pure ((), { state with server := some (Server.fromKnown
      ⟨created.server.server.metadata.sender,
        ⟨⟨created.server.server.identity, created.server.server.peers, ()⟩, 0⟩⟩) })

/-- Private initialization has exactly the original complete World effect and keeps the reply-derived provenance unchanged. -/
theorem initialize_erasure (interpret : Interpretation n)
    (created : PqxdhLiveServerConstruction.Created Unit) (state : State n) :
    Prod.map id (erase interpret) <$> (initializeServer created).run state =
      (fun result => (result.1, (result.2, origins state))) <$>
        (PqxdhRecordLiftWorld.initializeServer created).run (erase interpret state).1 := by
  cases found : state.server <;>
    simp [initializeServer, PqxdhRecordLiftWorld.initializeServer, StateT.run, found,
      erase, known_server_erasure, origins, known_server_origins]

/-- Reuse the World's actual uniform-query instrumentation for every local probabilistic computation. -/
def sampled {Y : Type} (work : ProbComp Y) : StateT (State n) ProbComp Y := fun state => do
  let result ← (simulateQ PqxdhRecordLiftWorld.countCoin work).run state.primitive.1.uniform
  pure (result.1, { state with primitive :=
    ({ state.primitive.1 with uniform := result.2 }, state.primitive.2) })

/-- Every original restricted effect is charged before dispatch, including refused administration. -/
def chargeEffect (query : (EnvEffects n).Domain) (state : State n) : State n :=
  let kind := effectKind query
  { state with primitive := ({ state.primitive.1 with
    effects := Function.update state.primitive.1.effects kind (state.primitive.1.effects kind + 1) },
      state.primitive.2) }

/-- Instrumented sampling preserves the complete original World computation after erasing only labels. -/
theorem sampled_erasure {Y : Type} (interpret : Interpretation n) (work : ProbComp Y)
    (state : State n) :
    Prod.map id (erase interpret) <$> (sampled work).run state =
      (fun result => (result.1, (result.2, origins state))) <$>
        (PqxdhRecordLiftWorld.sampled work).run (erase interpret state).1 := by
  simp only [sampled, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp,
    Functor.map_map, erase, origins, Prod.map, id_eq]

/-- Charging a restricted effect retains the exact World counter update and unchanged provenance. -/
theorem chargeEffect_erasure (interpret : Interpretation n) (query : (EnvEffects n).Domain)
    (state : State n) :
    erase interpret (chargeEffect query state) =
      (PqxdhRecordLiftWorld.chargeEffect query (erase interpret state).1, origins state) := rfl

/-- The actual chain/material-table interpretation used by the local source compiler. The origin parameter supplies provenance; stored source coordinates determine which cached values are read. -/
def interpret (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) : Interpretation n :=
  fun _ kernel => ⟨PqxdhRecordLiftMaterialTable.eraseKernel seeds table kernel⟩

/-- Both live chains retain their installation slot through source evolution. Cached material attribution is certified separately by the material driver. -/
def KernelOrigin (slot : Slot n) (kernel : LabeledKernel n) : Prop :=
  kernel.send_chain.slot = slot ∧ kernel.receive_chain.slot = slot

/-- Installed labels may only refer to a seed actually sampled by this World. -/
def KernelScoped (state : State n) : StoredKernel n → Prop
  | .known _ => True
  | .hidden slot kernel => SeedPresent state slot ∧ KernelOrigin slot kernel

/-- The mathematical totalization of the partial seed cache is irrelevant to an installed source kernel. -/
theorem hidden_interpretation_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (slot : Slot n) (kernel : LabeledKernel n) (present : SeedPresent state slot)
    (scopeOK : KernelOrigin slot kernel) :
    interpret left state.chain slot kernel = interpret right state.chain slot kernel := by
  have sendSame := chain_extension_agrees state left right hleft hright kernel.send_chain
    (scopeOK.1.symm ▸ present)
  have receiveSame := chain_extension_agrees state left right hleft hright kernel.receive_chain
    (scopeOK.2.symm ▸ present)
  simp only [interpret, PqxdhRecordLiftMaterialTable.eraseKernel,
    RawCtxMaterialInterpretation.mapRefined, RawCtxChainInterpretation.mapChains,
    sendSame, receiveSame]

/-- Known values are literal source kernels; hidden values use only their populated installation slot. -/
theorem stored_interpretation_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (stored : StoredKernel n) (scopeOK : KernelScoped state stored) :
    stored.erase (interpret left state.chain) = stored.erase (interpret right state.chain) := by
  cases stored with
  | known kernel => rfl
  | hidden slot kernel =>
      exact hidden_interpretation_agrees state left right hleft hright slot kernel scopeOK.1 scopeOK.2

/-- The literal native KDF operation preserves the entire ROM cache and all unrelated counters. It performs one charged KDF call and no uniform query. -/
theorem primitives_kdf {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (request : SymmetricRatchetKdfRequest) (state : PqxdhRecordLiftWorld.Primitive) :
    (PqxdhRecordLiftWorld.primitives setup codec (.inl request)).run state =
      pure (RawCtxSourceHkdf.response setup.source.crypto request,
        ({ state.1 with native := Function.update state.1.native .kdf (state.1.native .kdf + 1) }, state.2)) := by
  simp [PqxdhRecordLiftWorld.primitives, PqxdhDeploymentNative.primitives,
    RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose,
    RawCtxSharedPrimitive.nativeImpl, RawCtxSourceHkdf.kdfImpl, RawCtxMixedOwner.callKind,
    OracleSpec.query, StateT.run]
  rfl

/-- The local driver's full76 value is a lossless representation of the response from the actual instrumented World query. -/
noncomputable def nativeKdf {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    PqxdhRecordLiftChainCompiler.Kdf PqxdhRecordLiftWorld.Primitive := fun request =>
  PqxdhRecordLiftRealTable.fromResponse <$> PqxdhRecordLiftWorld.primitives setup codec (.inl request)

/-- The local real-callback requirement follows from literal World implementation equality; it is not a cryptographic hypothesis. -/
theorem nativeKdf_real {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    PqxdhRecordLiftChainCompiler.KdfReal setup.source (nativeKdf setup codec) := by
  intro input state result supported
  simp only [nativeKdf, StateT.run_map] at supported
  subst result
  exact PqxdhRecordLiftRealTable.fullResponse_from _

/-- The actual native callback performs its charged query even on a previously stored coordinate. Its exact private annotation update and complete primitive poststate follow without a callback premise. -/
theorem callback_world {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (coordinate : Label n)
    (state : PqxdhRecordLiftWorld.Primitive) :
    (simulateQ (fun request => PqxdhRecordLiftWorld.primitives setup codec (.inl request))
      ((PqxdhRecordLiftRealTable.callback seeds coordinate).run table)).run state =
      pure ((PqxdhRecordLiftRealTable.output setup.source seeds table coordinate,
        PqxdhRecordLiftRealTable.record setup.source seeds table coordinate),
        ({ state.1 with native := Function.update state.1.native .kdf (state.1.native .kdf + 1) }, state.2)) :=
  PqxdhRecordLiftRealTable.callback_real setup.source seeds table coordinate _ state _
    (primitives_kdf setup codec _ state)

/-- The exact role-directed source initializer with coordinates in place of private chain bytes. -/
def labelProgram (role : Role) (slot : Slot n) : RustM (LabeledKernel n) :=
  match role with
  | .server => PqxdhRecordLiftMaterialTable.serverLabels slot
  | .beacon => PqxdhRecordLiftMaterialTable.beaconLabels slot

/-- Source initialization always returns its complete labeled state. -/
theorem labelProgram_total (role : Role) (slot : Slot n) :
    ∃ kernel, labelProgram role slot = RustM.ok kernel := by
  cases role with
  | server =>
      obtain ⟨kernel, actual, _⟩ := (PqxdhRecordLiftMaterialTable.seeds_certified (∅ : PqxdhRecordLiftChainTable.Table (Slot n)) slot).1
      exact ⟨kernel, actual⟩
  | beacon =>
      obtain ⟨kernel, actual, _⟩ := (PqxdhRecordLiftMaterialTable.seeds_certified (∅ : PqxdhRecordLiftChainTable.Table (Slot n)) slot).2
      exact ⟨kernel, actual⟩

noncomputable def labeledKernel (role : Role) (slot : Slot n) : LabeledKernel n :=
  (labelProgram_total role slot).choose

/-- The selected labeled value is the result of the literal source constructor. -/
theorem labeledKernel_exact (role : Role) (slot : Slot n) :
    labelProgram role slot = RustM.ok (labeledKernel role slot) :=
  (labelProgram_total role slot).choose_spec

/-- Role-directed labels erase to the exact World seed kernel for both physical source orientations. -/
theorem labeledKernel_erasure (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (role : Role) (slot : Slot n) :
    interpret seeds table slot (labeledKernel role slot) = PqxdhRecordLiftWorld.kernel role (seeds slot) := by
  have actual : (interpret seeds table slot <$> labelProgram role slot) = hiddenKernel role (seeds slot) := by
    cases role with
    | server => exact (PqxdhRecordLiftMaterialTable.seeds_erasure seeds table slot).1
    | beacon => exact (PqxdhRecordLiftMaterialTable.seeds_erasure seeds table slot).2
  rw [labeledKernel_exact] at actual
  exact RustM.ok.inj (actual.trans (PqxdhRecordLiftWorld.hiddenKernel_total role (seeds slot)).choose_spec)

/-- Neither directional initializer introduces another slot. -/
theorem labeledKernel_origin (role : Role) (slot : Slot n) :
    KernelOrigin slot (labeledKernel role slot) := by
  have actual := labeledKernel_exact role slot
  cases role
  all_goals rw [← RustM.ok.inj actual]
  all_goals exact ⟨rfl, rfl⟩

/-- Resolution samples through the identical persistent seed cache, while the returned hidden value contains coordinates only. -/
noncomputable def resolve (role : Role) : KernelRef n → StateT (State n) ProbComp (StoredKernel n)
  | .known known => pure (.known known)
  | .hidden slot => fun state => do
      let result ← (sampled ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)).run state
      pure (.hidden slot (labeledKernel role slot), { result.2 with seeds := result.1.2 })

/-- Hidden resolution preserves prior sampled seeds and every existing record; the returned labeled kernel is linked to the actual newly cached or reused seed. -/
theorem resolve_hidden_facts (role : Role) (slot : Slot n) (state : State n)
    (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve role (.hidden slot)).run state)) :
    ∃ seed, result.1 = .hidden slot (labeledKernel role slot) ∧
      result.2.seeds.1 slot = some seed ∧ state.seeds.1 ≤ result.2.seeds.1 ∧
      result.2.used = state.used ∧ result.2.server = state.server ∧
      result.2.owners = state.owners ∧ result.2.ownerRaw = state.ownerRaw ∧
      result.2.produced = state.produced ∧ result.2.chain = state.chain ∧
      result.2.primitive.2 = state.primitive.2 ∧
      result.2.primitive.1.native = state.primitive.1.native ∧
      result.2.primitive.1.effects = state.primitive.1.effects := by
  simp only [resolve, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds) := by
    rw [← PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)
      state.primitive.1.uniform, support_map]
    exact ⟨inner, member, rfl⟩
  exact ⟨inner.1.1, rfl,
    (PqxdhRecordLiftLazyTable.step_facts slot state.seeds inner.1 original).1,
    (PqxdhRecordLiftLazyTable.step_facts slot state.seeds inner.1 original).2.1,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Internal totalized representation for erasure and private lookup/open/seal interpretation. Resolution samples the actual partial cache; derived slot scope excludes this default at reachable hidden references. -/
noncomputable def cachedSeeds (state : State n) : PqxdhRecordLiftChainTable.Seeds (Slot n) :=
  fun slot => (state.seeds.1 slot).getD Classical.ofNonempty

theorem cachedSeeds_extension (state : State n) : SeedExtension state (cachedSeeds state) := by
  intro slot seed found
  simp only [cachedSeeds, found, Option.getD_some]

def PhaseScoped (state : State n) : Phase n → Prop
  | .inactive _ => True
  | .established _ kernel => KernelScoped state kernel

/-- Every installed hidden record points only to its sampled origin. This is an operational invariant to establish from handlers, not an assumption on an environment. -/
def Scoped (state : State n) : Prop :=
  (∀ server, state.server = some server → ∀ keyId peer, server.peers keyId = some peer →
    KernelScoped state peer.kernel) ∧
  (∀ phase ∈ state.owners, PhaseScoped state phase)

noncomputable def project (state : State n) : PqxdhRecordLiftOrigins.State n :=
  erase (interpret (cachedSeeds state) state.chain) state

theorem peer_interpretation_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (peer : Peer n) (scopeOK : KernelScoped state peer.kernel) :
    Peer.erase (interpret left state.chain) peer = Peer.erase (interpret right state.chain) peer :=
  congrArg (fun kernel => (⟨peer.identity, kernel, ()⟩ : RawCtxServerRouting.Peer Unit))
    (stored_interpretation_agrees state left right hleft hright peer.kernel scopeOK)

theorem server_interpretation_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (server : Server n)
    (scopeOK : ∀ keyId peer, server.peers keyId = some peer → KernelScoped state peer.kernel) :
    Server.erase (interpret left state.chain) server = Server.erase (interpret right state.chain) server := by
  have peers : (fun keyId => (server.peers keyId).map (Peer.erase (interpret left state.chain))) =
      (fun keyId => (server.peers keyId).map (Peer.erase (interpret right state.chain))) := by
    funext keyId
    cases found : server.peers keyId with
    | none => rfl
    | some peer => exact congrArg some (peer_interpretation_agrees state left right hleft hright peer
        (scopeOK keyId peer found))
  simp only [Server.erase, peers]

theorem phase_interpretation_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (phase : Phase n) (scopeOK : PhaseScoped state phase) :
    Phase.erase (interpret left state.chain) phase = Phase.erase (interpret right state.chain) phase := by
  cases phase with
  | inactive tag => rfl
  | established shell kernel =>
      exact congrArg (PqxdhRecordLiftBeacon.Phase.established shell)
        (stored_interpretation_agrees state left right hleft hright kernel scopeOK)

/-- The complete dynamic peer map and owner list are independent of every unused-slot totalization choice. -/
theorem erase_interpretation_agrees (state : State n)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right) (scopeOK : Scoped state) :
    erase (interpret left state.chain) state = erase (interpret right state.chain) state := by
  have servers : state.server.map (Server.erase (interpret left state.chain)) =
      state.server.map (Server.erase (interpret right state.chain)) := by
    cases found : state.server with
    | none => rfl
    | some server => exact congrArg some (server_interpretation_agrees state left right hleft hright
        server (scopeOK.1 server found))
  have owners : state.owners.map (Phase.erase (interpret left state.chain)) =
      state.owners.map (Phase.erase (interpret right state.chain)) := by
    apply List.map_congr_left
    intro phase member
    exact phase_interpretation_agrees state left right hleft hright phase (scopeOK.2 phase member)
  simp only [erase, servers, owners]

def seedFrame (state : State n)
    (seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n))
    (primitive : PqxdhRecordLiftWorld.Primitive) : State n :=
  { state with seeds := seeds, primitive := primitive }

/-- Extending the sampled seed cache changes no existing record interpretation. Complete primitive instrumentation may change independently. -/
theorem project_seedFrame (state : State n)
    (seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n))
    (primitive : PqxdhRecordLiftWorld.Primitive) (mono : state.seeds.1 ≤ seeds.1)
    (scopeOK : Scoped state) :
    project (seedFrame state seeds primitive) =
      ({ (project state).1 with seeds := seeds, primitive := primitive }, (project state).2) := by
  have ext : SeedExtension state (cachedSeeds (seedFrame state seeds primitive)) := by
    intro slot seed found
    exact cachedSeeds_extension (seedFrame state seeds primitive) slot seed (mono found)
  exact congrArg (fun view : PqxdhRecordLiftOrigins.State n =>
    ({ view.1 with seeds := seeds, primitive := primitive }, view.2))
    (erase_interpretation_agrees state (cachedSeeds (seedFrame state seeds primitive)) (cachedSeeds state)
      ext (cachedSeeds_extension state) scopeOK)

noncomputable def eraseResolved (result : StoredKernel n × State n) :
    ConcreteRatchetKernel × PqxdhRecordLiftOrigins.State n :=
  (result.1.erase (interpret (cachedSeeds result.2) result.2.chain), project result.2)

/-- The actual lazy hidden resolution and its complete World poststate are restored by labeled erasure. -/
theorem resolve_erasure (role : Role) (ref : KernelRef n) (state : State n) (scopeOK : Scoped state) :
    eraseResolved <$> (resolve role ref).run state =
      (fun result => (result.1, (result.2, (project state).2))) <$>
        (PqxdhRecordLiftWorld.resolve role ref).run (project state).1 := by
  cases ref with
  | known known => rfl
  | hidden slot =>
      simp only [resolve, PqxdhRecordLiftWorld.resolve, sampled, PqxdhRecordLiftWorld.sampled,
        StateT.run, bind_pure_comp, Functor.map_map]
      simp only [← bind_pure_comp]
      refine bind_congr_of_forall_mem_support _ (fun inner member => ?_)
      apply congrArg pure
      have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds) := by
        rw [← PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)
          state.primitive.1.uniform, support_map]
        exact ⟨inner, member, rfl⟩
      have facts := PqxdhRecordLiftLazyTable.step_facts slot state.seeds inner.1 original
      let primitive : PqxdhRecordLiftWorld.Primitive :=
        ({ state.primitive.1 with uniform := inner.2 }, state.primitive.2)
      have framed := project_seedFrame state inner.1.2 primitive facts.2.1 scopeOK
      have cached := cachedSeeds_extension (seedFrame state inner.1.2 primitive) slot inner.1.1 facts.1
      simp only [eraseResolved, StoredKernel.erase, labeledKernel_erasure]
      dsimp only [seedFrame, primitive] at cached framed
      rw [cached, framed]
      rfl

def Unused (state : State n) (role : Role) : KernelRef n → Prop
  | .known _ => True
  | .hidden slot => state.used slot role = false

def markUsed (state : State n) (role : Role) : KernelRef n → State n
  | .known _ => state
  | .hidden slot => { state with used := Function.update state.used slot (Function.update (state.used slot) role true) }

def BeaconReady (state : State n) (owner : Nat) : Prop :=
  state.owners[owner]? = some (.inactive .initSent)

open Classical

/-- Source admission precedes seed resolution. Installing a private peer stores its origin and logical kernel, while retaining the exact immutable Server sender and identity. -/
noncomputable def installServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) : StateT (State n) ProbComp Bool := fun state =>
  match state.server with
  | none => pure (false, state)
  | some server =>
      if server.peers keyId = none ∧ Unused state .server ref then do
        let resolved ← (resolve .server ref).run state
        let next := markUsed resolved.2 .server ref
        pure (true, { next with server := some { server with
          peers := Function.update server.peers keyId (some ⟨identity, resolved.1⟩) } })
      else pure (false, state)

/-- Beacon installation preserves existing raw-attempt counts and uses the complete exact shell supplied at the frozen boundary. -/
noncomputable def installBeacon (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) :
    StateT (State n) ProbComp Bool := fun state =>
  if BeaconReady state owner ∧ Unused state .beacon ref then do
    let resolved ← (resolve .beacon ref).run state
    let next := markUsed resolved.2 .beacon ref
    pure (true, { next with owners := state.owners.set owner (.established shell resolved.1) })
  else pure (false, state)

/-- The frozen capability commands keep the original absence, phase, refusal and shared-ROM behavior. Inactive registration metadata remains environment-owned. -/
noncomputable def capability : QueryImpl (CapabilitySpec n) (StateT (State n) ProbComp)
  | .peerPresent keyId => fun state => pure
      ((state.server.bind fun server => server.peers keyId).isSome, state)
  | .ownerPresent owner => fun state => pure ((state.owners[owner]?).isSome, state)
  | .appendOwner _ _ phase => fun state => pure
      (state.owners.length, { state with owners := state.owners ++ [.inactive phase] })
  | .advanceOwner owner phase => fun state =>
      match state.owners[owner]? with
      | some (.inactive before) =>
          if PqxdhRecordLiftWorld.LegalAdvance before phase then
            pure (true, { state with owners := state.owners.set owner (.inactive phase) })
          else pure (false, state)
      | _ => pure (false, state)
  | .installServer keyId identity ref => installServer keyId identity ref
  | .installBeacon owner shell ref => installBeacon owner shell ref
  | .hash bytes => fun state => do
      let result ← (sampled ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2)).run state
      pure (result.1.1, { result.2 with primitive := (result.2.primitive.1, result.1.2) })

/-- Every environment, startup, ledger or adversary effect is charged before dispatch, including refused commands. -/
noncomputable def effects : QueryImpl (EnvEffects n) (StateT (State n) ProbComp) := fun query state =>
  match query with
  | .inl coin => (sampled (unifSpec.query coin : ProbComp _)).run (chargeEffect query state)
  | .inr request => (capability request).run (chargeEffect query state)

theorem initial_scoped : Scoped (initial : State n) := by
  simp [Scoped, initial]

/-- Used-role tracking is exactly the existing World update and has no hidden data-dependent branch. -/
theorem markUsed_erasure (state : State n) (role : Role) (ref : KernelRef n) :
    project (markUsed state role ref) =
      (PqxdhRecordLiftWorld.markUsed (project state).1 role ref, (project state).2) := by
  cases ref <;> rfl

/-- The admission marker is read identically before and after erasure. -/
theorem unused_erasure (state : State n) (role : Role) (ref : KernelRef n) :
    Unused state role ref ↔ PqxdhRecordLiftWorld.Unused (project state).1 role ref := by
  cases ref <;> rfl

/-- Extending the actual seed cache retains scope for every previously installed labeled kernel. -/
theorem kernelScoped_mono (before after : State n) (mono : before.seeds.1 ≤ after.seeds.1)
    (stored : StoredKernel n) (scopeOK : KernelScoped before stored) : KernelScoped after stored := by
  cases stored with
  | known kernel => trivial
  | hidden slot kernel =>
      obtain ⟨⟨seed, found⟩, origin⟩ := scopeOK
      exact ⟨⟨seed, mono found⟩, origin⟩

theorem scoped_same_records (before after : State n) (mono : before.seeds.1 ≤ after.seeds.1)
    (serverSame : after.server = before.server) (ownersSame : after.owners = before.owners)
    (scopeOK : Scoped before) : Scoped after := by
  constructor
  · intro server found keyId peer present
    exact kernelScoped_mono before after mono peer.kernel
      (scopeOK.1 server (serverSame.symm.trans found) keyId peer present)
  · intro phase member
    rw [ownersSame] at member
    cases phase with
    | inactive tag => trivial
    | established shell kernel =>
        exact kernelScoped_mono before after mono kernel (scopeOK.2 _ member)

/-- Resolution establishes scope for the returned value and preserves scope of every stored record. No seed distribution premise is needed. -/
theorem resolve_scoped (role : Role) (ref : KernelRef n) (state : State n) (scopeOK : Scoped state)
    (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve role ref).run state)) :
    Scoped result.2 ∧ KernelScoped result.2 result.1 := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run] at supported
      subst result
      exact ⟨scopeOK, trivial⟩
  | hidden slot =>
      obtain ⟨seed, returned, present, mono, _, serverSame, ownersSame, _⟩ :=
        resolve_hidden_facts role slot state result supported
      refine ⟨scoped_same_records state result.2 mono serverSame ownersSame scopeOK, ?_⟩
      rw [returned]
      exact ⟨⟨seed, present⟩, labeledKernel_origin role slot⟩

theorem resolve_fields (role : Role) (ref : KernelRef n) (state : State n)
    (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve role ref).run state)) :
    result.2.server = state.server ∧ result.2.owners = state.owners ∧
      state.seeds.1 ≤ result.2.seeds.1 ∧ result.2.chain = state.chain ∧
      result.1.origin = PqxdhRecordLiftOrigins.origin ref := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run] at supported
      subst result
      exact ⟨rfl, rfl, le_refl _, rfl, rfl⟩
  | hidden slot =>
      obtain ⟨_, returned, _, mono, _, serverSame, ownersSame, _, _, chainSame, _⟩ :=
        resolve_hidden_facts role slot state result supported
      exact ⟨serverSame, ownersSame, mono, chainSame, returned ▸ rfl⟩

theorem markUsed_scoped (state : State n) (role : Role) (ref : KernelRef n) (scopeOK : Scoped state) :
    Scoped (markUsed state role ref) := by
  cases ref with
  | known known => exact scopeOK
  | hidden slot => exact scoped_same_records state _ (le_refl _) rfl rfl scopeOK

theorem kernelScoped_markUsed (state : State n) (role : Role) (ref : KernelRef n) (stored : StoredKernel n) :
    KernelScoped (markUsed state role ref) stored ↔ KernelScoped state stored := by
  cases ref <;> rfl

theorem scoped_server_store (state : State n) (server : Server n)
    (existing : state.server = some server) (keyId : Std.U64) (peer : Peer n)
    (scopeOK : Scoped state) (peerScope : KernelScoped state peer.kernel) :
    Scoped { state with server := some { server with peers := Function.update server.peers keyId (some peer) } } := by
  constructor
  · intro actual found target present selected
    cases Option.some.inj found
    change Function.update server.peers keyId (some peer) target = some present at selected
    by_cases same : target = keyId
    · subst target
      simp only [Function.update_self, Option.some.injEq] at selected
      subst present
      exact peerScope
    · rw [Function.update_of_ne same] at selected
      exact scopeOK.1 server existing target present selected
  · exact scopeOK.2

theorem scoped_owner_store (state : State n) (owner : Nat) (phase : Phase n)
    (scopeOK : Scoped state) (phaseScope : PhaseScoped state phase) :
    Scoped { state with owners := state.owners.set owner phase } := by
  constructor
  · exact scopeOK.1
  · intro present member
    rcases List.mem_or_eq_of_mem_set member with prior | equal
    · exact scopeOK.2 present prior
    · subst present
      exact phaseScope

/-- Successful or refused Beacon installation preserves the sampled-slot invariant. -/
theorem installBeacon_scoped (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (scopeOK : Scoped state) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) : Scoped result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have resolved := resolve_scoped .beacon ref state scopeOK inner member
    have ownersSame : (markUsed inner.2 .beacon ref).owners = state.owners := by
      cases ref <;> exact (resolve_fields .beacon _ state inner member).2.1
    simpa only [ownersSame] using
      scoped_owner_store (markUsed inner.2 .beacon ref) owner (.established shell inner.1)
        (markUsed_scoped inner.2 .beacon ref resolved.1)
        ((kernelScoped_markUsed inner.2 .beacon ref inner.1).2 resolved.2)
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact scopeOK

/-- Both Server admission branches preserve scope, including a caller-known replacement value. -/
theorem installServer_scoped (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (scopeOK : Scoped state) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) : Scoped result.2 := by
  simp only [installServer, StateT.run] at supported
  cases found : state.server with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact scopeOK
  | some server =>
      simp only [found] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have resolved := resolve_scoped .server ref state scopeOK inner member
        have serverSame : (markUsed inner.2 .server ref).server = some server := by
          cases ref <;> exact (resolve_fields .server _ state inner member).1.trans found
        exact scoped_server_store (markUsed inner.2 .server ref) server serverSame keyId ⟨identity, inner.1⟩
          (markUsed_scoped inner.2 .server ref resolved.1)
          ((kernelScoped_markUsed inner.2 .server ref inner.1).2 resolved.2)
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact scopeOK

theorem scoped_append (state : State n) (phase : InactivePhase) (scopeOK : Scoped state) :
    Scoped { state with owners := state.owners ++ [.inactive phase] } := by
  constructor
  · exact scopeOK.1
  · intro present member
    rcases List.mem_append.mp member with prior | appended
    · exact scopeOK.2 present prior
    · simp only [List.mem_singleton] at appended
      subst present
      trivial

/-- Every actual restricted capability preserves sampled-slot scope; this is derived from all operational branches. -/
theorem capability_scoped (query : (CapabilitySpec n).Domain) (state : State n) (scopeOK : Scoped state)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : Scoped result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_scoped keyId identity ref state scopeOK result supported
  | installBeacon owner shell ref => exact installBeacon_scoped owner shell ref state scopeOK result supported
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact scopeOK
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact scopeOK
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact scoped_append state phase scopeOK
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact scopeOK
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      split at supported
      · split_ifs at supported with allowed
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact scoped_owner_store state owner (.inactive phase) scopeOK trivial
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact scopeOK
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact scopeOK

/-- Full original private World state; the logical table and derived provenance remain compiler auxiliaries. -/
noncomputable def world (state : State n) : PqxdhRecordLiftWorld.State n := (project state).1

/-- Legal Beacon admission is invariant under erasing private coordinates. -/
theorem beaconReady_erasure (state : State n) (owner : Nat) :
    BeaconReady state owner ↔ PqxdhRecordLiftWorld.BeaconReady (world state) owner := by
  change state.owners[owner]? = some (.inactive .initSent) ↔
    (state.owners.map (Phase.erase (interpret (cachedSeeds state) state.chain)))[owner]? =
      some (.inactive .initSent)
  rw [List.getElem?_map]
  cases found : state.owners[owner]? with
  | none => simp
  | some phase => cases phase <;> simp [Phase.erase]

/-- Reinstalling an owner preserves the exact native list update, with all non-owner World fields retained. -/
theorem world_owner_store (state : State n) (owner : Nat) (phase : Phase n) :
    world { state with owners := state.owners.set owner phase } =
      { world state with owners := (world state).owners.set owner (Phase.erase (interpret (cachedSeeds state) state.chain) phase) } := by
  simp only [world, project, erase, List.map_set]
  rfl

noncomputable def storedView (state : State n) (stored : StoredKernel n) : ConcreteRatchetKernel :=
  stored.erase (interpret (cachedSeeds state) state.chain)

noncomputable def eraseResolvedWorld (result : StoredKernel n × State n) :
    ConcreteRatchetKernel × PqxdhRecordLiftWorld.State n :=
  (storedView result.2 result.1, world result.2)

/-- The complete original World resolution is recovered, with the auxiliary origin annotation erased. -/
theorem resolve_world (role : Role) (ref : KernelRef n) (state : State n) (scopeOK : Scoped state) :
    eraseResolvedWorld <$> (resolve role ref).run state =
      (PqxdhRecordLiftWorld.resolve role ref).run (world state) := by
  change (fun result => (storedView result.2 result.1, world result.2)) <$>
    (resolve role ref).run state = _
  have same := congrArg (fun work => (Prod.map id Prod.fst) <$> work)
    (resolve_erasure role ref state scopeOK)
  simpa [Functor.map_map, Prod.map_def, Function.comp_def, eraseResolvedWorld,
    storedView, eraseResolved, world] using same

/-- Marking a role retains the identical original World marker update. -/
theorem world_markUsed (state : State n) (role : Role) (ref : KernelRef n) :
    world (markUsed state role ref) = PqxdhRecordLiftWorld.markUsed (world state) role ref :=
  congrArg Prod.fst (markUsed_erasure state role ref)

theorem storedView_markUsed (state : State n) (role : Role) (ref : KernelRef n) (stored : StoredKernel n) :
    storedView (markUsed state role ref) stored = storedView state stored := by
  cases ref <;> rfl

/-- Lazy resolution leaves all prior native records unchanged, even when it fills a previously absent seed slot. -/
theorem resolve_world_records (role : Role) (ref : KernelRef n) (state : State n) (scopeOK : Scoped state)
    (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve role ref).run state)) :
    (world result.2).server = (world state).server ∧ (world result.2).owners = (world state).owners := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | hidden slot =>
      simp only [resolve, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds) := by
        rw [← PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)
          state.primitive.1.uniform, support_map]
        exact ⟨inner, member, rfl⟩
      have framed := project_seedFrame state inner.1.2
        ({ state.primitive.1 with uniform := inner.2 }, state.primitive.2)
        (PqxdhRecordLiftLazyTable.step_facts slot state.seeds inner.1 original).2.1 scopeOK
      exact ⟨congrArg (fun view => view.1.server) framed, congrArg (fun view => view.1.owners) framed⟩

theorem installBeacon_finish_erasure (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (scopeOK : Scoped state) (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve .beacon ref).run state)) :
    world { markUsed result.2 .beacon ref with owners := state.owners.set owner (.established shell result.1) } =
      { PqxdhRecordLiftWorld.markUsed (world result.2) .beacon ref with
        owners := (world state).owners.set owner (.established shell (storedView result.2 result.1)) } := by
  have ownersSame : (markUsed result.2 .beacon ref).owners = state.owners := by
    cases ref <;> exact (resolve_fields .beacon _ state result supported).2.1
  have nativeOwners : (world (markUsed result.2 .beacon ref)).owners = (world state).owners := by
    rw [world_markUsed]
    cases ref <;> exact (resolve_world_records .beacon _ state scopeOK result supported).2
  rw [← ownersSame, world_owner_store]
  rw [nativeOwners, world_markUsed]
  change { PqxdhRecordLiftWorld.markUsed (world result.2) .beacon ref with
      owners := (world state).owners.set owner (.established shell (storedView (markUsed result.2 .beacon ref) result.1)) } = _
  rw [storedView_markUsed]

/-- Labeled Beacon installation returns the exact native success/refusal and full World poststate. -/
theorem installBeacon_erasure (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (scopeOK : Scoped state) :
    Prod.map id world <$> (installBeacon owner shell ref).run state =
      (PqxdhRecordLiftWorld.installBeacon owner shell ref).run (world state) := by
  have unused : PqxdhRecordLiftWorld.Unused (world state) .beacon ref ↔ Unused state .beacon ref :=
    (unused_erasure state .beacon ref).symm
  simp only [installBeacon, PqxdhRecordLiftWorld.installBeacon, StateT.run,
    ← beaconReady_erasure, unused]
  by_cases admitted : BeaconReady state owner ∧ Unused state .beacon ref
  · simp only [ite_eq_left admitted, bind_pure_comp, Functor.map_map]
    have same := resolve_world .beacon ref state scopeOK
    simp only [StateT.run] at same
    rw [← same, Functor.map_map]
    simp only [← bind_pure_comp]
    refine bind_congr_of_forall_mem_support _ (fun result supported => ?_)
    exact congrArg pure (congrArg (fun after => (true, after))
      (installBeacon_finish_erasure owner shell ref state scopeOK result supported))
  · simp only [ite_eq_right admitted, map_pure]
    rfl

theorem world_server_replace (state : State n) (server : Server n) :
    world { state with server := some server } =
      { world state with server := some (Server.erase (interpret (cachedSeeds state) state.chain) server) } := rfl

/-- Dynamic map update commutes with erasure, preserving the immutable Server identity, sender and raw counter. -/
theorem server_update_erasure (interpret : Interpretation n) (server : Server n) (keyId : Std.U64) (peer : Peer n) :
    Server.erase interpret { server with peers := Function.update server.peers keyId (some peer) } =
      { Server.erase interpret server with records :=
        { (Server.erase interpret server).records with server :=
          { (Server.erase interpret server).records.server with
            peers := Function.update (Server.erase interpret server).records.server.peers keyId (some (Peer.erase interpret peer)) } } } := by
  have peers : (fun target => (Function.update server.peers keyId (some peer) target).map (Peer.erase interpret)) =
      Function.update (fun target => (server.peers target).map (Peer.erase interpret)) keyId (some (Peer.erase interpret peer)) := by
    funext target
    by_cases same : target = keyId <;> simp [same]
  simp only [Server.erase, peers]

/-- Filling the seed cache cannot change an existing Server's interpreted peer map. -/
theorem resolve_server_erasure (role : Role) (ref : KernelRef n) (state : State n) (scopeOK : Scoped state)
    (server : Server n) (existing : state.server = some server) (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve role ref).run state)) :
    Server.erase (interpret (cachedSeeds result.2) result.2.chain) server =
      Server.erase (interpret (cachedSeeds state) state.chain) server := by
  have same := (resolve_world_records role ref state scopeOK result supported).1
  have stored := (resolve_fields role ref state result supported).1.trans existing
  change result.2.server.map (Server.erase (interpret (cachedSeeds result.2) result.2.chain)) =
    state.server.map (Server.erase (interpret (cachedSeeds state) state.chain)) at same
  rw [stored, existing, Option.map_some, Option.map_some] at same
  exact Option.some.inj same


theorem installServer_finish_erasure (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n) (scopeOK : Scoped state)
    (server : Server n) (existing : state.server = some server) (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve .server ref).run state)) :
    world { markUsed result.2 .server ref with server := some { server with
      peers := Function.update server.peers keyId (some ⟨identity, result.1⟩) } } =
      { PqxdhRecordLiftWorld.markUsed (world result.2) .server ref with
        server := some { Server.erase (interpret (cachedSeeds state) state.chain) server with records :=
          { (Server.erase (interpret (cachedSeeds state) state.chain) server).records with server :=
            { (Server.erase (interpret (cachedSeeds state) state.chain) server).records.server with
              peers := Function.update (Server.erase (interpret (cachedSeeds state) state.chain) server).records.server.peers
                keyId (some ⟨identity, storedView result.2 result.1, ()⟩) } } } } := by
  rw [world_server_replace, server_update_erasure, world_markUsed]
  have stable := resolve_server_erasure .server ref state scopeOK server existing result supported
  have marked : interpret (cachedSeeds (markUsed result.2 .server ref)) (markUsed result.2 .server ref).chain =
      interpret (cachedSeeds result.2) result.2.chain := by
    cases ref <;> rfl
  rw [marked, stable]
  rfl


/-- Labeled Server installation returns the exact native success/refusal and full World poststate. -/
theorem installServer_erasure (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n) (scopeOK : Scoped state) :
    Prod.map id world <$> (installServer keyId identity ref).run state =
      (PqxdhRecordLiftWorld.installServer keyId identity ref).run (world state) := by
  have unused : PqxdhRecordLiftWorld.Unused (world state) .server ref ↔ Unused state .server ref :=
    (unused_erasure state .server ref).symm
  have projected : (world state).server = state.server.map (Server.erase (interpret (cachedSeeds state) state.chain)) := rfl
  simp only [installServer, PqxdhRecordLiftWorld.installServer, StateT.run, projected, unused]
  cases existing : state.server with
  | none => simp only [Option.map_none, map_pure]; rfl
  | some server =>
      simp only [Option.map_some]
      have vacant : (Server.erase (interpret (cachedSeeds state) state.chain) server).records.server.peers keyId = none ↔
          server.peers keyId = none := Option.map_eq_none_iff
      simp only [vacant]
      by_cases admitted : server.peers keyId = none ∧ Unused state .server ref
      · simp only [ite_eq_left admitted, bind_pure_comp, Functor.map_map]
        have same := resolve_world .server ref state scopeOK
        simp only [StateT.run] at same
        rw [← same, Functor.map_map]
        simp only [← bind_pure_comp]
        refine bind_congr_of_forall_mem_support _ (fun result supported => ?_)
        exact congrArg pure (congrArg (fun after => (true, after))
          (installServer_finish_erasure keyId identity ref state scopeOK server existing result supported))
      · simp only [ite_eq_right admitted, map_pure]
        rfl


/-- Primitive work changes no logical record, coordinate, or cached seed. -/
theorem world_primitive (state : State n) (primitive : PqxdhRecordLiftWorld.Primitive) :
    world { state with primitive := primitive } = { world state with primitive := primitive } := rfl

theorem world_chargeEffect (query : (EnvEffects n).Domain) (state : State n) :
    world (chargeEffect query state) = PqxdhRecordLiftWorld.chargeEffect query (world state) := rfl

/-- Sampling retains the complete original World uniform instrumentation. -/
theorem sampled_world {Y : Type} (work : ProbComp Y) (state : State n) :
    Prod.map id world <$> (sampled work).run state =
      (PqxdhRecordLiftWorld.sampled work).run (world state) := by
  simp only [sampled, PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, Functor.map_map]
  rfl

/-- The private constructor handoff preserves the complete World server initialization. -/
theorem initialize_world (created : PqxdhLiveServerConstruction.Created Unit) (state : State n) :
    Prod.map id world <$> (initializeServer created).run state =
      (PqxdhRecordLiftWorld.initializeServer created).run (world state) := by
  cases found : state.server <;>
    simp [initializeServer, PqxdhRecordLiftWorld.initializeServer, StateT.run, world, project,
      erase, found, known_server_erasure]
  intro phase member
  rfl

/-- Constructor-supplied peers are known kernels, so initialization establishes their scope without a secret assumption. -/
theorem initialize_scoped (created : PqxdhLiveServerConstruction.Created Unit) (state : State n)
    (scopeOK : Scoped state) (result : Unit × State n)
    (supported : result ∈ support ((initializeServer created).run state)) : Scoped result.2 := by
  simp only [initializeServer, StateT.run] at supported
  cases found : state.server with
  | some server =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact scopeOK
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      constructor
      · intro server existing keyId peer present
        simp only [Option.some.injEq] at existing
        subst server
        simp only [Server.fromKnown] at present
        cases entry : created.server.server.peers keyId with
        | none => simp [entry] at present
        | some native =>
            simp only [entry, Option.map_some, Option.some.injEq] at present
            subst peer
            trivial
      · exact scopeOK.2


/-- Every restricted capability has the original complete World behavior after private-label erasure. -/
theorem capability_erasure (query : (CapabilitySpec n).Domain) (state : State n) (scopeOK : Scoped state) :
    Prod.map id world <$> (capability query).run state =
      (PqxdhRecordLiftWorld.capability query).run (world state) := by
  cases query with
  | installServer keyId identity ref => exact installServer_erasure keyId identity ref state scopeOK
  | installBeacon owner shell ref => exact installBeacon_erasure owner shell ref state scopeOK
  | peerPresent keyId =>
      simp only [capability, PqxdhRecordLiftWorld.capability, StateT.run, map_pure]
      change pure ((state.server.bind fun server => server.peers keyId).isSome, world state) = _
      cases existing : state.server with
      | none => simp [world, project, erase, existing]
      | some server =>
          cases present : server.peers keyId <;>
            simp [world, project, erase, existing, Server.erase, present]
  | ownerPresent owner =>
      simp only [capability, PqxdhRecordLiftWorld.capability, StateT.run, map_pure]
      simp [world, project, erase, List.getElem?_map]
  | appendOwner sender pin phase =>
      simp only [capability, PqxdhRecordLiftWorld.capability, StateT.run, map_pure,
        Prod.map_def, id_eq, world, project, erase, List.length_map, List.map_append, List.map_cons, List.map_nil]
      rfl
  | hash bytes =>
      simp only [capability, PqxdhRecordLiftWorld.capability, sampled, PqxdhRecordLiftWorld.sampled,
        StateT.run, bind_pure_comp, Functor.map_map]
      rfl
  | advanceOwner owner phase =>
      have projected : (world state).owners[owner]? =
          (state.owners[owner]?).map (Phase.erase (interpret (cachedSeeds state) state.chain)) :=
        List.getElem?_map
      simp only [capability, PqxdhRecordLiftWorld.capability, StateT.run, projected]
      cases present : state.owners[owner]? with
      | none => simp only [Option.map_none, map_pure]; rfl
      | some old =>
          cases old with
          | established shell kernel => simp only [Option.map_some, Phase.erase, map_pure]; rfl
          | inactive before =>
              simp only [Option.map_some, Phase.erase]
              by_cases legal : PqxdhRecordLiftWorld.LegalAdvance before phase
              · simp only [ite_eq_left legal, map_pure]
                exact congrArg pure (congrArg (fun after => (true, after))
                  (world_owner_store state owner (.inactive phase)))
              · simp only [ite_eq_right legal, map_pure]
                rfl


/-- Every restricted effect preserves the sampled-slot invariant through its actual operational branch. -/
theorem effects_scoped (query : (EnvEffects n).Domain) (state : State n) (scopeOK : Scoped state)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) : Scoped result.2 := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact scopeOK
  | inr request => exact capability_scoped request (chargeEffect (.inr request) state) scopeOK result supported

/-- Charged coin/hash/administrative effects exactly reproduce the frozen World's interpreter. -/
theorem effects_erasure (query : (EnvEffects n).Domain) (state : State n) (scopeOK : Scoped state) :
    Prod.map id world <$> (effects query).run state =
      (PqxdhRecordLiftWorld.effects query).run (world state) := by
  cases query with
  | inl coin =>
      simpa only [effects, PqxdhRecordLiftWorld.effects, StateT.run, world_chargeEffect] using
        sampled_world (unifSpec.query coin : ProbComp _) (chargeEffect (.inl coin) state)
  | inr request =>
      simpa only [effects, PqxdhRecordLiftWorld.effects, StateT.run, world_chargeEffect] using
        capability_erasure request (chargeEffect (.inr request) state) scopeOK

theorem initial_world : world (initial : State n) = PqxdhRecordLiftWorld.initial := rfl


/-- Every stored logical full76 answer belongs to a slot already sampled by a successful hidden installation. -/
def TableScoped (state : State n) : Prop :=
  ∀ coordinate value, state.chain coordinate = some value → SeedPresent state coordinate.slot

/-- The table's source response depends only on the selected coordinate's populated seed slot. -/
theorem output_extension_agrees (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (state : State n) (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (coordinate : Label n) (present : SeedPresent state coordinate.slot) :
    PqxdhRecordLiftRealTable.output source left state.chain coordinate =
      PqxdhRecordLiftRealTable.output source right state.chain coordinate := by
  simp only [PqxdhRecordLiftRealTable.output, PqxdhRecordLiftRealTable.request,
    chain_extension_agrees state left right hleft hright coordinate present]

/-- Real functional consistency survives any two totalizations of the actual partial seed cache. -/
theorem consistent_extension (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (state : State n) (scopeOK : TableScoped state)
    (left right : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (hleft : SeedExtension state left) (hright : SeedExtension state right)
    (consistent : PqxdhRecordLiftRealTable.Consistent source left state.chain) :
    PqxdhRecordLiftRealTable.Consistent source right state.chain := by
  intro coordinate value found
  exact (consistent coordinate value found).trans
    (output_extension_agrees source state left right hleft hright coordinate (scopeOK coordinate value found))

/-- Growing only the seed cache preserves the logical table's installation provenance. -/
theorem tableScoped_seedFrame (state : State n) (seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n))
    (primitive : PqxdhRecordLiftWorld.Primitive) (mono : state.seeds.1 ≤ seeds.1) (scopeOK : TableScoped state) :
    TableScoped (seedFrame state seeds primitive) := by
  intro coordinate value found
  obtain ⟨seed, present⟩ := scopeOK coordinate value found
  exact ⟨seed, mono present⟩

/-- Private lazy seed growth preserves existing real-table consistency; no fixed sampled family or byte-injectivity premise is used. -/
theorem realValid_seedFrame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (state : State n) (seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n))
    (primitive : PqxdhRecordLiftWorld.Primitive) (mono : state.seeds.1 ≤ seeds.1) (scopeOK : TableScoped state)
    (valid : PqxdhRecordLiftChainCompiler.RealValid source (cachedSeeds state) state.chain) :
    PqxdhRecordLiftChainCompiler.RealValid source (cachedSeeds (seedFrame state seeds primitive)) state.chain := by
  refine ⟨valid.1, consistent_extension source state scopeOK _ _ (cachedSeeds_extension state) ?_ valid.2⟩
  intro slot seed found
  exact cachedSeeds_extension (seedFrame state seeds primitive) slot seed (mono found)

theorem initial_tableScoped : TableScoped (initial : State n) := by
  intro coordinate value found
  simp [initial] at found


/-- Any adaptive restricted-effect continuation preserves the complete native result and World state; no observation or security event is substituted. -/
theorem effects_schedule_erasure {Y : Type} (client : OracleComp (EnvEffects n) Y)
    (state : State n) (scopeOK : Scoped state) :
    Prod.map id world <$> (simulateQ effects client).run state =
      (simulateQ PqxdhRecordLiftWorld.effects client).run (world state) :=
  map_run_simulateQ_eq_of_query_map_eq_inv' effects PqxdhRecordLiftWorld.effects Scoped world
    effects_scoped effects_erasure client state scopeOK


/-- All live hidden chain and skipped-material references are available, and the exact source control/coordinate certificate holds. Known kernels remain arbitrary caller-supplied native states. -/
def StoredReady (table : PqxdhRecordLiftChainTable.Table (Slot n)) : StoredKernel n → Prop
  | .known _ => True
  | .hidden _ kernel => PqxdhRecordLiftChainCompiler.KernelReferences table kernel ∧
      PqxdhRecordLiftChainCoordinates.Certified kernel

/-- A predicate over exactly the kernels held by current dynamic peers and established owners. -/
def RecordsSatisfy (predicate : StoredKernel n → Prop) (state : State n) : Prop :=
  (∀ server, state.server = some server → ∀ keyId peer, server.peers keyId = some peer → predicate peer.kernel) ∧
    (∀ phase ∈ state.owners, match phase with
      | .inactive _ => True
      | .established _ kernel => predicate kernel)

def Ready (state : State n) : Prop := RecordsSatisfy (StoredReady state.chain) state

/-- The exact source seed constructors establish live-reference and source-control facts for either physical role. -/
theorem labeledKernel_ready (table : PqxdhRecordLiftChainTable.Table (Slot n)) (role : Role) (slot : Slot n) :
    StoredReady table (.hidden slot (labeledKernel role slot)) := by
  cases role with
  | server =>
      obtain ⟨kernel, actual, _, refs, slots, _⟩ := (PqxdhRecordLiftMaterialTable.seeds_certified table slot).1
      have same : kernel = labeledKernel .server slot := RustM.ok.inj (actual.symm.trans (labeledKernel_exact .server slot))
      subst kernel
      obtain ⟨certified, actual, cert⟩ := (PqxdhRecordLiftChainCoordinates.seeds_certified slot).1
      have same : certified = labeledKernel .server slot := RustM.ok.inj (actual.symm.trans (labeledKernel_exact .server slot))
      subst certified
      exact ⟨⟨refs, slots⟩, cert⟩
  | beacon =>
      obtain ⟨kernel, actual, _, refs, slots, _⟩ := (PqxdhRecordLiftMaterialTable.seeds_certified table slot).2
      have same : kernel = labeledKernel .beacon slot := RustM.ok.inj (actual.symm.trans (labeledKernel_exact .beacon slot))
      subst kernel
      obtain ⟨certified, actual, cert⟩ := (PqxdhRecordLiftChainCoordinates.seeds_certified slot).2
      have same : certified = labeledKernel .beacon slot := RustM.ok.inj (actual.symm.trans (labeledKernel_exact .beacon slot))
      subst certified
      exact ⟨⟨refs, slots⟩, cert⟩

/-- Persistent full76 table growth preserves every existing chain and skipped-key reference. -/
theorem storedReady_mono (before after : PqxdhRecordLiftChainTable.Table (Slot n)) (mono : before ≤ after)
    (stored : StoredKernel n) (ready : StoredReady before stored) : StoredReady after stored := by
  cases stored with
  | known kernel => trivial
  | hidden slot kernel =>
      exact ⟨⟨⟨PqxdhRecordLiftChainTable.available_mono before after mono _ ready.1.1.1,
        PqxdhRecordLiftChainTable.available_mono before after mono _ ready.1.1.2⟩,
        PqxdhRecordLiftMaterialTable.slots_present_mono before after mono _ ready.1.2⟩, ready.2⟩

/-- Availability makes erasure of a held kernel stable under extension of the full76 table. -/
theorem storedView_table_mono (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (before after : PqxdhRecordLiftChainTable.Table (Slot n)) (mono : before ≤ after)
    (stored : StoredKernel n) (ready : StoredReady before stored) :
    stored.erase (interpret seeds after) = stored.erase (interpret seeds before) := by
  cases stored with
  | known kernel => rfl
  | hidden slot kernel =>
      simp only [StoredKernel.erase, interpret, PqxdhRecordLiftMaterialTable.eraseKernel,
        RawCtxMaterialInterpretation.mapRefined, RawCtxChainInterpretation.mapChains,
        PqxdhRecordLiftChainTable.chain_mono seeds before after mono _ ready.1.1.1,
        PqxdhRecordLiftChainTable.chain_mono seeds before after mono _ ready.1.1.2,
        PqxdhRecordLiftMaterialTable.slots_mono before after mono _ ready.1.2]


theorem recordsSatisfy_server_store (predicate : StoredKernel n → Prop) (state : State n)
    (server : Server n) (existing : state.server = some server) (keyId : Std.U64) (peer : Peer n)
    (before : RecordsSatisfy predicate state) (added : predicate peer.kernel) :
    RecordsSatisfy predicate { state with server := some { server with peers := Function.update server.peers keyId (some peer) } } := by
  constructor
  · intro selected found target stored present
    simp only [Option.some.injEq] at found
    subst selected
    change Function.update server.peers keyId (some peer) target = some stored at present
    by_cases same : target = keyId
    · subst target
      rw [Function.update_self] at present
      cases Option.some.inj present
      exact added
    · rw [Function.update_of_ne same] at present
      exact before.1 server existing target stored present
  · exact before.2

theorem recordsSatisfy_owner_store (predicate : StoredKernel n → Prop) (state : State n)
    (owner : Nat) (phase : Phase n) (before : RecordsSatisfy predicate state)
    (added : match phase with | .inactive _ => True | .established _ kernel => predicate kernel) :
    RecordsSatisfy predicate { state with owners := state.owners.set owner phase } := by
  constructor
  · exact before.1
  · intro selected member
    rcases List.mem_or_eq_of_mem_set member with prior | equal
    · exact before.2 selected prior
    · subst selected
      exact added

/-- Exact seed resolution preserves every old certificate and supplies one for its actual returned hidden kernel. -/
theorem resolve_ready (role : Role) (ref : KernelRef n) (state : State n) (ready : Ready state)
    (result : StoredKernel n × State n) (supported : result ∈ support ((resolve role ref).run state)) :
    Ready result.2 ∧ StoredReady result.2.chain result.1 := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run] at supported
      subst result
      exact ⟨ready, trivial⟩
  | hidden slot =>
      simp only [resolve, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ⟨ready, labeledKernel_ready state.chain role slot⟩

theorem markUsed_ready (state : State n) (role : Role) (ref : KernelRef n) (ready : Ready state) :
    Ready (markUsed state role ref) := by
  cases ref <;> exact ready

/-- A record certificate can change its surrounding private frame only through the actual table extension. -/
theorem ready_frame (before after : State n) (ready : Ready before)
    (server : after.server = before.server) (owners : after.owners = before.owners)
    (mono : before.chain ≤ after.chain) : Ready after := by
  constructor
  · intro found existing keyId peer selected
    rw [server] at existing
    exact storedReady_mono before.chain after.chain mono peer.kernel (ready.1 found existing keyId peer selected)
  · intro phase member
    rw [owners] at member
    cases phase with
    | inactive phase => trivial
    | established shell kernel => exact storedReady_mono before.chain after.chain mono kernel (ready.2 _ member)

/-- Beacon installation preserves existing source certificates and installs the actual role-directed seed certificate. -/
theorem installBeacon_ready (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (state : State n) (ready : Ready state) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) : Ready result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have resolved := resolve_ready .beacon ref state ready inner member
    have owners : (markUsed inner.2 .beacon ref).owners = state.owners := by
      cases ref <;> exact (resolve_fields .beacon _ state inner member).2.1
    rw [← owners]
    apply recordsSatisfy_owner_store _ _ _ _ (markUsed_ready inner.2 .beacon ref resolved.1)
    cases ref <;> exact resolved.2
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ready

/-- Server installation preserves every old peer certificate and installs the new one at exactly the vacant handle. -/
theorem installServer_ready (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (ready : Ready state) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) : Ready result.2 := by
  simp only [installServer, StateT.run] at supported
  cases found : state.server with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ready
  | some server =>
      simp only [found] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have resolved := resolve_ready .server ref state ready inner member
        have same : (markUsed inner.2 .server ref).server = some server := by
          cases ref <;> exact (resolve_fields .server _ state inner member).1.trans found
        apply recordsSatisfy_server_store _ _ server same keyId ⟨identity, inner.1⟩
          (markUsed_ready inner.2 .server ref resolved.1)
        cases ref <;> exact resolved.2
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ready


theorem initial_ready : Ready (initial : State n) := by
  simp [Ready, RecordsSatisfy, initial]

theorem ready_append (state : State n) (phase : InactivePhase) (ready : Ready state) :
    Ready { state with owners := state.owners ++ [.inactive phase] } := by
  constructor
  · exact ready.1
  · intro present member
    rcases List.mem_append.mp member with prior | appended
    · exact ready.2 present prior
    · simp only [List.mem_singleton] at appended
      subst present
      trivial

/-- The private constructor's caller-known peers impose no artificial hidden-kernel certificate. -/
theorem initialize_ready (created : PqxdhLiveServerConstruction.Created Unit) (state : State n)
    (ready : Ready state) (result : Unit × State n)
    (supported : result ∈ support ((initializeServer created).run state)) : Ready result.2 := by
  simp only [initializeServer, StateT.run] at supported
  cases found : state.server with
  | some server =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ready
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      constructor
      · intro server existing keyId peer present
        simp only [Option.some.injEq] at existing
        subst server
        simp only [Server.fromKnown] at present
        cases entry : created.server.server.peers keyId with
        | none => simp [entry] at present
        | some native =>
            simp only [entry, Option.map_some, Option.some.injEq] at present
            subst peer
            trivial
      · exact ready.2

/-- Every restricted administrative or hash capability preserves all live labeled source certificates. -/
theorem capability_ready (query : (CapabilitySpec n).Domain) (state : State n) (ready : Ready state)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : Ready result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_ready keyId identity ref state ready result supported
  | installBeacon owner shell ref => exact installBeacon_ready owner shell ref state ready result supported
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ready
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ready
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ready_append state phase ready
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ready
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      split at supported
      · split_ifs at supported with allowed
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact recordsSatisfy_owner_store _ state owner (.inactive phase) ready trivial
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact ready
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ready

theorem effects_ready (query : (EnvEffects n).Domain) (state : State n) (ready : Ready state)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) : Ready result.2 := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ready
  | inr request => exact capability_ready request (chargeEffect (.inr request) state) ready result supported

/-- The all-real source table invariant concerns actual populated slots and literal deterministic responses, independently of any key distribution. -/
def TableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (state : State n) : Prop :=
  TableScoped state ∧ PqxdhRecordLiftChainCompiler.RealValid source (cachedSeeds state) state.chain

/-- Actual lazy resolution preserves the all-real functional table invariant under its sampled cache extension. -/
theorem resolve_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (role : Role) (ref : KernelRef n) (state : State n) (good : TableGood source state)
    (result : StoredKernel n × State n) (supported : result ∈ support ((resolve role ref).run state)) :
    TableGood source result.2 := by
  cases ref with
  | known known =>
      simp only [resolve, StateT.run] at supported
      subst result
      exact good
  | hidden slot =>
      simp only [resolve, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have original : inner.1 ∈ support ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds) := by
        rw [← PqxdhRecordLiftWorld.countCoin_forget ((PqxdhRecordLiftLazyTable.impl slot).run state.seeds)
          state.primitive.1.uniform, support_map]
        exact ⟨inner, member, rfl⟩
      have mono := (PqxdhRecordLiftLazyTable.step_facts slot state.seeds inner.1 original).2.1
      exact ⟨tableScoped_seedFrame state inner.1.2 _ mono good.1,
        realValid_seedFrame source state inner.1.2 _ mono good.1 good.2⟩

theorem initial_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    TableGood source (initial : State n) :=
  ⟨initial_tableScoped, PqxdhRecordLiftChainCompiler.realValid_empty source _⟩


theorem markUsed_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (state : State n) (role : Role) (ref : KernelRef n) (good : TableGood source state) :
    TableGood source (markUsed state role ref) := by
  cases ref <;> exact good

theorem installBeacon_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) (state : State n) (good : TableGood source state)
    (result : Bool × State n) (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    TableGood source result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact markUsed_tableGood source inner.2 .beacon ref (resolve_tableGood source .beacon ref state good inner member)
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact good

theorem installServer_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (good : TableGood source state) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) : TableGood source result.2 := by
  simp only [installServer, StateT.run] at supported
  cases found : state.server with
  | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | some server =>
      simp only [found] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact markUsed_tableGood source inner.2 .server ref (resolve_tableGood source .server ref state good inner member)
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact good

theorem initialize_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (created : PqxdhLiveServerConstruction.Created Unit) (state : State n) (good : TableGood source state)
    (result : Unit × State n) (supported : result ∈ support ((initializeServer created).run state)) :
    TableGood source result.2 := by
  simp only [initializeServer, StateT.run] at supported
  split at supported <;> simp only [support_pure, Set.mem_singleton_iff] at supported <;> subst result <;> exact good

theorem capability_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : (CapabilitySpec n).Domain) (state : State n) (good : TableGood source state)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : TableGood source result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_tableGood source keyId identity ref state good result supported
  | installBeacon owner shell ref => exact installBeacon_tableGood source owner shell ref state good result supported
  | peerPresent keyId =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | ownerPresent owner =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | appendOwner sender pin phase =>
      simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | hash bytes =>
      simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact good
  | advanceOwner owner phase =>
      simp only [capability, StateT.run] at supported
      split at supported
      · split_ifs at supported with allowed
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact good
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact good
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact good

theorem effects_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : (EnvEffects n).Domain) (state : State n) (good : TableGood source state)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) : TableGood source result.2 := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact good
  | inr request => exact capability_tableGood source request (chargeEffect (.inr request) state) good result supported

/-- Invariant for reachable all-real private compiler states. Its clauses describe operational storage facts, not a Frame or noninterference premise; arbitrary satisfying states are not claimed reachable. -/
def Good (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (state : State n) : Prop :=
  Scoped state ∧ Ready state ∧ TableGood source state

theorem initial_good (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) : Good source (initial : State n) :=
  ⟨initial_scoped, initial_ready, initial_tableGood source⟩


/-- One complete send under a stored kernel. Hidden roles retain logical coordinates; caller-known roles invoke the literal original source send. -/
noncomputable def kernelSend {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P) (stored : StoredKernel n)
    (context : RawCtxSourceSend.SealContext) :
    StateT (PqxdhRecordLiftChainCompiler.Execution (Slot n) P) ProbComp
      (StoredKernel n × Option RawCtxSourceSend.Encrypted) := fun state =>
  match stored with
  | .known kernel => do
      let result ← (simulateQ native (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))).run state.2
      pure ((.known result.1.1, result.1.2), (state.1, result.2))
  | .hidden slot kernel => do
      let result ← (PqxdhRecordLiftChainCompiler.send seeds lookup (PqxdhRecordLiftNativeAdapters.sendSeal native)
        (RawCtxChainSend.normalBegin kernel context)).run state
      pure ((.hidden slot result.1.1, result.1.2), result.2)

/-- One complete receive uses the source opening adapter and its actual optional plaintext. -/
noncomputable def kernelReceive {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P) (stored : StoredKernel n)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    StateT (PqxdhRecordLiftChainCompiler.Execution (Slot n) P) ProbComp
      (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) := fun state =>
  match stored with
  | .known kernel => do
      let result ← (simulateQ native (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))).run state.2
      pure ((.known result.1.1, result.1.2), (state.1, result.2))
  | .hidden slot kernel => do
      let result ← (PqxdhRecordLiftChainCompiler.receive seeds lookup (PqxdhRecordLiftNativeAdapters.receiveOpen native)
        (RawCtxChainReceive.normalBegin kernel target context)).run state
      pure ((.hidden slot result.1.1, result.1.2), result.2)

/-- The complete kernel reply is interpreted under the final persistent table; only that auxiliary table is erased. -/
noncomputable def kernelResult {P Reply : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (result : (StoredKernel n × Reply) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P) :
    (ConcreteRatchetKernel × Reply) × P :=
  ((result.1.1.erase (interpret seeds result.2.1), result.1.2), result.2.2)

/-- Both known and hidden sends match the actual native source operation with its complete primitive poststate. -/
theorem kernelSend_erasure {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (realized : PqxdhRecordLiftChainCompiler.LookupRealized seeds valid lookup (PqxdhRecordLiftNativeAdapters.sendKdf native))
    (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 stored) :
    kernelResult seeds <$> (kernelSend seeds lookup native stored context).run state =
      (simulateQ native (simulateQ RawCtxSourceSend.adapter
        (RawCtxSourceSend.send (stored.erase (interpret seeds state.1)) context))).run state.2 := by
  cases stored with
  | known kernel =>
      simp only [kernelSend, StateT.run, bind_pure_comp, Functor.map_map]
      change id <$> _ = _
      exact id_map _
  | hidden slot kernel =>
      simpa only [kernelSend, StateT.run, bind_pure_comp, Functor.map_map, kernelResult,
        StoredKernel.erase, interpret, PqxdhRecordLiftNativeAdapters.concreteResult,
        PqxdhRecordLiftChainCompiler.eraseSendResult, Function.comp_def] using
        PqxdhRecordLiftNativeAdapters.send_adapter seeds valid lookup native preserves realized kernel context state good ready.1

/-- Both known and hidden receives retain exact source rollback/publication, optional plaintext and primitive state. -/
theorem kernelReceive_erasure {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (realized : PqxdhRecordLiftChainCompiler.LookupRealized seeds valid lookup (PqxdhRecordLiftNativeAdapters.receiveKdf native))
    (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 stored) :
    kernelResult seeds <$> (kernelReceive seeds lookup native stored target context).run state =
      (simulateQ native (simulateQ RawCtxWholeOwner.adapter
        (RawCtxOwnerOracle.receive (stored.erase (interpret seeds state.1)) target context))).run state.2 := by
  cases stored with
  | known kernel =>
      simp only [kernelReceive, StateT.run, bind_pure_comp, Functor.map_map]
      change id <$> _ = _
      exact id_map _
  | hidden slot kernel =>
      simpa only [kernelReceive, StateT.run, bind_pure_comp, Functor.map_map, kernelResult,
        StoredKernel.erase, interpret, PqxdhRecordLiftNativeAdapters.concreteResult,
        PqxdhRecordLiftChainCompiler.eraseResult, Function.comp_def] using
        PqxdhRecordLiftNativeAdapters.receive_adapter seeds valid lookup native preserves realized kernel target context state good ready.1


/-- Actual complete send execution preserves the stored origin, live certificate, table extension and installed-slot scope. -/
theorem kernelSend_preserves {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (frame : State n) (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 stored) (scopeOK : KernelScoped frame stored)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelSend seeds lookup native stored context).run state)) :
    valid result.2.1 ∧ state.1 ≤ result.2.1 ∧ StoredReady result.2.1 result.1.1 ∧
      KernelScoped frame result.1.1 ∧ result.1.1.origin = stored.origin := by
  cases stored with
  | known kernel =>
      simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ⟨good, le_rfl, trivial, trivial, rfl⟩
  | hidden slot kernel =>
      simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have facts := PqxdhRecordLiftChainCompiler.send_preserves seeds valid lookup
        (PqxdhRecordLiftNativeAdapters.sendSeal native) preserves _ state good
        (PqxdhRecordLiftChainCompiler.send_begin_references state.1 kernel ready.1 context) inner member
      have certified := PqxdhRecordLiftChainCoordinates.send_certified seeds lookup
        (PqxdhRecordLiftNativeAdapters.sendSeal native) kernel context ready.2 state inner member
      have coords := PqxdhRecordLiftChainCoordinates.send_origins kernel inner.1.1
        (PqxdhRecordLiftChainCoordinates.admitted_send_coordinates seeds lookup
          (PqxdhRecordLiftNativeAdapters.sendSeal native) kernel context state inner member)
      exact ⟨facts.1, facts.2.1, ⟨facts.2.2, certified⟩,
        ⟨scopeOK.1, coords.2.2.1.trans scopeOK.2.1, (congrArg (fun c => c.slot) coords.1).trans scopeOK.2.2⟩, rfl⟩

/-- Actual complete receive execution preserves the stored slot, source certificate and table references through cache consumption, future derivation and rollback. -/
theorem kernelReceive_preserves {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (frame : State n) (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 stored) (scopeOK : KernelScoped frame stored)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelReceive seeds lookup native stored target context).run state)) :
    valid result.2.1 ∧ state.1 ≤ result.2.1 ∧ StoredReady result.2.1 result.1.1 ∧
      KernelScoped frame result.1.1 ∧ result.1.1.origin = stored.origin := by
  cases stored with
  | known kernel =>
      simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact ⟨good, le_rfl, trivial, trivial, rfl⟩
  | hidden slot kernel =>
      simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have facts := PqxdhRecordLiftChainCompiler.admitted_receive_preserves seeds valid lookup
        (PqxdhRecordLiftNativeAdapters.receiveOpen native) preserves kernel target context ready.2.1.capacity
        state good ready.1 inner member
      have certified := PqxdhRecordLiftChainCoordinates.receive_certified seeds lookup
        (PqxdhRecordLiftNativeAdapters.receiveOpen native) kernel context target ready.2 state inner member
      have coords := PqxdhRecordLiftChainCoordinates.receive_origins kernel inner.1.1
        (PqxdhRecordLiftChainCoordinates.admitted_receive_coordinates seeds lookup
          (PqxdhRecordLiftNativeAdapters.receiveOpen native) kernel context target ready.2.1.capacity state inner member)
      exact ⟨facts.1, facts.2.1, ⟨facts.2.2, certified⟩,
        ⟨scopeOK.1, (congrArg (fun c => c.slot) coords.1).trans scopeOK.2.1, coords.2.1.trans scopeOK.2.2⟩, rfl⟩


/-- One currently selected record owner; source sender, expected peer and associated data remain separate. -/
structure Owner (n : Nat) where
  kernel : StoredKernel n
  expectedSender : Std.U64
  associatedData : Pqxdh.Bytes
  rawAttempts : Nat

noncomputable def Owner.erase (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (owner : Owner n) : RawCtxWholeOwner.OwnerState Unit :=
  ⟨⟨owner.kernel.erase (interpret seeds table), owner.expectedSender, owner.associatedData, ()⟩, owner.rawAttempts⟩

abbrev Native (P : Type) := QueryImpl RawCtxMixedOwner.NativeSpec (StateT P ProbComp)

noncomputable def receiveNative {P : Type} (native : Native P) : PqxdhRecordLiftNativeAdapters.ReceiveNative P :=
  native ∘ₛ RawCtxMixedOwner.receiveAdapter

noncomputable def sendNative {P : Type} (native : Native P) : PqxdhRecordLiftNativeAdapters.SendNative P :=
  native ∘ₛ RawCtxMixedOwner.sendAdapter

/-- Empty sends reject before taking a kernel; otherwise the exact source context feeds the complete labeled/native send. -/
noncomputable def ownerSend {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (owner : Owner n) :
    StateT (PqxdhRecordLiftChainCompiler.Execution (Slot n) P) ProbComp (Option RawCtxSourceSend.Encrypted × Owner n) :=
  fun state => if plaintext.isEmpty then pure ((none, owner), state) else do
    let context : RawCtxSourceSend.SealContext := ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩
    let result ← (kernelSend seeds lookup (sendNative native) owner.kernel context).run state
    pure ((result.1.2, { owner with kernel := result.1.1 }), result.2)

/-- Every existing-owner raw attempt increments once, before parsing/validation; rejected input never invokes a kernel callback. -/
noncomputable def ownerReceive {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n) :
    StateT (PqxdhRecordLiftChainCompiler.Execution (Slot n) P) ProbComp
      (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) := fun state =>
  let rejected := pure ((.None, { owner with rawAttempts := owner.rawAttempts + 1 }), state)
  if raw.isEmpty then rejected else
    match decode raw with
    | none => rejected
    | some frame =>
        if RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame then do
          let result ← (kernelReceive seeds lookup (receiveNative native) owner.kernel frame.sequence
            ⟨raw, frame, owner.associatedData⟩).run state
          pure ((result.1.2, { owner with kernel := result.1.1, rawAttempts := owner.rawAttempts + 1 }), result.2)
        else rejected

noncomputable def ownerStep {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) :
    StateT (PqxdhRecordLiftChainCompiler.Execution (Slot n) P) ProbComp (RawCtxMixedOwner.SourceSpec.Range query × Owner n) :=
  match query with
  | .inl plaintext => ownerSend seeds lookup native sender plaintext owner
  | .inr raw => ownerReceive seeds lookup native decode raw owner

noncomputable def ownerResult {P Reply : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P) :
    (Reply × RawCtxWholeOwner.OwnerState Unit) × P :=
  ((result.1.1, Owner.erase seeds result.2.1 result.1.2), result.2.2)

/-- The complete selected-owner send agrees with the original empty-input check, source context and native publication. -/
theorem ownerSend_erasure {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (realized : PqxdhRecordLiftChainCompiler.LookupRealized seeds valid lookup
      (PqxdhRecordLiftNativeAdapters.sendKdf (sendNative native)))
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 owner.kernel) :
    ownerResult seeds <$> (ownerSend seeds lookup native sender plaintext owner).run state =
      (simulateQ (sendNative native) ((RawCtxSourceSend.sendOwner sender plaintext).run (Owner.erase seeds state.1 owner))).run state.2 := by
  simp only [ownerSend, RawCtxSourceSend.sendOwner, StateT.run]
  by_cases empty : plaintext.isEmpty = true
  · simp only [empty, ↓reduceIte, map_pure, simulateQ_pure]
    rfl
  · simp only [Bool.eq_false_of_not_eq_true empty, Bool.false_eq_true, ↓reduceIte,
      bind_pure_comp, Functor.map_map, simulateQ_map]
    change _ = ((fun sent => (sent.2,
      (⟨⟨sent.1, owner.expectedSender, owner.associatedData, ()⟩, owner.rawAttempts⟩ : RawCtxWholeOwner.OwnerState Unit))) <$>
        simulateQ (sendNative native) (simulateQ RawCtxSourceSend.adapter
          (RawCtxSourceSend.send (owner.kernel.erase (interpret seeds state.1))
            ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩))).run state.2
    rw [StateT.run_map]
    have same := kernelSend_erasure seeds valid lookup (sendNative native) preserves realized owner.kernel
      ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ state good ready
    rw [← same, Functor.map_map]
    rfl


/-- Empty, malformed and invalid raws preserve the original no-callback rejection, while admitted raws use the exact complete native receive and publication. -/
theorem ownerReceive_erasure {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (realized : PqxdhRecordLiftChainCompiler.LookupRealized seeds valid lookup
      (PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative native)))
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 owner.kernel) :
    ownerResult seeds <$> (ownerReceive seeds lookup native decode raw owner).run state =
      (simulateQ (receiveNative native) ((RawCtxWholeOwner.rawReceive decode raw).run (Owner.erase seeds state.1 owner))).run state.2 := by
  simp only [ownerReceive, RawCtxWholeOwner.rawReceive, StateT.run]
  by_cases empty : raw.isEmpty = true
  · simp only [empty, ↓reduceIte, map_pure, simulateQ_pure]
    rfl
  · simp only [Bool.eq_false_of_not_eq_true empty, Bool.false_eq_true, ↓reduceIte]
    cases decoded : decode raw with
    | none => simp only [map_pure, simulateQ_pure]; rfl
    | some frame =>
        simp only [Owner.erase]
        by_cases admitted : RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame
        · simp only [ite_eq_left admitted, bind_pure_comp, Functor.map_map, simulateQ_map]
          change _ = ((fun received => (received.2,
            (⟨⟨received.1, owner.expectedSender, owner.associatedData, ()⟩, owner.rawAttempts + 1⟩ : RawCtxWholeOwner.OwnerState Unit))) <$>
              simulateQ (receiveNative native) (simulateQ RawCtxWholeOwner.adapter
                (RawCtxOwnerOracle.receive (owner.kernel.erase (interpret seeds state.1)) frame.sequence
                  ⟨raw, frame, owner.associatedData⟩))).run state.2
          rw [StateT.run_map]
          have same := kernelReceive_erasure seeds valid lookup (receiveNative native) preserves realized owner.kernel
            frame.sequence ⟨raw, frame, owner.associatedData⟩ state good ready
          rw [← same, Functor.map_map]
          rfl
        · simp only [admitted, ↓reduceIte, map_pure, simulateQ_pure]
          rfl

/-- The selected mixed owner agrees with the original source owner interpreter under the complete common primitive state. -/
theorem ownerStep_erasure {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (realizedSend : PqxdhRecordLiftChainCompiler.LookupRealized seeds valid lookup
      (PqxdhRecordLiftNativeAdapters.sendKdf (sendNative native)))
    (realizedReceive : PqxdhRecordLiftChainCompiler.LookupRealized seeds valid lookup
      (PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative native)))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 owner.kernel) :
    ownerResult seeds <$> (ownerStep seeds lookup native sender decode query owner).run state =
      (simulateQ native ((RawCtxMixedOwner.ownerImpl sender decode query).run (Owner.erase seeds state.1 owner))).run state.2 := by
  cases query with
  | inl plaintext =>
      simpa only [ownerStep, RawCtxMixedOwner.ownerImpl, StateT.run, sendNative,
        QueryImpl.simulateQ_compose] using
        ownerSend_erasure seeds valid lookup native preserves realizedSend sender plaintext owner state good ready
  | inr raw =>
      simpa only [ownerStep, RawCtxMixedOwner.ownerImpl, StateT.run, receiveNative,
        QueryImpl.simulateQ_compose] using
        ownerReceive_erasure seeds valid lookup native preserves realizedReceive decode raw owner state good ready


/-- Full local publication facts, including immutable owner metadata and the exact raw-attempt ghost. -/
def OwnerFacts {P Reply : Type} (frame : State n) (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (owner : Owner n) (rawCount : Nat)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P) : Prop :=
  valid result.2.1 ∧ state.1 ≤ result.2.1 ∧ StoredReady result.2.1 result.1.2.kernel ∧
    KernelScoped frame result.1.2.kernel ∧ result.1.2.kernel.origin = owner.kernel.origin ∧
      result.1.2.expectedSender = owner.expectedSender ∧ result.1.2.associatedData = owner.associatedData ∧
        result.1.2.rawAttempts = rawCount

theorem ownerFacts_unchanged {P Reply : Type} (frame : State n)
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (owner : Owner n) (reply : Reply) (rawCount : Nat)
    (good : valid state.1) (ready : StoredReady state.1 owner.kernel) (scopeOK : KernelScoped frame owner.kernel) :
    OwnerFacts frame valid state owner rawCount ((reply, { owner with rawAttempts := rawCount }), state) :=
  ⟨good, le_rfl, ready, scopeOK, rfl, rfl, rfl, rfl⟩

/-- The selected owner's source send retains all local invariants even on empty input, exhaustion and failed sealing. -/
theorem ownerSend_preserves {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (frame : State n) (sender : Std.U64) (plaintext : Pqxdh.Bytes) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 owner.kernel) (scopeOK : KernelScoped frame owner.kernel)
    (result : (Option RawCtxSourceSend.Encrypted × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerSend seeds lookup native sender plaintext owner).run state)) :
    OwnerFacts frame valid state owner owner.rawAttempts result := by
  simp only [ownerSend, StateT.run] at supported
  split_ifs at supported with empty
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ownerFacts_unchanged frame valid state owner none owner.rawAttempts good ready scopeOK
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    have facts := kernelSend_preserves seeds valid lookup (sendNative native) preserves frame owner.kernel
      ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ state good ready scopeOK inner member
    exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2, rfl, rfl, rfl⟩

/-- The selected owner's source receive keeps the certificate and exactly one raw increment on every parser, validation and opening branch. -/
theorem ownerReceive_preserves {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (frame : State n) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 owner.kernel) (scopeOK : KernelScoped frame owner.kernel)
    (result : (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerReceive seeds lookup native decode raw owner).run state)) :
    OwnerFacts frame valid state owner (owner.rawAttempts + 1) result := by
  simp only [ownerReceive, StateT.run] at supported
  split_ifs at supported with empty
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact ownerFacts_unchanged frame valid state owner core.option.Option.None (owner.rawAttempts + 1) good ready scopeOK
  · cases decoded : decode raw with
    | none =>
        simp only [decoded, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ownerFacts_unchanged frame valid state owner core.option.Option.None (owner.rawAttempts + 1) good ready scopeOK
    | some decodedFrame =>
        simp only [decoded] at supported
        split_ifs at supported with admitted
        · simp only [bind_pure_comp, support_map] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          have facts := kernelReceive_preserves seeds valid lookup (receiveNative native) preserves frame owner.kernel
            decodedFrame.sequence ⟨raw, decodedFrame, owner.associatedData⟩ state good ready scopeOK inner member
          exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2, rfl, rfl, rfl⟩
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact ownerFacts_unchanged frame valid state owner core.option.Option.None (owner.rawAttempts + 1) good ready scopeOK

def ownerRawAfter (query : RawCtxMixedOwner.SourceSpec.Domain) (before : Nat) : Nat :=
  match query with | .inl _ => before | .inr _ => before + 1

theorem ownerStep_preserves {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (valid : PqxdhRecordLiftChainTable.Table (Slot n) → Prop)
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (preserves : PqxdhRecordLiftChainCompiler.LookupPreserves valid lookup)
    (frame : State n) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P) (good : valid state.1)
    (ready : StoredReady state.1 owner.kernel) (scopeOK : KernelScoped frame owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerStep seeds lookup native sender decode query owner).run state)) :
    OwnerFacts frame valid state owner (ownerRawAfter query owner.rawAttempts) result := by
  cases query with
  | inl plaintext => exact ownerSend_preserves seeds valid lookup native preserves frame sender plaintext owner state good ready scopeOK result supported
  | inr raw => exact ownerReceive_preserves seeds valid lookup native preserves frame decode raw owner state good ready scopeOK result supported


/-- Both original mixed adapters forward the exact charged World KDF; this equality supplies their functional response instance. -/
theorem mixedKdf_world {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    PqxdhRecordLiftNativeAdapters.sendKdf (sendNative (PqxdhRecordLiftWorld.primitives setup codec)) = nativeKdf setup codec ∧
      PqxdhRecordLiftNativeAdapters.receiveKdf (receiveNative (PqxdhRecordLiftWorld.primitives setup codec)) = nativeKdf setup codec := by
  constructor
  · funext request
    change PqxdhRecordLiftRealTable.fromResponse <$>
      PqxdhRecordLiftLoggedAdapters.sendNative (PqxdhRecordLiftWorld.primitives setup codec) (.inl request) = _
    rw [PqxdhRecordLiftLoggedAdapters.sendNative_kdf]
    rfl
  · funext request
    change PqxdhRecordLiftRealTable.fromResponse <$>
      PqxdhRecordLiftLoggedAdapters.receiveNative (PqxdhRecordLiftWorld.primitives setup codec) (.inl request) = _
    rw [PqxdhRecordLiftLoggedAdapters.receiveNative_kdf]
    rfl

abbrev LookupPolicy (n : Nat) := PqxdhRecordLiftChainTable.Seeds (Slot n) →
  PqxdhRecordLiftChainCompiler.Lookup (Slot n) PqxdhRecordLiftWorld.Primitive

/-- The all-real policy invokes the actual charged native KDF on every callback, including repeated coordinates. -/
noncomputable def realPolicy {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) : LookupPolicy n := fun seeds =>
  PqxdhRecordLiftChainCompiler.realLookup seeds (nativeKdf setup codec)

/-- Execute one selected owner with the literal source writer log, original shared ROM/cache counters, and private persistent logical table. -/
noncomputable def ownerRun {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n) :=
  (ownerStep (cachedSeeds state) (PqxdhRecordLiftLoggedAdapters.liftLookup (policy (cachedSeeds state)))
    (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec))
    sender codec.frameRead query owner).run (state.chain, (state.primitive, []))

/-- The actual all-real selected-owner execution equals the original native logged operation, including failed-writer frames and all counters/cache. -/
theorem ownerRun_real {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (good : TableGood setup.source state) (ready : StoredReady state.chain owner.kernel) :
    ownerResult (cachedSeeds state) <$> ownerRun (realPolicy setup codec) setup codec sender query owner state =
      PqxdhRecordLiftLoggedAdapters.swapResult <$>
        (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) (PqxdhDeploymentNative.logged
          ((RawCtxMixedOwner.ownerImpl sender codec.frameRead query).run
            (Owner.erase (cachedSeeds state) state.chain owner)))).run state.primitive := by
  let valid := PqxdhRecordLiftChainCompiler.RealValid setup.source (cachedSeeds state)
  have preserves := PqxdhRecordLiftLoggedAdapters.liftLookup_preserves valid
    ((realPolicy setup codec) (cachedSeeds state))
    (PqxdhRecordLiftChainCompiler.realLookup_preserves setup.source (cachedSeeds state) _ (nativeKdf_real setup codec))
  have realized := PqxdhRecordLiftLoggedAdapters.liftLookup_realized (cachedSeeds state) valid
    ((realPolicy setup codec) (cachedSeeds state)) (nativeKdf setup codec)
    (PqxdhRecordLiftChainCompiler.realLookup_realized (cachedSeeds state) _ valid)
  have sendEq : PqxdhRecordLiftNativeAdapters.sendKdf
      (sendNative (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec))) =
      PqxdhRecordLiftLoggedAdapters.liftKdf (nativeKdf setup codec) := by
    exact (PqxdhRecordLiftLoggedAdapters.sendKdf_logged (PqxdhRecordLiftWorld.primitives setup codec)).trans
      (congrArg PqxdhRecordLiftLoggedAdapters.liftKdf (mixedKdf_world setup codec).1)
  have receiveEq : PqxdhRecordLiftNativeAdapters.receiveKdf
      (receiveNative (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec))) =
      PqxdhRecordLiftLoggedAdapters.liftKdf (nativeKdf setup codec) := by
    exact (PqxdhRecordLiftLoggedAdapters.receiveKdf_logged (PqxdhRecordLiftWorld.primitives setup codec)).trans
      (congrArg PqxdhRecordLiftLoggedAdapters.liftKdf (mixedKdf_world setup codec).2)
  have same := ownerStep_erasure (cachedSeeds state) valid _
    (PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec))
    preserves (sendEq.symm ▸ realized) (receiveEq.symm ▸ realized)
    sender codec.frameRead query owner (state.chain, (state.primitive, [])) good.2 ready
  exact same.trans (PqxdhRecordLiftLoggedAdapters.program_native_logged
    (PqxdhRecordLiftWorld.primitives setup codec) _ state.primitive)


/-- The source peer identity builds AD in Server/Beacon order; assigned target ID and immutable local sender are distinct. -/
noncomputable def serverOwner (server : Server n) (keyId : Std.U64) (peer : Peer n) : Owner n :=
  ⟨peer.kernel, keyId, RawCtxServerRouting.associatedBytes server.identity peer.identity, server.rawAttempts⟩

def beaconOwner (shell : BeaconShell) (kernel : StoredKernel n) (rawAttempts : Nat) : Owner n :=
  ⟨kernel, shell.control.server_binding.identity_key_id, PqxdhRefinement.absBytes shell.associatedData, rawAttempts⟩

/-- Source record work changes the complete primitive state and private full76 table together. -/
def recordFrame (state : State n) (table : PqxdhRecordLiftChainTable.Table (Slot n))
    (primitive : PqxdhRecordLiftWorld.Primitive) : State n :=
  { state with chain := table, primitive := primitive }

def produce (tag : PqxdhDeploymentInterface.FrameTag) (frames : List PqxdhDeploymentNative.Frame)
    (state : State n) : State n :=
  { state with produced := state.produced ++ frames.map fun frame => (tag, frame) }

/-- Reinstall the selected whole kernel and counter, preserving the original peer identity and all immutable Server fields. -/
def serverPublish {Reply : Type} (tag : PqxdhDeploymentInterface.FrameTag)
    (state : State n) (server : Server n) (keyId : Std.U64) (peer : Peer n)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame)) : Reply × State n :=
  (result.1.1, produce tag result.2.2.2 { recordFrame state result.2.1 result.2.2.1 with
    server := some { server with
      peers := Function.update server.peers keyId (some { peer with kernel := result.1.2.kernel })
      rawAttempts := result.1.2.rawAttempts } })

/-- Beacon publication keeps its exact source shell and preserves the independent raw counter for every other owner. -/
def beaconPublish {Reply : Type} (state : State n) (owner : Nat) (shell : BeaconShell)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame)) : Reply × State n :=
  (result.1.1, produce (PqxdhDeploymentNative.beaconTag owner) result.2.2.2
    { recordFrame state result.2.1 result.2.2.1 with
      owners := state.owners.set owner (.established shell result.1.2.kernel)
      ownerRaw := Function.update state.ownerRaw owner result.1.2.rawAttempts })

/-- The actual header router selects the dynamic peer entry before full raw decoding. Missing peers increment only an existing Server's raw ghost. -/
noncomputable def serverStep {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) :
    StateT (State n) ProbComp (RawCtxServerMixed.SourceSpec.Range query) := fun state =>
  match state.server with
  | none => match query with
      | .inl _ => pure (none, state)
      | .inr _ => pure (.None, state)
  | some server => match query with
      | .inl (plaintext, keyId) => match server.peers keyId with
          | none => pure (none, state)
          | some peer => serverPublish (PqxdhDeploymentNative.serverTag query) state server keyId peer <$>
              ownerRun policy setup codec server.sender (.inl plaintext) (serverOwner server keyId peer) state
      | .inr raw =>
          let rejected := pure (.None, { state with server := some { server with rawAttempts := server.rawAttempts + 1 } })
          match route raw with
          | none => rejected
          | some keyId => match server.peers keyId with
              | none => rejected
              | some peer => serverPublish (PqxdhDeploymentNative.serverTag query) state server keyId peer <$>
                  ownerRun policy setup codec server.sender (.inr raw) (serverOwner server keyId peer) state

/-- Missing owner handles have no raw attempt; existing inactive phases reject exactly and increment the independent ghost only for raw receive. -/
noncomputable def beaconStep {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) :
    StateT (State n) ProbComp (RawCtxMixedOwner.SourceSpec.Range query) := fun state =>
  match state.owners[owner]? with
  | none => pure (PqxdhDeploymentNative.absent query, state)
  | some (.inactive _) => match query with
      | .inl _ => pure (none, state)
      | .inr _ => pure (.None, { state with ownerRaw := Function.update state.ownerRaw owner (state.ownerRaw owner + 1) })
  | some (.established shell kernel) => beaconPublish state owner shell <$>
      ownerRun policy setup codec shell.identityKeyId query (beaconOwner shell kernel (state.ownerRaw owner)) state

/-- All frozen world operations execute against the actual dynamic storage. Only the private ordinary-record lookup is parameterized for later hybrids. -/
noncomputable def handler {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (WorldSpec n) (StateT (State n) ProbComp)
  | .inl created => initializeServer created
  | .inr (.inl query) => effects query
  | .inr (.inr (.inl (.inl query))) => serverStep policy setup codec route (.inl query)
  | .inr (.inr (.inl (.inr raw))) => serverStep policy setup codec route (.inr raw)
  | .inr (.inr (.inr (owner, .inl plaintext))) => beaconStep policy setup codec owner (.inl plaintext)
  | .inr (.inr (.inr (owner, .inr raw))) => beaconStep policy setup codec owner (.inr raw)

/-- Internal execution retains its whole private state and the original program result, including environment E. Security observations must use the separate permitted projection. -/
noncomputable def run {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :=
  (simulateQ (handler policy setup codec route)
    (program env setup.source.crypto codec serverKid bounds mode adversary)).run initial

theorem world_produce (tag : PqxdhDeploymentInterface.FrameTag) (frames : List PqxdhDeploymentNative.Frame)
    (state : State n) : world (produce tag frames state) = PqxdhRecordLiftWorld.produce tag frames (world state) := rfl


/-- Every held peer kernel has the same bytes after persistent table growth. -/
theorem server_table_mono (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (before after : PqxdhRecordLiftChainTable.Table (Slot n)) (mono : before ≤ after)
    (server : Server n) (ready : ∀ keyId peer, server.peers keyId = some peer → StoredReady before peer.kernel) :
    Server.erase (interpret seeds after) server = Server.erase (interpret seeds before) server := by
  have peers : (fun keyId => (server.peers keyId).map (Peer.erase (interpret seeds after))) =
      (fun keyId => (server.peers keyId).map (Peer.erase (interpret seeds before))) := by
    funext keyId
    cases found : server.peers keyId with
    | none => rfl
    | some peer =>
        exact congrArg some (congrArg (fun kernel => RawCtxServerRouting.Peer.mk peer.identity kernel ())
          (storedView_table_mono seeds before after mono peer.kernel (ready keyId peer found)))
  simp only [Server.erase, peers]

/-- Table growth preserves the entire erased dynamic map and owner list, including every unselected record. -/
theorem erase_table_mono (state : State n) (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (mono : state.chain ≤ table) (ready : Ready state) :
    erase (interpret seeds table) state = erase (interpret seeds state.chain) state := by
  have servers : state.server.map (Server.erase (interpret seeds table)) =
      state.server.map (Server.erase (interpret seeds state.chain)) := by
    cases found : state.server with
    | none => rfl
    | some server => exact congrArg some (server_table_mono seeds state.chain table mono server (ready.1 server found))
  have owners : state.owners.map (Phase.erase (interpret seeds table)) =
      state.owners.map (Phase.erase (interpret seeds state.chain)) := by
    apply List.map_congr_left
    intro phase member
    cases phase with
    | inactive phase => rfl
    | established shell kernel =>
        exact congrArg (PqxdhRecordLiftBeacon.Phase.established shell)
          (storedView_table_mono seeds state.chain table mono kernel (ready.2 _ member))
  simp only [erase, servers, owners]

/-- Record callbacks change the full primitive state while extending the private table; all old records keep their exact native interpretation. -/
theorem world_recordFrame (state : State n) (table : PqxdhRecordLiftChainTable.Table (Slot n))
    (primitive : PqxdhRecordLiftWorld.Primitive) (mono : state.chain ≤ table) (ready : Ready state) :
    world (recordFrame state table primitive) = { world state with primitive := primitive } := by
  exact congrArg (fun view : PqxdhRecordLiftOrigins.State n => { view.1 with primitive := primitive })
    (erase_table_mono state (cachedSeeds state) table mono ready)


/-- The actual all-real owner run preserves the complete local certificate and extends the table. -/
theorem ownerRun_preserves {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (good : TableGood setup.source state) (ready : StoredReady state.chain owner.kernel)
    (scopeOK : KernelScoped state owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (supported : result ∈ support (ownerRun (realPolicy setup codec) setup codec sender query owner state)) :
    OwnerFacts state (PqxdhRecordLiftChainCompiler.RealValid setup.source (cachedSeeds state))
      (state.chain, (state.primitive, [])) owner (ownerRawAfter query owner.rawAttempts) result := by
  exact ownerStep_preserves (cachedSeeds state) _ _ _
    (PqxdhRecordLiftLoggedAdapters.liftLookup_preserves _ _
      (PqxdhRecordLiftChainCompiler.realLookup_preserves setup.source (cachedSeeds state) _ (nativeKdf_real setup codec)))
    state sender codec.frameRead query owner (state.chain, (state.primitive, [])) good.2 ready scopeOK result supported

def worldBeaconPublish {Reply : Type} (state : PqxdhRecordLiftWorld.State n) (owner : Nat) (shell : BeaconShell)
    (result : (Reply × RawCtxWholeOwner.OwnerState Unit) ×
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame)) : Reply × PqxdhRecordLiftWorld.State n :=
  (result.1.1, PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag owner) result.2.2
    { state with owners := state.owners.set owner (.established shell result.1.2.owner.kernel)
                 ownerRaw := Function.update state.ownerRaw owner result.1.2.rawAttempts
                 primitive := result.2.1 })

theorem world_ownerRaw (state : State n) (ownerRaw : Nat → Nat) :
    world { state with ownerRaw := ownerRaw } = { world state with ownerRaw := ownerRaw } := rfl

/-- Selected Beacon publication commutes with final-table erasure while every unselected owner is framed by persistence. -/
theorem beaconPublish_erasure {Reply : Type} (state : State n) (owner : Nat) (shell : BeaconShell)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (mono : state.chain ≤ result.2.1) (ready : Ready state) :
    Prod.map id world (beaconPublish state owner shell result) =
      worldBeaconPublish (world state) owner shell (ownerResult (cachedSeeds state) result) := by
  simp only [beaconPublish, Prod.map, id_eq, world_produce]
  have framed := world_recordFrame state result.2.1 result.2.2.1 mono ready
  have stored := world_owner_store
    ({ recordFrame state result.2.1 result.2.2.1 with
      ownerRaw := Function.update state.ownerRaw owner result.1.2.rawAttempts }) owner
    (.established shell result.1.2.kernel)
  rw [world_ownerRaw, framed] at stored
  exact congrArg (fun after => (result.1.1,
    PqxdhRecordLiftWorld.produce (PqxdhDeploymentNative.beaconTag owner) result.2.2.2 after)) stored


/-- The existing World's established Beacon branch is exactly the logged whole-owner call and its literal publication. -/
theorem world_beacon_selected {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhRecordLiftWorld.State n)
    (shell : BeaconShell) (kernel : ConcreteRatchetKernel)
    (selected : state.owners[owner]? = some (.established shell kernel)) :
    (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run state =
      worldBeaconPublish state owner shell <$> (PqxdhRecordLiftLoggedAdapters.swapResult <$>
        (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) (PqxdhDeploymentNative.logged
          ((RawCtxMixedOwner.ownerImpl shell.identityKeyId codec.frameRead query).run
            ⟨⟨kernel, shell.control.server_binding.identity_key_id,
              PqxdhRefinement.absBytes shell.associatedData, ()⟩, state.ownerRaw owner⟩))).run state.primitive) := by
  have mapApply {A B : Type} (f : A → B) (work : StateT PqxdhRecordLiftWorld.Primitive ProbComp A) :
      (f <$> work) state.primitive = Prod.map f id <$> work state.primitive := by
    change (f <$> work).run state.primitive = _
    rw [StateT.run_map]
    rfl
  simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, selected, PqxdhRecordLiftBeacon.handler,
    bind_pure_comp, PqxdhDeploymentNative.logged_map, simulateQ_map, mapApply, Functor.map_map]
  rfl


/-- Established Beacon execution retains the complete native World result, with no observation projection or successful-opening premise. -/
theorem beaconStep_selected_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n) (good : Good setup.source state)
    (shell : BeaconShell) (kernel : StoredKernel n)
    (selected : state.owners[owner]? = some (.established shell kernel)) :
    Prod.map id world <$> (beaconStep (realPolicy setup codec) setup codec owner query).run state =
      (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run (world state) := by
  have member : Phase.established shell kernel ∈ state.owners := List.mem_of_getElem? selected
  have ready : StoredReady state.chain kernel := good.2.1.2 _ member
  have scopeOK : KernelScoped state kernel := good.1.2 _ member
  have nativeSelected : (world state).owners[owner]? =
      some (.established shell (storedView state kernel)) := by
    simp only [world, project, erase, List.getElem?_map, selected, Option.map_some, Phase.erase, storedView]
  rw [world_beacon_selected setup codec owner query (world state) shell (storedView state kernel) nativeSelected]
  have same := ownerRun_real setup codec shell.identityKeyId query
    (beaconOwner shell kernel (state.ownerRaw owner)) state good.2.2 ready
  change _ = worldBeaconPublish (world state) owner shell <$>
    (PqxdhRecordLiftLoggedAdapters.swapResult <$>
      (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) (PqxdhDeploymentNative.logged
        ((RawCtxMixedOwner.ownerImpl shell.identityKeyId codec.frameRead query).run
          (Owner.erase (cachedSeeds state) state.chain (beaconOwner shell kernel (state.ownerRaw owner)))))).run state.primitive)
  rw [← same, Functor.map_map]
  simp only [beaconStep, StateT.run, selected, Functor.map_map]
  simp only [← bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ (fun result supported => ?_)
  have facts := ownerRun_preserves setup codec shell.identityKeyId query
    (beaconOwner shell kernel (state.ownerRaw owner)) state good.2.2 ready scopeOK result supported
  exact congrArg pure (beaconPublish_erasure state owner shell result facts.2.1 good.2.1)


/-- An existing inactive Beacon rejects without primitive work and increments its raw ghost exactly for raw receive. -/
theorem world_beacon_inactive {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : PqxdhRecordLiftWorld.State n)
    (phase : InactivePhase) (selected : state.owners[owner]? = some (.inactive phase)) :
    (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run state =
      match query with
      | .inl _ => pure (none, state)
      | .inr _ => pure (.None, { state with ownerRaw := Function.update state.ownerRaw owner (state.ownerRaw owner + 1) }) := by
  have same : state.owners.set owner (.inactive phase) = state.owners := by
    obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp selected
    rw [← found, List.set_getElem_self bound]
  have pureApply {A : Type} (value : A) :
      (pure value : StateT PqxdhRecordLiftWorld.Primitive ProbComp A) state.primitive = pure (value, state.primitive) := by
    change (pure value : StateT PqxdhRecordLiftWorld.Primitive ProbComp A).run state.primitive = _
    rw [StateT.run_pure]
  cases query <;>
    simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, selected, PqxdhRecordLiftBeacon.handler,
      PqxdhRecordLiftBeacon.rejected, PqxdhDeploymentNative.logged_pure, simulateQ_pure,
      pureApply, pure_bind, PqxdhRecordLiftWorld.produce, List.map_nil, List.append_nil, same,
      Function.update_eq_self]

/-- All Beacon handles, including absent and inactive ones, retain the exact complete World result. -/
theorem beaconStep_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n) (good : Good setup.source state) :
    Prod.map id world <$> (beaconStep (realPolicy setup codec) setup codec owner query).run state =
      (PqxdhRecordLiftWorld.beaconStep setup codec owner query).run (world state) := by
  cases selected : state.owners[owner]? with
  | none =>
      have absent : (world state).owners[owner]? = none := by
        simp only [world, project, erase, List.getElem?_map, selected, Option.map_none]
      simp only [beaconStep, PqxdhRecordLiftWorld.beaconStep, StateT.run, selected, absent, map_pure]
      rfl
  | some phase =>
      cases phase with
      | established shell kernel => exact beaconStep_selected_erasure setup codec owner query state good shell kernel selected
      | inactive phase =>
          have inactive : (world state).owners[owner]? = some (.inactive phase) := by
            simp only [world, project, erase, List.getElem?_map, selected, Option.map_some, Phase.erase]
          rw [world_beacon_inactive setup codec owner query (world state) phase inactive]
          cases query <;> simp only [beaconStep, StateT.run, selected, map_pure] <;> rfl


noncomputable def sourceServerOwner (server : PqxdhRecordLiftWorld.Server) (keyId : Std.U64)
    (peer : RawCtxServerRouting.Peer Unit) : RawCtxWholeOwner.OwnerState Unit :=
  ⟨RawCtxServerRouting.selectedOwner keyId
    (RawCtxServerRouting.associatedBytes server.records.server.identity peer.identity) peer, server.records.rawAttempts⟩

def sourceServerPublish {Reply : Type} (server : PqxdhRecordLiftWorld.Server) (keyId : Std.U64)
    (peer : RawCtxServerRouting.Peer Unit) (result : Reply × RawCtxWholeOwner.OwnerState Unit) :
    Reply × RawCtxServerRouting.State Unit Unit :=
  (result.1, ⟨RawCtxServerRouting.putPeer server.records.server keyId peer result.2.owner.kernel, result.2.rawAttempts⟩)


/-- Original Server send selects the same whole-owner call and reinstalls its exact result in the original peer map. -/
theorem source_server_send (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (plaintext : Pqxdh.Bytes) (server : PqxdhRecordLiftWorld.Server)
    (keyId : Std.U64) (peer : RawCtxServerRouting.Peer Unit)
    (selected : server.records.server.peers keyId = some peer) :
    (RawCtxServerMixed.serverImpl (fun _ => server.sender) route decode (.inl (plaintext, keyId))).run server.records =
      sourceServerPublish server keyId peer <$>
        (RawCtxMixedOwner.ownerImpl server.sender decode (.inl plaintext)).run (sourceServerOwner server keyId peer) := by
  simp only [RawCtxServerMixed.serverImpl, StateT.run, RawCtxServerMixed.sendServer,
    RawCtxServerSend.sendServer_selected (fun _ => server.sender) plaintext keyId server.records peer selected,
    bind_pure_comp, simulateQ_map, QueryImpl.simulateQ_compose,
    RawCtxMixedOwner.ownerImpl, RawCtxMixedOwner.sendAdapter]
  rfl

/-- Original header routing and AD lookup select the same peer before invoking the complete raw owner operation. -/
theorem source_server_raw (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (server : PqxdhRecordLiftWorld.Server)
    (keyId : Std.U64) (peer : RawCtxServerRouting.Peer Unit)
    (selected : server.records.server.peers keyId = some peer) (routed : route raw = some keyId) :
    (RawCtxServerMixed.serverImpl (fun _ => server.sender) route decode (.inr raw)).run server.records =
      sourceServerPublish server keyId peer <$>
        (RawCtxMixedOwner.ownerImpl server.sender decode (.inr raw)).run (sourceServerOwner server keyId peer) := by
  simp only [RawCtxServerMixed.serverImpl, StateT.run, RawCtxServerMixed.rawServer, routed,
    RawCtxServerRouting.peerAssociatedData, selected, bind_pure_comp,
    RawCtxMixedOwner.ownerImpl]
  rfl


def worldServerPublish {Reply : Type} (tag : PqxdhDeploymentInterface.FrameTag)
    (state : PqxdhRecordLiftWorld.State n) (server : PqxdhRecordLiftWorld.Server)
    (keyId : Std.U64) (peer : RawCtxServerRouting.Peer Unit)
    (result : (Reply × RawCtxWholeOwner.OwnerState Unit) ×
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame)) : Reply × PqxdhRecordLiftWorld.State n :=
  (result.1.1, PqxdhRecordLiftWorld.produce tag result.2.2
    { state with server := some { server with records := (sourceServerPublish server keyId peer result.1).2 }
                 primitive := result.2.1 })

theorem server_raw_erasure (interpret : Interpretation n) (server : Server n) (rawAttempts : Nat) :
    Server.erase interpret { server with rawAttempts := rawAttempts } =
      { Server.erase interpret server with records :=
        { (Server.erase interpret server).records with rawAttempts := rawAttempts } } := rfl

/-- Whole Server publication frames every other peer under table persistence and retains the original sender and identities. -/
theorem serverPublish_erasure {Reply : Type} (tag : PqxdhDeploymentInterface.FrameTag)
    (state : State n) (server : Server n) (existing : state.server = some server)
    (keyId : Std.U64) (peer : Peer n)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (mono : state.chain ≤ result.2.1) (ready : Ready state) :
    Prod.map id world (serverPublish tag state server keyId peer result) =
      worldServerPublish tag (world state) (Server.erase (interpret (cachedSeeds state) state.chain) server)
        keyId (Peer.erase (interpret (cachedSeeds state) state.chain) peer)
          (ownerResult (cachedSeeds state) result) := by
  simp only [serverPublish, Prod.map, id_eq, world_produce, world_server_replace]
  have framed := world_recordFrame state result.2.1 result.2.2.1 mono ready
  have old := server_table_mono (cachedSeeds state) state.chain result.2.1 mono server (ready.1 server existing)
  have updated := server_update_erasure (interpret (cachedSeeds state) result.2.1)
    { server with rawAttempts := result.1.2.rawAttempts } keyId { peer with kernel := result.1.2.kernel }
  rw [server_raw_erasure, old] at updated
  rw [framed]
  change (result.1.1, PqxdhRecordLiftWorld.produce tag result.2.2.2
    { world state with primitive := result.2.2.1
                       server := some (Server.erase (interpret (cachedSeeds state) result.2.1)
        { server with peers := Function.update server.peers keyId (some { peer with kernel := result.1.2.kernel })
                      rawAttempts := result.1.2.rawAttempts }) }) = _
  rw [updated]
  rfl


/-- Logging and complete primitive interpretation commute with the original selected-peer publication equation. -/
theorem world_server_selected {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : PqxdhRecordLiftWorld.State n)
    (server : PqxdhRecordLiftWorld.Server) (existing : state.server = some server)
    (keyId : Std.U64) (peer : RawCtxServerRouting.Peer Unit)
    (work : OracleComp RawCtxMixedOwner.NativeSpec (RawCtxServerMixed.SourceSpec.Range query × RawCtxWholeOwner.OwnerState Unit))
    (selected : (RawCtxServerMixed.serverImpl (fun _ => server.sender) route codec.frameRead query).run server.records =
      sourceServerPublish server keyId peer <$> work) :
    (PqxdhRecordLiftWorld.serverStep setup codec route query).run state =
      worldServerPublish (PqxdhDeploymentNative.serverTag query) state server keyId peer <$>
        (PqxdhRecordLiftLoggedAdapters.swapResult <$>
          (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) (PqxdhDeploymentNative.logged work)).run state.primitive) := by
  have mapApply {A B : Type} (f : A → B) (work : StateT PqxdhRecordLiftWorld.Primitive ProbComp A) :
      (f <$> work) state.primitive = Prod.map f id <$> work state.primitive := by
    change (f <$> work).run state.primitive = _
    rw [StateT.run_map]
    rfl
  simp only [StateT.run] at selected
  simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, existing, selected,
    bind_pure_comp, PqxdhDeploymentNative.logged_map, simulateQ_map, mapApply, Functor.map_map]
  rfl

/-- A selected Server send retains the complete original logged World operation and dynamic publication. -/
theorem serverStep_send_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (plaintext : Pqxdh.Bytes) (keyId : Std.U64) (state : State n) (good : Good setup.source state)
    (server : Server n) (existing : state.server = some server) (peer : Peer n) (selected : server.peers keyId = some peer) :
    Prod.map id world <$> (serverStep (realPolicy setup codec) setup codec route (.inl (plaintext, keyId))).run state =
      (PqxdhRecordLiftWorld.serverStep setup codec route (.inl (plaintext, keyId))).run (world state) := by
  let nativeServer := Server.erase (interpret (cachedSeeds state) state.chain) server
  let nativePeer := Peer.erase (interpret (cachedSeeds state) state.chain) peer
  have nativeExisting : (world state).server = some nativeServer := by
    simp only [world, project, erase, existing, Option.map_some, nativeServer]
  have nativeSelected : nativeServer.records.server.peers keyId = some nativePeer := by
    simp only [nativeServer, nativePeer, Server.erase, selected, Option.map_some]
  rw [world_server_selected setup codec route (.inl (plaintext, keyId)) (world state) nativeServer nativeExisting keyId nativePeer
    _ (source_server_send route codec.frameRead plaintext nativeServer keyId nativePeer nativeSelected)]
  have ready := good.2.1.1 server existing keyId peer selected
  have scopeOK := good.1.1 server existing keyId peer selected
  have same := ownerRun_real setup codec server.sender (.inl plaintext) (serverOwner server keyId peer) state good.2.2 ready
  change _ = worldServerPublish (PqxdhDeploymentNative.serverTag (.inl (plaintext, keyId))) (world state) nativeServer keyId nativePeer <$>
    (PqxdhRecordLiftLoggedAdapters.swapResult <$>
      (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) (PqxdhDeploymentNative.logged
        ((RawCtxMixedOwner.ownerImpl server.sender codec.frameRead (.inl plaintext)).run
          (Owner.erase (cachedSeeds state) state.chain (serverOwner server keyId peer))))).run state.primitive)
  rw [← same, Functor.map_map]
  simp only [serverStep, StateT.run, existing, selected, Functor.map_map]
  simp only [← bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ (fun result supported => ?_)
  have facts := ownerRun_preserves setup codec server.sender (.inl plaintext) (serverOwner server keyId peer)
    state good.2.2 ready scopeOK result supported
  exact congrArg pure (serverPublish_erasure (PqxdhDeploymentNative.serverTag (.inl (plaintext, keyId)))
    state server existing keyId peer result facts.2.1 good.2.1)


/-- A routed raw Server receive retains the original optional plaintext, whole kernel, full native counters/cache and all writer frames. -/
theorem serverStep_raw_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (raw : Pqxdh.Bytes) (keyId : Std.U64) (state : State n) (good : Good setup.source state)
    (server : Server n) (existing : state.server = some server) (peer : Peer n)
    (selected : server.peers keyId = some peer) (routed : route raw = some keyId) :
    Prod.map id world <$> (serverStep (realPolicy setup codec) setup codec route (.inr raw)).run state =
      (PqxdhRecordLiftWorld.serverStep setup codec route (.inr raw)).run (world state) := by
  let nativeServer := Server.erase (interpret (cachedSeeds state) state.chain) server
  let nativePeer := Peer.erase (interpret (cachedSeeds state) state.chain) peer
  have nativeExisting : (world state).server = some nativeServer := by
    simp only [world, project, erase, existing, Option.map_some, nativeServer]
  have nativeSelected : nativeServer.records.server.peers keyId = some nativePeer := by
    simp only [nativeServer, nativePeer, Server.erase, selected, Option.map_some]
  rw [world_server_selected setup codec route (.inr raw) (world state) nativeServer nativeExisting keyId nativePeer
    _ (source_server_raw route codec.frameRead raw nativeServer keyId nativePeer nativeSelected routed)]
  have ready := good.2.1.1 server existing keyId peer selected
  have scopeOK := good.1.1 server existing keyId peer selected
  have same := ownerRun_real setup codec server.sender (.inr raw) (serverOwner server keyId peer) state good.2.2 ready
  change _ = worldServerPublish (PqxdhDeploymentNative.serverTag (.inr raw)) (world state) nativeServer keyId nativePeer <$>
    (PqxdhRecordLiftLoggedAdapters.swapResult <$>
      (simulateQ (PqxdhRecordLiftWorld.primitives setup codec) (PqxdhDeploymentNative.logged
        ((RawCtxMixedOwner.ownerImpl server.sender codec.frameRead (.inr raw)).run
          (Owner.erase (cachedSeeds state) state.chain (serverOwner server keyId peer))))).run state.primitive)
  rw [← same, Functor.map_map]
  simp only [serverStep, StateT.run, existing, routed, selected, Functor.map_map]
  simp only [← bind_pure_comp]
  refine bind_congr_of_forall_mem_support _ (fun result supported => ?_)
  have facts := ownerRun_preserves setup codec server.sender (.inr raw) (serverOwner server keyId peer)
    state good.2.2 ready scopeOK result supported
  exact congrArg pure (serverPublish_erasure (PqxdhDeploymentNative.serverTag (.inr raw))
    state server existing keyId peer result facts.2.1 good.2.1)

/-- An original Server program that rejects purely changes no primitive field and emits no frame. -/
theorem world_server_pure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : PqxdhRecordLiftWorld.State n)
    (server : PqxdhRecordLiftWorld.Server) (existing : state.server = some server)
    (reply : RawCtxServerMixed.SourceSpec.Range query) (after : RawCtxServerRouting.State Unit Unit)
    (source : (RawCtxServerMixed.serverImpl (fun _ => server.sender) route codec.frameRead query).run server.records = pure (reply, after)) :
    (PqxdhRecordLiftWorld.serverStep setup codec route query).run state =
      pure (reply, { state with server := some { server with records := after } }) := by
  have pureApply {A : Type} (value : A) :
      (pure value : StateT PqxdhRecordLiftWorld.Primitive ProbComp A) state.primitive = pure (value, state.primitive) := by
    change (pure value : StateT PqxdhRecordLiftWorld.Primitive ProbComp A).run state.primitive = _
    rw [StateT.run_pure]
  simp only [StateT.run] at source
  simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, existing, source,
    PqxdhDeploymentNative.logged_pure, simulateQ_pure, pureApply, pure_bind,
    PqxdhRecordLiftWorld.produce, List.map_nil, List.append_nil]


/-- Every Server branch, including uninitialized, unroutable and missing-peer rejection, equals the complete original World step. -/
theorem serverStep_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n) (good : Good setup.source state) :
    Prod.map id world <$> (serverStep (realPolicy setup codec) setup codec route query).run state =
      (PqxdhRecordLiftWorld.serverStep setup codec route query).run (world state) := by
  cases existing : state.server with
  | none =>
      have absent : (world state).server = none := by simp only [world, project, erase, existing, Option.map_none]
      cases query <;>
        simp only [serverStep, PqxdhRecordLiftWorld.serverStep, StateT.run, existing, absent, map_pure] <;> rfl
  | some server =>
      let nativeServer := Server.erase (interpret (cachedSeeds state) state.chain) server
      have nativeExisting : (world state).server = some nativeServer := by
        simp only [world, project, erase, existing, Option.map_some, nativeServer]
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | some peer => exact serverStep_send_erasure setup codec route plaintext keyId state good server existing peer selected
          | none =>
              have nativeMissing : nativeServer.records.server.peers keyId = none := by
                simp only [nativeServer, Server.erase, selected, Option.map_none]
              have source : (RawCtxServerMixed.serverImpl (fun _ => nativeServer.sender) route codec.frameRead
                  (.inl (plaintext, keyId))).run nativeServer.records = pure (none, nativeServer.records) := by
                simp only [RawCtxServerMixed.serverImpl, StateT.run, RawCtxServerMixed.sendServer,
                  RawCtxServerSend.sendServer_missing _ _ _ _ nativeMissing, simulateQ_pure]
              rw [world_server_pure setup codec route (.inl (plaintext, keyId)) (world state) nativeServer nativeExisting none nativeServer.records source]
              simp only [serverStep, StateT.run, existing, selected, map_pure]
              change pure (none, world state) = pure (none, { world state with server := some nativeServer })
              rw [← nativeExisting]
      | inr raw =>
          cases routed : route raw with
          | none =>
              have source : (RawCtxServerMixed.serverImpl (fun _ => nativeServer.sender) route codec.frameRead
                  (.inr raw)).run nativeServer.records = pure (.None, { nativeServer.records with rawAttempts := nativeServer.records.rawAttempts + 1 }) := by
                simp only [RawCtxServerMixed.serverImpl, StateT.run, RawCtxServerMixed.rawServer, routed]
              rw [world_server_pure setup codec route (.inr raw) (world state) nativeServer nativeExisting .None _ source]
              simp only [serverStep, StateT.run, existing, routed, map_pure, Prod.map, id_eq,
                world_server_replace, server_raw_erasure]
              rfl
          | some keyId =>
              cases selected : server.peers keyId with
              | some peer => exact serverStep_raw_erasure setup codec route raw keyId state good server existing peer selected routed
              | none =>
                  have source : (RawCtxServerMixed.serverImpl (fun _ => nativeServer.sender) route codec.frameRead
                      (.inr raw)).run nativeServer.records = pure (.None, { nativeServer.records with rawAttempts := nativeServer.records.rawAttempts + 1 }) := by
                    simp only [RawCtxServerMixed.serverImpl, StateT.run, RawCtxServerMixed.rawServer, routed,
                      RawCtxServerRouting.peerAssociatedData, nativeServer, Server.erase, selected, Option.map_none]
                    rfl
                  rw [world_server_pure setup codec route (.inr raw) (world state) nativeServer nativeExisting .None _ source]
                  simp only [serverStep, StateT.run, existing, routed, selected, map_pure, Prod.map, id_eq,
                    world_server_replace, server_raw_erasure]
                  rfl


/-- The literal real callback writes only its requested coordinate, regardless of the native reply or caller state. -/
theorem realLookup_writesOnly {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (kdf : PqxdhRecordLiftChainCompiler.Kdf P) :
    PqxdhRecordLiftTableScope.LookupWritesOnly (PqxdhRecordLiftChainCompiler.realLookup seeds kdf) := by
  intro coordinate state result supported other value found
  simp only [PqxdhRecordLiftChainCompiler.realLookup, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  by_cases same : other = coordinate
  · exact Or.inl same
  · exact Or.inr ⟨value, (QueryCache.cacheQuery_of_ne state.1 inner.1 same).symm.trans found⟩

/-- Labeled sends cannot create a table entry for an unallocated slot, including failed sealing after the KDF write. -/
theorem kernelSend_allowed {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.SendNative P)
    (footprint : PqxdhRecordLiftTableScope.LookupWritesOnly lookup) (frame : State n)
    (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (before : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent frame) state.1)
    (scopeOK : KernelScoped frame stored)
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelSend seeds lookup native stored context).run state)) :
    PqxdhRecordLiftTableScope.TableAllowed (SeedPresent frame) result.2.1 := by
  cases stored with
  | known kernel =>
      simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      exact before
  | hidden slot kernel =>
      simp only [kernelSend, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact PqxdhRecordLiftTableScope.admitted_send_allowed (SeedPresent frame) seeds lookup footprint
        (PqxdhRecordLiftNativeAdapters.sendSeal native) kernel context
        (scopeOK.2.1.symm ▸ scopeOK.1) state before inner member

/-- The full receive recursion, cached opening and rollback keep every table write in a previously sampled slot. -/
theorem kernelReceive_allowed {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P)
    (native : PqxdhRecordLiftNativeAdapters.ReceiveNative P)
    (footprint : PqxdhRecordLiftTableScope.LookupWritesOnly lookup) (frame : State n)
    (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (before : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent frame) state.1)
    (scopeOK : KernelScoped frame stored)
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((kernelReceive seeds lookup native stored target context).run state)) :
    PqxdhRecordLiftTableScope.TableAllowed (SeedPresent frame) result.2.1 := by
  cases stored with
  | known kernel =>
      simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      exact before
  | hidden slot kernel =>
      simp only [kernelReceive, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact PqxdhRecordLiftTableScope.admitted_receive_allowed (SeedPresent frame) seeds lookup footprint
        (PqxdhRecordLiftNativeAdapters.receiveOpen native) kernel context target
        (scopeOK.2.2.symm ▸ scopeOK.1) state before inner member


/-- Empty sends, parser rejection and the admitted source drivers all retain the allocated-slot table domain. -/
theorem ownerStep_allowed {P : Type} (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (lookup : PqxdhRecordLiftChainCompiler.Lookup (Slot n) P) (native : Native P)
    (footprint : PqxdhRecordLiftTableScope.LookupWritesOnly lookup) (frame : State n)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : Owner n) (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (before : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent frame) state.1)
    (scopeOK : KernelScoped frame owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n) P)
    (supported : result ∈ support ((ownerStep seeds lookup native sender decode query owner).run state)) :
    PqxdhRecordLiftTableScope.TableAllowed (SeedPresent frame) result.2.1 := by
  cases query with
  | inl plaintext =>
      simp only [ownerStep, ownerSend, StateT.run] at supported
      split_ifs at supported with empty
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact before
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        exact kernelSend_allowed seeds lookup (sendNative native) footprint frame owner.kernel
          ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩ state before scopeOK inner member
  | inr raw =>
      simp only [ownerStep, ownerReceive, StateT.run] at supported
      split_ifs at supported with empty
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact before
      · cases decoded : decode raw with
        | none =>
            simp only [decoded, support_pure, Set.mem_singleton_iff] at supported
            subst result
            exact before
        | some decodedFrame =>
            simp only [decoded] at supported
            split_ifs at supported with admitted
            · simp only [bind_pure_comp, support_map] at supported
              obtain ⟨inner, member, rfl⟩ := supported
              exact kernelReceive_allowed seeds lookup (receiveNative native) footprint frame owner.kernel
                decodedFrame.sequence ⟨raw, decodedFrame, owner.associatedData⟩ state before scopeOK inner member
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact before

/-- The actual logged real interpreter preserves allocation scope without changing the seed cache. -/
theorem ownerRun_allowed {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (before : TableScoped state) (scopeOK : KernelScoped state owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (supported : result ∈ support (ownerRun (realPolicy setup codec) setup codec sender query owner state)) :
    PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) result.2.1 :=
  ownerStep_allowed (cachedSeeds state) _ _
    (PqxdhRecordLiftTableScope.liftLookup_writesOnly _ (realLookup_writesOnly (cachedSeeds state) (nativeKdf setup codec)))
    state sender codec.frameRead query owner (state.chain, (state.primitive, [])) before scopeOK result supported


/-- Primitive effects and persistent valid table growth frame the operational invariant of all held records. -/
theorem good_recordFrame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (state : State n)
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (primitive : PqxdhRecordLiftWorld.Primitive)
    (good : Good source state) (mono : state.chain ≤ table)
    (valid : PqxdhRecordLiftChainCompiler.RealValid source (cachedSeeds state) table)
    (allowed : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) table) :
    Good source (recordFrame state table primitive) :=
  ⟨scoped_same_records state _ le_rfl rfl rfl good.1,
    ready_frame state _ good.2.1 rfl rfl mono, allowed, valid⟩

/-- The independent Server raw-attempt ghost cannot alter any kernel, seed or table certificate. -/
theorem good_serverRaw (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (state : State n) (server : Server n) (existing : state.server = some server)
    (rawAttempts : Nat) (good : Good source state) :
    Good source { state with server := some { server with rawAttempts := rawAttempts } } := by
  refine ⟨⟨?_, good.1.2⟩, ⟨?_, good.2.1.2⟩, good.2.2⟩
  · intro actual found keyId peer selected
    cases Option.some.inj found
    exact good.1.1 server existing keyId peer selected
  · intro actual found keyId peer selected
    cases Option.some.inj found
    exact good.2.1.1 server existing keyId peer selected

/-- Reinstalling one selected Beacon retains all operational invariants and every untouched record. -/
theorem beaconPublish_good {Reply : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (state : State n) (owner : Nat) (shell : BeaconShell) (beforeOwner : Owner n) (rawCount : Nat)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (good : Good source state)
    (facts : OwnerFacts state (PqxdhRecordLiftChainCompiler.RealValid source (cachedSeeds state))
      (state.chain, (state.primitive, [])) beforeOwner rawCount result)
    (allowed : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) result.2.1) :
    Good source (beaconPublish state owner shell result).2 := by
  let framed := recordFrame state result.2.1 result.2.2.1
  have framedGood := good_recordFrame source state result.2.1 result.2.2.1 good facts.2.1 facts.1 allowed
  exact ⟨scoped_owner_store framed owner (.established shell result.1.2.kernel) framedGood.1 facts.2.2.2.1,
    recordsSatisfy_owner_store (StoredReady result.2.1) framed owner (.established shell result.1.2.kernel)
      framedGood.2.1 facts.2.2.1, framedGood.2.2⟩

/-- Reinstalling one dynamic Server peer retains all operational invariants, including the independent raw count. -/
theorem serverPublish_good {Reply : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (tag : PqxdhDeploymentInterface.FrameTag) (state : State n) (server : Server n)
    (existing : state.server = some server) (keyId : Std.U64) (peer : Peer n) (beforeOwner : Owner n) (rawCount : Nat)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (good : Good source state)
    (facts : OwnerFacts state (PqxdhRecordLiftChainCompiler.RealValid source (cachedSeeds state))
      (state.chain, (state.primitive, [])) beforeOwner rawCount result)
    (allowed : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) result.2.1) :
    Good source (serverPublish tag state server keyId peer result).2 := by
  let framed := recordFrame state result.2.1 result.2.2.1
  have framedGood := good_recordFrame source state result.2.1 result.2.2.1 good facts.2.1 facts.1 allowed
  let counted := { framed with server := some { server with rawAttempts := result.1.2.rawAttempts } }
  have countedGood := good_serverRaw source framed server existing result.1.2.rawAttempts framedGood
  exact ⟨scoped_server_store counted { server with rawAttempts := result.1.2.rawAttempts } rfl keyId
      { peer with kernel := result.1.2.kernel } countedGood.1 facts.2.2.2.1,
    recordsSatisfy_server_store (StoredReady result.2.1) counted { server with rawAttempts := result.1.2.rawAttempts } rfl keyId
      { peer with kernel := result.1.2.kernel } countedGood.2.1 facts.2.2.1, countedGood.2.2⟩


/-- Every supported Beacon operation preserves the source-derived allocation, reference and control invariants. -/
theorem beaconStep_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n) (good : Good setup.source state)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep (realPolicy setup codec) setup codec owner query).run state)) :
    Good setup.source result.2 := by
  cases selected : state.owners[owner]? with
  | none =>
      simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact good
      | established shell kernel =>
          simp only [beaconStep, StateT.run, selected, support_map] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          have present := List.mem_of_getElem? selected
          have ready : StoredReady state.chain kernel := good.2.1.2 _ present
          have scopeOK : KernelScoped state kernel := good.1.2 _ present
          exact beaconPublish_good setup.source state owner shell (beaconOwner shell kernel (state.ownerRaw owner))
            (ownerRawAfter query (state.ownerRaw owner)) inner good
            (ownerRun_preserves setup codec shell.identityKeyId query _ state good.2.2 ready scopeOK inner member)
            (ownerRun_allowed setup codec shell.identityKeyId query _ state good.2.2.1 scopeOK inner member)

/-- Every actual Server routing branch preserves the same invariant, with no selected-peer or successful-operation hypothesis. -/
theorem serverStep_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n) (good : Good setup.source state)
    (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep (realPolicy setup codec) setup codec route query).run state)) :
    Good setup.source result.2 := by
  cases existing : state.server with
  | none =>
      cases query <;>
        simp only [serverStep, StateT.run, existing, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact good
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [serverStep, StateT.run, existing, selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact good
          | some peer =>
              simp only [serverStep, StateT.run, existing, selected, support_map] at supported
              obtain ⟨inner, member, rfl⟩ := supported
              have ready := good.2.1.1 server existing keyId peer selected
              have scopeOK := good.1.1 server existing keyId peer selected
              exact serverPublish_good setup.source _ state server existing keyId peer (serverOwner server keyId peer)
                server.rawAttempts inner good
                (ownerRun_preserves setup codec server.sender (.inl plaintext) _ state good.2.2 ready scopeOK inner member)
                (ownerRun_allowed setup codec server.sender (.inl plaintext) _ state good.2.2.1 scopeOK inner member)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, StateT.run, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact good_serverRaw setup.source state server existing (server.rawAttempts + 1) good
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact good_serverRaw setup.source state server existing (server.rawAttempts + 1) good
              | some peer =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_map] at supported
                  obtain ⟨inner, member, rfl⟩ := supported
                  have ready := good.2.1.1 server existing keyId peer selected
                  have scopeOK := good.1.1 server existing keyId peer selected
                  exact serverPublish_good setup.source _ state server existing keyId peer (serverOwner server keyId peer)
                    (server.rawAttempts + 1) inner good
                    (ownerRun_preserves setup codec server.sender (.inr raw) _ state good.2.2 ready scopeOK inner member)
                    (ownerRun_allowed setup codec server.sender (.inr raw) _ state good.2.2.1 scopeOK inner member)


/-- Every actual private-world request preserves the invariant from which the local source interpretation laws are derived. -/
theorem handler_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (good : Good setup.source state)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler (realPolicy setup codec) setup codec route query).run state)) :
    Good setup.source result.2 := by
  cases query with
  | inl created =>
      exact ⟨initialize_scoped created state good.1 result supported,
        initialize_ready created state good.2.1 result supported,
        initialize_tableGood setup.source created state good.2.2 result supported⟩
  | inr outer =>
      cases outer with
      | inl effect =>
          exact ⟨effects_scoped effect state good.1 result supported,
            effects_ready effect state good.2.1 result supported,
            effects_tableGood setup.source effect state good.2.2 result supported⟩
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact serverStep_good setup codec route (.inl send) state good result supported
              | inr raw => exact serverStep_good setup codec route (.inr raw) state good result supported
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact beaconStep_good setup codec owner (.inl plaintext) state good result supported
              | inr raw => exact beaconStep_good setup codec owner (.inr raw) state good result supported

/-- All world effects, installation and ordinary record operations have the exact source result and complete native poststate. -/
theorem handler_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (good : Good setup.source state) :
    Prod.map id world <$> (handler (realPolicy setup codec) setup codec route query).run state =
      (PqxdhRecordLiftWorld.handler setup codec route query).run (world state) := by
  cases query with
  | inl created => exact initialize_world created state
  | inr outer =>
      cases outer with
      | inl effect => exact effects_erasure effect state good.1
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact serverStep_erasure setup codec route (.inl send) state good
              | inr raw => exact serverStep_erasure setup codec route (.inr raw) state good
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact beaconStep_erasure setup codec owner (.inl plaintext) state good
              | inr raw => exact beaconStep_erasure setup codec owner (.inr raw) state good

/-- Complete adaptive source simulation retains every program result, full native world field and arbitrary continuation. The state invariant is operational and is derived from initial execution below. -/
theorem schedule_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (good : Good setup.source state) :
    Prod.map id world <$> (simulateQ (handler (realPolicy setup codec) setup codec route) client).run state =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) client).run (world state) :=
  map_run_simulateQ_eq_of_query_map_eq_inv' (handler (realPolicy setup codec) setup codec route)
    (PqxdhRecordLiftWorld.handler setup codec route) (Good setup.source) world
    (handler_good setup codec route) (handler_erasure setup codec route) client state good

/-- From the actual empty state, every adaptive WorldSpec schedule is exactly the original World after erasing private labels and table. No reachability or secrecy premise is supplied by the caller. -/
theorem initial_schedule_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) :
    Prod.map id world <$> (simulateQ (handler (realPolicy setup codec) setup codec route) client).run initial =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) client).run PqxdhRecordLiftWorld.initial :=
  schedule_erasure setup codec route client initial (initial_good setup.source)

/-- The frozen open program's actual execution, including environment E and the world-owned ledger, agrees with the complete original World run. This is an internal operational equation, not a security-event domain. -/
theorem run_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    Prod.map id world <$> run (realPolicy setup codec) setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary :=
  initial_schedule_erasure setup codec route (program env setup.source.crypto codec serverKid bounds mode adversary)


/-- Every actual supported adaptive execution retains the operational invariant; it is not postulated for future calls. -/
theorem schedule_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (good : Good setup.source state)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler (realPolicy setup codec) setup codec route) client).run state)) :
    Good setup.source result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact ih inner.1 inner.2 (handler_good setup codec route query state good inner member) result continued

/-- In particular the invariant holds for every supported result of the frozen program, without an environment Frame hypothesis. -/
theorem run_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run (realPolicy setup codec) setup codec route env serverKid bounds mode adversary)) :
    Good setup.source result.2 :=
  schedule_good setup codec route (program env setup.source.crypto codec serverKid bounds mode adversary)
    initial (initial_good setup.source) result supported

/-- The analysis result exposes exactly the existing CE ledger and produced-frame projection, without private coordinates or seeds. -/
def observed {E X : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n) :=
  result.1.map fun value => (value.2.1.1, value.2.1.2, result.2.produced)

def rawCounters (state : State n) : PqxdhRecordLiftWorld.RawCounters :=
  ⟨(state.server.map Server.rawAttempts).getD 0, state.ownerRaw⟩

/-- The integrity analysis projection adds only the exact source raw-attempt ghosts to the permitted ledger/produced projection. -/
def analysis {E X : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n) :=
  result.1.map fun value => (value.2.1.1, value.2.1.2, result.2.produced, rawCounters result.2)

theorem observed_erasure {E X : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n) :
    observed result = PqxdhRecordLiftWorld.observed (Prod.map id world result) := rfl

theorem rawCounters_erasure (state : State n) : rawCounters state = PqxdhRecordLiftWorld.rawCounters (world state) := by
  cases existing : state.server <;> simp only [rawCounters, PqxdhRecordLiftWorld.rawCounters,
    world, project, erase, existing, Option.map_none, Option.map_some, Server.erase]

theorem analysis_erasure {E X : Type} (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
    (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n) :
    analysis result = PqxdhRecordLiftWorld.analysis (Prod.map id world result) := by
  simp only [analysis, PqxdhRecordLiftWorld.analysis, Prod.map, id_eq, rawCounters_erasure]
  rfl

/-- The permitted CE-shaped analysis output agrees with the original World game in either mode. Event admissibility and all cryptographic inequalities remain separate. -/
theorem observed_run_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    observed <$> run (realPolicy setup codec) setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.game setup codec route env serverKid bounds mode adversary := by
  rw [PqxdhRecordLiftWorld.game, ← run_erasure setup codec route env serverKid bounds mode adversary, Functor.map_map]
  congr 1

/-- The same complete-run equation retains raw-attempt counters for the eventual integrity event. -/
theorem analysis_run_erasure {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    analysis <$> run (realPolicy setup codec) setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.analysis <$> PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary := by
  rw [← run_erasure setup codec route env serverKid bounds mode adversary, Functor.map_map]
  congr 1
  funext result
  exact analysis_erasure result

end BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.origin_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.origin_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.peer_origin_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.peer_origin_exists

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.owner_origin_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.owner_origin_exists

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_peer_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_peer_exists

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_owner_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_owner_exists

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.seedExtension_exists' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.seedExtension_exists

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.seedExtension_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.seedExtension_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.chain_seed_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.chain_seed_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.chain_extension_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.chain_extension_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.known_peer_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.known_peer_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.known_server_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.known_server_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.known_server_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.known_server_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.sampled_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.sampled_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.chargeEffect_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.chargeEffect_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.hidden_interpretation_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.hidden_interpretation_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.stored_interpretation_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.stored_interpretation_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.primitives_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.primitives_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.nativeKdf_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.nativeKdf_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.callback_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.callback_world

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labelProgram_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labelProgram_total

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_hidden_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_hidden_facts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.cachedSeeds_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.cachedSeeds_extension

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.peer_interpretation_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.peer_interpretation_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_interpretation_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_interpretation_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.phase_interpretation_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.phase_interpretation_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_interpretation_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_interpretation_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.project_seedFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.project_seedFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.unused_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.unused_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelScoped_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelScoped_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_same_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_same_records

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelScoped_markUsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelScoped_markUsed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_server_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_server_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_owner_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_owner_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.scoped_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconReady_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconReady_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_owner_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_owner_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_world

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_markUsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_markUsed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.storedView_markUsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.storedView_markUsed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_world_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_world_records

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_finish_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_finish_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_server_replace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_server_replace

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_update_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_update_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_server_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_server_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_finish_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_finish_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_primitive

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_chargeEffect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_chargeEffect

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.sampled_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.sampled_world

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_world

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_scoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_scoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_world

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.output_extension_agrees' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.output_extension_agrees

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.consistent_extension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.consistent_extension

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.tableScoped_seedFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.tableScoped_seedFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.realValid_seedFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.realValid_seedFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_tableScoped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_tableScoped

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_schedule_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_schedule_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.labeledKernel_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.storedReady_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.storedReady_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.storedView_table_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.storedView_table_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.recordsSatisfy_server_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.recordsSatisfy_server_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.recordsSatisfy_owner_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.recordsSatisfy_owner_store

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ready_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ready_frame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ready_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ready_append

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_ready

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.resolve_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.markUsed_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installBeacon_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.installServer_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initialize_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.capability_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.effects_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelSend_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelSend_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelReceive_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelReceive_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelSend_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelSend_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelReceive_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelReceive_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerSend_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerSend_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerReceive_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerReceive_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerStep_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerStep_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerFacts_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerFacts_unchanged

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerSend_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerSend_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerReceive_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerReceive_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerStep_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerStep_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.mixedKdf_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.mixedKdf_world

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerRun_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerRun_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_produce' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_produce

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_table_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_table_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_table_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.erase_table_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_recordFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_recordFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerRun_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerRun_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_ownerRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_ownerRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconPublish_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconPublish_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_beacon_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_beacon_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconStep_selected_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconStep_selected_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_beacon_inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_beacon_inactive

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconStep_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconStep_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.source_server_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.source_server_send

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.source_server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.source_server_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_raw_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.server_raw_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverPublish_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverPublish_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_server_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_server_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_send_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_send_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_raw_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_raw_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_server_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.world_server_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.realLookup_writesOnly' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.realLookup_writesOnly

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelSend_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelSend_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelReceive_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.kernelReceive_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerStep_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerStep_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerRun_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.ownerRun_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.good_recordFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.good_recordFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.good_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.good_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconPublish_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconPublish_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverPublish_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverPublish_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconStep_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.beaconStep_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.serverStep_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.handler_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.handler_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.handler_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.handler_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.schedule_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.schedule_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_schedule_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.initial_schedule_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.run_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.run_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.schedule_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.run_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.observed_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.observed_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.rawCounters_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.rawCounters_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.analysis_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.analysis_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.observed_run_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.observed_run_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.analysis_run_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler.analysis_run_erasure

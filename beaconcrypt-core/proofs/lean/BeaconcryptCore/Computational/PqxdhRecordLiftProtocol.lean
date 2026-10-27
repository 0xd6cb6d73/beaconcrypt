-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldCompiler
import BeaconcryptCore.Computational.PqxdhRecordLiftOpaqueDrivers

/-! The global source client has dynamic labeled record control but no seed, chain-table or primitive-state argument. Private services interpret allocation, source callbacks and logging. Exact execution factoring is separate from any permitted security observation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftProtocol
open PqxdhRecordLiftInterface
open PqxdhRecordLiftWorldCompiler (StoredKernel Peer Server Phase Owner Label LabeledKernel)
variable {n : Nat}

/-- Internal source control; hidden records contain coordinates, never interpreted seed or table bytes. This is not an environment state or a security observation. -/
structure Control (n : Nat) where
  server : Option (Server n)
  owners : List (Phase n)
  ownerRaw : Nat → Nat
  used : Slot n → Role → Bool

/-- All concrete private material and native instrumentation remain on the service side. Pending is the literal native writer log for the current selected-owner operation. -/
structure Private (n : Nat) where
  primitive : PqxdhRecordLiftWorld.Primitive
  seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)
  chain : PqxdhRecordLiftChainTable.Table (Slot n)
  produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)
  pending : List PqxdhDeploymentNative.Frame

def control (state : PqxdhRecordLiftWorldCompiler.State n) : Control n :=
  ⟨state.server, state.owners, state.ownerRaw, state.used⟩

def privateState (state : PqxdhRecordLiftWorldCompiler.State n) : Private n :=
  ⟨state.primitive, state.seeds, state.chain, state.produced, []⟩

def join (state : Control n) (secret : Private n) : PqxdhRecordLiftWorldCompiler.State n :=
  ⟨state.server, state.owners, state.ownerRaw, secret.produced, secret.primitive,
    secret.seeds, state.used, secret.chain⟩

/-- The ordinary whole-state projection is lossless at request boundaries, where the private writer buffer is empty. -/
theorem join_split (state : PqxdhRecordLiftWorldCompiler.State n) :
    join (control state) (privateState state) = state := rfl

abbrev Opening (n : Nat) := PqxdhRecordLiftOpaqueDrivers.LabeledOpening (Slot n) RawCtxWholeOwner.OpenContext
abbrev Sealing (n : Nat) := PqxdhRecordLiftOpaqueDrivers.LabeledSeal (Slot n) RawCtxSourceSend.SealContext

/-- These are private compiler requests. No request returns hidden bytes, a hidden kernel, a primitive counter, a cache, or a log. Known operations return only the updated caller-known concrete kernel and the original optional reply. -/
inductive Service (n : Nat) where
  | allocate (slot : Slot n)
  | coin (coin : unifSpec.Domain)
  | hash (bytes : Pqxdh.Bytes)
  | charge (kind : EffectKind)
  | lookup (coordinate : Label n)
  | opening (pending : Opening n)
  | sealing (pending : Sealing n)
  | knownSend (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext)
  | knownReceive (kernel : ConcreteRatchetKernel) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
  | publish (tag : PqxdhDeploymentInterface.FrameTag)

abbrev ServiceSpec (n : Nat) : OracleSpec (Service n)
  | .allocate _ | .charge _ | .lookup _ | .publish _ => Unit
  | .coin coin => unifSpec.Range coin
  | .hash _ => CtxRomAuth.CtxDigest
  | .opening _ => core.option.Option RawCtxWholeOwner.Decrypted
  | .sealing _ => Option RawCtxSourceSend.Encrypted
  | .knownSend _ _ => ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted
  | .knownReceive _ _ _ => ConcreteRatchetKernel × core.option.Option RawCtxWholeOwner.Decrypted

abbrev LocalSpec (n : Nat) := PqxdhRecordLiftOpaqueDrivers.ServiceSpec (Slot n)
  RawCtxWholeOwner.OpenContext RawCtxWholeOwner.Decrypted RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted

def localLift : QueryImpl (LocalSpec n) (OracleComp (ServiceSpec n))
  | .inl coordinate => (ServiceSpec n).query (.lookup coordinate)
  | .inr (.inl pending) => (ServiceSpec n).query (.opening pending)
  | .inr (.inr pending) => (ServiceSpec n).query (.sealing pending)

/-- Allocation replies only with unit. Source initialization is deterministic over the role and slot. -/
noncomputable def resolve (role : Role) : KernelRef n → OracleComp (ServiceSpec n) (StoredKernel n)
  | .known kernel => pure (.known kernel)
  | .hidden slot => do
      let _ ← (ServiceSpec n).query (.allocate slot)
      pure (.hidden slot (PqxdhRecordLiftWorldCompiler.labeledKernel role slot))

/-- Hidden send recursion is the actual opaque source program, without an interpretation argument. -/
noncomputable def kernelSend (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext) :
    OracleComp (ServiceSpec n) (StoredKernel n × Option RawCtxSourceSend.Encrypted) :=
  match stored with
  | .known kernel => do
      let result ← (ServiceSpec n).query (.knownSend kernel context)
      pure (.known result.1, result.2)
  | .hidden slot kernel => do
      let result ← simulateQ localLift (PqxdhRecordLiftOpaqueDrivers.admittedSend kernel context)
      pure (.hidden slot result.1, result.2)

/-- Hidden receive keeps each opening material coordinate until the private service answers with the actual optional plaintext. -/
noncomputable def kernelReceive (stored : StoredKernel n) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) :
    OracleComp (ServiceSpec n) (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) :=
  match stored with
  | .known kernel => do
      let result ← (ServiceSpec n).query (.knownReceive kernel target context)
      pure (.known result.1, result.2)
  | .hidden slot kernel => do
      let result ← simulateQ localLift (PqxdhRecordLiftOpaqueDrivers.admittedReceive kernel target context)
      pure (.hidden slot result.1, result.2)

noncomputable def ownerSend (sender : Std.U64) (plaintext : Pqxdh.Bytes) (owner : Owner n) :
    OracleComp (ServiceSpec n) (Option RawCtxSourceSend.Encrypted × Owner n) :=
  if plaintext.isEmpty then pure (none, owner) else do
    let result ← kernelSend owner.kernel ⟨plaintext, owner.expectedSender, sender, owner.associatedData⟩
    pure (result.2, { owner with kernel := result.1 })

noncomputable def ownerReceive (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n) :
    OracleComp (ServiceSpec n) (core.option.Option RawCtxWholeOwner.Decrypted × Owner n) :=
  let rejected := pure (.None, { owner with rawAttempts := owner.rawAttempts + 1 })
  if raw.isEmpty then rejected else
    match decode raw with
    | none => rejected
    | some frame =>
        if RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame then do
          let result ← kernelReceive owner.kernel frame.sequence ⟨raw, frame, owner.associatedData⟩
          pure (result.2, { owner with kernel := result.1, rawAttempts := owner.rawAttempts + 1 })
        else rejected

noncomputable def ownerStep (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) :
    OracleComp (ServiceSpec n) (RawCtxMixedOwner.SourceSpec.Range query × Owner n) :=
  match query with
  | .inl plaintext => ownerSend sender plaintext owner
  | .inr raw => ownerReceive decode raw owner

/-- Publication carries only its caller tag. The service appends the actual attempted native frames, including a failed writer, and returns no log. -/
noncomputable def ownerRun (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) :
    OracleComp (ServiceSpec n) (RawCtxMixedOwner.SourceSpec.Range query × Owner n) := do
  let result ← ownerStep sender decode query owner
  let _ ← (ServiceSpec n).query (.publish tag)
  pure result

open Classical

abbrev Client (n : Nat) := StateT (Control n) (OracleComp (ServiceSpec n))

def initialControl : Control n := control PqxdhRecordLiftWorldCompiler.initial

def initialPrivate : Private n := privateState PqxdhRecordLiftWorldCompiler.initial

/-- Duplicate initialization cannot reset the source control. Existing constructor peers are imported as caller-known kernels. -/
def initializeServer (created : PqxdhLiveServerConstruction.Created Unit) : Client n Unit :=
  fun state => match state.server with
  | some _ => pure ((), state)
  | none => pure ((), { state with server := some (PqxdhRecordLiftWorldCompiler.Server.fromKnown
      ⟨created.server.server.metadata.sender,
        ⟨⟨created.server.server.identity, created.server.server.peers, ()⟩, 0⟩⟩) })

def Unused (state : Control n) (role : Role) : KernelRef n → Prop
  | .known _ => True
  | .hidden slot => state.used slot role = false

def markUsed (state : Control n) (role : Role) : KernelRef n → Control n
  | .known _ => state
  | .hidden slot => { state with used := Function.update state.used slot (Function.update (state.used slot) role true) }

def BeaconReady (state : Control n) (owner : Nat) : Prop :=
  state.owners[owner]? = some (.inactive .initSent)

/-- Admission is decided from source control before requesting hidden allocation. -/
noncomputable def installServer (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) : Client n Bool := fun state =>
  match state.server with
  | none => pure (false, state)
  | some server =>
      if server.peers keyId = none ∧ Unused state .server ref then do
        let stored ← resolve .server ref
        let next := markUsed state .server ref
        pure (true, { next with server := some { server with
          peers := Function.update server.peers keyId (some ⟨identity, stored⟩) } })
      else pure (false, state)

noncomputable def installBeacon (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) :
    Client n Bool := fun state =>
  if BeaconReady state owner ∧ Unused state .beacon ref then do
    let stored ← resolve .beacon ref
    let next := markUsed state .beacon ref
    pure (true, { next with owners := state.owners.set owner (.established shell stored) })
  else pure (false, state)

/-- The exact frozen capability dispatcher needs no private state to decide source absence, phase or one-use checks. -/
noncomputable def capability : QueryImpl (CapabilitySpec n) (Client n)
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
  | .hash bytes => StateT.lift ((ServiceSpec n).query (.hash bytes))

/-- Charge every actual EnvEffects request, including startup, public and secrecy-ledger routes, before answering it. -/
noncomputable def effects : QueryImpl (EnvEffects n) (Client n) := fun query =>
  let action : Client n ((EnvEffects n).Range query) := match query with
    | .inl coin => StateT.lift ((ServiceSpec n).query (.coin coin))
    | .inr request => capability request
  do
    let _ ← StateT.lift ((ServiceSpec n).query (.charge (effectKind query)))
    action

/-- Header routing precedes full decoding, and source rejection counters distinguish an absent Server from an existing Server with no selected peer. -/
noncomputable def serverStep (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) : Client n (RawCtxServerMixed.SourceSpec.Range query) := fun state =>
  match state.server with
  | none => match query with
      | .inl _ => pure (none, state)
      | .inr _ => pure (.None, state)
  | some server => match query with
      | .inl (plaintext, keyId) => match server.peers keyId with
          | none => pure (none, state)
          | some peer => do
              let result ← ownerRun (PqxdhDeploymentNative.serverTag query) server.sender decode (.inl plaintext)
                (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer)
              pure (result.1, { state with server := some { server with
                peers := Function.update server.peers keyId (some { peer with kernel := result.2.kernel })
                rawAttempts := result.2.rawAttempts } })
      | .inr raw =>
          let rejected := pure (.None, { state with server := some { server with rawAttempts := server.rawAttempts + 1 } })
          match route raw with
          | none => rejected
          | some keyId => match server.peers keyId with
              | none => rejected
              | some peer => do
                  let result ← ownerRun (PqxdhDeploymentNative.serverTag query) server.sender decode (.inr raw)
                    (PqxdhRecordLiftWorldCompiler.serverOwner server keyId peer)
                  pure (result.1, { state with server := some { server with
                    peers := Function.update server.peers keyId (some { peer with kernel := result.2.kernel })
                    rawAttempts := result.2.rawAttempts } })

/-- Existing inactive owners retain their independent raw counters; missing indices have no attempted receive. -/
noncomputable def beaconStep (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) : Client n (RawCtxMixedOwner.SourceSpec.Range query) := fun state =>
  match state.owners[owner]? with
  | none => pure (PqxdhDeploymentNative.absent query, state)
  | some (.inactive _) => match query with
      | .inl _ => pure (none, state)
      | .inr _ => pure (.None, { state with ownerRaw := Function.update state.ownerRaw owner (state.ownerRaw owner + 1) })
  | some (.established shell kernel) => do
      let result ← ownerRun (PqxdhDeploymentNative.beaconTag owner) shell.identityKeyId decode query
        (PqxdhRecordLiftWorldCompiler.beaconOwner shell kernel (state.ownerRaw owner))
      pure (result.1, { state with
        owners := state.owners.set owner (.established shell result.2.kernel)
        ownerRaw := Function.update state.ownerRaw owner result.2.rawAttempts })

/-- The whole dynamic protocol client takes no seed bytes, table contents or private primitive state as an argument. -/
noncomputable def handler (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (WorldSpec n) (Client n)
  | .inl created => initializeServer created
  | .inr (.inl query) => effects query
  | .inr (.inr (.inl (.inl query))) => serverStep decode route (.inl query)
  | .inr (.inr (.inl (.inr raw))) => serverStep decode route (.inr raw)
  | .inr (.inr (.inr (owner, .inl plaintext))) => beaconStep decode owner (.inl plaintext)
  | .inr (.inr (.inr (owner, .inr raw))) => beaconStep decode owner (.inr raw)

/-- Arbitrary adaptive WorldSpec continuations are compiled without a private-state parameter. The original E and ledger remain in Result when the frozen program is supplied. -/
noncomputable def schedule {Result : Type} (decode : RawCtxReceive.FrameDecoder)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (state : Control n) : OracleComp (ServiceSpec n) (Result × Control n) :=
  (simulateQ (handler decode route) client).run state

abbrev RecordState (n : Nat) := PqxdhRecordLiftChainCompiler.Execution (Slot n)
  (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame)

def recordState (secret : Private n) : RecordState n :=
  (secret.chain, (secret.primitive, secret.pending))

def putRecord (secret : Private n) (records : RecordState n) : Private n :=
  { secret with chain := records.1, primitive := records.2.1, pending := records.2.2 }

noncomputable def cachedSeeds (secret : Private n) : PqxdhRecordLiftChainTable.Seeds (Slot n) :=
  fun slot => (secret.seeds.1 slot).getD Classical.ofNonempty

/-- The interpreter uses the same counted sampler; structural state moves introduce no random query. -/
def sampled {Result : Type} (work : ProbComp Result) : StateT (Private n) ProbComp Result := fun secret => do
  let result ← (simulateQ PqxdhRecordLiftWorld.countCoin work).run secret.primitive.1.uniform
  pure (result.1, { secret with primitive :=
    ({ secret.primitive.1 with uniform := result.2 }, secret.primitive.2) })

def withRecord {Result : Type} (work : StateT (RecordState n) ProbComp Result) :
    StateT (Private n) ProbComp Result := fun secret => do
  let result ← work.run (recordState secret)
  pure (result.1, putRecord secret result.2)

def primitiveWork {Result : Type}
    (work : StateT (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame) ProbComp Result) :
    StateT (RecordState n) ProbComp Result := fun state => do
  let result ← work.run state.2
  pure (result.1, (state.1, result.2))

noncomputable def recordNative {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :=
  PqxdhRecordLiftLoggedAdapters.loggedNative (PqxdhRecordLiftWorld.primitives setup codec)

/-- Concrete byte interpretation is confined to the private services. Every lookup and primitive effect uses the original native instrumentation and writer log. -/
noncomputable def localInterpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n)) :
    QueryImpl (LocalSpec n) (StateT (RecordState n) ProbComp) :=
  PqxdhRecordLiftOpaqueDrivers.interpreter seeds (PqxdhRecordLiftLoggedAdapters.liftLookup (policy seeds))
    (PqxdhRecordLiftNativeAdapters.receiveOpen (PqxdhRecordLiftWorldCompiler.receiveNative (recordNative setup codec)))
    (PqxdhRecordLiftNativeAdapters.sendSeal (PqxdhRecordLiftWorldCompiler.sendNative (recordNative setup codec)))

/-- Publishing merely moves the literal writer buffer into the tagged analysis log. It neither fabricates a successful ciphertext nor changes any primitive bill. -/
def publish (tag : PqxdhDeploymentInterface.FrameTag) (secret : Private n) : Private n :=
  { secret with produced := secret.produced ++ secret.pending.map (fun frame => (tag, frame)), pending := [] }

/-- The executable private interpreter keeps all seeds, table outputs, random-oracle cache and counters out of replies to the protocol client. -/
noncomputable def interpreter {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp)
  | .allocate slot => fun secret => do
      let result ← (sampled ((PqxdhRecordLiftLazyTable.impl slot).run secret.seeds)).run secret
      pure ((), { result.2 with seeds := result.1.2 })
  | .coin coin => sampled (unifSpec.query coin : ProbComp _)
  | .hash bytes => fun secret => do
      let result ← (sampled ((CtxRomAuth.ctxRandomOracle ((), bytes)).run secret.primitive.2)).run secret
      pure (result.1.1, { result.2 with primitive := (result.2.primitive.1, result.1.2) })
  | .charge kind => fun secret => pure ((), { secret with primitive :=
      ({ secret.primitive.1 with effects := Function.update secret.primitive.1.effects kind (secret.primitive.1.effects kind + 1) }, secret.primitive.2) })
  | .lookup coordinate => fun secret =>
      (withRecord (localInterpreter policy setup codec (cachedSeeds secret) (.inl coordinate))).run secret
  | .opening pending => fun secret =>
      (withRecord (localInterpreter policy setup codec (cachedSeeds secret) (.inr (.inl pending)))).run secret
  | .sealing pending => fun secret =>
      (withRecord (localInterpreter policy setup codec (cachedSeeds secret) (.inr (.inr pending)))).run secret
  | .knownSend kernel context => withRecord (primitiveWork
      (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative (recordNative setup codec))
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))))
  | .knownReceive kernel target context => withRecord (primitiveWork
      (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative (recordNative setup codec))
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))))
  | .publish tag => fun secret => pure ((), publish tag secret)

/-- Full internal execution, distinct from later security observation. The client is compiled before the private interpreter receives any state. -/
noncomputable def execute {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : Control n) (secret : Private n) :=
  (simulateQ (interpreter policy setup codec) (schedule codec.frameRead route client state)).run secret

/-- One labeled private callback changes exactly the local source table/native/log state and leaves the seed and prior produced frame unchanged. -/
theorem local_query_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (LocalSpec n).Domain) (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (localLift query)).run (putRecord secret records) =
      Prod.map id (putRecord secret) <$>
        (localInterpreter policy setup codec (cachedSeeds secret) query).run records := by
  rcases query with coordinate | pending
  · simp only [localLift, simulateQ_spec_query, interpreter, withRecord, StateT.run,
      putRecord, recordState, bind_pure_comp]
    rfl
  · rcases pending with pending | pending
    all_goals simp only [localLift, simulateQ_spec_query, interpreter, withRecord, StateT.run,
      putRecord, recordState, bind_pure_comp]
    all_goals rfl

/-- Complete opaque programs factor through the exact local execution state, preserving the private seed and prior production frame. -/
theorem local_program_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (program : OracleComp (LocalSpec n) Result) (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (simulateQ localLift program)).run (putRecord secret records) =
      Prod.map id (putRecord secret) <$>
        (simulateQ (localInterpreter policy setup codec (cachedSeeds secret)) program).run records := by
  induction program using OracleComp.inductionOn generalizing records with
  | pure result => simp [putRecord]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, local_query_factor, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2

/-- Both caller-known and hidden sends retain their exact source result and complete native/table/log state. -/
theorem kernelSend_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (kernelSend stored context)).run (putRecord secret records) =
      Prod.map id (putRecord secret) <$>
        (PqxdhRecordLiftWorldCompiler.kernelSend (cachedSeeds secret)
          (PqxdhRecordLiftLoggedAdapters.liftLookup (policy (cachedSeeds secret)))
          (PqxdhRecordLiftWorldCompiler.sendNative (recordNative setup codec)) stored context).run records := by
  cases stored with
  | known kernel =>
      simp only [kernelSend, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure]
      simp only [interpreter, withRecord, primitiveWork, PqxdhRecordLiftWorldCompiler.kernelSend,
        StateT.run, putRecord, recordState, bind_pure_comp, Functor.map_map]
      rfl
  | hidden slot kernel =>
      simp only [kernelSend, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        local_program_factor, bind_map_left]
      simp only [localInterpreter, PqxdhRecordLiftOpaqueDrivers.admitted_send_interpretation]
      simp only [PqxdhRecordLiftWorldCompiler.kernelSend, StateT.run, bind_pure_comp, Functor.map_map]
      rfl

/-- Both caller-known and hidden receives retain their exact source result and complete native/table/log state. -/
theorem kernelReceive_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (kernelReceive stored target context)).run (putRecord secret records) =
      Prod.map id (putRecord secret) <$>
        (PqxdhRecordLiftWorldCompiler.kernelReceive (cachedSeeds secret)
          (PqxdhRecordLiftLoggedAdapters.liftLookup (policy (cachedSeeds secret)))
          (PqxdhRecordLiftWorldCompiler.receiveNative (recordNative setup codec)) stored target context).run records := by
  cases stored with
  | known kernel =>
      simp only [kernelReceive, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure]
      simp only [interpreter, withRecord, primitiveWork, PqxdhRecordLiftWorldCompiler.kernelReceive,
        StateT.run, putRecord, recordState, bind_pure_comp, Functor.map_map]
      rfl
  | hidden slot kernel =>
      simp only [kernelReceive, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
        local_program_factor, bind_map_left]
      simp only [localInterpreter, PqxdhRecordLiftOpaqueDrivers.admitted_receive_interpretation]
      simp only [PqxdhRecordLiftWorldCompiler.kernelReceive, StateT.run, bind_pure_comp, Functor.map_map]
      rfl

/-- The empty-input decision and complete selected-owner send factor without any reachability premise. -/
theorem ownerSend_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (sender : Std.U64) (plaintext : Pqxdh.Bytes) (owner : Owner n)
    (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (ownerSend sender plaintext owner)).run (putRecord secret records) =
      Prod.map id (putRecord secret) <$>
        (PqxdhRecordLiftWorldCompiler.ownerSend (cachedSeeds secret)
          (PqxdhRecordLiftLoggedAdapters.liftLookup (policy (cachedSeeds secret)))
          (recordNative setup codec) sender plaintext owner).run records := by
  by_cases empty : plaintext.isEmpty
  · simp [ownerSend, PqxdhRecordLiftWorldCompiler.ownerSend, empty, StateT.run]
    rfl
  · simp only [ownerSend, empty, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, kernelSend_factor, bind_map_left]
    simp only [PqxdhRecordLiftWorldCompiler.ownerSend, StateT.run, empty, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, Functor.map_map]
    rfl

/-- Full raw admission, rejection and optional opening replies retain the same independent attempt counter. -/
theorem ownerReceive_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n)
    (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (ownerReceive decode raw owner)).run (putRecord secret records) =
      Prod.map id (putRecord secret) <$>
        (PqxdhRecordLiftWorldCompiler.ownerReceive (cachedSeeds secret)
          (PqxdhRecordLiftLoggedAdapters.liftLookup (policy (cachedSeeds secret)))
          (recordNative setup codec) decode raw owner).run records := by
  by_cases empty : raw.isEmpty = true
  · simp [ownerReceive, PqxdhRecordLiftWorldCompiler.ownerReceive, empty, StateT.run]
    rfl
  · cases decoded : decode raw with
    | none =>
        simp [ownerReceive, PqxdhRecordLiftWorldCompiler.ownerReceive, empty, decoded, StateT.run]
        rfl
    | some frame =>
        by_cases admitted : RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame
        · simp only [ownerReceive, empty, Bool.false_eq_true, ↓reduceIte, decoded, admitted,
            simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
            kernelReceive_factor, bind_map_left]
          simp only [PqxdhRecordLiftWorldCompiler.ownerReceive, StateT.run, empty, Bool.false_eq_true,
            ↓reduceIte, decoded, admitted, bind_pure_comp, Functor.map_map]
          rfl
        · simp [ownerReceive, PqxdhRecordLiftWorldCompiler.ownerReceive, empty, decoded, admitted, StateT.run]
          rfl

/-- Complete selected-owner source execution factors with arbitrary local writer-log contents. -/
theorem ownerStep_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (ownerStep sender decode query owner)).run (putRecord secret records) =
      Prod.map id (putRecord secret) <$>
        (PqxdhRecordLiftWorldCompiler.ownerStep (cachedSeeds secret)
          (PqxdhRecordLiftLoggedAdapters.liftLookup (policy (cachedSeeds secret)))
          (recordNative setup codec) sender decode query owner).run records := by
  cases query with
  | inl plaintext => exact ownerSend_factor policy setup codec sender plaintext owner secret records
  | inr raw => exact ownerReceive_factor policy setup codec decode raw owner secret records

/-- Publishing the exact local writer log preserves the complete optional reply and clears the private buffer. -/
theorem ownerRun_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (secret : Private n) (records : RecordState n) :
    (simulateQ (interpreter policy setup codec) (ownerRun tag sender decode query owner)).run (putRecord secret records) =
      (fun result => (result.1, publish tag (putRecord secret result.2))) <$>
        (PqxdhRecordLiftWorldCompiler.ownerStep (cachedSeeds secret)
          (PqxdhRecordLiftLoggedAdapters.liftLookup (policy (cachedSeeds secret)))
          (recordNative setup codec) sender decode query owner).run records := by
  simp only [ownerRun, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, ownerStep_factor, bind_map_left]
  simp only [interpreter, StateT.run, map_pure, bind_pure_comp]
  rfl

/-- At a real request boundary the writer buffer starts empty; publication returns the same complete selected-owner execution and clears it again. -/
theorem ownerRun_world {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n)
    (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) (ownerRun tag sender codec.frameRead query owner)).run (privateState state) =
      (fun result => (result.1, publish tag (putRecord (privateState state) result.2))) <$>
        PqxdhRecordLiftWorldCompiler.ownerRun policy setup codec sender query owner state :=
  ownerRun_factor policy setup codec tag sender codec.frameRead query owner
    (privateState state) (state.chain, (state.primitive, []))

def splitResult {Result : Type} (result : Result × PqxdhRecordLiftWorldCompiler.State n) :
    (Result × Control n) × Private n :=
  ((result.1, control result.2), privateState result.2)

/-- The complete dynamic Beacon handler factors through private callbacks; its exact result proves the pending buffer empty again. -/
theorem beaconStep_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((beaconStep codec.frameRead owner query).run (control state))).run
      (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.beaconStep policy setup codec owner query).run state := by
  cases found : state.owners[owner]? with
  | none =>
      cases query <;> simp only [beaconStep, PqxdhRecordLiftWorldCompiler.beaconStep,
        StateT.run, control, found, simulateQ_pure, map_pure]
      all_goals rfl
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;> simp only [beaconStep, PqxdhRecordLiftWorldCompiler.beaconStep,
            StateT.run, control, found, simulateQ_pure, map_pure]
          all_goals rfl
      | established shell kernel =>
          simp only [beaconStep, StateT.run, control, found]
          change (simulateQ (interpreter policy setup codec) _).run (privateState state) = _
          simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, ownerRun_world, bind_map_left]
          simp only [PqxdhRecordLiftWorldCompiler.beaconStep, found, bind_pure_comp, Functor.map_map]
          rfl

/-- The dynamic Server map, exact header-first routing and per-attempt counter factor through the same private record services. -/
theorem serverStep_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((serverStep codec.frameRead route query).run (control state))).run
      (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.serverStep policy setup codec route query).run state := by
  cases existing : state.server with
  | none =>
      cases query <;> simp only [serverStep, PqxdhRecordLiftWorldCompiler.serverStep, splitResult,
        StateT.run, control, existing, simulateQ_pure, map_pure]
      all_goals rfl
  | some server =>
      cases query with
      | inl request =>
          rcases request with ⟨plaintext, keyId⟩
          cases selected : server.peers keyId with
          | none =>
              simp only [serverStep, PqxdhRecordLiftWorldCompiler.serverStep, splitResult,
                StateT.run, control, existing, selected, simulateQ_pure, map_pure]
              rfl
          | some peer =>
              simp only [serverStep, StateT.run, control, existing, selected]
              change (simulateQ (interpreter policy setup codec) _).run (privateState state) = _
              simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, ownerRun_world, bind_map_left]
              simp only [PqxdhRecordLiftWorldCompiler.serverStep, existing, selected, bind_pure_comp, Functor.map_map]
              rfl
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, PqxdhRecordLiftWorldCompiler.serverStep, splitResult,
                StateT.run, control, existing, routed, simulateQ_pure, map_pure]
              rfl
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, PqxdhRecordLiftWorldCompiler.serverStep, splitResult,
                    StateT.run, control, existing, routed, selected, simulateQ_pure, map_pure]
                  rfl
              | some peer =>
                  simp only [serverStep, StateT.run, control, existing, routed, selected]
                  change (simulateQ (interpreter policy setup codec) _).run (privateState state) = _
                  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, ownerRun_world, bind_map_left]
                  simp only [PqxdhRecordLiftWorldCompiler.serverStep, existing, routed, selected, bind_pure_comp, Functor.map_map]
                  rfl

/-- Allocation exposes no seed to control, while full interpreted resolution retains the actual persistent seed cache and counted sampling. -/
theorem resolve_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (role : Role) (ref : KernelRef n) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((fun stored => (stored, control state)) <$> resolve role ref)).run
      (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.resolve role ref).run state := by
  cases ref with
  | known kernel =>
      simp only [resolve, map_pure, simulateQ_pure, StateT.run_pure,
        PqxdhRecordLiftWorldCompiler.resolve]
      rfl
  | hidden slot =>
      simp only [resolve, simulateQ_map, StateT.run_map, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure]
      simp only [interpreter, sampled, PqxdhRecordLiftWorldCompiler.resolve,
        PqxdhRecordLiftWorldCompiler.sampled, StateT.run, privateState, bind_pure_comp, Functor.map_map]
      rfl

/-- Vacant-peer and per-role checks precede the identical persistent allocation, preserving every nonselected record. -/
theorem installServer_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((installServer keyId identity ref).run (control state))).run
      (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.installServer keyId identity ref).run state := by
  cases existing : state.server with
  | none =>
      simp only [installServer, PqxdhRecordLiftWorldCompiler.installServer, StateT.run,
        splitResult, control, existing, simulateQ_pure, map_pure]
      rfl
  | some server =>
      have current : (control state).server = some server := existing
      have unused : Unused (control state) .server ref = PqxdhRecordLiftWorldCompiler.Unused state .server ref := rfl
      by_cases allowed : server.peers keyId = none ∧ PqxdhRecordLiftWorldCompiler.Unused state .server ref
      · simp only [installServer, StateT.run, current, unused, allowed, and_self, ↓reduceIte]
        change (simulateQ (interpreter policy setup codec) _).run (privateState state) = _
        simp only [PqxdhRecordLiftWorldCompiler.installServer, existing, allowed, and_self, ↓reduceIte]
        cases ref with
        | known kernel =>
            simp only [resolve, PqxdhRecordLiftWorldCompiler.resolve, pure_bind, simulateQ_pure, StateT.run]
            rfl
        | hidden slot =>
            simp only [resolve, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
              StateT.run_bind, StateT.run_pure]
            simp only [interpreter, sampled, PqxdhRecordLiftWorldCompiler.resolve,
              PqxdhRecordLiftWorldCompiler.sampled, StateT.run, privateState, bind_pure_comp, Functor.map_map]
            rfl
      · simp only [installServer, PqxdhRecordLiftWorldCompiler.installServer, StateT.run, current, existing,
          unused, allowed, ↓reduceIte, simulateQ_pure, map_pure]
        rfl

/-- Legal-phase and per-role Beacon installation retains its exact shell and previous raw-attempt count. -/
theorem installBeacon_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((installBeacon owner shell ref).run (control state))).run
      (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.installBeacon owner shell ref).run state := by
  have ready : BeaconReady (control state) owner = PqxdhRecordLiftWorldCompiler.BeaconReady state owner := rfl
  have unused : Unused (control state) .beacon ref = PqxdhRecordLiftWorldCompiler.Unused state .beacon ref := rfl
  by_cases allowed : PqxdhRecordLiftWorldCompiler.BeaconReady state owner ∧ PqxdhRecordLiftWorldCompiler.Unused state .beacon ref
  · simp only [installBeacon, PqxdhRecordLiftWorldCompiler.installBeacon, StateT.run, ready, unused,
      allowed, and_self, ↓reduceIte]
    change (simulateQ (interpreter policy setup codec) _).run (privateState state) = _
    cases ref with
    | known kernel =>
        simp only [resolve, PqxdhRecordLiftWorldCompiler.resolve, pure_bind, simulateQ_pure, StateT.run]
        rfl
    | hidden slot =>
        simp only [resolve, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
          StateT.run_bind, StateT.run_pure]
        simp only [interpreter, sampled, PqxdhRecordLiftWorldCompiler.resolve,
          PqxdhRecordLiftWorldCompiler.sampled, StateT.run, privateState, bind_pure_comp, Functor.map_map]
        rfl
  · simp only [installBeacon, PqxdhRecordLiftWorldCompiler.installBeacon, StateT.run, ready, unused,
      allowed, ↓reduceIte, simulateQ_pure, map_pure]
    rfl

/-- The same private constructor handoff initializes the source control and cannot reset an existing Server. -/
theorem initialize_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((initializeServer created).run (control state))).run (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.initializeServer created).run state := by
  cases existing : state.server <;>
    simp only [initializeServer, PqxdhRecordLiftWorldCompiler.initializeServer, StateT.run,
      splitResult, control, existing, simulateQ_pure, map_pure]
  all_goals rfl

/-- Every restricted capability, including the shared hash and refused administrative request, has the identical source effect. -/
theorem capability_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (CapabilitySpec n).Domain) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((capability query).run (control state))).run (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.capability query).run state := by
  cases query with
  | peerPresent keyId =>
      simp only [capability, PqxdhRecordLiftWorldCompiler.capability, StateT.run, control,
        simulateQ_pure, map_pure]
      rfl
  | ownerPresent owner =>
      simp only [capability, PqxdhRecordLiftWorldCompiler.capability, StateT.run, control,
        simulateQ_pure, map_pure]
      rfl
  | appendOwner sender identity phase =>
      simp only [capability, PqxdhRecordLiftWorldCompiler.capability, StateT.run, control,
        simulateQ_pure, map_pure]
      rfl
  | advanceOwner owner phase =>
      cases found : state.owners[owner]? with
      | none =>
          simp only [capability, PqxdhRecordLiftWorldCompiler.capability, StateT.run, control,
            found, simulateQ_pure, map_pure]
          rfl
      | some old =>
          cases old with
          | established shell kernel =>
              simp only [capability, PqxdhRecordLiftWorldCompiler.capability, StateT.run, control,
                found, simulateQ_pure, map_pure]
              rfl
          | inactive before =>
              by_cases legal : PqxdhRecordLiftWorld.LegalAdvance before phase
              all_goals simp only [capability, PqxdhRecordLiftWorldCompiler.capability, StateT.run,
                control, found, legal, ↓reduceIte, simulateQ_pure, map_pure]
              all_goals rfl
  | installServer keyId identity ref => exact installServer_factor policy setup codec keyId identity ref state
  | installBeacon owner shell ref => exact installBeacon_factor policy setup codec owner shell ref state
  | hash bytes =>
      change (simulateQ (interpreter policy setup codec)
        ((fun reply => (reply, control state)) <$> ((ServiceSpec n).query (.hash bytes) : OracleComp (ServiceSpec n) _))).run
          (privateState state) = _
      simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map]
      simp only [interpreter, sampled, PqxdhRecordLiftWorldCompiler.capability,
        PqxdhRecordLiftWorldCompiler.sampled, StateT.run, privateState, bind_pure_comp, Functor.map_map]
      rfl

/-- The private bookkeeping service applies exactly the source EnvEffects counter update, with no primitive query. -/
theorem charge_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (EnvEffects n).Domain) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (interpreter policy setup codec (.charge (effectKind query))).run (privateState state) =
      pure ((), privateState (PqxdhRecordLiftWorldCompiler.chargeEffect query state)) := rfl

/-- Every startup, environment, public and ledger effect follows the original counted source route. -/
theorem effects_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (EnvEffects n).Domain) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((effects query).run (control state))).run (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.effects query).run state := by
  cases query with
  | inl coin =>
      simp only [effects, StateT.run_lift, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rw [charge_factor policy setup codec (.inl coin) state]
      simp only [pure_bind]
      simp only [interpreter, sampled, PqxdhRecordLiftWorldCompiler.effects,
        PqxdhRecordLiftWorldCompiler.sampled, StateT.run, privateState, bind_pure_comp, Functor.map_map]
      rfl
  | inr query =>
      simp only [effects, simulateQ_bind, StateT.run_bind]
      exact capability_factor policy setup codec query (PqxdhRecordLiftWorldCompiler.chargeEffect (.inr query) state)

/-- Every actual WorldSpec operation factors exactly, returning the original result, split full state, and an empty private writer buffer. -/
theorem handler_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : PqxdhRecordLiftWorldCompiler.State n) :
    (simulateQ (interpreter policy setup codec) ((handler codec.frameRead route query).run (control state))).run
      (privateState state) =
      splitResult <$> (PqxdhRecordLiftWorldCompiler.handler policy setup codec route query).run state := by
  rcases query with created | query
  · exact initialize_factor policy setup codec created state
  · rcases query with effect | record
    · exact effects_factor policy setup codec effect state
    · rcases record with server | ⟨owner, beacon⟩
      · cases server with
        | inl request => exact serverStep_factor policy setup codec route (.inl request) state
        | inr raw => exact serverStep_factor policy setup codec route (.inr raw) state
      · cases beacon with
        | inl plaintext => exact beaconStep_factor policy setup codec owner (.inl plaintext) state
        | inr raw => exact beaconStep_factor policy setup codec owner (.inr raw) state

/-- The whole adaptive client is interpreted exactly by the private services. No reachability, lookup-realness or security premise is needed; an empty pending buffer is derived at every request boundary. -/
theorem schedule_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : PqxdhRecordLiftWorldCompiler.State n) :
    execute policy setup codec route client (control state) (privateState state) =
      splitResult <$> (simulateQ (PqxdhRecordLiftWorldCompiler.handler policy setup codec route) client).run state := by
  unfold execute schedule
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => simp [splitResult]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, handler_factor, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2

def rejoin {Result : Type} (result : (Result × Control n) × Private n) :
    Result × PqxdhRecordLiftWorldCompiler.State n :=
  (result.1.1, join result.1.2 result.2)

/-- Rejoining erases only the additional empty writer buffer and reconstructs every compiler field. -/
theorem rejoin_splitResult {Result : Type} (result : Result × PqxdhRecordLiftWorldCompiler.State n) :
    rejoin (splitResult result) = result := rfl

/-- Complete internal execution reconstructs the actual dynamic compiler state for every adaptive schedule and lookup policy. -/
theorem schedule_join {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : PqxdhRecordLiftWorldCompiler.State n) :
    rejoin <$> execute policy setup codec route client (control state) (privateState state) =
      (simulateQ (PqxdhRecordLiftWorldCompiler.handler policy setup codec route) client).run state := by
  rw [schedule_factor, Functor.map_map]
  change id <$> _ = _
  exact id_map _

/-- Empty pending logs are derived for complete schedules, including startup failure and every refusal path. -/
theorem schedule_pending_empty {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : PqxdhRecordLiftWorldCompiler.State n)
    (result : (Result × Control n) × Private n)
    (supported : result ∈ support (execute policy setup codec route client (control state) (privateState state))) :
    result.2.pending = [] := by
  rw [schedule_factor, support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  rfl

/-- The frozen environment/adversary/ledger program compiles to private services before any private material or lookup policy is supplied. Caller-known bytes and public decoder/crypto parameters remain ordinary source inputs. -/
noncomputable def program {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :=
  schedule codec.frameRead route
    (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary) initialControl

/-- Actual private interpretation of the complete frozen program. Full private results remain internal and are not an event domain. -/
noncomputable def run {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :=
  (simulateQ (interpreter policy setup codec)
    (program env setup.source.crypto codec route serverKid bounds mode adversary)).run initialPrivate

/-- Both modes retain the original client result, E, world-owned ledger and every compiler/private field. -/
theorem run_factor {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    run policy setup codec route env serverKid bounds mode adversary =
      splitResult <$> PqxdhRecordLiftWorldCompiler.run policy setup codec route env serverKid bounds mode adversary :=
  schedule_factor policy setup codec route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    PqxdhRecordLiftWorldCompiler.initial

/-- Starting from actual empty state, the all-real private interpretation is the complete original World source execution. No reachable-prefix or secrecy premise is postulated. -/
theorem initial_schedule_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) :
    (Prod.map id PqxdhRecordLiftWorldCompiler.world ∘ rejoin) <$>
      execute (PqxdhRecordLiftWorldCompiler.realPolicy setup codec) setup codec route client initialControl initialPrivate =
      (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) client).run PqxdhRecordLiftWorld.initial := by
  have fact := congrArg (fun work : ProbComp (Result × PqxdhRecordLiftWorldCompiler.State n) =>
      Prod.map id PqxdhRecordLiftWorldCompiler.world <$> work)
    (schedule_join (PqxdhRecordLiftWorldCompiler.realPolicy setup codec) setup codec route client
      PqxdhRecordLiftWorldCompiler.initial)
  simpa only [Functor.map_map, Function.comp_def, initialControl, initialPrivate] using fact.trans
    (PqxdhRecordLiftWorldCompiler.initial_schedule_erasure setup codec route client)

/-- The complete original frozen World run is recovered while retaining arbitrary environment E and the exact private test/fresh ledger. -/
theorem run_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    (Prod.map id PqxdhRecordLiftWorldCompiler.world ∘ rejoin) <$>
      run (PqxdhRecordLiftWorldCompiler.realPolicy setup codec) setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary :=
  initial_schedule_source setup codec route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)

abbrev RunResult (n : Nat) (E X : Type) :=
  (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E) ×
    Control n) × Private n

/-- This record-analysis view reads only the actual result, world-owned ledger and produced frames. It reads no seed, label, primitive counter, table or environment state. -/
def observed {E X : Type} (result : RunResult n E X) :=
  result.1.1.map fun value => (value.2.1.1, value.2.1.2, result.2.produced)

def rawCounters (state : Control n) : PqxdhRecordLiftWorld.RawCounters :=
  ⟨(state.server.map Server.rawAttempts).getD 0, state.ownerRaw⟩

/-- Integrity additionally retains only the exact raw-attempt counters. Later E-only continuations use the unprojected program result before this analysis view. -/
def analysis {E X : Type} (result : RunResult n E X) :=
  result.1.1.map fun value => (value.2.1.1, value.2.1.2, result.2.produced, rawCounters result.1.2)

/-- The record-analysis projection agrees definitionally with the reviewed compiler view. -/
theorem observed_splitResult {E X : Type}
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftWorldCompiler.State n) :
    observed (splitResult result) = PqxdhRecordLiftWorldCompiler.observed result := rfl

/-- Raw-attempt ghosts agree as well; actual primitive work remains interpreter-private. -/
theorem analysis_splitResult {E X : Type}
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftWorldCompiler.State n) :
    analysis (splitResult result) = PqxdhRecordLiftWorldCompiler.analysis result := rfl

/-- The same CE-shaped record observation is obtained from the actual World run in either mode. This functional equality is not a cryptographic event bound. -/
theorem observed_run_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    observed <$> run (PqxdhRecordLiftWorldCompiler.realPolicy setup codec) setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.game setup codec route env serverKid bounds mode adversary := by
  rw [run_factor, Functor.map_map]
  exact PqxdhRecordLiftWorldCompiler.observed_run_erasure setup codec route env serverKid bounds mode adversary

/-- The exact raw-attempt analysis view is retained for the later integrity event; event admissibility remains separate. -/
theorem analysis_run_source {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    analysis <$> run (PqxdhRecordLiftWorldCompiler.realPolicy setup codec) setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.analysis <$> PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary := by
  rw [run_factor, Functor.map_map]
  exact PqxdhRecordLiftWorldCompiler.analysis_run_erasure setup codec route env serverKid bounds mode adversary

end BeaconcryptCore.Computational.PqxdhRecordLiftProtocol

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.join_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.join_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.local_query_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.local_query_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.local_program_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.local_program_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.kernelSend_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.kernelSend_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.kernelReceive_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.kernelReceive_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerSend_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerSend_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerReceive_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerReceive_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerStep_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerStep_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerRun_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerRun_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerRun_world' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.ownerRun_world

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.beaconStep_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.beaconStep_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.serverStep_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.serverStep_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.resolve_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.resolve_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.installServer_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.installServer_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.installBeacon_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.installBeacon_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.initialize_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.initialize_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.capability_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.capability_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.charge_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.charge_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.effects_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.effects_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.handler_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.handler_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.schedule_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.schedule_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.rejoin_splitResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.rejoin_splitResult

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.schedule_join' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.schedule_join

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.schedule_pending_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.schedule_pending_empty

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.run_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.run_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.initial_schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.initial_schedule_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.run_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.observed_splitResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.observed_splitResult

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.analysis_splitResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.analysis_splitResult

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.observed_run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.observed_run_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.analysis_run_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocol.analysis_run_source

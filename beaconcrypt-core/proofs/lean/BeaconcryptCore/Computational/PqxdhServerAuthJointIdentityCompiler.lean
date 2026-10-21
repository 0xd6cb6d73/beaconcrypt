import BeaconcryptCore.Computational.PqxdhServerAuthObservedExecution

/-! Route the actual R1 Beacon identity operations through the existing joint signing/DH interface. The executable compiler receives no target identity seed. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes PublicChallenge sourceScalarDh)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhRootTableInitialization (rootArray)
open PqxdhPhase2GapDhSource (peer)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Local randomness remains on its original uniform channel. -/
def coins {Result : Type} (work : ProbComp Result) : OracleComp AdversarySpec Result :=
  simulateQ (fun query => AdversarySpec.query (.inl query)) work

/-- Mathematical challenger projection. Only this interpreter receives the target seed. -/
def plain (primitives : Primitives) (seed : IdentitySeed) : QueryImpl AdversarySpec ProbComp
  | .inl query => unifSpec.query query
  | .inr query => pure (primitiveReply primitives seed query)

/-- Retaining the complete joint history changes no reply or source computation. -/
theorem plain_run {Result : Type} (primitives : Primitives) (seed : IdentitySeed)
    (work : OracleComp AdversarySpec Result) (history : History) :
    Prod.fst <$> (simulateQ (jointImpl primitives seed) work).run history = simulateQ (plain primitives seed) work := by
  induction work using OracleComp.inductionOn generalizing history with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, map_bind]
      cases query <;> simp [plain, ih]
      all_goals simp [StateT.run, jointImpl]

/-- All local sampling is preserved at its original position. -/
theorem coins_plain {Result : Type} (primitives : Primitives) (seed : IdentitySeed)
    (work : ProbComp Result) : simulateQ (plain primitives seed) (coins work) = work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp [coins, simulateQ_bind, plain] at *
      exact bind_congr ih

/-- The target public identity replaces the unavailable seed in the original Phase1 projection. -/
def publicProjection (setup : Setup baseSpec KemSK) (publicValue : PublicChallenge)
    (target : PublicIdentity) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) :
    PqxdhLivePhase1Bundle.Public Unit (Unit ⊕ ScalarBytes) KemSK where
  index _ := 0
  identity _ := target.ed25519
  dh
    | .inl () => publicValue.prekey
    | .inr scalar => setup.dh.publicKey scalar
  kem _ := kemPk

/-- Actual Phase1 callbacks: local retained one-time material, three joint signatures, original optional writer. -/
def signingImpl (codec : Codec Reader Response) (oneTime : ScalarBytes) :
    QueryImpl (PqxdhLivePhase1Bundle.Spec (Unit ⊕ ScalarBytes)) (OracleComp AdversarySpec)
  | .inl () => pure (some (.inr oneTime))
  | .inr (.inl (.inl query)) => AdversarySpec.query (.inl query)
  | .inr (.inl (.inr .create)) => pure none
  | .inr (.inl (.inr (.service _ (.sign message)))) => some <$> AdversarySpec.query (.inr (.sign message))
  | .inr (.inl (.inr (.service _ (.staticDh _)))) => pure none
  | .inr (.inl (.inr (.reveal _))) => pure none
  | .inr (.inr bundle) => pure (codec.write1 bundle)

set_option backward.isDefEq.respectTransparency false in
/-- Every original callback has the same reply under the joint challenger, including refusal. -/
theorem signing_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (oneTime : ScalarBytes) :
    plain setup.joint seed ∘ₛ signingImpl codec oneTime = phase1Impl setup codec seed oneTime := by
  funext query
  rcases query with gen | ((coin | request) | bundle) <;> try rfl
  cases request <;> try rfl
  rename_i index service
  cases service <;> simp [QueryImpl.apply_compose, signingImpl, phase1Impl, simulateQ_map, simulateQ_pure, plain, primitiveReply]

/-- The original full bundle runs with the same private key handles and optional writer result. -/
def phase1 (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (target : PublicIdentity) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    OracleComp AdversarySpec (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) :=
  simulateQ (signingImpl codec oneTime)
    (PqxdhLivePhase1Bundle.bundle (publicProjection setup publicValue target kemPk) (freshBeacon setup publicValue kemSk))

/-- Exact complete Phase1 execution under the ordinary challenger, including writer failure and the retained native state. -/
theorem phase1_plain (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (publicValue : PublicChallenge) (oneTime : ScalarBytes)
    (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK) :
    simulateQ (plain setup.joint seed) (phase1 setup codec (setup.joint.publicKeys seed) publicValue oneTime kemPk kemSk) =
      phase1Run setup codec seed publicValue oneTime kemPk kemSk := by
  rw [phase1, ← QueryImpl.simulateQ_compose, signing_query]
  rfl

/-- Every nonidentity operation remains real and local; the sole identity-secret DH callback is forwarded to the joint challenger. -/
noncomputable def auxiliary (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response)
      (OracleComp AdversarySpec)
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind toWord32)
  | .privateConversion () => pure (some ())
  | .decapsulate ciphertext secret => coins (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (Option.map rootArray <$> setup.kem.decaps secret (PqxdhPhase2InputBytes.ciphertext ciphertext)))
  | .dhPair (.inl ()) _ => pure none
  | .dhPair (.inr scalar) point => pure ((sourceScalarDh setup.source.crypto scalar (peer point)).map rootArray)
  | .dhIdentity () point => Option.map rootArray <$> AdversarySpec.query (.inr (.staticDh (peer point)))
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

set_option backward.isDefEq.respectTransparency false in
/-- Exact auxiliary callback equality includes malformed inputs, rejected DH and the actual local KEM program. -/
theorem auxiliary_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (seed : IdentitySeed) :
    plain setup.joint seed ∘ₛ auxiliary setup codec = beaconAux setup codec seed := by
  funext query
  cases query <;> simp only [QueryImpl.apply_compose, auxiliary, beaconAux, simulateQ_pure,
    simulateQ_map, simulateQ_spec_query, plain, primitiveReply, map_pure, coins_plain]
  rename_i pair point
  cases pair <;> rfl

/-- Original selected-prekey callbacks with only the target identity routed to its challenger. -/
noncomputable def prefixImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (scalar : ScalarBytes) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ (Unit ⊕ ScalarBytes)) KemSK Unit Response)
      (StateT Unit (OracleComp AdversarySpec)) :=
  PqxdhPhase2GapDhSource.nativeImpl setup.dh scalar (fun query => StateT.lift (auxiliary setup codec query))
    (fun _ => pure ())

set_option backward.isDefEq.respectTransparency false in
/-- The full callback state and original native preparation are preserved by interpreting the same joint service. -/
theorem prefix_query (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (seed : IdentitySeed) :
    (plain setup.joint seed).mapStateTBase (prefixImpl setup codec scalar) =
      PqxdhPhase2GapDhSource.nativeImpl setup.dh scalar (beaconAuxUnit setup codec seed) (fun _ => pure ()) := by
  have aux := fun query => congrFun (auxiliary_query setup codec seed) query
  simp only [QueryImpl.apply_compose] at aux
  funext query state
  cases query <;> simp only [prefixImpl, PqxdhPhase2GapDhSource.nativeImpl, QueryImpl.mapStateTBase,
    StateT.run_lift, simulateQ_bind, simulateQ_pure, beaconAuxUnit]
  all_goals try simp only [aux, StateT.mk, StateT.lift]
  rename_i pair point
  cases pair <;> simp [StateT.run, StateT.lift, aux]
  rfl

/-- Literal native preparation, with local prekey/one-time/KEM secrets and only the target identity secret unavailable. -/
noncomputable def prepare (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    OracleComp AdversarySpec (Option (PqxdhBeaconPhase2Preparation.Prepared Response)) :=
  (simulateQ (prefixImpl setup codec scalar)
    (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)).run' ()

/-- Complete original preparation, including all early rejection and prior local effects, equals the routed program. -/
theorem prepare_plain (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (seed : IdentitySeed) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    simulateQ (plain setup.joint seed) (prepare setup codec scalar control identity oneTime kem raw) =
      (PqxdhServerAuthNative.nativeBeaconPrefix setup codec scalar seed control identity oneTime kem raw).run' () := by
  simp only [prepare, StateT.run'_eq, simulateQ_map, QueryImpl.simulateQ_mapStateTBase_run, prefix_query,
    PqxdhServerAuthNative.nativeBeaconPrefix]

/-- The target identity seed is absent from the compiler state; all original native protocol and cache fields remain. -/
abbrev Game (KemSK : Type) := StateT (PqxdhServerAuthNative.NativeState KemSK) (OracleComp AdversarySpec)

/-- Actual complete native tail after routed preparation; the Server seed is local and the target Beacon seed is never an argument. -/
noncomputable def stage (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    Game KemSK (Option PqxdhBeaconPhase2Publication.Staged) := fun state => do
  let prepared ← prepare setup codec scalar control identity oneTime kem raw
  match prepared with
  | none => pure (none, state)
  | some original => coins ((PqxdhServerAuthNative.nativeBeaconTail setup codec
      (PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed scalar) original).run state)

set_option backward.isDefEq.respectTransparency false in
/-- Preparation and the full native record continuation preserve the same optional result, Extract/CTX caches and protocol state. -/
theorem stage_plain (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed beaconSeed : IdentitySeed) (scalar : ScalarBytes) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    simulateQ (plain setup.joint beaconSeed) ((stage setup codec serverSeed scalar control identity oneTime kem raw).run state) =
      (PqxdhServerAuthNative.nativeBeaconStage setup codec serverSeed scalar beaconSeed control identity oneTime kem raw).run state := by
  simp only [stage, StateT.run, simulateQ_bind, prepare_plain, PqxdhServerAuthNative.nativeBeaconStage,
    PqxdhServerAuthNative.nativeCoins_bind]
  apply bind_congr
  rintro (_ | original) <;> simp only [simulateQ_pure, coins_plain]
  rfl

/-- The original one-shot finish keeps the whole tail and final native publication/abort. -/
noncomputable def finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes) : Game KemSK (Option Pqxdh.Bytes) := fun state =>
  match state.2.beacon.beacon.phase with
  | .initSent control _ oneTime kem => do
      let staged ← (stage setup codec serverSeed scalar control state.2.beacon.beacon.identity oneTime kem raw).run state
      let current := staged.2.2
      let result := PqxdhBeaconPhase2Publication.finish control current.beacon staged.1
      pure (result.1, staged.2.1, { current with beacon := result.2, ghost := current.ghost.accept (acceptedOf staged.1 result.1) })
  | _ => pure (none, state)

set_option backward.isDefEq.respectTransparency false in
/-- Every original finish branch has the same optional public reply and complete native poststate, not merely the same acceptance bit. -/
theorem finish_plain (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (serverSeed beaconSeed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    simulateQ (plain setup.joint beaconSeed) ((finish setup codec serverSeed scalar raw).run state) =
      (PqxdhServerAuthNative.nativeFinish setup codec serverSeed scalar beaconSeed raw).run state := by
  simp only [StateT.run, finish, PqxdhServerAuthNative.nativeFinish, PqxdhServerAuthNative.nativeGet_bind]
  cases phase : state.2.beacon.beacon.phase <;> simp only [simulateQ_pure]
  all_goals first | rfl | skip
  simp only [simulateQ_bind, simulateQ_pure, PqxdhServerAuthNative.native_bind_run]
  rename_i control prekey oneTime kem
  have actual := stage_plain setup codec serverSeed beaconSeed scalar control state.2.beacon.beacon.identity oneTime kem raw state
  simp only [StateT.run] at actual
  rw [actual]
  apply bind_congr
  intro result
  rfl

/-- The original API with the target-dependent finish routed above. Every other callback is independent of the Beacon seed, as checked by `handler_plain`, and retains its entire native computation. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar : ScalarBytes) : QueryImpl ServerAuthSpec (Game KemSK)
  | .inr (.finish raw) => finish setup codec serverSeed scalar raw
  | query => fun state => coins ((PqxdhServerAuthNative.nativeHandler setup codec checks serverSeed scalar serverSeed query).run state)

set_option backward.isDefEq.respectTransparency false in
/-- Every API callback has the original reply and complete state under the joint challenger; the locally available Server seed is never used as a substitute for target-dependent work. -/
theorem handler_plain (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed beaconSeed : IdentitySeed) (scalar : ScalarBytes) :
    (plain setup.joint beaconSeed).mapStateTBase (handler setup codec checks serverSeed scalar) =
      PqxdhServerAuthNative.nativeHandler setup codec checks serverSeed scalar beaconSeed := by
  funext query state
  rcases query with coin | (raw | build | raw | hmac | bytes | key)
  all_goals simp only [QueryImpl.mapStateTBase, StateT.mk, handler, StateT.run, coins_plain]
  all_goals first | rfl | skip
  exact finish_plain setup codec serverSeed beaconSeed scalar raw state

/-- The entire adaptive public program is the original source execution with its complete private state. -/
theorem program_plain {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed beaconSeed : IdentitySeed) (scalar : ScalarBytes) (work : OracleComp ServerAuthSpec Result)
    (state : PqxdhServerAuthNative.NativeState KemSK) :
    simulateQ (plain setup.joint beaconSeed) ((simulateQ (handler setup codec checks serverSeed scalar) work).run state) =
      (simulateQ (PqxdhServerAuthNative.nativeHandler setup codec checks serverSeed scalar beaconSeed) work).run state := by
  rw [QueryImpl.simulateQ_mapStateTBase_run, handler_plain]

/-- Complete Phase1 publication followed by the original public program. Both original source outputs and private protocol state remain available to the proof consumer. -/
noncomputable def execution {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (scalar oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (work : AuthInput → OracleComp ServerAuthSpec Result) (target : PublicIdentity) := do
  let publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed scalar
  let published ← phase1 setup codec target publicValue oneTime keys.1 keys.2
  let result ← (simulateQ (handler setup codec checks serverSeed scalar)
    (work ⟨publicValue.identity, setup.serverKeyId, published.1, none⟩)).run
      (PqxdhJointDhExtractFamily.empty, initialGameState setup publicValue published.2)
  pure (published, result)

/-- One actual joint execution reproduces the complete original Phase1 and adaptive native continuation; no source field or occurrence premise is assumed. -/
theorem execution_plain {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed beaconSeed : IdentitySeed) (scalar oneTime : ScalarBytes)
    (keys : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (work : AuthInput → OracleComp ServerAuthSpec Result) :
    simulateQ (plain setup.joint beaconSeed)
      (execution setup codec checks serverSeed scalar oneTime keys work (setup.joint.publicKeys beaconSeed)) = (do
        let publicValue := PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed scalar
        let published ← phase1Run setup codec beaconSeed publicValue oneTime keys.1 keys.2
        let result ← (simulateQ (PqxdhServerAuthNative.nativeHandler setup codec checks serverSeed scalar beaconSeed)
          (work ⟨publicValue.identity, setup.serverKeyId, published.1, none⟩)).run
            (PqxdhJointDhExtractFamily.empty, initialGameState setup publicValue published.2)
        pure (published, result)) := by
  simp only [execution, simulateQ_bind, phase1_plain, program_plain, simulateQ_pure]

/-- A concrete joint-interface client samples all nontarget private material locally and executes the actual observed R1 program. The target seed remains solely in the challenger. -/
noncomputable def client (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (observation : PqxdhServerAuthObservedGame.Observation)
    (target : PublicIdentity) : OracleComp AdversarySpec Bool := do
  let serverSeed ← coins sampleSeed
  let scalar ← coins PqxdhJointGapDh.sampleScalar
  let keys ← coins (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let oneTime ← coins PqxdhJointGapDh.sampleScalar
  let result ← execution setup codec checks serverSeed scalar oneTime keys
    (fun input => PqxdhServerAuthApiJournal.record (adversary input)) target
  pure (observation serverSeed scalar result.2.2.2.ghost result.2.1.2)

set_option backward.isDefEq.respectTransparency false in
/-- Every local sampler and full native/journal continuation of the joint client is the original source computation. -/
theorem client_plain (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (observation : PqxdhServerAuthObservedGame.Observation) (beaconSeed : IdentitySeed) :
    simulateQ (plain setup.joint beaconSeed) (client setup codec checks adversary observation (setup.joint.publicKeys beaconSeed)) = (do
      let serverSeed ← sampleSeed
      let scalar ← PqxdhJointGapDh.sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      let oneTime ← PqxdhJointGapDh.sampleScalar
      let published ← phase1Run setup codec beaconSeed
        (PqxdhJointGapDh.challenge setup.joint setup.dh serverSeed scalar) oneTime keys.1 keys.2
      PqxdhServerAuthObservedExecution.native setup codec checks adversary false observation
        ⟨serverSeed, scalar, beaconSeed, oneTime, keys, published⟩) := by
  simp only [client, simulateQ_bind, coins_plain, execution_plain, simulateQ_pure, bind_assoc, pure_bind]
  simp only [PqxdhServerAuthObservedExecution.native, PqxdhServerAuthEntryFactor.contextInput,
    PqxdhServerAuthEntryFactor.contextState, PqxdhServerAuthEntryFactor.Context.publicValue,
    Bool.false_eq_true, ite_false, bind_pure_comp]

/-- Sampling the target seed in the challenger before the local Server seed preserves every evaluated continuation, including all private state and interleaved replies. -/
theorem seed_order {Result : Type} [MeasurableSpace Result]
    (next : IdentitySeed → IdentitySeed → ProbComp Result) :
    𝒟[do let beaconSeed ← sampleSeed; let serverSeed ← sampleSeed; next serverSeed beaconSeed] =
      𝒟[do let serverSeed ← sampleSeed; let beaconSeed ← sampleSeed; next serverSeed beaconSeed] := by
  exact (OracleComp.EvalDistEq.bind_bind_swap _ _ _).evalDist_eq

/-- The ordinary joint challenger retains its real history while the final observer reads only the original source result. -/
noncomputable def observed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (observation : PqxdhServerAuthObservedGame.Observation) : ProbComp Bool := do
  let beaconSeed ← sampleSeed
  Prod.fst <$> PqxdhJointIdentity.run setup.joint beaconSeed (client setup codec checks adversary observation)

/-- The concrete seed-free joint client has exactly the complete production-order observed distribution, not a marginal key simulation. -/
theorem observed_ordered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (adversary : Adversary) (observation : PqxdhServerAuthObservedGame.Observation) :
    𝒟[observed setup codec checks adversary observation] =
      𝒟[PqxdhServerAuthObservedExecution.orderedGame setup codec checks adversary false observation] := by
  simp only [observed, PqxdhJointIdentity.run, plain_run, client_plain,
    PqxdhServerAuthObservedExecution.orderedGame]
  exact seed_order _

end BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.plain_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.plain_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.coins_plain' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.coins_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.signing_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.signing_query
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.phase1_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.phase1_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.auxiliary_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.auxiliary_query
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.prefix_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.prefix_query
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.prepare_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.prepare_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.stage_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.stage_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.finish_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.finish_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.handler_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.handler_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.program_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.program_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.execution_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.execution_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.client_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.client_plain
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.seed_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.seed_order
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.observed_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityCompiler.observed_ordered

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld

/-! Actual supported private-service prefixes and source-derived predecessor availability. The prefix relation retains the complete adaptive remainder and private state; it is an internal operational certificate, not an adversary observation. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftAvailability

/-- A literal supported prefix of a stateful interpreter, retaining its exact program remainder and state. -/
inductive Reaches {ι State Result : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT State ProbComp)) :
    OracleComp spec Result → State → OracleComp spec Result → State → Prop where
  | here (client : OracleComp spec Result) (before : State) :
      Reaches impl client before client before
  | later (query : spec.Domain) (next : spec.Range query → OracleComp spec Result)
      (before : State) (step : spec.Range query × State)
      (rest : OracleComp spec Result) (after : State)
      (actual : step ∈ support ((impl query).run before))
      (tail : Reaches impl (next step.1) step.2 rest after) :
      Reaches impl (spec.query query >>= next) before rest after

/-- Every reached query obeys its actual prestate predicate; continuations range over all supported original replies. -/
def Safe {ι State Result : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT State ProbComp)) (predicate : spec.Domain → State → Prop)
    (client : OracleComp spec Result) : State → Prop :=
  OracleComp.recOn client (fun _ _ => True)
    (fun request _ continued state => predicate request state ∧
      ∀ result ∈ support ((impl request).run state), continued result.1 result.2)

/-- The query-safety certificate follows every actual supported adaptive prefix. -/
theorem Safe.reaches {ι State Result : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)} {predicate : spec.Domain → State → Prop}
    {client rest : OracleComp spec Result} {before after : State}
    (safe : Safe impl predicate client before) (reached : Reaches impl client before rest after) :
    Safe impl predicate rest after := by
  induction reached with
  | here client before => exact safe
  | later query next before step rest after actual tail ih =>
      exact ih (safe.2 step actual)

/-- The certificate exposes the predicate at the exact prestate of any reached query. -/
theorem Safe.query_at {ι State Result : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)} {predicate : spec.Domain → State → Prop}
    {client : OracleComp spec Result} {before after : State}
    (safe : Safe impl predicate client before) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec Result)
    (reached : Reaches impl client before (spec.query query >>= next) after) :
    predicate query after := (safe.reaches reached).1

/-- Query safety composes with every continuation at its actual supported complete poststate. -/
theorem Safe.bind {ι State Result Next : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)} {predicate : spec.Domain → State → Prop}
    (client : OracleComp spec Result) (next : Result → OracleComp spec Next) (state : State)
    (safe : Safe impl predicate client state)
    (continued : ∀ result ∈ support ((simulateQ impl client).run state), Safe impl predicate (next result.1) result.2) :
    Safe impl predicate (client >>= next) state := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simpa only [pure_bind] using continued (value, state) (by simp)
  | query_bind query tail ih =>
      rw [bind_assoc]
      refine ⟨safe.1, fun first actual => ?_⟩
      apply ih first.1 first.2 (safe.2 first actual)
      intro last member
      apply continued last
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff]
      exact ⟨first, actual, member⟩

/-- Mapping only the caller result preserves every query-prefix certificate and complete interpreter state. -/
theorem Safe.map {ι State Result Next : Type} {spec : OracleSpec ι}
    {impl : QueryImpl spec (StateT State ProbComp)} {predicate : spec.Domain → State → Prop}
    (client : OracleComp spec Result) (f : Result → Next) (state : State)
    (safe : Safe impl predicate client state) : Safe impl predicate (f <$> client) state := by
  simpa only [bind_pure_comp] using
    safe.bind client (fun value => pure (f value)) state (fun _ _ => trivial)

open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable PqxdhRecordLiftChainCompiler

/-- Only lookup requires table closure and an available predecessor. The predicate reads the exact local table before that lookup executes. -/
def LocalAllowed {Slot OpenContext Plaintext SealContext Output PrimitiveState : Type}
    (query : (PqxdhRecordLiftOpaqueDrivers.ServiceSpec Slot OpenContext Plaintext SealContext Output).Domain)
    (state : Execution Slot PrimitiveState) : Prop :=
  match query with
  | .inl coordinate => Closed state.1 ∧ Available state.1 coordinate
  | .inr _ => True

/-- Every lookup emitted by complete actual receive recursion has its predecessor in the current table, including skipped derivations and retries. -/
theorem receive_safe {Slot OpenContext Plaintext SealContext Output PrimitiveState : Type}
    (seeds : Seeds Slot) (valid : Table Slot → Prop) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (preserves : LookupPreserves valid lookup) (effect : Effect Slot OpenContext)
    (state : Execution Slot PrimitiveState) (good : valid state.1)
    (closed : ∀ table, valid table → Closed table) (refs : References state.1 effect) :
    Safe (PqxdhRecordLiftOpaqueDrivers.interpreter seeds lookup opening sealing) LocalAllowed
      (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect) state := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state with
  | h depth ih =>
    cases effect with
    | rejected entry context =>
        rw [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        trivial
    | openRequested pending =>
        rw [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        exact ⟨trivial, fun _ _ => trivial⟩
    | kdfRequested pending =>
        rw [PqxdhRecordLiftOpaqueDrivers.receiveProgram]
        refine ⟨⟨closed state.1 good, refs.1.2⟩, fun reply supported => ?_⟩
        change reply ∈ support ((PqxdhRecordLiftOpaqueDrivers.interpreter seeds lookup opening sealing
          (.inl pending.request)).run state) at supported
        simp only [PqxdhRecordLiftOpaqueDrivers.interpreter, StateT.run_map, support_map] at supported
        obtain ⟨inner, member, rfl⟩ := supported
        have facts := preserves pending.request state good refs.1.2 inner member
        exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
          _ inner.2 facts.2.2
          (resume_references state.1 inner.2.1 facts.1 pending refs inner.1 facts.2.1) rfl

/-- The sole lookup of an admitted send is available before execution; exhaustion makes none and sealing keeps its original optional reply. -/
theorem send_safe {Slot OpenContext Plaintext SealContext Output PrimitiveState : Type}
    (seeds : Seeds Slot) (lookup : Lookup Slot PrimitiveState)
    (opening : Open OpenContext Plaintext PrimitiveState) (sealing : Seal SealContext Output PrimitiveState)
    (start : Start Slot SealContext) (state : Execution Slot PrimitiveState)
    (closed : Closed state.1) (refs : SendReferences state.1 start) :
    Safe (PqxdhRecordLiftOpaqueDrivers.interpreter seeds lookup opening sealing) LocalAllowed
      (PqxdhRecordLiftOpaqueDrivers.sendProgram start) state := by
  cases start with
  | exhausted entry context =>
      rw [PqxdhRecordLiftOpaqueDrivers.sendProgram]
      trivial
  | requested pending =>
      rw [PqxdhRecordLiftOpaqueDrivers.sendProgram]
      exact ⟨⟨closed, refs.1.2⟩, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩

/-- A single literal query exposes its actual precondition and supported continuation without unfolding the free-monad encoding. -/
theorem safe_query_bind {ι State Result : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT State ProbComp)) (predicate : spec.Domain → State → Prop)
    (query : spec.Domain) (next : spec.Range query → OracleComp spec Result) (state : State) :
    Safe impl predicate (spec.query query >>= next) state ↔
      predicate query state ∧ ∀ result ∈ support ((impl query).run state),
        Safe impl predicate (next result.1) result.2 := Iff.rfl

/-- The global private lookup requires table closure and an available predecessor in the literal current private table. Other services do not impose a lookup condition. -/
def Allowed {n : Nat} (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain)
    (state : PqxdhRecordLiftProtocol.Private n) : Prop :=
  match query with
  | .lookup coordinate => Closed state.chain ∧ Available state.chain coordinate
  | _ => True

/-- Lifting an opaque local source program preserves every actual pre-query table certificate, retaining complete private callback states. -/
theorem local_safe {n : Nat} {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (program : OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result)
    (secret : PqxdhRecordLiftProtocol.Private n) (records : PqxdhRecordLiftProtocol.RecordState n)
    (safe : Safe (PqxdhRecordLiftProtocol.localInterpreter policy setup codec
      (PqxdhRecordLiftProtocol.cachedSeeds secret)) LocalAllowed program records) :
    Safe (PqxdhRecordLiftProtocol.interpreter policy setup codec) Allowed
      (simulateQ PqxdhRecordLiftProtocol.localLift program) (PqxdhRecordLiftProtocol.putRecord secret records) := by
  induction program using OracleComp.inductionOn generalizing records with
  | pure value =>
      rw [simulateQ_pure]
      trivial
  | query_bind query next ih =>
      rw [safe_query_bind] at safe
      simp only [simulateQ_bind, simulateQ_spec_query]
      have factor := PqxdhRecordLiftProtocol.local_query_factor policy setup codec query secret records
      rcases query with coordinate | (pending | pending)
      all_goals
        simp only [PqxdhRecordLiftProtocol.localLift, simulateQ_spec_query] at factor ⊢
        rw [safe_query_bind]
        refine ⟨safe.1, fun result member => ?_⟩
        rw [factor, support_map] at member
        obtain ⟨inner, reached, rfl⟩ := member
        exact ih inner.1 inner.2 (safe.2 inner reached)

open PqxdhRecordLiftInterface PqxdhRecordLiftWorldCompiler

/-- Every hidden send lookup is closed and available at its literal global private prestate. Caller-known sends make no private lookup. -/
theorem kernelSend_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (stored : StoredKernel n)
    (context : RawCtxSourceSend.SealContext) (secret : PqxdhRecordLiftProtocol.Private n)
    (closed : Closed secret.chain) (ready : StoredReady secret.chain stored) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed (PqxdhRecordLiftProtocol.kernelSend stored context) secret := by
  cases stored with
  | known kernel => exact ⟨trivial, fun _ _ => trivial⟩
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelSend, bind_pure_comp]
      apply Safe.map
      exact local_safe _ setup codec _ secret (PqxdhRecordLiftProtocol.recordState secret)
        (send_safe _ _ _ _ _ _ closed (send_begin_references secret.chain kernel ready.1 context))

/-- Every hidden receive lookup is closed and available before execution, through all actual skipped-key recursion. -/
theorem kernelReceive_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (stored : StoredKernel n) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (secret : PqxdhRecordLiftProtocol.Private n)
    (valid : PqxdhRecordLiftChainOracle.Valid setup.source (PqxdhRecordLiftProtocol.cachedSeeds secret) ideal secret.chain)
    (ready : StoredReady secret.chain stored) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed (PqxdhRecordLiftProtocol.kernelReceive stored target context) secret := by
  cases stored with
  | known kernel => exact ⟨trivial, fun _ _ => trivial⟩
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp]
      apply Safe.map
      exact local_safe _ setup codec _ secret (PqxdhRecordLiftProtocol.recordState secret)
        (receive_safe _ _ _ _ _
          (PqxdhRecordLiftLoggedAdapters.liftLookup_preserves _ _
            (PqxdhRecordLiftChainOracle.lookup_preserves _ _ _)) _ _ valid
          (fun _ good => good.1)
          ⟨begin_available secret.chain kernel ready.1.1 target context,
            begin_present secret.chain kernel ready.1.2 target context⟩)

/-- The literal owner dispatch preserves the lookup certificate through empty messages, parsing, validation, sends and receives. -/
theorem ownerStep_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (secret : PqxdhRecordLiftProtocol.Private n)
    (valid : PqxdhRecordLiftChainOracle.Valid setup.source (PqxdhRecordLiftProtocol.cachedSeeds secret) ideal secret.chain)
    (ready : StoredReady secret.chain owner.kernel) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed (PqxdhRecordLiftProtocol.ownerStep sender decode query owner) secret := by
  cases query with
  | inl plaintext =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend]
      split
      · trivial
      · simp only [bind_pure_comp]
        exact Safe.map _ _ _ (kernelSend_safe setup codec ideal owner.kernel _ secret valid.1 ready)
  | inr raw =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive]
      split
      · trivial
      · split
        · trivial
        · split
          · simp only [bind_pure_comp]
            exact Safe.map _ _ _ (kernelReceive_safe setup codec ideal owner.kernel _ _ secret valid ready)
          · trivial

/-- Actual tagged publication makes no lookup and preserves the source operation's prefix certificate, including failed writers. -/
theorem ownerRun_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (tag : PqxdhDeploymentInterface.FrameTag)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (secret : PqxdhRecordLiftProtocol.Private n)
    (valid : PqxdhRecordLiftChainOracle.Valid setup.source (PqxdhRecordLiftProtocol.cachedSeeds secret) ideal secret.chain)
    (ready : StoredReady secret.chain owner.kernel) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner) secret := by
  exact Safe.bind _ _ secret (ownerStep_safe setup codec ideal sender decode query owner secret valid ready)
    (fun _ _ => ⟨trivial, fun _ _ => trivial⟩)

/-- Dynamic Beacon routing derives the selected kernel certificate from current source storage; absent and inactive owners make no lookup. -/
theorem beacon_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State n) (good : PqxdhRecordLiftMixedWorld.Good setup.source ideal state) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed ((PqxdhRecordLiftProtocol.beaconStep codec.frameRead owner query).run
        (PqxdhRecordLiftProtocol.control state)) (PqxdhRecordLiftProtocol.privateState state) := by
  cases selected : state.owners[owner]? with
  | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, PqxdhRecordLiftProtocol.control, selected]
      trivial
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, PqxdhRecordLiftProtocol.control, selected] <;>
            trivial
      | established shell kernel =>
          simp only [PqxdhRecordLiftProtocol.beaconStep, StateT.run, PqxdhRecordLiftProtocol.control, selected, bind_pure_comp]
          exact Safe.map _ _ _ (ownerRun_safe setup codec ideal _ shell.identityKeyId codec.frameRead query _ _
            good.2.2.2.1 (good.2.1.2 _ (List.mem_of_getElem? selected)))

/-- Dynamic Server routing derives the selected kernel certificate from the actual peer map, after the source header routing checks. -/
theorem server_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State n) (good : PqxdhRecordLiftMixedWorld.Good setup.source ideal state) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed ((PqxdhRecordLiftProtocol.serverStep codec.frameRead route query).run
        (PqxdhRecordLiftProtocol.control state)) (PqxdhRecordLiftProtocol.privateState state) := by
  cases existing : state.server with
  | none =>
      cases query <;>
        simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing] <;>
        trivial
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, selected]
              trivial
          | some peer =>
              simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, selected, bind_pure_comp]
              exact Safe.map _ _ _ (ownerRun_safe setup codec ideal _ server.sender codec.frameRead (.inl plaintext) _ _
                good.2.2.2.1 (good.2.1.1 server existing keyId peer selected))
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, routed]
              trivial
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, routed, selected]
                  trivial
              | some peer =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, routed, selected, bind_pure_comp]
                  exact Safe.map _ _ _ (ownerRun_safe setup codec ideal _ server.sender codec.frameRead (.inr raw) _ _
                    good.2.2.2.1 (good.2.1.1 server existing keyId peer selected))

/-- Restricted environment capabilities never invoke a record lookup; installation only allocates a private seed slot. -/
theorem capability_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (CapabilitySpec n).Domain) (state : PqxdhRecordLiftProtocol.Control n)
    (secret : PqxdhRecordLiftProtocol.Private n) :
    Safe (PqxdhRecordLiftProtocol.interpreter policy setup codec) Allowed
      ((PqxdhRecordLiftProtocol.capability query).run state) secret := by
  cases query with
  | peerPresent keyId => trivial
  | ownerPresent owner => trivial
  | appendOwner sender pin phase => trivial
  | hash bytes => exact ⟨trivial, fun _ _ => trivial⟩
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftProtocol.capability, StateT.run]
      split
      · split <;> trivial
      · trivial
  | installServer keyId identity ref =>
      simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installServer, StateT.run]
      split
      · trivial
      · split
        · cases ref <;> simp only [PqxdhRecordLiftProtocol.resolve, bind_assoc, pure_bind]
          · trivial
          · exact ⟨trivial, fun _ _ => trivial⟩
        · trivial
  | installBeacon owner shell ref =>
      simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installBeacon, StateT.run]
      split
      · cases ref <;> simp only [PqxdhRecordLiftProtocol.resolve, bind_assoc, pure_bind]
        · trivial
        · exact ⟨trivial, fun _ _ => trivial⟩
      · trivial

/-- Charging and forwarding actual environment effects introduce no hidden-record lookup, for any original capability reply. -/
theorem effects_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : LookupPolicy n) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (EnvEffects n).Domain) (state : PqxdhRecordLiftProtocol.Control n)
    (secret : PqxdhRecordLiftProtocol.Private n) :
    Safe (PqxdhRecordLiftProtocol.interpreter policy setup codec) Allowed
      ((PqxdhRecordLiftProtocol.effects query).run state) secret := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine ⟨trivial, fun result member => ?_⟩
  cases query with
  | inl coin => exact ⟨trivial, fun _ _ => trivial⟩
  | inr request => exact capability_safe policy setup codec request state result.2

/-- Every actual WorldSpec request has the private lookup certificate, deriving selected storage facts from the current mixed invariant. -/
theorem handler_safe {n : Nat} {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n)
    (good : PqxdhRecordLiftMixedWorld.Good setup.source ideal state) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed ((PqxdhRecordLiftProtocol.handler codec.frameRead route query).run
        (PqxdhRecordLiftProtocol.control state)) (PqxdhRecordLiftProtocol.privateState state) := by
  rcases query with created | query
  · simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.initializeServer,
      StateT.run, PqxdhRecordLiftProtocol.control]
    split <;> trivial
  · rcases query with effect | record
    · exact effects_safe _ setup codec effect _ _
    · rcases record with server | ⟨owner, beacon⟩
      · cases server with
        | inl request => exact server_safe setup codec ideal route (.inl request) state good
        | inr raw => exact server_safe setup codec ideal route (.inr raw) state good
      · cases beacon with
        | inl plaintext => exact beacon_safe setup codec ideal owner (.inl plaintext) state good
        | inr raw => exact beacon_safe setup codec ideal owner (.inr raw) state good

/-- Every actual adaptive schedule carries the query-prefix certificate through full private handler states and original replies. -/
theorem schedule_safe {n : Nat} {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n)
    (good : PqxdhRecordLiftMixedWorld.Good setup.source ideal state) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed (PqxdhRecordLiftProtocol.schedule codec.frameRead route client
        (PqxdhRecordLiftProtocol.control state)) (PqxdhRecordLiftProtocol.privateState state) := by
  unfold PqxdhRecordLiftProtocol.schedule
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply Safe.bind _ _ _ (handler_safe setup codec ideal route query state good)
      intro result member
      rw [PqxdhRecordLiftProtocol.handler_factor, support_map] at member
      obtain ⟨inner, member, rfl⟩ := member
      exact ih inner.1 inner.2 (PqxdhRecordLiftMixedWorld.handler_good setup codec ideal route query state good inner member)

/-- Starting from the actual empty state discharges every storage and predecessor premise for any adaptive WorldSpec client. -/
theorem initial_schedule_safe {n : Nat} {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed (PqxdhRecordLiftProtocol.schedule codec.frameRead route client PqxdhRecordLiftProtocol.initialControl)
      PqxdhRecordLiftProtocol.initialPrivate :=
  schedule_safe setup codec ideal route client initial (PqxdhRecordLiftMixedWorld.initial_good setup.source ideal)

/-- Every reached private lookup in the initialized actual source has a closed current table and an available predecessor, with the complete original continuation retained. -/
theorem initial_lookup {n : Nat} {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (coordinate : Coordinate (Slot n))
    (next : Unit → OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) (Result × PqxdhRecordLiftProtocol.Control n))
    (secret : PqxdhRecordLiftProtocol.Private n)
    (reached : Reaches (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      (PqxdhRecordLiftProtocol.schedule codec.frameRead route client PqxdhRecordLiftProtocol.initialControl)
      PqxdhRecordLiftProtocol.initialPrivate
      ((PqxdhRecordLiftProtocol.ServiceSpec n).query (.lookup coordinate) >>= next) secret) :
    Closed secret.chain ∧ Available secret.chain coordinate :=
  (initial_schedule_safe setup codec ideal route client).query_at (.lookup coordinate) next reached

/-- The frozen environment, private-send ledger and adversary program has the same actual pre-query certificate in both modes, without a Frame or reachability hypothesis. -/
theorem program_safe {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    Safe (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      Allowed (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)
      PqxdhRecordLiftProtocol.initialPrivate :=
  initial_schedule_safe setup codec ideal route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)

end BeaconcryptCore.Computational.PqxdhRecordLiftAvailability

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.reaches' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.reaches

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.query_at' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.query_at

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.Safe.map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.receive_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.receive_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.send_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.send_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.safe_query_bind' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.safe_query_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.local_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.local_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.kernelSend_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.kernelSend_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.kernelReceive_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.kernelReceive_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.ownerStep_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.ownerStep_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.ownerRun_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.ownerRun_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.beacon_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.beacon_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.server_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.server_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.capability_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.capability_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.effects_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.effects_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.handler_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.handler_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.schedule_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.schedule_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.initial_schedule_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.initial_schedule_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.initial_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.initial_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.program_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftAvailability.program_safe

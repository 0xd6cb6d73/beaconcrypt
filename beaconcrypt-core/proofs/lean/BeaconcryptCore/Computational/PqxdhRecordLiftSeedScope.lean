-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftGlobalSeedCut
import BeaconcryptCore.Computational.PqxdhRecordLiftAvailability

/-! Source-derived table absence at the actual first hidden allocation. -/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol PqxdhRecordLiftAvailability
variable {n : Nat}

/-- Every retained chain answer belongs to an already sampled seed slot. -/
def Scoped (secret : Private n) : Prop :=
  PqxdhRecordLiftWorldCompiler.TableScoped (join initialControl secret)

/-- Only allocation exposes the table's already allocated slot provenance. -/
def Allowed (query : Service n) (secret : Private n) : Prop :=
  match query with
  | .allocate _ => Scoped secret
  | _ => True

/-- A source Server installation reaches its allocation before changing any chain data. -/
theorem installServer_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : Control n) (secret : Private n) (scope : Scoped secret) :
    Safe (interpreter policy setup codec) Allowed
      ((installServer keyId identity ref).run state) secret := by
  simp only [installServer, StateT.run]
  split
  · trivial
  · split
    · cases ref <;> simp only [resolve, bind_assoc, pure_bind]
      · trivial
      · exact ⟨scope, fun _ _ => trivial⟩
    · trivial

/-- Every query of a local record driver is allocation-free, for every original reply and private state. -/
theorem local_safe {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (program : OracleComp (LocalSpec n) Result) (secret : Private n) :
    Safe (interpreter policy setup codec) Allowed (simulateQ localLift program) secret := by
  induction program using OracleComp.inductionOn generalizing secret with
  | pure value => trivial
  | query_bind query next ih =>
      rcases query with coordinate | (opening | sealing)
      all_goals
        simp only [simulateQ_bind, simulateQ_spec_query, localLift]
        exact ⟨trivial, fun result _ => ih result.1 result.2⟩

/-- Restricted capabilities expose allocation only at the original, unchanged chain-table prestate. -/
theorem capability_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (CapabilitySpec n).Domain) (state : Control n) (secret : Private n)
    (scope : Scoped secret) :
    Safe (interpreter policy setup codec) Allowed ((capability query).run state) secret := by
  cases query with
  | peerPresent keyId => trivial
  | ownerPresent owner => trivial
  | appendOwner sender pin phase => trivial
  | hash bytes => exact ⟨trivial, fun _ _ => trivial⟩
  | advanceOwner owner phase =>
      simp only [capability, StateT.run]
      split
      · split <;> trivial
      · trivial
  | installServer keyId identity ref =>
      exact installServer_safe policy setup codec keyId identity ref state secret scope
  | installBeacon owner shell ref =>
      simp only [capability, installBeacon, StateT.run]
      split
      · cases ref <;> simp only [resolve, bind_assoc, pure_bind]
        · trivial
        · exact ⟨scope, fun _ _ => trivial⟩
      · trivial

/-- Charging an environment effect changes no slot provenance before the actual capability runs. -/
theorem effects_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : (EnvEffects n).Domain) (state : Control n) (secret : Private n)
    (scope : Scoped secret) :
    Safe (interpreter policy setup codec) Allowed ((effects query).run state) secret := by
  simp only [effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine ⟨trivial, fun result member => ?_⟩
  simp only [interpreter, StateT.run] at member
  subst result
  cases query with
  | inl coin => exact ⟨trivial, fun _ _ => trivial⟩
  | inr request => exact capability_safe policy setup codec request state _ scope

/-- Hidden and caller-known sends cannot allocate any seed slot. -/
theorem kernelSend_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n)
    (context : RawCtxSourceSend.SealContext) (secret : Private n) :
    Safe (interpreter policy setup codec) Allowed (kernelSend stored context) secret := by
  cases stored with
  | known kernel => exact ⟨trivial, fun _ _ => trivial⟩
  | hidden slot kernel =>
      simp only [kernelSend, bind_pure_comp]
      exact Safe.map _ _ _ (local_safe policy setup codec _ secret)

/-- Cached and future hidden receive recursion, and caller-known receives, cannot allocate seed slots. -/
theorem kernelReceive_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (stored : PqxdhRecordLiftWorldCompiler.StoredKernel n) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (secret : Private n) :
    Safe (interpreter policy setup codec) Allowed (kernelReceive stored target context) secret := by
  cases stored with
  | known kernel => exact ⟨trivial, fun _ _ => trivial⟩
  | hidden slot kernel =>
      simp only [kernelReceive, bind_pure_comp]
      exact Safe.map _ _ _ (local_safe policy setup codec _ secret)

/-- The complete owner dispatcher is allocation-free, including rejected raw input and optional failures. -/
theorem ownerStep_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : PqxdhRecordLiftWorldCompiler.Owner n)
    (secret : Private n) :
    Safe (interpreter policy setup codec) Allowed (ownerStep sender decode query owner) secret := by
  cases query with
  | inl plaintext =>
      simp only [ownerStep, ownerSend]
      split
      · trivial
      · simp only [bind_pure_comp]
        exact Safe.map _ _ _ (kernelSend_safe policy setup codec owner.kernel _ secret)
  | inr raw =>
      simp only [ownerStep, ownerReceive]
      split
      · trivial
      · split
        · trivial
        · split
          · simp only [bind_pure_comp]
            exact Safe.map _ _ _ (kernelReceive_safe policy setup codec owner.kernel _ _ secret)
          · trivial

/-- Publishing the actual writer buffer introduces no allocation after an owner operation. -/
theorem ownerRun_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : PqxdhRecordLiftWorldCompiler.Owner n) (secret : Private n) :
    Safe (interpreter policy setup codec) Allowed (ownerRun tag sender decode query owner) secret := by
  exact Safe.bind _ _ secret (ownerStep_safe policy setup codec sender decode query owner secret)
    (fun _ _ => ⟨trivial, fun _ _ => trivial⟩)

/-- Actual Beacon routing cannot allocate, even for arbitrary stored phases and kernels. -/
theorem beacon_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : PqxdhRecordLiftWorldCompiler.State n) :
    Safe (interpreter policy setup codec) Allowed
      ((beaconStep codec.frameRead owner query).run (control state)) (privateState state) := by
  cases selected : state.owners[owner]? with
  | none =>
      simp only [beaconStep, StateT.run, PqxdhRecordLiftProtocol.control, selected]
      trivial
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;> simp only [beaconStep, StateT.run, PqxdhRecordLiftProtocol.control, selected] <;> trivial
      | established shell kernel =>
          simp only [beaconStep, StateT.run, PqxdhRecordLiftProtocol.control, selected, bind_pure_comp]
          exact Safe.map _ _ _ (ownerRun_safe policy setup codec _ shell.identityKeyId codec.frameRead query _ _)

/-- Actual Server routing cannot allocate through either plaintext send or raw receive. -/
theorem server_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : PqxdhRecordLiftWorldCompiler.State n) :
    Safe (interpreter policy setup codec) Allowed
      ((serverStep codec.frameRead route query).run (control state)) (privateState state) := by
  cases existing : state.server with
  | none =>
      cases query <;> simp only [serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing] <;> trivial
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, selected]
              trivial
          | some peer =>
              simp only [serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, selected, bind_pure_comp]
              exact Safe.map _ _ _ (ownerRun_safe policy setup codec _ server.sender codec.frameRead (.inl plaintext) _ _)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, routed]
              trivial
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, routed, selected]
                  trivial
              | some peer =>
                  simp only [serverStep, StateT.run, PqxdhRecordLiftProtocol.control, existing, routed, selected, bind_pure_comp]
                  exact Safe.map _ _ _ (ownerRun_safe policy setup codec _ server.sender codec.frameRead (.inr raw) _ _)

/-- Every actual world request exposes only allocation prestates with the original chain-table provenance. -/
theorem handler_safe {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (policy : PqxdhRecordLiftWorldCompiler.LookupPolicy n)
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : PqxdhRecordLiftWorldCompiler.State n)
    (scope : PqxdhRecordLiftWorldCompiler.TableScoped state) :
    Safe (interpreter policy setup codec) Allowed
      ((handler codec.frameRead route query).run (control state)) (privateState state) := by
  rcases query with created | query
  · simp only [handler, initializeServer, StateT.run, PqxdhRecordLiftProtocol.control]
    split <;> trivial
  · rcases query with effect | record
    · exact effects_safe policy setup codec effect _ _ scope
    · rcases record with server | ⟨owner, beacon⟩
      · cases server with
        | inl request => exact server_safe policy setup codec route (.inl request) state
        | inr raw => exact server_safe policy setup codec route (.inr raw) state
      · cases beacon with
        | inl plaintext => exact beacon_safe policy setup codec owner (.inl plaintext) state
        | inr raw => exact beacon_safe policy setup codec owner (.inr raw) state

/-- Actual mixed-world preservation carries allocation provenance through the complete adaptive world schedule. -/
theorem schedule_safe {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (state : PqxdhRecordLiftWorldCompiler.State n)
    (good : PqxdhRecordLiftMixedWorld.Good setup.source ideal state) :
    Safe (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec) Allowed
      (schedule codec.frameRead route client (control state)) (privateState state) := by
  unfold schedule
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure]
      trivial
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply Safe.bind _ _ _ (handler_safe _ setup codec route query state good.2.2.1)
      intro result member
      rw [PqxdhRecordLiftProtocol.handler_factor, support_map] at member
      obtain ⟨inner, member, rfl⟩ := member
      exact ih inner.1 inner.2 (PqxdhRecordLiftMixedWorld.handler_good setup codec ideal route query state good inner member)

/-- Literal empty initialization discharges all provenance premises for the adaptive schedule. -/
theorem initial_schedule_safe {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result) :
    Safe (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec) Allowed
      (schedule codec.frameRead route client initialControl) initialPrivate :=
  schedule_safe setup codec ideal route client PqxdhRecordLiftWorldCompiler.initial
    (PqxdhRecordLiftMixedWorld.initial_good setup.source ideal)

open PqxdhRecordLiftGlobalSeedCut in
/-- The actual first-allocation scanner reaches the exact original remainder and private state, without conditioning. -/
theorem scan_reaches {Result : Type} (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (target : Slot n)
    (client : OracleComp (ServiceSpec n) Result) (before : Private n)
    (result : Cut n Result × Private n)
    (supported : result ∈ support ((simulateQ impl (scan target client)).run before)) :
    Reaches impl client before (finish target result.1) result.2 := by
  induction client using OracleComp.inductionOn generalizing before with
  | pure value =>
      change result ∈ support (pure (PqxdhRecordLiftFirstLookup.Cut.complete value, before) : ProbComp _) at supported
      simp only [mem_support_pure_iff] at supported
      simpa only [supported, finish] using Reaches.here (impl := impl) (pure value) before
  | query_bind query next ih =>
      cases query with
      | allocate coordinate =>
          change result ∈ support ((simulateQ impl (if coordinate = target then pure (.pending next) else
            (((ServiceSpec n).query (.allocate coordinate) : OracleComp (ServiceSpec n) Unit) >>= fun reply => scan target (next reply)))).run before) at supported
          split_ifs at supported with same
          · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
            subst coordinate
            simpa only [supported, finish] using Reaches.here (impl := impl) (((ServiceSpec n).query (.allocate target) : OracleComp (ServiceSpec n) Unit) >>= next) before
          · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
            obtain ⟨middle, actual, tail⟩ := supported
            exact .later _ _ _ _ _ _ actual (ih middle.1 middle.2 tail)
      | _ =>
          change result ∈ support ((simulateQ impl ((((ServiceSpec n).query _ : OracleComp (ServiceSpec n) _) >>= fun reply => scan target (next reply)))).run before) at supported
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
          exact supported.elim (fun middle reached => .later _ _ _ _ _ _ reached.1 (ih middle.1 middle.2 reached.2))

/-- Every supported pending allocation cut inherits its precise source query-prestate certificate. -/
theorem pending_query {Result : Type}
    (impl : QueryImpl (ServiceSpec n) (StateT (Private n) ProbComp))
    (target : Slot n) (client : OracleComp (ServiceSpec n) Result) (before : Private n)
    (safe : Safe impl Allowed client before)
    (next : Unit → OracleComp (ServiceSpec n) Result) (after : Private n)
    (supported : (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support
      ((simulateQ impl (PqxdhRecordLiftGlobalSeedCut.scan target client)).run before)) :
    Scoped after :=
  (safe.reaches (scan_reaches impl target client before (.pending next, after) supported)).1

/-- Source table provenance makes every coordinate of an unsampled slot absent, with no byte or direction assumption. -/
theorem scoped_missing_slot (secret : Private n) (scope : Scoped secret) (target : Slot n)
    (missing : secret.seeds.1 target = none) (coordinate : PqxdhRecordLiftWorldCompiler.Label n)
    (same : coordinate.slot = target) : secret.chain coordinate = none := by
  cases found : secret.chain coordinate with
  | none => rfl
  | some value =>
      obtain ⟨seed, present⟩ := scope coordinate value found
      change secret.seeds.1 coordinate.slot = some seed at present
      rw [same, missing] at present
      contradiction

/-- At an actual initialized first-allocation cut, the missing seed forces the entire selected-slot table to be absent. -/
theorem pending_schedule {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (target : Slot n) (next : Unit → OracleComp (ServiceSpec n) (Result × Control n))
    (after : Private n)
    (supported : (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support
      ((simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
        (PqxdhRecordLiftGlobalSeedCut.scan target
          (schedule codec.frameRead route client initialControl))).run initialPrivate)) :
    Scoped after ∧ after.seeds.1 target = none ∧
      ∀ coordinate, coordinate.slot = target → after.chain coordinate = none := by
  have scope := pending_query _ target _ initialPrivate
    (initial_schedule_safe setup codec ideal route client) next after supported
  have missing := PqxdhRecordLiftGlobalSeedCut.scan_initial_missing setup.source ideal setup codec target
    (schedule codec.frameRead route client initialControl) (.pending next, after) supported
  exact ⟨scope, missing, fun coordinate same => scoped_missing_slot after scope target missing coordinate same⟩

/-- Both directional initial children are absent at the same actual first-allocation prefix. -/
theorem pending_children {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (target : Slot n) (next : Unit → OracleComp (ServiceSpec n) (Result × Control n))
    (after : Private n)
    (supported : (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support
      ((simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
        (PqxdhRecordLiftGlobalSeedCut.scan target
          (schedule codec.frameRead route client initialControl))).run initialPrivate)) :
    ∀ direction, after.chain ⟨target, direction, PqxdhRecordLiftChainTable.start direction⟩ = none :=
  fun _ => (pending_schedule setup codec ideal route client target next after supported).2.2 _ rfl

/-- The proof-attached actual sampler preserves the same allocation scope and entire missing-slot table fact. -/
theorem sampled_schedule {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (target : Slot n)
    (result : { result : PqxdhRecordLiftGlobalSeedCut.Cut n (Result × Control n) × Private n //
      result.2.seeds.1 target = none })
    (supported : result ∈ support (PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source ideal setup codec target
      (schedule codec.frameRead route client initialControl)))
    (next : Unit → OracleComp (ServiceSpec n) (Result × Control n))
    (pending : result.val.1 = .pending next) :
    Scoped result.val.2 ∧ result.val.2.seeds.1 target = none ∧
      ∀ coordinate, coordinate.slot = target → result.val.2.chain coordinate = none := by
  have actual : result.val ∈ support ((simulateQ
      (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
      (PqxdhRecordLiftGlobalSeedCut.scan target
        (schedule codec.frameRead route client initialControl))).run initialPrivate) := by
    unfold PqxdhRecordLiftMixedWorld.policy
    rw [← PqxdhRecordLiftGlobalSeedCut.prefix_forget setup.source ideal setup codec target
      (schedule codec.frameRead route client initialControl), support_map]
    exact ⟨result, supported, rfl⟩
  have same : result.val = (.pending next, result.val.2) := Prod.ext pending rfl
  rw [same] at actual
  exact pending_schedule setup codec ideal route client target next result.val.2 actual

/-- Both frozen environment/adversary programs carry these derived facts at their actual sampled first-allocation cuts. -/
theorem sampled_program {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (target : Slot n)
    (result : { result : PqxdhRecordLiftGlobalSeedCut.Cut n
      (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
        (X × PqxdhDeploymentSecrecy.Ledger) × E) × Control n) × Private n //
      result.2.seeds.1 target = none })
    (supported : result ∈ support (PqxdhRecordLiftGlobalSeedCut.sampledPrefix setup.source ideal setup codec target
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)))
    (next : Unit → OracleComp (ServiceSpec n)
      (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
        (X × PqxdhDeploymentSecrecy.Ledger) × E) × Control n)) (pending : result.val.1 = .pending next) :
    Scoped result.val.2 ∧ result.val.2.seeds.1 target = none ∧
      ∀ coordinate, coordinate.slot = target → result.val.2.chain coordinate = none :=
  sampled_schedule setup codec ideal route
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)
    target result supported next pending

/-- Preparing either directional mask preserves the derived absence of every child whose input reads that seed half. -/
theorem prepared_reads_missing {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftWorldCompiler.Label n → Bool)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (target : Slot n) (next : Unit → OracleComp (ServiceSpec n) (Result × Control n))
    (after : Private n)
    (supported : (PqxdhRecordLiftFirstLookup.Cut.pending next, after) ∈ support
      ((simulateQ (interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
        (PqxdhRecordLiftGlobalSeedCut.scan target
          (schedule codec.frameRead route client initialControl))).run initialPrivate))
    (direction : Bool) (other : PqxdhSecretInputKdf.RootOutput)
    (coordinate : PqxdhRecordLiftWorldCompiler.Label n)
    (reads : PqxdhRecordLiftGlobalSeedCut.Reads
      (PqxdhRecordLiftGlobalSeedCut.prepare after target direction other) coordinate) :
    (PqxdhRecordLiftGlobalSeedCut.prepare after target direction other).before.chain coordinate = none :=
  (pending_schedule setup codec ideal route client target next after supported).2.2 coordinate reads.1

end BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.installServer_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.installServer_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.local_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.local_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.capability_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.capability_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.effects_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.effects_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.kernelSend_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.kernelSend_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.kernelReceive_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.kernelReceive_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.ownerStep_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.ownerStep_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.ownerRun_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.ownerRun_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.beacon_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.beacon_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.server_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.server_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.handler_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.handler_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.schedule_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.schedule_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.initial_schedule_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.initial_schedule_safe

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.scan_reaches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.scan_reaches

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.pending_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.pending_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.scoped_missing_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.scoped_missing_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.pending_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.pending_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.pending_children' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.pending_children

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.sampled_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.sampled_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.sampled_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.sampled_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.prepared_reads_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftSeedScope.prepared_reads_missing

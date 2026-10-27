-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftMixedRecords
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocol

/-! Actual mixed policies preserve source record invariants and finite callback budgets through dynamic storage and adaptive world scheduling. These are operational facts about the concrete interpreter, not cryptographic assumptions or arbitrary private-state observation bounds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld
open PqxdhRecordLiftInterface PqxdhRecordLiftWorldCompiler
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftChainCompiler
open PqxdhRecordLiftChainOrder PqxdhRecordLiftBudget
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat}

/-- A concrete coordinate selector; it receives neither primitive counters nor environment state. -/
noncomputable def policy (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) : LookupPolicy n := fun seeds =>
  PqxdhRecordLiftChainOracle.lookup source seeds ideal

/-- The actual logged owner run inherits the joint ordinary-record source cap, including known kernels and private test/fresh sends. -/
theorem ownerRun_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support (ownerRun (policy setup.source ideal) setup codec sender query owner state)) :
    result.2.2.1.1.native .kdf ≤ state.primitive.1.native .kdf + (if query.isLeft then 1 else 51) :=
  PqxdhRecordLiftMixedRecords.ownerStep_kdf setup codec (cachedSeeds state) ideal sender codec.frameRead
    query owner (state.chain, (state.primitive, [])) result supported

/-- Actual dynamic Server routing preserves the source cap on absent peers, malformed routes, sends and receives. -/
theorem server_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n)
    (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep (policy setup.source ideal) setup codec route query).run state)) :
    result.2.primitive.1.native .kdf ≤ state.primitive.1.native .kdf + (if query.isLeft then 1 else 51) := by
  cases existing : state.server with
  | none =>
      cases query <;>
        simp only [serverStep, StateT.run, existing, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact Nat.le_add_right _ _
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [serverStep, StateT.run, existing, selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact Nat.le_add_right _ _
          | some peer =>
              simp only [serverStep, StateT.run, existing, selected, support_map] at supported
              obtain ⟨inner, member, rfl⟩ := supported
              exact ownerRun_kdf setup codec ideal server.sender (.inl plaintext) _ state inner member
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, StateT.run, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact Nat.le_add_right _ _
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact Nat.le_add_right _ _
              | some peer =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_map] at supported
                  obtain ⟨inner, member, rfl⟩ := supported
                  exact ownerRun_kdf setup codec ideal server.sender (.inr raw) _ state inner member

/-- Existing inactive owners and absent handles retain their distinct source behavior while respecting the same native KDF cap. -/
theorem beacon_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep (policy setup.source ideal) setup codec owner query).run state)) :
    result.2.primitive.1.native .kdf ≤ state.primitive.1.native .kdf + (if query.isLeft then 1 else 51) := by
  cases selected : state.owners[owner]? with
  | none =>
      simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Nat.le_add_right _ _
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [beaconStep, StateT.run, selected, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact Nat.le_add_right _ _
      | established shell kernel =>
          simp only [beaconStep, StateT.run, selected, support_map] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          exact ownerRun_kdf setup codec ideal shell.identityKeyId query _ state inner member

/-- Hidden resolution changes neither native-call nor direct-effect counts. -/
theorem resolve_counters (role : Role) (ref : KernelRef n) (state : State n)
    (result : StoredKernel n × State n)
    (supported : result ∈ support ((resolve role ref).run state)) :
    (result.2.primitive.1.native, result.2.primitive.1.effects) =
      (state.primitive.1.native, state.primitive.1.effects) := by
  cases ref with
  | known known =>
    simp only [resolve, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | hidden slot =>
    simp only [resolve, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    rfl

/-- Server admission performs no native primitive or direct-effect request. -/
theorem install_server_counters (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) :
    (result.2.primitive.1.native, result.2.primitive.1.effects) =
      (state.primitive.1.native, state.primitive.1.effects) := by
  cases server : state.server with
  | none =>
    simp only [installServer, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | some current =>
    simp only [installServer, StateT.run, server] at supported
    split_ifs at supported
    · simp only [bind_pure_comp, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      have unchanged := resolve_counters .server ref state inner reached
      cases ref <;> exact unchanged
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl

/-- Beacon admission performs no native primitive or direct-effect request. -/
theorem install_beacon_counters (owner : Nat) (shell : BeaconShell)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    (result.2.primitive.1.native, result.2.primitive.1.effects) =
      (state.primitive.1.native, state.primitive.1.effects) := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have unchanged := resolve_counters .beacon ref state inner reached
    cases ref <;> exact unchanged
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl

/-- Every restricted capability preserves both call-count functions; effects are charged by its outer wrapper. -/
theorem capability_counters (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) :
    (result.2.primitive.1.native, result.2.primitive.1.effects) =
      (state.primitive.1.native, state.primitive.1.effects) := by
  cases query with
  | installServer keyId identity ref => exact install_server_counters keyId identity ref state result supported
  | installBeacon owner shell ref => exact install_beacon_counters owner shell ref state result supported
  | peerPresent keyId | ownerPresent owner | appendOwner sender pin phase =>
    simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | hash bytes =>
    simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    rfl
  | advanceOwner owner phase =>
    simp only [capability, StateT.run] at supported
    split at supported
    · split_ifs at supported <;>
        simp only [support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> rfl
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl

/-- Every direct effect charges exactly its own class and leaves all native counters unchanged. -/
theorem effects_counters (query : (EnvEffects n).Domain) (state : State n)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) :
    (result.2.primitive.1.native, result.2.primitive.1.effects) =
      ((chargeEffect query state).primitive.1.native, (chargeEffect query state).primitive.1.effects) := by
  cases query with
  | inl coin =>
    simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    rfl
  | inr request => exact capability_counters request (chargeEffect (.inr request) state) result supported

/-- Only record requests incur native costs, with separate send and receive weights. -/
theorem handler_kdf {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : State n)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler (policy setup.source ideal) setup codec route query).run state)) :
    result.2.primitive.1.native .kdf ≤ state.primitive.1.native .kdf +
      (if WorldRecord .send query then 1
       else if WorldRecord .raw query then 51 else 0) := by
  cases query with
  | inl created =>
    cases server : state.server <;>
      simp only [handler, initializeServer, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact Nat.le_add_right _ _
  | inr outer =>
    cases outer with
    | inl effect =>
      have same := congrArg (fun counts => counts.1 .kdf) (effects_counters effect state result supported)
      simpa [WorldRecord, chargeEffect] using same.le
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send => simpa [WorldRecord, recordKind] using server_kdf setup codec ideal route (.inl send) state result supported
        | inr raw => simpa [WorldRecord, recordKind] using server_kdf setup codec ideal route (.inr raw) state result supported
      | inr ownerQuery =>
        rcases ownerQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext => simpa [WorldRecord, recordKind] using beacon_kdf setup codec ideal owner (.inl plaintext) state result supported
        | inr raw => simpa [WorldRecord, recordKind] using beacon_kdf setup codec ideal owner (.inr raw) state result supported

/-- Every adaptive mixed-world schedule has the joint source KDF bound, for every concrete coordinate selector. -/
theorem schedule_kdf {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) X) (sends receives : Nat)
    (sendBound : client.IsQueryBoundP (WorldRecord .send) sends)
    (rawBound : client.IsQueryBoundP (WorldRecord .raw) receives)
    (state : State n) (result : X × State n)
    (supported : result ∈ support ((simulateQ (handler (policy setup.source ideal) setup codec route) client).run state)) :
    result.2.primitive.1.native .kdf ≤ state.primitive.1.native .kdf + sends + 51 * receives := by
  simpa only [Nat.one_mul] using
    (PqxdhRecordLiftWorldBudget.weighted_support (WorldRecord .send) (WorldRecord .raw)
      (by
        rintro (created | (effect | record)) first second
        · exact first
        · exact first
        · exact RecordKind.noConfusion (first.symm.trans second))
      (handler (policy setup.source ideal) setup codec route) (fun state => state.primitive.1.native .kdf)
      1 51 (fun query before after reached => handler_kdf setup codec ideal route query before after reached)
      client sends receives sendBound rawBound state result supported)

open PqxdhDeploymentInterface

/-- The executed open program derives the total source cap `S + 51R` for every concrete mixed policy, using only the adversary's existing request budget. -/
theorem run_kdf {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run (policy setup.source ideal) setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.native .kdf ≤ budget.sends + 51 * budget.receives := by
  simpa only [initial, PqxdhRecordLiftWorld.Counts.empty, Nat.zero_add] using
    schedule_kdf setup codec ideal route _ budget.sends budget.receives
      (program_record_bound env setup.source.crypto codec serverKid bounds mode budget adversary respects .send)
      (program_record_bound env setup.source.crypto codec serverKid bounds mode budget adversary respects .raw)
      initial result supported

/-- Operational storage, predecessor and depth facts for the current concrete selector and actual partial seed cache. -/
def TableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (state : State n) : Prop :=
  TableScoped state ∧ PqxdhRecordLiftChainOracle.Valid source (cachedSeeds state) ideal state.chain ∧
    DepthBound state.chain (state.primitive.1.native .kdf)

/-- A mixed-world invariant derived below from actual initialization and handlers, not a premise about arbitrary environments. -/
def Good (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (state : State n) : Prop :=
  Scoped state ∧ Ready state ∧ TableGood source ideal state

/-- The actual empty private world establishes every mixed operational clause for every selector. -/
theorem initial_good (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) : Good source ideal (initial : State n) :=
  ⟨initial_scoped, initial_ready, initial_tableScoped,
    PqxdhRecordLiftChainOracle.valid_empty source _ ideal, depth_empty⟩

/-- Real-coordinate consistency survives actual lazy seed-cache growth; ideal values and predecessor closure are retained literally. -/
theorem valid_seedFrame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (state : State n)
    (seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n))
    (primitive : PqxdhRecordLiftWorld.Primitive) (mono : state.seeds.1 ≤ seeds.1)
    (scopeOK : TableScoped state)
    (valid : PqxdhRecordLiftChainOracle.Valid source (cachedSeeds state) ideal state.chain) :
    PqxdhRecordLiftChainOracle.Valid source (cachedSeeds (seedFrame state seeds primitive)) ideal state.chain := by
  refine ⟨valid.1, ?_⟩
  intro coordinate value real found
  exact (valid.2 coordinate value real found).trans
    (output_extension_agrees source state _ _ (cachedSeeds_extension state)
      (fun slot seed present => cachedSeeds_extension (seedFrame state seeds primitive) slot seed (mono present))
      coordinate (scopeOK coordinate value found))

/-- Actual lazy resolution preserves the mixed operational table invariant under its sampled cache extension. -/
theorem resolve_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (role : Role) (ref : KernelRef n) (state : State n) (good : TableGood source ideal state)
    (result : StoredKernel n × State n) (supported : result ∈ support ((resolve role ref).run state)) :
    TableGood source ideal result.2 := by
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
        valid_seedFrame source ideal state inner.1.2 _ mono good.1 good.2.1, good.2.2⟩

theorem markUsed_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (state : State n) (role : Role) (ref : KernelRef n) (good : TableGood source ideal state) :
    TableGood source ideal (markUsed state role ref) := by
  cases ref <;> exact good

theorem installBeacon_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (owner : Nat) (shell : BeaconShell) (ref : KernelRef n) (state : State n) (good : TableGood source ideal state)
    (result : Bool × State n) (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    TableGood source ideal result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact markUsed_tableGood source ideal inner.2 .beacon ref (resolve_tableGood source ideal .beacon ref state good inner member)
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact good

theorem installServer_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (state : State n) (good : TableGood source ideal state) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) : TableGood source ideal result.2 := by
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
        exact markUsed_tableGood source ideal inner.2 .server ref (resolve_tableGood source ideal .server ref state good inner member)
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact good

theorem initialize_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (created : PqxdhLiveServerConstruction.Created Unit) (state : State n) (good : TableGood source ideal state)
    (result : Unit × State n) (supported : result ∈ support ((initializeServer created).run state)) :
    TableGood source ideal result.2 := by
  simp only [initializeServer, StateT.run] at supported
  split at supported <;> simp only [support_pure, Set.mem_singleton_iff] at supported <;> subst result <;> exact good

theorem capability_tableGood (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (query : (CapabilitySpec n).Domain) (state : State n) (good : TableGood source ideal state)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : TableGood source ideal result.2 := by
  cases query with
  | installServer keyId identity ref => exact installServer_tableGood source ideal keyId identity ref state good result supported
  | installBeacon owner shell ref => exact installBeacon_tableGood source ideal owner shell ref state good result supported
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
    (ideal : Coordinate (Slot n) → Bool) (query : (EnvEffects n).Domain) (state : State n) (good : TableGood source ideal state)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) : TableGood source ideal result.2 := by
  cases query with
  | inl coin =>
      simp only [effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      exact good
  | inr request => exact capability_tableGood source ideal request (chargeEffect (.inr request) state) good result supported

theorem ownerRun_preserves {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (good : TableGood setup.source ideal state) (ready : StoredReady state.chain owner.kernel)
    (scopeOK : KernelScoped state owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (supported : result ∈ support (ownerRun (policy setup.source ideal) setup codec sender query owner state)) :
    OwnerFacts state (PqxdhRecordLiftChainOracle.Valid setup.source (cachedSeeds state) ideal)
      (state.chain, (state.primitive, [])) owner (ownerRawAfter query owner.rawAttempts) result := by
  exact ownerStep_preserves (cachedSeeds state) _ _ _
    (PqxdhRecordLiftLoggedAdapters.liftLookup_preserves _ _
      (PqxdhRecordLiftChainOracle.lookup_preserves setup.source (cachedSeeds state) ideal))
    state sender codec.frameRead query owner (state.chain, (state.primitive, [])) good.2.1 ready scopeOK result supported

/-- Every selected owner's actual mixed execution preserves table depth relative to its complete native KDF ledger. -/
theorem ownerRun_depth {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (good : TableGood setup.source ideal state) (ready : StoredReady state.chain owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × PqxdhRecordLiftLoggedAdapters.Frames))
    (supported : result ∈ support (ownerRun (policy setup.source ideal) setup codec sender query owner state)) :
    DepthBound result.2.1 (result.2.2.1.1.native .kdf) :=
  PqxdhRecordLiftMixedRecords.ownerStep_depth setup codec (cachedSeeds state) ideal sender codec.frameRead
    query owner (state.chain, (state.primitive, [])) good.2.1 ready good.2.2 result supported

theorem ownerRun_allowed {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : State n)
    (before : TableScoped state) (scopeOK : KernelScoped state owner.kernel)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) ×
      PqxdhRecordLiftChainCompiler.Execution (Slot n) (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (supported : result ∈ support (ownerRun (policy setup.source ideal) setup codec sender query owner state)) :
    PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) result.2.1 :=
  ownerStep_allowed (cachedSeeds state) _ _
    (PqxdhRecordLiftTableScope.liftLookup_writesOnly _ (PqxdhRecordLiftMixedRecords.lookup_writesOnly setup.source (cachedSeeds state) ideal))
    state sender codec.frameRead query owner (state.chain, (state.primitive, [])) before scopeOK result supported


/-- Persistent mixed table growth preserves every untouched dynamic record and carries the actual post-operation depth count. -/
theorem good_recordFrame (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (state : State n)
    (table : Table (Slot n)) (primitive : PqxdhRecordLiftWorld.Primitive)
    (good : Good source ideal state) (mono : state.chain ≤ table)
    (valid : PqxdhRecordLiftChainOracle.Valid source (cachedSeeds state) ideal table)
    (allowed : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) table)
    (depth : DepthBound table (primitive.1.native .kdf)) :
    Good source ideal (recordFrame state table primitive) :=
  ⟨scoped_same_records state _ le_rfl rfl rfl good.1,
    ready_frame state _ good.2.1 rfl rfl mono, allowed, valid, depth⟩

/-- The independent Server raw-attempt ghost cannot alter any kernel, seed or table certificate. -/
theorem good_serverRaw (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (state : State n) (server : Server n) (existing : state.server = some server)
    (rawAttempts : Nat) (good : Good source ideal state) :
    Good source ideal { state with server := some { server with rawAttempts := rawAttempts } } := by
  refine ⟨⟨?_, good.1.2⟩, ⟨?_, good.2.1.2⟩, good.2.2⟩
  · intro actual found keyId peer selected
    cases Option.some.inj found
    exact good.1.1 server existing keyId peer selected
  · intro actual found keyId peer selected
    cases Option.some.inj found
    exact good.2.1.1 server existing keyId peer selected

/-- Reinstalling one selected Beacon retains all operational invariants and every untouched record. -/
theorem beaconPublish_good {Reply : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (state : State n) (owner : Nat) (shell : BeaconShell) (beforeOwner : Owner n) (rawCount : Nat)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (good : Good source ideal state)
    (facts : OwnerFacts state (PqxdhRecordLiftChainOracle.Valid source (cachedSeeds state) ideal)
      (state.chain, (state.primitive, [])) beforeOwner rawCount result)
    (allowed : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) result.2.1)
    (depth : DepthBound result.2.1 (result.2.2.1.1.native .kdf)) :
    Good source ideal (beaconPublish state owner shell result).2 := by
  let framed := recordFrame state result.2.1 result.2.2.1
  have framedGood := good_recordFrame source ideal state result.2.1 result.2.2.1 good facts.2.1 facts.1 allowed depth
  exact ⟨scoped_owner_store framed owner (.established shell result.1.2.kernel) framedGood.1 facts.2.2.2.1,
    recordsSatisfy_owner_store (StoredReady result.2.1) framed owner (.established shell result.1.2.kernel)
      framedGood.2.1 facts.2.2.1, framedGood.2.2⟩

/-- Reinstalling one dynamic Server peer retains all operational invariants, including the independent raw count. -/
theorem serverPublish_good {Reply : Type} (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : Coordinate (Slot n) → Bool) (tag : PqxdhDeploymentInterface.FrameTag) (state : State n) (server : Server n)
    (existing : state.server = some server) (keyId : Std.U64) (peer : Peer n) (beforeOwner : Owner n) (rawCount : Nat)
    (result : (Reply × Owner n) × PqxdhRecordLiftChainCompiler.Execution (Slot n)
      (PqxdhRecordLiftWorld.Primitive × List PqxdhDeploymentNative.Frame))
    (good : Good source ideal state)
    (facts : OwnerFacts state (PqxdhRecordLiftChainOracle.Valid source (cachedSeeds state) ideal)
      (state.chain, (state.primitive, [])) beforeOwner rawCount result)
    (allowed : PqxdhRecordLiftTableScope.TableAllowed (SeedPresent state) result.2.1)
    (depth : DepthBound result.2.1 (result.2.2.1.1.native .kdf)) :
    Good source ideal (serverPublish tag state server keyId peer result).2 := by
  let framed := recordFrame state result.2.1 result.2.2.1
  have framedGood := good_recordFrame source ideal state result.2.1 result.2.2.1 good facts.2.1 facts.1 allowed depth
  let counted := { framed with server := some { server with rawAttempts := result.1.2.rawAttempts } }
  have countedGood := good_serverRaw source ideal framed server existing result.1.2.rawAttempts framedGood
  exact ⟨scoped_server_store counted { server with rawAttempts := result.1.2.rawAttempts } rfl keyId
      { peer with kernel := result.1.2.kernel } countedGood.1 facts.2.2.2.1,
    recordsSatisfy_server_store (StoredReady result.2.1) counted { server with rawAttempts := result.1.2.rawAttempts } rfl keyId
      { peer with kernel := result.1.2.kernel } countedGood.2.1 facts.2.2.1, countedGood.2.2⟩


/-- Every supported Beacon operation preserves the source-derived allocation, reference and control invariants. -/
theorem beaconStep_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State n) (good : Good setup.source ideal state)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep (policy setup.source ideal) setup codec owner query).run state)) :
    Good setup.source ideal result.2 := by
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
          exact beaconPublish_good setup.source ideal state owner shell (beaconOwner shell kernel (state.ownerRaw owner))
            (ownerRawAfter query (state.ownerRaw owner)) inner good
            (ownerRun_preserves setup codec ideal shell.identityKeyId query _ state good.2.2 ready scopeOK inner member)
            (ownerRun_allowed setup codec ideal shell.identityKeyId query _ state good.2.2.1 scopeOK inner member)
            (ownerRun_depth setup codec ideal shell.identityKeyId query _ state good.2.2 ready inner member)

/-- Every actual Server routing branch preserves the same invariant, with no selected-peer or successful-operation hypothesis. -/
theorem serverStep_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : State n) (good : Good setup.source ideal state)
    (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep (policy setup.source ideal) setup codec route query).run state)) :
    Good setup.source ideal result.2 := by
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
              exact serverPublish_good setup.source ideal _ state server existing keyId peer (serverOwner server keyId peer)
                server.rawAttempts inner good
                (ownerRun_preserves setup codec ideal server.sender (.inl plaintext) _ state good.2.2 ready scopeOK inner member)
                (ownerRun_allowed setup codec ideal server.sender (.inl plaintext) _ state good.2.2.1 scopeOK inner member)
                (ownerRun_depth setup codec ideal server.sender (.inl plaintext) _ state good.2.2 ready inner member)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [serverStep, StateT.run, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact good_serverRaw setup.source ideal state server existing (server.rawAttempts + 1) good
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact good_serverRaw setup.source ideal state server existing (server.rawAttempts + 1) good
              | some peer =>
                  simp only [serverStep, StateT.run, existing, routed, selected, support_map] at supported
                  obtain ⟨inner, member, rfl⟩ := supported
                  have ready := good.2.1.1 server existing keyId peer selected
                  have scopeOK := good.1.1 server existing keyId peer selected
                  exact serverPublish_good setup.source ideal _ state server existing keyId peer (serverOwner server keyId peer)
                    (server.rawAttempts + 1) inner good
                    (ownerRun_preserves setup codec ideal server.sender (.inr raw) _ state good.2.2 ready scopeOK inner member)
                    (ownerRun_allowed setup codec ideal server.sender (.inr raw) _ state good.2.2.1 scopeOK inner member)
                    (ownerRun_depth setup codec ideal server.sender (.inr raw) _ state good.2.2 ready inner member)


/-- Every actual private-world request preserves the invariant from which the local source interpretation laws are derived. -/
theorem handler_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : State n) (good : Good setup.source ideal state)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler (policy setup.source ideal) setup codec route query).run state)) :
    Good setup.source ideal result.2 := by
  cases query with
  | inl created =>
      exact ⟨initialize_scoped created state good.1 result supported,
        initialize_ready created state good.2.1 result supported,
        initialize_tableGood setup.source ideal created state good.2.2 result supported⟩
  | inr outer =>
      cases outer with
      | inl effect =>
          exact ⟨effects_scoped effect state good.1 result supported,
            effects_ready effect state good.2.1 result supported,
            effects_tableGood setup.source ideal effect state good.2.2 result supported⟩
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact serverStep_good setup codec ideal route (.inl send) state good result supported
              | inr raw => exact serverStep_good setup codec ideal route (.inr raw) state good result supported
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact beaconStep_good setup codec ideal owner (.inl plaintext) state good result supported
              | inr raw => exact beaconStep_good setup codec ideal owner (.inr raw) state good result supported

/-- Every actual supported adaptive execution retains the operational invariant; it is not postulated for future calls. -/
theorem schedule_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (state : State n) (good : Good setup.source ideal state)
    (result : Result × State n)
    (supported : result ∈ support ((simulateQ (handler (policy setup.source ideal) setup codec route) client).run state)) :
    Good setup.source ideal result.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact ih inner.1 inner.2 (handler_good setup codec ideal route query state good inner member) result continued

/-- In particular the invariant holds for every supported result of the frozen program, without an environment Frame hypothesis. -/
theorem run_good {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X : Type}
    (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run (policy setup.source ideal) setup codec route env serverKid bounds mode adversary)) :
    Good setup.source ideal result.2 :=
  schedule_good setup codec ideal route (program env setup.source.crypto codec serverKid bounds mode adversary)
    initial (initial_good setup.source ideal) result supported

/-- Every populated coordinate in the actual mixed program lies in the finite source range; the range counts all ordinary records, not only hidden ones. -/
theorem run_depth {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run (policy setup.source ideal) setup codec route env serverKid bounds mode adversary)) :
    DepthBound result.2.chain (budget.sends + 51 * budget.receives) :=
  depth_mono result.2.chain
    (run_good setup codec ideal route env serverKid bounds mode adversary result supported).2.2.2.2
    (run_kdf setup codec ideal route env serverKid bounds mode budget adversary respects result supported)

/-- The all-real endpoint is exactly the frozen literal native KDF policy, including its call accounting. -/
theorem policy_real {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    policy (n := n) setup.source (fun _ => false) = realPolicy setup codec := by
  funext seeds
  exact PqxdhRecordLiftChainOracle.lookup_source setup codec seeds

/-- The exact key-free protocol factor inherits all mixed operational facts at completed request boundaries. Private state remains internal to this theorem. -/
theorem protocol_run_good {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X)
    (result : (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftProtocol.Control n) × PqxdhRecordLiftProtocol.Private n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.run (policy setup.source ideal)
      setup codec route env serverKid bounds mode adversary)) :
    Good setup.source ideal (PqxdhRecordLiftProtocol.join result.1.2 result.2) := by
  rw [PqxdhRecordLiftProtocol.run_factor, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact run_good setup codec ideal route env serverKid bounds mode adversary inner member

/-- The actual key-free protocol interpretation has the same executed KDF cap and finite table range; no private counter is returned to its client. -/
theorem protocol_run_bounds {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (ideal : Coordinate (Slot n) → Bool) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (result : (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × PqxdhRecordLiftProtocol.Control n) × PqxdhRecordLiftProtocol.Private n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.run (policy setup.source ideal)
      setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.native .kdf ≤ budget.sends + 51 * budget.receives ∧
      DepthBound result.2.chain (budget.sends + 51 * budget.receives) := by
  rw [PqxdhRecordLiftProtocol.run_factor, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact ⟨run_kdf setup codec ideal route env serverKid bounds mode budget adversary respects inner member,
    run_depth setup codec ideal route env serverKid bounds mode budget adversary respects inner member⟩

end BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.server_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.server_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.beacon_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.beacon_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.resolve_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.resolve_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.install_server_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.install_server_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.install_beacon_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.install_beacon_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.capability_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.capability_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.effects_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.effects_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.handler_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.handler_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.schedule_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.schedule_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.run_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.run_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.initial_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.initial_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.valid_seedFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.valid_seedFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.resolve_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.resolve_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.markUsed_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.markUsed_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.installBeacon_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.installBeacon_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.installServer_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.installServer_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.initialize_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.initialize_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.capability_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.capability_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.effects_tableGood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.effects_tableGood

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_preserves

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_allowed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.ownerRun_allowed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.good_recordFrame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.good_recordFrame

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.good_serverRaw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.good_serverRaw

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.beaconPublish_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.beaconPublish_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.serverPublish_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.serverPublish_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.beaconStep_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.beaconStep_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.serverStep_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.serverStep_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.handler_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.handler_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.schedule_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.schedule_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.run_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.run_depth' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.run_depth

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.policy_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.policy_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.protocol_run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.protocol_run_good

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.protocol_run_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftMixedWorld.protocol_run_bounds

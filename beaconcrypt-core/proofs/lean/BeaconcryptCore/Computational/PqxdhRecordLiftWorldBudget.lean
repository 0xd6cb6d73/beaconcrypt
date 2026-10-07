-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorld
import BeaconcryptCore.Computational.PqxdhRecordLiftBudget
import BeaconcryptCore.Computational.PqxdhDeploymentCompileBudget

/-! Actual supported counter bounds for the executable record world. Native primitive calls, direct effects and underlying uniform draws have separate ledgers. No cryptographic or source-reachability premise is introduced. -/

open OracleComp OracleSpec CoreModels Aeneas
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget

open Classical

/-- Two selectively bounded request classes pay their own costs; all remaining requests cost zero. -/
theorem weighted_support {ι State Result : Type} {spec : OracleSpec ι}
    (first second : spec.Domain → Prop) [DecidablePred first] [DecidablePred second]
    (disjoint : ∀ query, first query → ¬ second query)
    (impl : QueryImpl spec (StateT State ProbComp)) (metric : State → Nat)
    (firstCost secondCost : Nat)
    (step : ∀ query state result, result ∈ support ((impl query).run state) →
      metric result.2 ≤ metric state +
        (if first query then firstCost else if second query then secondCost else 0))
    (client : OracleComp spec Result) (firstBound secondBound : Nat)
    (boundedFirst : client.IsQueryBoundP first firstBound)
    (boundedSecond : client.IsQueryBoundP second secondBound)
    (state : State) (result : Result × State)
    (supported : result ∈ support ((simulateQ impl client).run state)) :
    metric result.2 ≤ metric state + firstCost * firstBound + secondCost * secondBound := by
  induction client using OracleComp.inductionOn generalizing firstBound secondBound state result
  case query_bind query next ih =>
    simp only [isQueryBoundP_query_bind_iff, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at boundedFirst boundedSecond supported
    obtain ⟨middle, headSupport, tailSupport⟩ := supported
    have costs := And.intro (step query state middle headSupport)
      (ih middle.1 _ _ (boundedFirst.2 middle.1) (boundedSecond.2 middle.1)
        middle.2 result tailSupport)
    by_cases isFirst : first query
    · obtain ⟨left, rfl⟩ : ∃ left, firstBound = left + 1 :=
        ⟨firstBound - 1, (Nat.sub_add_cancel (boundedFirst.1.resolve_left (not_not.mpr isFirst))).symm⟩
      simp only [isFirst, disjoint query isFirst, ite_true, ite_false,
        Nat.add_sub_cancel_right, Nat.mul_add, Nat.mul_one] at costs ⊢
      omega
    · by_cases isSecond : second query
      · obtain ⟨left, rfl⟩ : ∃ left, secondBound = left + 1 :=
          ⟨secondBound - 1, (Nat.sub_add_cancel (boundedSecond.1.resolve_left (not_not.mpr isSecond))).symm⟩
        simp only [isFirst, isSecond, ite_true, ite_false,
          Nat.add_sub_cancel_right, Nat.mul_add, Nat.mul_one] at costs ⊢
        omega
      · simp only [isFirst, isSecond, ite_false, Nat.add_zero] at costs
        omega
  case pure value =>
    simp_all
    omega

open PqxdhServerAuthExperiment (Setup Codec)

/-- The literal native interpreter increments its selected call counter within the supplied source cap. -/
theorem native_support {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result) (kind : RawCtxMixedOwner.CallKind)
    (bound : Nat) (bounded : client.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = kind) bound)
    (state : PqxdhRecordLiftWorld.Primitive) (result : Result × PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.primitives setup codec) client).run state)) :
    result.2.1.native kind ≤ state.1.native kind + bound := by
  refine (weighted_support (fun query => RawCtxMixedOwner.callKind query = kind) (fun _ => False)
    (fun _ _ => not_false) (PqxdhRecordLiftWorld.primitives setup codec) (fun state => state.1.native kind)
    1 0 ?_ client bound 0 bounded (isQueryBoundP_false client 0) state result supported).trans ?_
  · intro query before after reached
    simp only [PqxdhRecordLiftWorld.primitives, StateT.run, bind_pure_comp, support_map] at reached
    obtain ⟨inner, _, rfl⟩ := reached
    by_cases same : RawCtxMixedOwner.callKind query = kind
    · simp [same]
    · simp [same, Function.update_of_ne (Ne.symm same)]
  · simp

open PqxdhRecordLiftWorld (countCoin)

/-- The actual uniform-byte sampler makes exactly one underlying query. -/
theorem sample_byte (count : Nat) :
    (simulateQ countCoin ($ᵗ UInt8)).run count =
      (fun byte => (byte, count + 1)) <$> ($ᵗ UInt8) := by
  change (simulateQ countCoin
    ((@FinEnum.equiv UInt8 FinEnum.instUInt8).symm <$>
      ($[0..255] : ProbComp (Fin 256)))).run count =
    (fun byte => (byte, count + 1)) <$>
      ((@FinEnum.equiv UInt8 FinEnum.instUInt8).symm <$>
        ($[0..255] : ProbComp (Fin 256)))
  rw [simulateQ_map, StateT.run_map]
  simp only [ProbComp.uniformFin, simulateQ_spec_query, StateT.run, countCoin,
    Functor.map_map]
  rfl

/-- Sampling a byte vector makes one underlying query for each entry. -/
theorem sample_vector (length count : Nat) :
    (simulateQ countCoin ($ᵗ Vector UInt8 length)).run count =
      (fun bytes => (bytes, count + length)) <$> ($ᵗ Vector UInt8 length) := by
  induction length generalizing count with
  | zero => rfl
  | succ length ih =>
    change (simulateQ countCoin
      (Vector.push <$> ($ᵗ Vector UInt8 length) <*> ($ᵗ UInt8))).run count =
      (fun bytes => (bytes, count + (length + 1))) <$>
        (Vector.push <$> ($ᵗ Vector UInt8 length) <*> ($ᵗ UInt8))
    simp only [seq_eq_bind_map, bind_map_left, simulateQ_bind, StateT.run_bind,
      ih, simulateQ_map, StateT.run_map, sample_byte, Functor.map_map, Nat.add_assoc]
    simp only [map_bind, Functor.map_map]

/-- Fixed-width source byte strings have the same exact sampler count. -/
theorem sample_fixed_bytes (length count : Nat) :
    (simulateQ countCoin ($ᵗ List.Vector UInt8 length)).run count =
      (fun bytes => (bytes, count + length)) <$> ($ᵗ List.Vector UInt8 length) := by
  change (simulateQ countCoin
    (List.Vector.ofFn <$>
      ((fun (bytes : Vector UInt8 length) (index : Fin length) => bytes.get index) <$>
        ($ᵗ Vector UInt8 length)))).run count =
    (fun bytes => (bytes, count + length)) <$>
      (List.Vector.ofFn <$>
        ((fun (bytes : Vector UInt8 length) (index : Fin length) => bytes.get index) <$>
          ($ᵗ Vector UInt8 length)))
  simp only [simulateQ_map, StateT.run_map, sample_vector, Functor.map_map]

/-- The actual pair sampler for a registration seed makes exactly sixty-four uniform queries. -/
theorem sample_seed (count : Nat) :
    (simulateQ countCoin ($ᵗ PqxdhRecordLiftSeed.Seed)).run count =
      (fun seed => (seed, count + 64)) <$> ($ᵗ PqxdhRecordLiftSeed.Seed) := by
  change (simulateQ countCoin
    ((·, ·) <$> ($ᵗ List.Vector UInt8 32) <*> ($ᵗ List.Vector UInt8 32))).run count =
    (fun seed => (seed, count + 64)) <$>
      ((·, ·) <$> ($ᵗ List.Vector UInt8 32) <*> ($ᵗ List.Vector UInt8 32))
  simp only [seq_eq_bind_map, bind_map_left, simulateQ_bind, StateT.run_bind,
    sample_fixed_bytes, simulateQ_map, StateT.run_map, Functor.map_map, map_bind,
    Nat.add_assoc]

open PqxdhRecordLiftInterface PqxdhRecordLiftWorld

/-- A seed-cache miss retains the complete World state and charges exactly sixty-four uniform queries. -/
theorem resolve_miss_count {n : Nat} (role : Role) (slot : Slot n) (state : State n)
    (missing : state.seeds.1 slot = none) :
    (resolve role (.hidden slot)).run state =
      (fun seed => (kernel role seed, { state with
        seeds := (state.seeds.1.cacheQuery slot seed,
          ⟨state.seeds.2.lookups + 1, state.seeds.2.draws + 1⟩)
        primitive := ({ state.primitive.1 with uniform := state.primitive.1.uniform + 64 },
          state.primitive.2) })) <$> ($ᵗ PqxdhRecordLiftSeed.Seed) := by
  rw [resolve_miss role slot state missing, sample_seed, Functor.map_map]

/-- An actual Server attempt inherits its source cap, including absent peers and rejected raw inputs. -/
theorem server_native {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (kind : RawCtxMixedOwner.CallKind) (state : State n)
    (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep setup codec route query).run state)) :
    result.2.primitive.1.native kind ≤ state.primitive.1.native kind +
      (match query with
       | .inl _ => RawCtxMixedOwner.sendCost kind
       | .inr _ => RawCtxMixedOwner.receiveCost kind) := by
  cases server : state.server with
  | none =>
    cases query <;>
      simp only [serverStep, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact Nat.le_add_right _ _
  | some current =>
    simp only [serverStep, StateT.run, server, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply native_support setup codec _ kind _ ?_ state.primitive inner reached
    apply PqxdhDeploymentCompileBudget.logged_bound
    cases query with
    | inl send => exact RawCtxServerMixed.send_bound _ send.1 send.2 _ kind
    | inr raw => exact RawCtxServerMixed.raw_bound route codec.frameRead raw _ kind

/-- An actual Beacon attempt inherits its source cap for every phase, including inactive and absent owners. -/
theorem beacon_native {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (kind : RawCtxMixedOwner.CallKind) (state : State n)
    (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep setup codec owner query).run state)) :
    result.2.primitive.1.native kind ≤ state.primitive.1.native kind +
      (match query with
       | .inl _ => RawCtxMixedOwner.sendCost kind
       | .inr _ => RawCtxMixedOwner.receiveCost kind) := by
  cases found : state.owners[owner]? with
  | none =>
    simp only [beaconStep, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | some phase =>
    simp only [beaconStep, StateT.run, found, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    apply native_support setup codec _ kind _ ?_ state.primitive inner reached
    cases query <;> exact PqxdhDeploymentCompileBudget.logged_bound _ _ _ []
      (PqxdhRecordLiftBeacon.handler_bound codec.frameRead _ _ kind)

/-- Hidden resolution changes neither native-call nor direct-effect counts. -/
theorem resolve_counters {n : Nat} (role : Role) (ref : KernelRef n) (state : State n)
    (result : ConcreteRatchetKernel × State n)
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
theorem install_server_counters {n : Nat} (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
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
theorem install_beacon_counters {n : Nat} (owner : Nat) (shell : BeaconShell)
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
theorem capability_counters {n : Nat} (query : (CapabilitySpec n).Domain) (state : State n)
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
theorem effects_counters {n : Nat} (query : (EnvEffects n).Domain) (state : State n)
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

open PqxdhRecordLiftBudget

/-- Only record requests incur native costs, with separate send and receive weights. -/
theorem handler_native {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (kind : RawCtxMixedOwner.CallKind) (state : State n)
    (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler setup codec route query).run state)) :
    result.2.primitive.1.native kind ≤ state.primitive.1.native kind +
      (if WorldRecord .send query then RawCtxMixedOwner.sendCost kind
       else if WorldRecord .raw query then RawCtxMixedOwner.receiveCost kind else 0) := by
  cases query with
  | inl created =>
    cases server : state.server <;>
      simp only [handler, initializeServer, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact Nat.le_add_right _ _
  | inr outer =>
    cases outer with
    | inl effect =>
      have same := congrArg (fun counts => counts.1 kind) (effects_counters effect state result supported)
      simpa [WorldRecord, chargeEffect] using same.le
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send => simpa [WorldRecord, recordKind] using server_native setup codec route (.inl send) kind state result supported
        | inr raw => simpa [WorldRecord, recordKind] using server_native setup codec route (.inr raw) kind state result supported
      | inr ownerQuery =>
        rcases ownerQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext => simpa [WorldRecord, recordKind] using beacon_native setup codec owner (.inl plaintext) kind state result supported
        | inr raw => simpa [WorldRecord, recordKind] using beacon_native setup codec owner (.inr raw) kind state result supported

/-- Arbitrary adaptive World schedules obey the two literal source weights. -/
theorem schedule_native {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) X)
    (kind : RawCtxMixedOwner.CallKind) (sends receives : Nat)
    (sendBound : client.IsQueryBoundP (WorldRecord .send) sends)
    (rawBound : client.IsQueryBoundP (WorldRecord .raw) receives)
    (state : State n) (result : X × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route) client).run state)) :
    result.2.primitive.1.native kind ≤ state.primitive.1.native kind +
      RawCtxMixedOwner.sendCost kind * sends + RawCtxMixedOwner.receiveCost kind * receives := by
  apply weighted_support (WorldRecord .send) (WorldRecord .raw) ?_
    (handler setup codec route) (fun state => state.primitive.1.native kind)
    (RawCtxMixedOwner.sendCost kind) (RawCtxMixedOwner.receiveCost kind)
    (fun query state result reached => handler_native setup codec route query kind state result reached)
    client sends receives sendBound rawBound state result supported
  rintro (created | (effect | record)) first second
  · exact first
  · exact first
  · exact RecordKind.noConfusion (first.symm.trans second)

open PqxdhDeploymentInterface

/-- The executed open program obeys every native source-call cap with only the outer adversary budget. -/
theorem run_native {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget)
    (adversary : OracleComp (ModeSpec mode) X) (respects : budget.Respects adversary)
    (kind : RawCtxMixedOwner.CallKind)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.native kind ≤
      RawCtxMixedOwner.sendCost kind * budget.sends + RawCtxMixedOwner.receiveCost kind * budget.receives := by
  simpa only [initial, Counts.empty, Nat.zero_add] using schedule_native setup codec route _ kind budget.sends budget.receives
    (program_record_bound env setup.source.crypto codec serverKid bounds mode budget adversary respects .send)
    (program_record_bound env setup.source.crypto codec serverKid bounds mode budget adversary respects .raw)
    initial result supported

/-- Actual ordinary-record KDF calls obey the frozen derivation formula; no Frame premise is needed. -/
theorem run_kdf {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps)
    (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.native .kdf ≤ caps.derivations := by
  simpa only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost, Nat.one_mul,
    Caps.derivations] using run_native setup codec route env serverKid bounds mode caps.outer
      adversary respects .kdf result supported

/-- Interpreting any native program preserves the separate direct-effect counter function. -/
theorem native_effects {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (state : Primitive) (result : X × Primitive)
    (supported : result ∈ support ((simulateQ (primitives setup codec) client).run state)) :
    result.2.1.effects = state.1.effects := by
  refine simulateQ_run_preservesInv (primitives setup codec)
    (fun current => current.1.effects = state.1.effects) ?_ client state rfl result supported
  intro query before unchanged after reached
  simp only [primitives, StateT.run, bind_pure_comp, support_map] at reached
  obtain ⟨inner, _, rfl⟩ := reached
  exact unchanged

/-- Server record execution leaves direct-effect accounting unchanged. -/
theorem server_effects {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State n) (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep setup codec route query).run state)) :
    result.2.primitive.1.effects = state.primitive.1.effects := by
  cases server : state.server with
  | none =>
    cases query <;>
      simp only [serverStep, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> rfl
  | some current =>
    simp only [serverStep, StateT.run, server, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact native_effects setup codec _ state.primitive inner reached

/-- Beacon record execution leaves direct-effect accounting unchanged. -/
theorem beacon_effects {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State n) (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep setup codec owner query).run state)) :
    result.2.primitive.1.effects = state.primitive.1.effects := by
  cases found : state.owners[owner]? with
  | none =>
    simp only [beaconStep, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | some phase =>
    simp only [beaconStep, StateT.run, found, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact native_effects setup codec _ state.primitive inner reached

/-- One World request increases a direct-effect counter only when it belongs to that exact effect class. -/
theorem handler_effects {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (kind : EffectKind) (state : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler setup codec route query).run state)) :
    result.2.primitive.1.effects kind ≤ state.primitive.1.effects kind +
      (if WorldEffect kind query then 1 else 0) := by
  cases query with
  | inl created =>
    cases server : state.server <;>
      simp only [handler, initializeServer, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact Nat.le_add_right _ _
  | inr outer =>
    cases outer with
    | inl effect =>
      have same := congrArg (fun counts => counts.2 kind) (effects_counters effect state result supported)
      by_cases matching : effectKind effect = kind
      · simpa [WorldEffect, chargeEffect, matching] using same.le
      · simpa [WorldEffect, chargeEffect, matching, Function.update_of_ne (Ne.symm matching)] using same.le
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send => simpa [WorldEffect] using (congrFun (server_effects setup codec route (.inl send) state result supported) kind).le
        | inr raw => simpa [WorldEffect] using (congrFun (server_effects setup codec route (.inr raw) state result supported) kind).le
      | inr ownerQuery =>
        rcases ownerQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext => simpa [WorldEffect] using (congrFun (beacon_effects setup codec owner (.inl plaintext) state result supported) kind).le
        | inr raw => simpa [WorldEffect] using (congrFun (beacon_effects setup codec owner (.inr raw) state result supported) kind).le

/-- Structural effect-request bounds control the actual final direct-effect counter. -/
theorem schedule_effects {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) X)
    (kind : EffectKind) (bound : Nat) (bounded : client.IsQueryBoundP (WorldEffect kind) bound)
    (state : State n) (result : X × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route) client).run state)) :
    result.2.primitive.1.effects kind ≤ state.primitive.1.effects kind + bound := by
  simpa only [Nat.one_mul, Nat.zero_mul, Nat.add_zero] using
    weighted_support (WorldEffect kind) (fun _ => False) (fun _ _ => not_false)
      (handler setup codec route) (fun state => state.primitive.1.effects kind) 1 0
      (fun query state result reached => by simpa using handler_effects setup codec route query kind state result reached)
      client bound 0 bounded (isQueryBoundP_false client 0) state result supported

/-- Frame and the outer budget bound the actual direct-effect counters, with startup charged separately. -/
theorem run_effects {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary)
    (kind : EffectKind)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.effects kind ≤
      startupCost startupCoins kind + (directCost caps.outer bounds kind + caps.envTotal allowance kind) := by
  simpa only [initial, Counts.empty, Nat.zero_add] using schedule_effects setup codec route _ kind _
    (program_bound env startupCoins allowance framed setup.source.crypto codec serverKid bounds mode caps
      adversary respects kind) initial result supported

/-- Both actual routes to the shared hash oracle fit the literal public, record and environment allowance. -/
theorem run_hash {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
      caps.outer.hash + caps.outer.sends + caps.outer.receives + caps.envTotal allowance .hash := by
  have nativeBound := run_native setup codec route env serverKid bounds mode caps.outer
    adversary respects .hash result supported
  have effectBound := run_effects setup codec route env serverKid bounds mode caps
    startupCoins allowance framed adversary respects .hash result supported
  simp only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost, Nat.one_mul,
    startupCost, directCost, Nat.zero_add] at nativeBound effectBound
  omega

/-- A genuine total-query bound controls the actual underlying uniform counter. -/
theorem uniform_support {X : Type} (work : ProbComp X) (bound : Nat)
    (bounded : work.IsTotalQueryBound bound) (count : Nat) (result : X × Nat)
    (supported : result ∈ support ((simulateQ countCoin work).run count)) :
    result.2 ≤ count + bound := by
  simpa only [id_eq, Nat.one_mul, Nat.zero_mul, Nat.add_zero] using
    weighted_support (fun _ => True) (fun _ => False) (fun _ _ => not_false)
      countCoin id 1 0 (fun query before after reached => by
        simp only [countCoin, StateT.run, support_map] at reached
        obtain ⟨inner, _, rfl⟩ := reached
        exact le_refl _)
      work bound 0 ((isQueryBoundP_true_iff work bound).2 bounded)
      (isQueryBoundP_false work 0) count result supported

/-- The actual source primitive draws randomness only for a shared-hash miss, bounded by its sixty-four-byte reply. -/
theorem primitive_uniform_bound {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (cache : CtxRomAuth.CtxRO.QueryCache) :
    ((PqxdhDeploymentNative.primitives setup codec query).run ((), cache)).IsTotalQueryBound
      (64 * if RawCtxMixedOwner.callKind query = .hash then 1 else 0) := by
  have bounded := RawCtxMixedShared.shared_uniform setup.source.crypto codec.frameWrite
    (RawCtxSourceHkdf.kdfImpl setup.source) 0 (RawCtxSourceHkdf.kdf_uniform setup.source)
    (RawCtxMixedOwner.NativeSpec.query query) 1
    (if RawCtxMixedOwner.callKind query = .hash then 1 else 0)
    (by simp [isQueryBoundP_query_iff])
    (by by_cases matching : RawCtxMixedOwner.callKind query = .hash <;>
        simp [isQueryBoundP_query_iff, matching]) ((), cache)
  simpa only [PqxdhDeploymentNative.primitives, simulateQ_spec_query, Nat.zero_mul, Nat.zero_add] using bounded

/-- Literal native uniform increments are paid by the literal native hash-call increments. -/
theorem primitive_uniform {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : Primitive)
    (result : RawCtxMixedOwner.NativeSpec.Range query × Primitive)
    (supported : result ∈ support ((primitives setup codec query).run state)) :
    result.2.1.uniform + 64 * state.1.native .hash ≤
      state.1.uniform + 64 * result.2.1.native .hash := by
  simp only [primitives, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have bound := uniform_support _ _ (primitive_uniform_bound setup codec query state.2)
    state.1.uniform inner reached
  by_cases matching : RawCtxMixedOwner.callKind query = .hash
  · simp only [matching, ite_true, Nat.mul_one, Function.update_self] at bound ⊢
    omega
  · simp only [matching, ite_false, Nat.mul_zero, Nat.add_zero,
      Function.update_of_ne (Ne.symm matching)] at bound ⊢
    omega

/-- Every supported native execution pays its uniform work from its actual hash-call count. -/
theorem native_uniform {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (client : OracleComp RawCtxMixedOwner.NativeSpec X) (state : Primitive) (result : X × Primitive)
    (supported : result ∈ support ((simulateQ (primitives setup codec) client).run state)) :
    result.2.1.uniform + 64 * state.1.native .hash ≤
      state.1.uniform + 64 * result.2.1.native .hash := by
  refine simulateQ_run_preservesInv (primitives setup codec)
    (fun current => current.1.uniform + 64 * state.1.native .hash ≤
      state.1.uniform + 64 * current.1.native .hash) ?_ client state (le_refl _) result supported
  intro query before invariant after reached
  have bound := primitive_uniform setup codec query before after reached
  omega

/-- Hidden resolution pays all of its actual uniform work from its own fresh-seed counter. -/
theorem resolve_uniform {n : Nat} (role : Role) (ref : KernelRef n) (state : State n)
    (result : ConcreteRatchetKernel × State n)
    (supported : result ∈ support ((resolve role ref).run state)) :
    result.2.primitive.1.uniform + 64 * state.seeds.2.draws ≤
      state.primitive.1.uniform + 64 * result.2.seeds.2.draws := by
  cases ref with
  | known known =>
    simp only [resolve, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | hidden slot =>
    cases cached : state.seeds.1 slot with
    | none =>
      rw [resolve_miss_count role slot state cached, support_map] at supported
      obtain ⟨seed, _, rfl⟩ := supported
      simp only
      omega
    | some seed =>
      rw [resolve_hit role slot state seed cached, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact le_refl _

/-- All Server admission branches pay uniform work solely from fresh hidden-seed draws. -/
theorem install_server_uniform {n : Nat} (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) :
    result.2.primitive.1.uniform + 64 * state.seeds.2.draws ≤
      state.primitive.1.uniform + 64 * result.2.seeds.2.draws := by
  cases server : state.server with
  | none =>
    simp only [installServer, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | some current =>
    simp only [installServer, StateT.run, server] at supported
    split_ifs at supported
    · simp only [bind_pure_comp, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      have bound := resolve_uniform .server ref state inner reached
      cases ref <;> exact bound
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact le_refl _

/-- All Beacon admission branches pay uniform work solely from fresh hidden-seed draws. -/
theorem install_beacon_uniform {n : Nat} (owner : Nat) (shell : BeaconShell)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    result.2.primitive.1.uniform + 64 * state.seeds.2.draws ≤
      state.primitive.1.uniform + 64 * result.2.seeds.2.draws := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have bound := resolve_uniform .beacon ref state inner reached
    cases ref <;> exact bound
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _

/-- A restricted capability draws only fresh seed bytes or at most one hash reply. -/
theorem capability_uniform {n : Nat} (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) :
    result.2.primitive.1.uniform + 64 * state.seeds.2.draws ≤
      state.primitive.1.uniform + 64 * result.2.seeds.2.draws +
        (if effectKind (.inr query) = .hash then 64 else 0) := by
  cases query with
  | installServer keyId identity ref =>
    simpa [effectKind] using install_server_uniform keyId identity ref state result supported
  | installBeacon owner shell ref =>
    simpa [effectKind] using install_beacon_uniform owner shell ref state result supported
  | peerPresent keyId | ownerPresent owner | appendOwner sender pin phase =>
    simp only [capability, StateT.run, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact Nat.le_add_right _ _
  | hash bytes =>
    simp only [capability, sampled, StateT.run, bind_pure_comp, Functor.map_map, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have bound := uniform_support _ 64
      (CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.primitive.2)
      state.primitive.1.uniform inner reached
    simp only [effectKind, ite_true]
    omega
  | advanceOwner owner phase =>
    simp only [capability, StateT.run] at supported
    split at supported
    · split_ifs at supported <;>
        simp only [support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact Nat.le_add_right _ _
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Nat.le_add_right _ _

/-- Actual call counters supply credit for underlying uniform work; seed draws remain a separate term. -/
def uniformCredit {n : Nat} (state : State n) : Nat :=
  state.primitive.1.effects .coin +
    64 * (state.primitive.1.effects .hash + state.primitive.1.native .hash + state.seeds.2.draws)

/-- Direct coins and restricted capabilities respect the literal uniform ledger. -/
theorem effects_uniform {n : Nat} (query : (EnvEffects n).Domain) (state : State n)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((effects query).run state)) :
    result.2.primitive.1.uniform + uniformCredit state ≤
      state.primitive.1.uniform + uniformCredit result.2 := by
  cases query with
  | inl coin =>
    simp only [effects, sampled, simulateQ_spec_query, countCoin, StateT.run,
      bind_pure_comp, Functor.map_map, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    simp [uniformCredit, chargeEffect, effectKind]
    omega
  | inr request =>
    have counters := capability_counters request (chargeEffect (.inr request) state) result supported
    have nativeSame := congrArg (fun counts => counts.1 .hash) counters
    have coinSame := congrArg (fun counts => counts.2 .coin) counters
    have hashSame := congrArg (fun counts => counts.2 .hash) counters
    have bound := capability_uniform request (chargeEffect (.inr request) state) result supported
    simp only [uniformCredit]
    cases request <;> simp [chargeEffect, effectKind] at bound nativeSame coinSame hashSame ⊢ <;> omega

/-- Actual Server execution preserves the combined uniform-credit inequality. -/
theorem server_uniform {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (state : State n) (result : RawCtxServerMixed.SourceSpec.Range query × State n)
    (supported : result ∈ support ((serverStep setup codec route query).run state)) :
    result.2.primitive.1.uniform + uniformCredit state ≤
      state.primitive.1.uniform + uniformCredit result.2 := by
  cases server : state.server with
  | none =>
    cases query <;>
      simp only [serverStep, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact le_refl _
  | some current =>
    simp only [serverStep, StateT.run, server, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have bound := native_uniform setup codec _ state.primitive inner reached
    have coins := congrFun (native_effects setup codec _ state.primitive inner reached) .coin
    have hashes := congrFun (native_effects setup codec _ state.primitive inner reached) .hash
    simp only [uniformCredit, produce]
    omega

/-- Actual Beacon execution preserves the combined uniform-credit inequality. -/
theorem beacon_uniform {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State n) (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
    (supported : result ∈ support ((beaconStep setup codec owner query).run state)) :
    result.2.primitive.1.uniform + uniformCredit state ≤
      state.primitive.1.uniform + uniformCredit result.2 := by
  cases found : state.owners[owner]? with
  | none =>
    simp only [beaconStep, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_refl _
  | some phase =>
    simp only [beaconStep, StateT.run, found, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have bound := native_uniform setup codec _ state.primitive inner reached
    have coins := congrFun (native_effects setup codec _ state.primitive inner reached) .coin
    have hashes := congrFun (native_effects setup codec _ state.primitive inner reached) .hash
    simp only [uniformCredit, produce]
    omega

/-- Every World request respects the same uniform ledger, without a supplied reachability invariant. -/
theorem handler_uniform {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler setup codec route query).run state)) :
    result.2.primitive.1.uniform + uniformCredit state ≤
      state.primitive.1.uniform + uniformCredit result.2 := by
  cases query with
  | inl created =>
    cases server : state.server <;>
      simp only [handler, initializeServer, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> exact le_refl _
  | inr outer =>
    cases outer with
    | inl effect => exact effects_uniform effect state result supported
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send => exact server_uniform setup codec route (.inl send) state result supported
        | inr raw => exact server_uniform setup codec route (.inr raw) state result supported
      | inr ownerQuery =>
        rcases ownerQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext => exact beacon_uniform setup codec owner (.inl plaintext) state result supported
        | inr raw => exact beacon_uniform setup codec owner (.inr raw) state result supported

/-- Actual uniform accounting survives every adaptive World continuation. -/
theorem schedule_uniform {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) X)
    (state : State n) (result : X × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route) client).run state)) :
    result.2.primitive.1.uniform + uniformCredit state ≤
      state.primitive.1.uniform + uniformCredit result.2 := by
  refine simulateQ_run_preservesInv (handler setup codec route)
    (fun current => current.primitive.1.uniform + uniformCredit state ≤
      state.primitive.1.uniform + uniformCredit current) ?_ client state (le_refl _) result supported
  intro query before invariant after reached
  have bound := handler_uniform setup codec route query before after reached
  omega

/-- Starting from the actual empty World, the returned counters themselves bound all underlying uniform draws. -/
theorem run_uniform_counts {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.uniform ≤ result.2.primitive.1.effects .coin +
      64 * (result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash) +
      64 * result.2.seeds.2.draws := by
  have bound := schedule_uniform setup codec route _ initial result supported
  simpa [uniformCredit, initial, Counts.empty, PqxdhRecordLiftLazyTable.initial,
    Nat.mul_add, Nat.add_assoc] using bound

/-- Finite seed-cache occupancy records slots, independently of any coincidences between sampled bytes. -/
def cachedSlots {n : Nat} (cache : (SeedSpec n).QueryCache) : Finset (Slot n) :=
  Finset.univ.filter fun slot => (cache slot).isSome

/-- A missing-slot insertion increases occupancy by exactly one. -/
theorem cachedSlots_miss {n : Nat} (cache : (SeedSpec n).QueryCache) (slot : Slot n)
    (seed : PqxdhRecordLiftSeed.Seed) (missing : cache slot = none) :
    (cachedSlots (cache.cacheQuery slot seed)).card = (cachedSlots cache).card + 1 := by
  have inserted : cachedSlots (cache.cacheQuery slot seed) = insert slot (cachedSlots cache) := by
    ext candidate
    by_cases same : candidate = slot
    · subst candidate
      simp [cachedSlots]
    · simp [cachedSlots, QueryCache.cacheQuery_of_ne, same]
  rw [inserted]
  simp [cachedSlots, missing]

/-- Seed occupancy cannot exceed the declared finite slot count. -/
theorem cachedSlots_bound {n : Nat} (cache : (SeedSpec n).QueryCache) :
    (cachedSlots cache).card ≤ n := by
  simpa [Slot, cachedSlots] using Finset.card_le_card (Finset.filter_subset
    (fun slot : Slot n => (cache slot).isSome) Finset.univ)

/-- Draw increments equal newly occupied slots, also from an arbitrary initial cache. -/
def SeedAccounting {n : Nat} (before after : State n) : Prop :=
  after.seeds.2.draws + (cachedSlots before.seeds.1).card =
    before.seeds.2.draws + (cachedSlots after.seeds.1).card

/-- The actual hidden hit/miss branches preserve exact seed draw-to-occupancy accounting. -/
theorem resolve_seed_accounting {n : Nat} (role : Role) (ref : KernelRef n) (state : State n)
    (result : ConcreteRatchetKernel × State n)
    (supported : result ∈ support ((resolve role ref).run state)) :
    SeedAccounting state result.2 := by
  cases ref with
  | known known =>
    simp only [resolve, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | hidden slot =>
    cases cached : state.seeds.1 slot with
    | none =>
      rw [resolve_miss_count role slot state cached, support_map] at supported
      obtain ⟨seed, _, rfl⟩ := supported
      simp only [SeedAccounting, cachedSlots_miss state.seeds.1 slot seed cached]
      omega
    | some seed =>
      rw [resolve_hit role slot state seed cached, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl

/-- Server admission retains exact seed occupancy accounting on success and refusal. -/
theorem install_server_seed_accounting {n : Nat} (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installServer keyId identity ref).run state)) :
    SeedAccounting state result.2 := by
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
      have accounted := resolve_seed_accounting .server ref state inner reached
      cases ref <;> exact accounted
    · simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl

/-- Beacon admission retains exact seed occupancy accounting on success and refusal. -/
theorem install_beacon_seed_accounting {n : Nat} (owner : Nat) (shell : BeaconShell)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((installBeacon owner shell ref).run state)) :
    SeedAccounting state result.2 := by
  simp only [installBeacon, StateT.run] at supported
  split_ifs at supported
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    have accounted := resolve_seed_accounting .beacon ref state inner reached
    cases ref <;> exact accounted
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl

/-- No restricted capability can create an unaccounted seed draw or erase an occupied slot. -/
theorem capability_seed_accounting {n : Nat} (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((capability query).run state)) : SeedAccounting state result.2 := by
  cases query with
  | installServer keyId identity ref => exact install_server_seed_accounting keyId identity ref state result supported
  | installBeacon owner shell ref => exact install_beacon_seed_accounting owner shell ref state result supported
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

/-- Every actual World request preserves the exact seed draw-to-occupancy relation. -/
theorem handler_seed_accounting {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (state : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((handler setup codec route query).run state)) :
    SeedAccounting state result.2 := by

  have serverCase (query : RawCtxServerMixed.SourceSpec.Domain)
      (result : RawCtxServerMixed.SourceSpec.Range query × State n)
      (supported : result ∈ support ((serverStep setup codec route query).run state)) :
      SeedAccounting state result.2 := by
    cases server : state.server with
    | none =>
      cases query <;>
        simp only [serverStep, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> rfl
    | some current =>
      simp only [serverStep, StateT.run, server, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      rfl
  have beaconCase (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
      (result : RawCtxMixedOwner.SourceSpec.Range query × State n)
      (supported : result ∈ support ((beaconStep setup codec owner query).run state)) :
      SeedAccounting state result.2 := by
    cases found : state.owners[owner]? with
    | none =>
      simp only [beaconStep, StateT.run, found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
    | some phase =>
      simp only [beaconStep, StateT.run, found, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      rfl
  cases query with
  | inl created =>
    cases server : state.server <;>
      simp only [handler, initializeServer, StateT.run, server, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;> rfl
  | inr outer =>
    cases outer with
    | inl effect =>
      cases effect with
      | inl coin =>
        simp only [handler, effects, sampled, StateT.run, bind_pure_comp, support_map] at supported
        obtain ⟨inner, _, rfl⟩ := supported
        rfl
      | inr request =>
        exact capability_seed_accounting request (chargeEffect (.inr request) state) result supported
    | inr record =>
      cases record with
      | inl serverQuery =>
        cases serverQuery with
        | inl send => exact serverCase (.inl send) result supported
        | inr raw => exact serverCase (.inr raw) result supported
      | inr ownerQuery =>
        rcases ownerQuery with ⟨owner, query⟩
        cases query with
        | inl plaintext => exact beaconCase owner (.inl plaintext) result supported
        | inr raw => exact beaconCase owner (.inr raw) result supported

/-- Exact seed accounting is preserved by every adaptive World program. -/
theorem schedule_seed_accounting {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) X)
    (state : State n) (result : X × State n)
    (supported : result ∈ support ((simulateQ (handler setup codec route) client).run state)) :
    SeedAccounting state result.2 := by
  refine simulateQ_run_preservesInv (handler setup codec route) (SeedAccounting state)
    ?_ client state rfl result supported
  intro query before invariant after reached
  have step := handler_seed_accounting setup codec route query before after reached
  unfold SeedAccounting at invariant step ⊢
  omega

/-- From the actual empty World, fresh seed draws equal occupied slots and cannot exceed the finite slot count. -/
theorem run_seed_draws {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode adversary)) :
    result.2.seeds.2.draws = (cachedSlots result.2.seeds.1).card ∧ result.2.seeds.2.draws ≤ n := by
  have accounted := schedule_seed_accounting setup codec route _ initial result supported
  have exactCount : result.2.seeds.2.draws = (cachedSlots result.2.seeds.1).card := by
    simpa [SeedAccounting, initial, PqxdhRecordLiftLazyTable.initial, cachedSlots] using accounted
  exact ⟨exactCount, exactCount.le.trans (cachedSlots_bound result.2.seeds.1)⟩

/-- The actual World uniform count fits explicit startup, wrapper, environment, record-hash and finite-seed costs. -/
theorem run_uniform {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (adversary : OracleComp (ModeSpec mode) X) (respects : caps.outer.Respects adversary)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode adversary)) :
    result.2.primitive.1.uniform ≤
      startupCoins + caps.outer.coin + caps.outer.test + bounds.max * caps.outer.fresh +
        caps.envTotal allowance .coin +
      64 * (caps.outer.hash + caps.outer.sends + caps.outer.receives + caps.envTotal allowance .hash) +
      64 * n := by
  have counts := run_uniform_counts setup codec route env serverKid bounds mode adversary result supported
  have coins := run_effects setup codec route env serverKid bounds mode caps startupCoins allowance framed
    adversary respects .coin result supported
  have hashes := run_hash setup codec route env serverKid bounds mode caps startupCoins allowance framed
    adversary respects result supported
  have draws := (run_seed_draws setup codec route env serverKid bounds mode adversary result supported).2
  simp only [startupCost, directCost] at coins
  omega

end BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.weighted_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.weighted_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.native_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.native_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_byte' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_byte

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_vector

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_fixed_bytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_fixed_bytes

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_seed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.sample_seed

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_miss_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_miss_count

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.server_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.server_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.beacon_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.beacon_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_server_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_server_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_beacon_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_beacon_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.capability_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.capability_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.effects_counters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.effects_counters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_kdf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.native_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.native_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.server_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.server_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.beacon_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.beacon_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.uniform_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.uniform_support

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.primitive_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.primitive_uniform_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.primitive_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.primitive_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.native_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.native_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_server_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_server_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_beacon_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_beacon_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.capability_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.capability_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.effects_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.effects_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.server_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.server_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.beacon_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.beacon_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_uniform_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_uniform_counts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.cachedSlots_miss' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.cachedSlots_miss

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.cachedSlots_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.cachedSlots_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_seed_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.resolve_seed_accounting

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_server_seed_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_server_seed_accounting

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_beacon_seed_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.install_beacon_seed_accounting

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.capability_seed_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.capability_seed_accounting

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_seed_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.handler_seed_accounting

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_seed_accounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.schedule_seed_accounting

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_seed_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_seed_draws

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget.run_uniform

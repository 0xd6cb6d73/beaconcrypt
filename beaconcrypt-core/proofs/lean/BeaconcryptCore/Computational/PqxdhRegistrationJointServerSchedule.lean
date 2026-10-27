-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointPublicShared
import BeaconcryptCore.Computational.PqxdhRegistrationJointRevealCosts

/-! The full adaptive one-Server/many-Beacon source schedule retains the initialized Server slot alongside all Beacon ownership facts. Raw acceptance records its actual private DH service trace; every existing request and current-field disclosure remains available. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhRegistrationJointSchedule (State Invariant)
open PqxdhRegistrationJointRevealSchedule (Spec)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Shared private/native work reinstalls both complete components while keeping every Beacon owner. -/
def onBackend (work : StateT (PqxdhRegistrationJointFinish.State KemSK) ProbComp Result) :
    StateT (State KemSK) ProbComp Result := fun state =>
  (fun result => (result.1, { state with pool := result.2.1, shared := result.2.2 })) <$>
    work.run (state.pool, state.shared)

/-- The source scheduler changes only the private annotation on acceptance. The public request language, current-field reveals, every source branch and the full adaptive continuation stay unchanged. -/
noncomputable def source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) :
    QueryImpl (Spec KemSK) (StateT (State KemSK) ProbComp)
  | .inl (.inr (.accept raw)) => onBackend (PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw)
  | query => PqxdhRegistrationJointRevealSchedule.source setup codec checks seed query

/-- The private acceptance trace projects to the same actual raw acceptance and complete owner registry. -/
theorem accept_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
      (onBackend (PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw)).run state =
        (PqxdhRegistrationSchedule.onShared
          (nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw)).run
            (PqxdhRegistrationJointSchedule.source state) := by
  simp only [onBackend, PqxdhRegistrationSchedule.onShared, StateT.run, Functor.map_map]
  simpa only [StateT.run, Functor.map_map, PqxdhRegistrationJointSchedule.source] using congrArg
    (fun work => (fun result => (result.1, (⟨result.2, state.owners.map PqxdhRegistrationJointOwnership.Entry.owner⟩ : PqxdhRegistrationSchedule.State KemSK))) <$> work)
    (PqxdhRegistrationJointServerAccept.source_native setup codec checks seed identityIndex raw (state.pool, state.shared))

/-- Every public request projects to the original native scheduler with the same complete owner registry, pending state, caches and current-field answer. -/
theorem query_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain) (state : State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
      (source setup codec checks seed identityIndex query).run state =
        (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed query).run
          (PqxdhRegistrationJointSchedule.source state) := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request <;> first
    | exact accept_native setup codec checks seed identityIndex _ state
    | exact PqxdhRegistrationJointRevealSchedule.query_projection setup codec checks seed _ state
  all_goals exact PqxdhRegistrationJointRevealSchedule.query_projection setup codec checks seed _ state

/-- The entire adaptive source execution projects to the native experiment. Only private service annotations are erased; the final decision and all source state remain. -/
theorem program_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result)
    (state : State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
      (simulateQ (source setup codec checks seed identityIndex) program).run state =
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed) program).run
          (PqxdhRegistrationJointSchedule.source state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result =>
          (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks seed) (next result.1)).run result.2)
        (query_native setup codec checks seed identityIndex query state)

/-- Every supported bundle trace preserves the entire seed array, independently of selected-owner provenance or writer success. -/
theorem bundle_seeds (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : PqxdhRegistrationSchedule.Owner KemSK) (pool : PqxdhDynamicIdentityPool.SourceState)
    (result : (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) × PqxdhDynamicIdentityPool.SourceState)
    (supported : result ∈ support (PqxdhRegistrationJointBundle.trace setup codec index owner pool)) :
    result.2.seeds = pool.seeds := by
  cases phase : owner.beacon.phase <;>
    simp only [PqxdhRegistrationJointBundle.trace, phase, support_map, Set.mem_image, mem_support_pure_iff] at supported
  case fresh =>
    obtain ⟨scalar, _, rfl⟩ := supported
    exact PqxdhRegistrationJointBundle.after_seeds setup codec index owner (some scalar) pool
  all_goals subst result
  all_goals first | rfl | exact PqxdhRegistrationJointBundle.after_seeds setup codec index owner none pool

/-- A complete accepting or rejecting Server attempt retains all Beacon ownership facts; only histories and the actual shared native state may change. -/
theorem accept_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) (raw : Pqxdh.Bytes)
    (state : State KemSK) (result : Option Nat × State KemSK) (owned : Invariant state)
    (supported : result ∈ support ((onBackend (PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw)).run state)) :
    Invariant result.2 := by
  obtain ⟨reached, member, rfl⟩ : ∃ reached ∈ support
      ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw).run (state.pool, state.shared)),
      (reached.1, { state with pool := reached.2.1, shared := reached.2.2 }) = result := by
    simpa only [onBackend, StateT.run, support_map, Set.mem_image] using supported
  have slots := PqxdhRegistrationJointServerAccept.source_slots setup codec checks seed identityIndex raw (state.pool, state.shared) reached member
  exact fun entry member => PqxdhRegistrationJointOwnership.owned_slots state.pool reached.2.1 entry slots.1 slots.2 (owned entry member)

/-- Every actual command preserves all Beacon ownership facts, with arbitrary compromise requests and no honest-target restriction. -/
theorem query_owned (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (state : State KemSK) (result : (Spec KemSK).Range query × State KemSK) (owned : Invariant state)
    (supported : result ∈ support ((source setup codec checks seed identityIndex query).run state)) :
    Invariant result.2 := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request <;> first
    | exact accept_owned setup codec checks seed identityIndex _ state result owned supported
    | exact PqxdhRegistrationJointRevealSchedule.query_owned setup codec checks seed _ state result owned supported
  all_goals exact PqxdhRegistrationJointRevealSchedule.query_owned setup codec checks seed _ state result owned supported

/-- Original native shared callbacks cannot alter any private identity slot. -/
theorem native_slot (work : NativeGame KemSK Result) (state : State KemSK) (result : Result × State KemSK)
    (seed : IdentitySeed) (index : Nat) (owned : state.pool.1.seeds[index]? = some seed)
    (supported : result ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state)) :
    result.2.pool.1.seeds[index]? = some seed := by
  obtain ⟨reached, _, rfl⟩ : ∃ reached ∈ support (work.run state.shared),
      (reached.1, { state with shared := reached.2 }) = result := by
    simpa only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] using supported
  exact owned

/-- Every original command preserves every earlier identity slot, even when later creation appends a different identity with the same public encoding. This is exact-index preservation. -/
theorem base_query_slot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed seed : IdentitySeed) (index : Nat) (query : PqxdhRegistrationSchedule.Spec.Domain)
    (state : State KemSK) (result : PqxdhRegistrationSchedule.Spec.Range query × State KemSK)
    (owned : state.pool.1.seeds[index]? = some seed)
    (supported : result ∈ support ((PqxdhRegistrationJointSchedule.handler setup codec checks serverSeed query).run state)) :
    result.2.pool.1.seeds[index]? = some seed := by
  rcases query with coin | request
  case inr =>
    cases request <;> first
    | exact native_slot _ state result seed index owned supported
    | skip
    case finish address raw =>
      cases found : state.owners[address]? <;>
        simp only [PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish,
          StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
      case some entry =>
        obtain ⟨reached, member, rfl⟩ := supported
        have slots := PqxdhRegistrationJointFinish.annotated_program_slots setup codec entry.identityIndex entry.kemIndex
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.owner) (state.pool, state.shared) reached member
        simpa only [slots.1] using owned
      case none => simpa only [supported] using owned
    case bundle address =>
      cases found : state.owners[address]? <;>
        simp only [PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle,
          StateT.run, found, support_map, Set.mem_image, mem_support_pure_iff] at supported
      case some entry =>
        obtain ⟨reached, member, rfl⟩ := supported
        simpa only [bundle_seeds setup codec entry.identityIndex entry.owner state.pool.1 reached member] using owned
      case none => simpa only [supported] using owned
    case create pin keyId =>
      simp only [PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.create,
        StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨material, _, rfl⟩ := supported
      change (state.pool.1.seeds ++ [material.seed])[index]? = some seed
      simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp owned).choose] using owned
  case inl =>
    simp only [PqxdhRegistrationJointSchedule.handler, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
    exact supported.elim (fun _ witness => witness.2 ▸ owned)

/-- Current-field disclosure changes only history; it cannot overwrite the initialized Server slot or any other private identity slot. -/
theorem read_slot (request : Nat × PqxdhRegistrationJointLiveRead.Field) (state : State KemSK)
    (seed : IdentitySeed) (index : Nat) (owned : state.pool.1.seeds[index]? = some seed) :
    (PqxdhRegistrationJointLiveRead.sourceStep request state).2.pool.1.seeds[index]? = some seed := by
  cases found : state.owners[request.1]?
  case some entry => simpa only [PqxdhRegistrationJointLiveRead.sourceStep, found,
    (PqxdhRegistrationJointLiveRead.entry_slots request.2 entry state.pool).1] using owned
  case none => simpa only [PqxdhRegistrationJointLiveRead.sourceStep, found] using owned

/-- Repeated raw acceptance preserves any earlier private identity slot, including the initialized Server slot. -/
theorem accept_slot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed seed : IdentitySeed) (identityIndex index : Nat) (raw : Pqxdh.Bytes)
    (state : State KemSK) (result : Option Nat × State KemSK) (owned : state.pool.1.seeds[index]? = some seed)
    (supported : result ∈ support ((onBackend (PqxdhRegistrationJointServerAccept.source setup codec checks serverSeed identityIndex raw)).run state)) :
    result.2.pool.1.seeds[index]? = some seed := by
  obtain ⟨reached, member, rfl⟩ : ∃ reached ∈ support
      ((PqxdhRegistrationJointServerAccept.source setup codec checks serverSeed identityIndex raw).run (state.pool, state.shared)),
      (reached.1, { state with pool := reached.2.1, shared := reached.2.2 }) = result := by
    simpa only [onBackend, StateT.run, support_map, Set.mem_image] using supported
  simpa only [(PqxdhRegistrationJointServerAccept.source_slots setup codec checks serverSeed identityIndex raw
    (state.pool, state.shared) reached member).1] using owned

/-- Every command in the complete disclosure-capable schedule retains every earlier private identity slot. No freshness, public-key injectivity or selected-owner premise is needed. -/
theorem query_slot (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed seed : IdentitySeed) (identityIndex index : Nat) (query : (Spec KemSK).Domain)
    (state : State KemSK) (result : (Spec KemSK).Range query × State KemSK)
    (owned : state.pool.1.seeds[index]? = some seed)
    (supported : result ∈ support ((source setup codec checks serverSeed identityIndex query).run state)) :
    result.2.pool.1.seeds[index]? = some seed := by
  rcases query with (coin | request) | read
  case inl.inr =>
    cases request with
    | accept raw => exact accept_slot setup codec checks serverSeed seed identityIndex index raw state result owned supported
    | create pin keyId => exact base_query_slot setup codec checks serverSeed seed index (.inr (.create pin keyId)) state result owned supported
    | bundle address => exact base_query_slot setup codec checks serverSeed seed index (.inr (.bundle address)) state result owned supported
    | finish address raw => exact base_query_slot setup codec checks serverSeed seed index (.inr (.finish address raw)) state result owned supported
    | build session payload => exact base_query_slot setup codec checks serverSeed seed index (.inr (.build session payload)) state result owned supported
    | hmac key message => exact base_query_slot setup codec checks serverSeed seed index (.inr (.hmac key message)) state result owned supported
    | hash bytes => exact base_query_slot setup codec checks serverSeed seed index (.inr (.hash bytes)) state result owned supported
    | reveal keyId => exact base_query_slot setup codec checks serverSeed seed index (.inr (.reveal keyId)) state result owned supported
  case inl.inl => exact base_query_slot setup codec checks serverSeed seed index (.inl coin) state result owned supported
  case inr =>
    have reached : result = PqxdhRegistrationJointLiveRead.sourceStep read state := by
      simpa only [source, PqxdhRegistrationJointRevealSchedule.source, StateT.run, support_pure, Set.mem_singleton_iff] using supported
    simpa only [reached] using read_slot read state seed index owned

/-- Exact representation invariant for the initialized Server and every current Beacon; it makes no statement about origin honesty, freshness or secrecy. -/
def Owned (seed : IdentitySeed) (identityIndex : Nat) (state : State KemSK) : Prop :=
  Invariant state ∧ state.pool.1.seeds[identityIndex]? = some seed

/-- Actual supported replies preserve the complete joint representation invariant, including all permitted current-field disclosures. -/
theorem query_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) (query : (Spec KemSK).Domain)
    (state : State KemSK) (result : (Spec KemSK).Range query × State KemSK) (owned : Owned seed identityIndex state)
    (supported : result ∈ support ((source setup codec checks seed identityIndex query).run state)) :
    Owned seed identityIndex result.2 := by
  exact ⟨query_owned setup codec checks seed identityIndex query state result owned.1 supported,
    query_slot setup codec checks seed seed identityIndex identityIndex query state result owned.2 supported⟩

/-- Every finite adaptive schedule preserves the initialized Server index and all current Beacon ownership facts on its actual reached complete state. -/
theorem program_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (identityIndex : Nat) (program : OracleComp (Spec KemSK) Result)
    (state : State KemSK) (result : Result × State KemSK) (owned : Owned seed identityIndex state)
    (supported : result ∈ support ((simulateQ (source setup codec checks seed identityIndex) program).run state)) :
    Owned seed identityIndex result.2 := by
  exact (run_rel (source setup codec checks seed identityIndex)
    (fun before after => Owned seed identityIndex before → Owned seed identityIndex after)
    (fun _ owned => owned) (fun _ _ _ left right owned => right (left owned))
    (fun query before after member owned => query_invariant setup codec checks seed identityIndex query before after owned member)
    program state result supported) owned

end BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.accept_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.program_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.bundle_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.bundle_seeds

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.accept_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.accept_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.native_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.native_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.base_query_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.base_query_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.read_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.read_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.accept_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.accept_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.query_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerSchedule.program_invariant

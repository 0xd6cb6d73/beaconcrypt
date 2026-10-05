-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointServerPrefixCosts

/-! Source-ordered Server initialization into the existing private joint identity service. A generated seed is sampled only by its standard create interpreter; supplied seed bytes stay caller-known and retain their imported origin. The executable constructor returns a seedless owner. Installing a source-produced seed in mathematical analysis state is representation, not a security assumption or an extra secret oracle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth
open PqxdhJointIdentity PqxdhServerAuthExperiment
open PqxdhRegistrationJointPreparation (Pool)
open PqxdhRegistrationJointServerPrefix (State onPool onAux)
open PqxdhLiveServerConstruction (Origin Created Metadata)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK P A Result : Type}

/-- Complete current Server owner representation, with public identity and exact origin but no identity seed coordinate. -/
structure ClientCreated (P : Type) where
  publicIdentity : PublicIdentity
  server : RawCtxServerRouting.State Metadata P
  control : beaconcrypt_core.pqxdh.ServerState
  consumed : List Pqxdh.Bytes
  origin : Origin

def encode (created : Created P) : ClientCreated P :=
  ⟨created.publicIdentity, created.server, created.control, created.consumed, created.origin⟩

def initialized (identityIndex : Nat) (sender : Std.U64) (origin : Origin) (publicIdentity : PublicIdentity) : ClientCreated P :=
  { publicIdentity := publicIdentity
    server := ⟨⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, fun _ => none, ⟨identityIndex, sender⟩⟩, 0⟩
    control := ⟨sender⟩
    consumed := []
    origin := origin }

inductive LocalRequest where
  | initialize
  | importSeed (knownSeed : IdentitySeed)

abbrev LocalSpec : OracleSpec LocalRequest
  | .initialize => Bool
  | .importSeed _ => Nat × PublicIdentity

abbrev Spec (KemSK : Type) := PqxdhLiveKemBirth.Spec KemSK + LocalSpec

/-- Known supplied material occupies a distinct indexed slot without pretending that a uniform create request occurred. Its origin remains in the constructed owner. -/
def importKnown (joint : Primitives) (seed : IdentitySeed) (pool : Pool KemSK) :
    (Nat × PublicIdentity) × Pool KemSK :=
  ((pool.1.seeds.length, joint.publicKeys seed), ({ pool.1 with seeds := pool.1.seeds ++ [seed] }, pool.2))

def impl (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool) :
    QueryImpl (Spec KemSK) (StateT (State KemSK A) ProbComp)
  | .inl query => onPool (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query)
  | .inr .initialize => onAux ensureInit
  | .inr (.importSeed seed) => fun state =>
      let result := importKnown setup.joint seed state.1
      pure (result.1, (result.2, state.2))

/-- Initialization precedes the exact length check or the standard joint-service creation query. No unavailable generated seed leaves its interpreter. -/
def client (sender : Std.U64) (supplied : Option Pqxdh.Bytes) : OracleComp (Spec KemSK) (Option (ClientCreated P)) := do
  let ready ← (Spec KemSK).query (.inr .initialize)
  if ready then
    match supplied with
    | some bytes => match PqxdhLiveServerConstruction.parseSeed bytes with
      | none => pure none
      | some knownSeed => do
        let identity ← (Spec KemSK).query (.inr (.importSeed knownSeed))
        pure (some (initialized identity.1 sender .imported identity.2))
    | none => do
      let identity ← (Spec KemSK).query (.inl (.inl (.inr .create)))
      pure (identity.map fun identity => initialized identity.1 sender .generated identity.2)
  else pure none

/-- Mathematical installation of the exact source constructor result. Imported and generated origins are never conflated in the service history. -/
def install (created : Created P) (pool : Pool KemSK) : Pool KemSK :=
  let extended := { pool.1 with seeds := pool.1.seeds ++ [created.seed] }
  let identity := match created.origin with
    | .generated => PqxdhDynamicIdentityPool.record (.inr .create)
        (some (pool.1.seeds.length, created.publicIdentity)) extended
    | .imported => extended
  (identity, pool.2)

def source (joint : Primitives) (ensureInit : StateT A ProbComp Bool) (sender : Std.U64)
    (supplied : Option Pqxdh.Bytes) : StateT (State KemSK A) ProbComp (Option (Created P)) := fun state =>
  (fun result => (result.1, ((match result.1 with
    | none => state.1
    | some created => install created state.1), result.2))) <$>
    (PqxdhLiveServerConstruction.construct joint ensureInit state.1.1.seeds.length sender supplied).run state.2

set_option backward.isDefEq.respectTransparency false in
/-- The full interpreted constructor equals actual source-order initialization, with its complete runtime/private state and distinct imported/generated origin. -/
theorem client_source (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (state : State KemSK A) :
    (simulateQ (impl setup ensureInit) (client (P := P) sender supplied)).run state =
      (fun result => (result.1.map encode, result.2)) <$> (source setup.joint ensureInit sender supplied).run state := by
  simp only [client, source, simulateQ_bind, simulateQ_spec_query,
    PqxdhLiveServerConstruction.construct, StateT.run, impl, map_bind]
  change StateT.run (_ >>= _) state = _
  rw [StateT.run_bind]
  simp only [onAux, StateT.run, bind_map_left]
  apply bind_congr
  rintro ⟨ready, runtime⟩
  cases ready
  case false => simp only [Bool.false_eq_true, ite_false, simulateQ_pure, map_pure]; rfl
  case true =>
    simp only [ite_true]
    cases supplied
    case none =>
      simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, impl]
      change StateT.run (_ >>= _) (state.1, runtime) = _
      rw [StateT.run_bind]
      simp only [onPool, PqxdhLiveKemBirth.impl, PqxdhDynamicIdentityPool.lazyImpl, PqxdhDynamicIdentityPool.poolImpl,
        StateT.run, bind_map_left, map_bind, map_pure, Functor.map_map]
      simp only [bind_assoc, pure_bind]
      change (sampleSeed >>= fun seed => pure _) = _
      rw [bind_pure_comp]
      rfl
    case some bytes =>
      cases parsed : PqxdhLiveServerConstruction.parseSeed bytes <;>
        simp only [parsed, simulateQ_pure, simulateQ_bind, simulateQ_spec_query, impl,
          Option.map_none, Option.map_some, map_pure]
      all_goals rfl

/-- Every returned source owner comes from the same actual constructor run; the only private-pool change is installation of its exact seed. -/
theorem source_constructor (joint : Primitives) (ensureInit : StateT A ProbComp Bool)
    (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (state after : State KemSK A) (created : Created P)
    (supported : (some created, after) ∈ support ((source joint ensureInit sender supplied).run state)) :
    after.1 = install created state.1 ∧
      (some created, after.2) ∈ support ((PqxdhLiveServerConstruction.construct joint ensureInit state.1.1.seeds.length sender supplied).run state.2) := by
  simp only [source, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨⟨answer, runtime⟩, supported, equality⟩ := supported
  cases answer <;> simp only [Prod.mk.injEq, Option.some.injEq, reduceCtorEq] at equality
  case none => exact False.elim equality.1
  case some => rcases equality with ⟨rfl, rfl⟩; exact ⟨rfl, supported⟩

/-- Both source origins install the exact new private seed at the next index. -/
theorem install_slot (created : Created P) (pool : Pool KemSK) :
    (install created pool).1.seeds[pool.1.seeds.length]? = some created.seed := by
  cases origin : created.origin <;> simp [install, origin, PqxdhDynamicIdentityPool.record]

/-- Initialization appends exactly the source seed, retaining every prior seed and KEM pair without any resampling. -/
theorem install_arrays (created : Created P) (pool : Pool KemSK) :
    (install created pool).1.seeds = pool.1.seeds ++ [created.seed] ∧
      (install created pool).2.keys = pool.2.keys := by
  cases origin : created.origin <;> simp [install, origin, PqxdhDynamicIdentityPool.record]

/-- The actual initialized owner's private service index holds its exact seed, for generated or caller-supplied construction, without an honesty premise. -/
theorem source_owned (joint : Primitives) (ensureInit : StateT A ProbComp Bool)
    (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (state after : State KemSK A) (created : Created P)
    (supported : (some created, after) ∈ support ((source joint ensureInit sender supplied).run state)) :
    after.1.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed := by
  have actual := source_constructor joint ensureInit sender supplied state after created supported
  obtain ⟨seed, shape, _⟩ := PqxdhLiveServerConstruction.construct_origin joint ensureInit state.1.1.seeds.length
    sender supplied state.2 after.2 created actual.2
  have index : created.server.server.metadata.identityIndex = state.1.1.seeds.length := by
    rw [shape]; rfl
  rw [actual.1, index]
  exact install_slot created state.1

/-- Origin is fixed by the actual supplied/generated branch, and every imported seed equals the caller's exact bytes. Imports cannot be relabelled as generated targets. -/
theorem source_origin (joint : Primitives) (ensureInit : StateT A ProbComp Bool)
    (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (state after : State KemSK A) (created : Created P)
    (supported : (some created, after) ∈ support ((source joint ensureInit sender supplied).run state)) :
    created.origin = (if supplied.isNone then .generated else .imported) ∧
      (match supplied with | none => True | some bytes => created.seed.toList = bytes) := by
  obtain ⟨seed, shape, bytes⟩ := PqxdhLiveServerConstruction.construct_origin joint ensureInit state.1.1.seeds.length
    sender supplied state.2 after.2 created (source_constructor joint ensureInit sender supplied state after created supported).2
  cases supplied <;> simp only [shape, PqxdhLiveServerConstruction.initialized]
  all_goals exact ⟨True.intro, bytes⟩

/-- The complete evaluated constructor charges every initialization attempt and exactly the generated branch's 32-byte sampler allowance. Imported seed installation adds no random draw. -/
theorem client_uniform (setup : Setup baseSpec KemSK) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (bounded : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (state : State KemSK A) :
    ((simulateQ (impl setup ensureInit) (client (P := P) sender supplied)).run state).IsTotalQueryBound
      (qInit + if supplied.isNone then 32 else 0) := by
  rw [client_source, IsTotalQueryBound, isQueryBound_map_iff]
  simpa only [source, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhLiveServerConstruction.construct_uniform (P := P) setup.joint ensureInit qInit bounded
      state.1.1.seeds.length sender supplied state.2

end BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.client_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.source_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.source_constructor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.install_slot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.install_slot

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.install_arrays' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.install_arrays

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.source_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.source_owned

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.source_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.source_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointServerBirth.client_uniform

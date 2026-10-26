import BeaconcryptCore.Computational.PqxdhServerAuthSourceCosts

/-!
The Server constructor uses the requested source position, a generated seed or the exact caller-supplied bytes, and the existing joint Ed25519/converted-X25519 primitive interface. Native initialization remains an explicit optional callback. Imported seeds have a distinct origin and are never relabelled as uniform draws. The returned private constructor value initializes the actual empty peer map, consumed registrations and extracted Server control; a separate registry adapter publishes only its public handle and identity.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveServerConstruction
open PqxdhJointIdentity
variable {P A : Type}

/-- The private identity-service index and original Server key identifier are distinct fields. -/
structure Metadata where
  identityIndex : Nat
  sender : Std.U64

inductive Origin where
  | generated
  | imported
  deriving DecidableEq

/-- The complete constructor value is interpreter-private; the public API later projects only the created handle and public identity. -/
structure Created (P : Type) where
  seed : IdentitySeed
  publicIdentity : PublicIdentity
  server : RawCtxServerRouting.State Metadata P
  control : pqxdh.ServerState
  consumed : List Pqxdh.Bytes
  origin : Origin

/-- Supplied seed bytes undergo the production length check before key construction. -/
def parseSeed (bytes : Pqxdh.Bytes) : Option IdentitySeed :=
  if length : bytes.length = 32 then some ⟨bytes, length⟩ else none

/-- This is the source struct initialization following successful primitive key construction. Equal public bytes at different indices remain permitted. -/
def initialized (primitives : Primitives) (identityIndex : Nat) (sender : Std.U64)
    (origin : Origin) (seed : IdentitySeed) : Created P :=
  let publicIdentity := primitives.publicKeys seed
  { seed := seed
    publicIdentity := publicIdentity
    server := ⟨⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, fun _ => none, ⟨identityIndex, sender⟩⟩, 0⟩
    control := ⟨sender⟩
    consumed := []
    origin := origin }

/-- Source order is initialization, supplied-seed validation or actual seed sampling, and then struct construction. No future Server seed is sampled here. -/
def construct (primitives : Primitives) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (sender : Std.U64) (supplied : Option Pqxdh.Bytes) :
    StateT A ProbComp (Option (Created P)) := fun state => do
  let ready ← ensureInit.run state
  if ready.1 then
    match supplied with
    | some bytes => pure ((parseSeed bytes).map (initialized primitives identityIndex sender .imported), ready.2)
    | none => (fun seed => (some (initialized primitives identityIndex sender .generated seed), ready.2)) <$> sampleSeed
  else pure (none, ready.2)

/-- Exact extracted control initialization follows the same requested source Server identifier. -/
theorem control_source (primitives : Primitives) (identityIndex : Nat) (sender : Std.U64)
    (origin : Origin) (seed : IdentitySeed) :
    pqxdh.ServerState.new sender = ok (initialized (P := P) primitives identityIndex sender origin seed).control := by
  rfl

/-- Source initialization is charged on every attempt; only an unsupplied seed incurs 32 uniform byte draws. -/
theorem construct_uniform (primitives : Primitives) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (bounded : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (identityIndex : Nat) (sender : Std.U64) (supplied : Option Pqxdh.Bytes) (state : A) :
    ((construct (P := P) primitives ensureInit identityIndex sender supplied).run state).IsTotalQueryBound
      (qInit + if supplied.isNone then 32 else 0) := by
  cases supplied <;> simp only [construct, StateT.run, Option.isNone_none, Option.isNone_some, ite_true, Bool.false_eq_true, ite_false, Nat.add_zero]
  · apply isTotalQueryBound_bind (bounded state)
    intro ready
    split
    · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using sampleSeed_uniform_bound
    · trivial
  · exact isTotalQueryBound_bind (n₁ := qInit) (n₂ := 0) (bounded state) (fun ready => by split <;> trivial)

/-- Every successfully returned role is the literal initialized source value. Imported bytes are retained exactly and do not acquire a generated-seed origin. -/
theorem construct_origin (primitives : Primitives) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : Nat) (sender : Std.U64) (supplied : Option Pqxdh.Bytes)
    (state after : A) (created : Created P)
    (supported : (some created, after) ∈ support ((construct primitives ensureInit identityIndex sender supplied).run state)) :
    ∃ seed, created = initialized primitives identityIndex sender (if supplied.isNone then .generated else .imported) seed ∧
      (match supplied with | none => True | some bytes => seed.toList = bytes) := by
  simp only [construct, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨ready, _, supported⟩ := supported
  split at supported
  · cases supplied with
    | none =>
        simp only [support_map, Set.mem_image] at supported
        obtain ⟨seed, _, equality⟩ := supported
        cases equality
        exact ⟨seed, rfl, trivial⟩
    | some bytes =>
        simp only [parseSeed] at supported
        split at supported
        · simp only [mem_support_pure_iff, Prod.mk.injEq] at supported
          exact ⟨_, Option.some.inj supported.1, rfl⟩
        · simp at supported
  · simp at supported

end BeaconcryptCore.Computational.PqxdhLiveServerConstruction

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveServerConstruction.control_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveServerConstruction.control_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveServerConstruction.construct_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveServerConstruction.construct_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhLiveServerConstruction.construct_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveServerConstruction.construct_origin

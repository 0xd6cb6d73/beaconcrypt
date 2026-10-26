-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleInitial

/-! The public constructor accepts arbitrary pin bytes and runs the actual initialization and 32-byte pin parse before the source-ordered generator. Typed construction is internal to this surface. Public owner and pending handles remain arbitrary natural numbers, including future and missing slots. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- `Beacon::try_new` parses the pin with libsodium-rs 0.2.4 `crypto_sign::PublicKey::from_bytes` (beacon.rs:67-68), which only checks that the input is exactly 32 bytes long and copies it. Construction performs no conversion or point check. A pin that `ed25519_pk_to_curve25519` rejects is noticed only by finish, which converts the response identity (beacon.rs:432) and requires it to equal the pin byte for byte (core pqxdh.rs:545); such a Beacon is created normally and can publish bundles, a finish call before its bundle leaves it unchanged, and its first finish attempt after the bundle aborts it. The finish model reproduces this by construction; it is not proved as a separate theorem. The `Checks` argument is not consulted; it is kept so that existing call sites and statements keep their form. -/
def parsePin (_checks : Checks) (bytes : Pqxdh.Bytes) : Option Word32 :=
  toWord32 bytes

/-- The raw pin parse is exactly the 32-byte width parse for every `checks`; no point predicate is consulted, as in `Beacon::try_new`. -/
theorem parsePin_eq_toWord32 (checks : Checks) (bytes : Pqxdh.Bytes) :
    parsePin checks bytes = toWord32 bytes := rfl

/-- Runtime initialization runs first on every attempt, including pin bytes of the wrong width. Failed initialization or a wrong-width pin keeps all original protocol state and draws no Beacon key material, as `Beacon::try_new` returns `KeyGenError` there; every 32-byte pin, including one that is not a valid Ed25519 point, then runs the original typed constructor exactly once. -/
noncomputable def rawCreate (setup : Setup baseSpec KemSK) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bytes : Pqxdh.Bytes) (keyId : Std.U64) :
    StateT (A × State KemSK) ProbComp (Option Nat) := fun state => do
  let initialized ← ensureInit.run state.1
  if initialized.1 then
    match parsePin checks bytes with
    | none => pure (none, initialized.2, state.2)
    | some pin => (fun result => (some result.1, initialized.2, result.2)) <$>
        (create setup pin keyId).run state.2
  else pure (none, initialized.2, state.2)

/-- The internal typed constructor is not an additional public bypass around raw initialization and the pin width parse. -/
def IsConstructor : Request → Prop
  | .create _ _ => True
  | _ => False

inductive SurfaceRequest where
  | create (pin : Pqxdh.Bytes) (keyId : Std.U64)
  | call (request : { request : Request // ¬ IsConstructor request })

abbrev SurfaceQuerySpec : OracleSpec SurfaceRequest
  | .create _ _ => Option Nat
  | .call request => QuerySpec.Range request.val

abbrev SurfaceSpec := unifSpec + SurfaceQuerySpec

/-- Every existing operation retains its actual complete state and response. Runtime bookkeeping is separate from the shared protocol and primitive caches. -/
def onProtocol (work : Game KemSK Result) : StateT (A × State KemSK) ProbComp Result := fun state =>
  (fun result => (result.1, state.1, result.2)) <$> work.run state.2

/-- This is the raw public surface of the joint scheduler. None of the ordinary lookup, signing, admission, writer, finish or public-primitive operations consults an origin registry. -/
noncomputable def surfaceHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool) :
    QueryImpl SurfaceSpec (StateT (A × State KemSK) ProbComp)
  | .inl coin => onProtocol (handler setup codec checks serverSeed (.inl coin))
  | .inr (.create bytes keyId) => rawCreate setup checks ensureInit bytes keyId
  | .inr (.call request) => onProtocol (handler setup codec checks serverSeed (.inr request.val))

/-- A missing or future handle remains an ordinary public call; the raw surface cannot manufacture a typed constructor as a second admission route. -/
theorem surface_call_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (request : { request : Request // ¬ IsConstructor request }) (state : A × State KemSK) :
    (surfaceHandler setup codec checks serverSeed ensureInit (.inr (.call request))).run state =
      (fun result => (result.1, state.1, result.2)) <$>
        (handler setup codec checks serverSeed (.inr request.val)).run state.2 := by
  rfl

/-- The raw constructor exposes the complete initialization and generator continuation in source order, not only a marginal key distribution. -/
theorem rawCreate_continuation (setup : Setup baseSpec KemSK) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bytes : Pqxdh.Bytes) (keyId : Std.U64)
    (state : A × State KemSK) (next : Option Nat × (A × State KemSK) → ProbComp Result) :
    ((rawCreate setup checks ensureInit bytes keyId).run state >>= next) = (do
      let initialized ← ensureInit.run state.1
      if initialized.1 then
        match parsePin checks bytes with
        | none => next (none, initialized.2, state.2)
        | some pin => do
            let result ← (create setup pin keyId).run state.2
            next (some result.1, initialized.2, result.2)
      else next (none, initialized.2, state.2)) := by
  simp only [rawCreate, StateT.run, bind_assoc]
  apply bind_congr
  rintro ⟨ready, runtime⟩
  cases ready <;> cases parsePin checks bytes <;> simp [bind_map_left]

/-- Every raw construction attempt either rejects without changing protocol state or reaches the exact typed constructor at its 32-byte pin; no point validity is implied. Runtime effects remain in the returned runtime coordinate. -/
theorem rawCreate_cases (setup : Setup baseSpec KemSK) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (bytes : Pqxdh.Bytes) (keyId : Std.U64)
    (state : A × State KemSK) (result : Option Nat × (A × State KemSK))
    (supported : result ∈ support ((rawCreate setup checks ensureInit bytes keyId).run state)) :
    (result.1 = none ∧ result.2.2 = state.2) ∨
      ∃ pin index, parsePin checks bytes = some pin ∧ result.1 = some index ∧
        (index, result.2.2) ∈ support ((create setup pin keyId).run state.2) := by
  simp only [rawCreate, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨ready, runtime⟩, _, reached⟩ := supported
  cases ready <;> simp only [Bool.false_eq_true, ite_false, ite_true, mem_support_pure_iff] at reached
  · exact Or.inl ⟨congrArg Prod.fst reached, congrArg (fun value => value.2.2) reached⟩
  · cases parsed : parsePin checks bytes <;> simp only [parsed, mem_support_pure_iff, support_map, Set.mem_image] at reached
    · exact Or.inl ⟨congrArg Prod.fst reached, congrArg (fun value => value.2.2) reached⟩
    · obtain ⟨⟨index, after⟩, born, rfl⟩ := reached
      exact Or.inr ⟨_, index, rfl, rfl, born⟩

/-- The old source-operation label reached by this public request. Pin bytes of the wrong width have no constructor label, while initialization failure may still reject before the labelled operation. Labels do not remove any attempted request from execution or billing. -/
def surfaceLabel (checks : Checks) : SurfaceSpec.Domain → Option Spec.Domain
  | .inl coin => some (.inl coin)
  | .inr (.create bytes keyId) => (parsePin checks bytes).map (fun pin => .inr (.create pin keyId))
  | .inr (.call request) => some (.inr request.val)

/-- The public raw surface transports actual per-operation state relations. Its additional failure branches are genuine unchanged-state rejections; no source support or target honesty is assumed. -/
theorem surface_relation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (relation : Option Spec.Domain → State KemSK → State KemSK → Prop)
    (unchanged : ∀ label state, relation label state state)
    (step : ∀ query state result, result ∈ support ((handler setup codec checks serverSeed query).run state) →
      relation (some query) state result.2)
    (query : SurfaceSpec.Domain) (state : A × State KemSK)
    (result : SurfaceSpec.Range query × (A × State KemSK))
    (supported : result ∈ support ((surfaceHandler setup codec checks serverSeed ensureInit query).run state)) :
    relation (surfaceLabel checks query) state.2 result.2.2 := by
  rcases query with coin | request
  · simp only [surfaceHandler, onProtocol, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨original, reached, rfl⟩ := supported
    exact step (.inl coin) state.2 original reached
  · cases request with
    | create bytes keyId =>
        rcases rawCreate_cases setup checks ensureInit bytes keyId state result supported with
          ⟨_, same⟩ | ⟨pin, index, parsed, _, reached⟩
        · simpa only [same] using unchanged (surfaceLabel checks (.inr (.create bytes keyId))) state.2
        · simpa only [surfaceLabel, parsed, Option.map_some] using
            step (.inr (.create pin keyId)) state.2 (index, result.2.2) reached
    | call request =>
        simp only [surfaceHandler, onProtocol, StateT.run, support_map, Set.mem_image] at supported
        obtain ⟨original, reached, rfl⟩ := supported
        exact step (.inr request.val) state.2 original reached

/-- Every complete adaptive raw-surface execution transports the original source relation, including arbitrary rejected constructor attempts and all original optional replies. The runtime state remains in the execution rather than being reset between operations. -/
theorem surface_program_relation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (relation : State KemSK → State KemSK → Prop)
    (reflexive : ∀ state, relation state state)
    (transitive : ∀ first middle last, relation first middle → relation middle last → relation first last)
    (step : ∀ query state result, result ∈ support ((handler setup codec checks serverSeed query).run state) →
      relation state result.2)
    (program : OracleComp SurfaceSpec Result) (state : A × State KemSK)
    (result : Result × (A × State KemSK))
    (supported : result ∈ support ((simulateQ (surfaceHandler setup codec checks serverSeed ensureInit) program).run state)) :
    relation state.2 result.2.2 := by
  apply run_rel (surfaceHandler setup codec checks serverSeed ensureInit)
    (fun before after => relation before.2 after.2) (fun current => reflexive current.2)
    (fun first middle last => transitive first.2 middle.2 last.2) ?_ program state result supported
  exact surface_relation setup codec checks serverSeed ensureInit (fun _ => relation)
    (fun _ => reflexive) step

/-- Rejected raw constructors cannot reset the actual consumed set. Every arbitrary raw-surface continuation retains its complete prefix and the source uniqueness invariant. -/
theorem surface_consumed (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp SurfaceSpec Result) (state : A × State KemSK)
    (result : Result × (A × State KemSK))
    (supported : result ∈ support ((simulateQ (surfaceHandler setup codec checks serverSeed ensureInit) program).run state)) :
    state.2.shared.2.server.consumed.IsPrefix result.2.2.shared.2.server.consumed ∧
      (state.2.shared.2.server.consumed.Nodup → result.2.2.shared.2.server.consumed.Nodup) := by
  exact surface_program_relation setup codec checks serverSeed ensureInit
    (fun before after => before.shared.2.server.consumed.IsPrefix after.shared.2.server.consumed ∧
      (before.shared.2.server.consumed.Nodup → after.shared.2.server.consumed.Nodup))
    (fun _ => ⟨List.prefix_rfl, id⟩)
    (fun _ _ _ first second => ⟨first.1.trans second.1, second.2 ∘ first.2⟩)
    (fun query before after member => PqxdhRegistrationAdmission.admission_invariant _ _
      (handler_admission setup codec checks serverSeed query before after member)) program state result supported

/-- Classify the old source operations reached through the raw surface. A rejected raw constructor still counts in its own public-construction and runtime bills, even when this projection has no source label. -/
def SurfaceClass (checks : Checks) (predicate : Spec.Domain → Prop) (query : SurfaceSpec.Domain) : Prop :=
  (surfaceLabel checks query).elim False predicate

instance (checks : Checks) (predicate : Spec.Domain → Prop) [DecidablePred predicate] :
    DecidablePred (SurfaceClass checks predicate) := fun query => by
  unfold SurfaceClass
  cases surfaceLabel checks query <;> dsimp only [Option.elim] <;> infer_instance

/-- Original per-operation state-growth bounds extend to every adaptive raw-surface client. Initialization failure contributes no state growth, and no rejected original request is removed from its predicate's allowance. -/
theorem surface_count (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (predicate : Spec.Domain → Prop) [DecidablePred predicate] (measure : State KemSK → Nat)
    (step : ∀ query state result, result ∈ support ((handler setup codec checks serverSeed query).run state) →
      measure result.2 ≤ measure state + if predicate query then 1 else 0)
    (program : OracleComp SurfaceSpec Result) (q : Nat)
    (bounded : program.IsQueryBoundP (SurfaceClass checks predicate) q)
    (state : A × State KemSK) (result : Result × (A × State KemSK))
    (supported : result ∈ support ((simulateQ (surfaceHandler setup codec checks serverSeed ensureInit) program).run state)) :
    measure result.2.2 ≤ measure state.2 + q := by
  classical
  apply run_count (surfaceHandler setup codec checks serverSeed ensureInit) (SurfaceClass checks predicate)
    (fun current => measure current.2) ?_ program q bounded state result supported
  intro query before after member
  have projected := surface_relation setup codec checks serverSeed ensureInit
    (fun label first last => measure last ≤ measure first + if label.elim False predicate then 1 else 0)
    (fun _ _ => by simp) (fun original first last reached => by
      by_cases charged : predicate original <;>
        simpa only [Option.elim, charged, ite_true, ite_false] using step original first last reached)
    query before after member
  by_cases charged : SurfaceClass checks predicate query <;>
    simp_all only [SurfaceClass, ite_true, ite_false]

/-- The public raw constructor and every subsequent capability preserve terminal owners, already consumed allocated tokens, and the unexposed compatibility field. Future guessed handles are not classified as spent. -/
theorem surface_lifecycle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (ensureInit : StateT A ProbComp Bool)
    (program : OracleComp SurfaceSpec Result) (state : A × State KemSK)
    (result : Result × (A × State KemSK))
    (supported : result ∈ support ((simulateQ (surfaceHandler setup codec checks serverSeed ensureInit) program).run state)) :
    (∀ (index : Nat) (owner : Owner KemSK), state.2.owners[index]? = some owner → Terminal owner → result.2.2.owners[index]? = some owner) ∧
      (∀ index, PqxdhRegistrationPending.Spent index state.2.shared.2 →
        PqxdhRegistrationPending.Spent index result.2.2.shared.2) ∧
      result.2.2.shared.2.beacon = state.2.shared.2.beacon := by
  refine ⟨?_, ?_, ?_⟩
  · intro index owner present terminal
    exact surface_program_relation setup codec checks serverSeed ensureInit
      (fun before after => before.owners[index]? = some owner → after.owners[index]? = some owner)
      (fun _ found => found) (fun _ _ _ first second found => second (first found))
      (fun query before after member found =>
        handler_terminal setup codec checks serverSeed query index owner before after found terminal member)
      program state result supported present
  · intro index spent
    exact surface_program_relation setup codec checks serverSeed ensureInit
      (fun before after => PqxdhRegistrationPending.Spent index before.shared.2 →
        PqxdhRegistrationPending.Spent index after.shared.2)
      (fun _ => id) (fun _ _ _ first second => second ∘ first)
      (fun query before after member disposed =>
        handler_spent setup codec checks serverSeed query index before after disposed member)
      program state result supported spent
  · exact surface_program_relation setup codec checks serverSeed ensureInit
      (fun before after => after.shared.2.beacon = before.shared.2.beacon)
      (fun _ => rfl) (fun _ _ _ first second => second.trans first)
      (handler_bookkeeping setup codec checks serverSeed) program state result supported

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_call_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_call_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.rawCreate_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.rawCreate_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.rawCreate_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.rawCreate_cases
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_relation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_program_relation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_program_relation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_consumed
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_count
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_lifecycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.surface_lifecycle
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.parsePin_eq_toWord32' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.parsePin_eq_toWord32

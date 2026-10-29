-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
import BeaconcryptCore.Computational.RegistrationNativePairedChoice
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

/-! The paired native key interface separates the actual optional root-preparation phase from admitted material demand. Prepared references and callback counts are public scheduling metadata; protected PRKs remain in one private table indexed by the complete source input. Discarded prepare-time PRK reads can be deferred by a proved lazy-cache commutation, while known inputs retain the real fixed source function. No PRK-dependent root is sampled as independent side information. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKeyPhases
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput HmacSha512)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open LazyOracleDiscard (StateLens CacheLens Commutes LawEq)

inductive Value where
  | known : PqxdhServerAuthKeySchedule.Output → Value
  | hidden : PqxdhServerAuthKeySchedule.Output → Value

inductive Request where
  | prepare : Message → Request
  | demand : Message → Request

abbrev CommandSpec : OracleSpec Request
  | .prepare _ => Option Message
  | .demand _ => Option Value

abbrev Spec := unifSpec + CommandSpec

/-- Actual root callback counts and material-demand counts are retained separately. A refused or unprepared request still contributes to its scheduling count. -/
structure Meta where
  prepared : Pqxdh.Bytes → Bool
  prepares : Nat
  roots : Nat
  demands : Nat
  material : Nat

def emptyMeta : Meta := ⟨fun _ => false, 0, 0, 0, 0⟩
abbrev State := Meta × HmacOracle.QueryCache

def initial : State := (emptyMeta, ∅)
def cacheLens : CacheLens HmacOracle State := StateLens.snd _ _

def onMeta {Result : Type} (work : StateT Meta ProbComp Result) : StateT State ProbComp Result :=
  (StateLens.fst _ _).lift work

theorem onMeta_run {Result : Type} (work : StateT Meta ProbComp Result) (before : State) :
    (onMeta work).run before = (fun result => (result.1, (result.2, before.2))) <$> work.run before.1 := rfl

theorem onMeta_commutes {Result : Type} (work : StateT Meta ProbComp Result) :
    Commutes cacheLens (onMeta work) := by
  apply LazyOracleDiscard.commutes_frame cacheLens
  intro before cache
  simp only [onMeta, StateLens.lift, StateLens.fst, cacheLens, StateLens.snd,
    StateT.run, Functor.map_map]

def prepareMeta (input : Message → Option Pqxdh.Bytes) (message : Message) :
    StateT Meta ProbComp (Option Message) := fun before =>
  match input message with
  | none => pure (none, { before with prepares := before.prepares + 1 })
  | some bytes => pure (some message, { before with
      prepared := Function.update before.prepared bytes true
      prepares := before.prepares + 1
      roots := before.roots + 1 })

def demandMeta (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) :
    StateT Meta ProbComp (Option (Pqxdh.Bytes × Bool)) := fun before =>
  let counted := { before with demands := before.demands + 1 }
  match input message with
  | none => pure (none, counted)
  | some bytes =>
    if before.prepared bytes then
      pure (some (bytes, inside bytes), { counted with material := before.material + 1 })
    else pure (none, counted)

def point (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) :
    Option Pqxdh.Bytes := (input message).filter (fun bytes => inside bytes)

/-- Material is evaluated only on a successful prepared demand. Public side inputs use the unchanged source root/key schedule. -/
noncomputable def erased (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT State ProbComp)
  | .inl coin => onMeta (StateT.lift (unifSpec.query coin))
  | .inr (.prepare message) => onMeta (prepareMeta input message)
  | .inr (.demand message) => do
      let selected ← onMeta (demandMeta input inside message)
      match selected with
      | none => pure none
      | some (bytes, protectedInput) =>
          if protectedInput then
            (fun prk => some (.hidden (PqxdhServerAuthKeySchedule.keySchedule source hmac prk))) <$>
              cacheLens.query bytes
          else pure (some (.known (PqxdhServerAuthKeySchedule.fromRoot source
            (RegistrationNativeRelatedRoot.nativeRoot source bytes))))

theorem erased_commutes (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (query : Spec.Domain) :
    Commutes cacheLens (erased source hmac input inside query) := by
  cases query with
  | inl coin => exact onMeta_commutes _
  | inr request => cases request with
    | prepare message => exact onMeta_commutes _
    | demand message =>
      apply LazyOracleDiscard.commutes_bind cacheLens (onMeta_commutes _)
      intro selected
      cases selected with
      | none => exact LazyOracleDiscard.commutes_pure _ _
      | some selected =>
        rcases selected with ⟨bytes, protectedInput⟩
        cases protectedInput
        · exact LazyOracleDiscard.commutes_pure _ _
        · exact LazyOracleDiscard.commutes_map _ _ (LazyOracleDiscard.commutes_query _ _)

def pendingPoint (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    Spec.Domain → Option Pqxdh.Bytes
  | .inr (.prepare message) => point input inside message
  | _ => none

noncomputable def pointed (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (query : Spec.Domain) :
    StateT State ProbComp (Spec.Range query × Option Pqxdh.Bytes) :=
  (fun reply => (reply, pendingPoint input inside query)) <$> erased source hmac input inside query

/-- The prepare-time private PRK completion is executed at the root callback, while the complete108 output is evaluated only by the later demand branch. -/
noncomputable def eager (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) :
    QueryImpl Spec (StateT State ProbComp) := fun query before => do
  let reached ← (erased source hmac input inside query).run before
  let after ← cacheLens.completeOpt (pendingPoint input inside query) reached.2
  pure (reached.1, after)

theorem eager_prepare_run (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool) (message : Message) (before : State) :
    (eager source hmac input inside (.inr (.prepare message))).run before = (do
      let reached ← (onMeta (prepareMeta input message)).run before
      let after ← cacheLens.completeOpt (point input inside message) reached.2
      pure (reached.1, after)) := rfl

/-- All early PRK completions can be erased through an arbitrary adaptive prepare/demand schedule, retaining every public root/demand count and every side-input reply. The relation is derived from this concrete handler's commutation. -/
theorem defer_preparation {Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (input : Message → Option Pqxdh.Bytes) (inside : Pqxdh.Bytes → Bool)
    (work : OracleComp Spec Result) (before : State) :
    LawEq (Prod.map id Prod.fst <$> (simulateQ (eager source hmac input inside) work).run before)
      (Prod.map id Prod.fst <$> (simulateQ (erased source hmac input inside) work).run before) := by
  have factor : ∀ query state, LawEq ((eager source hmac input inside query).run state)
      ((pointed source hmac input inside query).run state >>= fun result =>
        (result.1.1, ·) <$> cacheLens.completeOpt result.1.2 result.2) := by
    intro query state
    apply LawEq.of_eq
    simp only [pointed, StateT.run_map, bind_map_left]
    simp only [eager, StateT.run, map_eq_bind_pure_comp]
    rfl
  have oblivious : ∀ query, Commutes cacheLens (Prod.fst <$> pointed source hmac input inside query) := by
    intro query
    simpa only [pointed, Functor.map_map, Function.comp_def, id_map'] using
      erased_commutes source hmac input inside query
  have erasedEq : (fun query => Prod.fst <$> pointed source hmac input inside query :
      QueryImpl Spec (StateT State ProbComp)) = erased source hmac input inside := by
    funext query
    simp only [pointed, Functor.map_map, id_map']
  have projected := LazyOracleDiscard.discard_erase_proj cacheLens (eager source hmac input inside)
    (pointed source hmac input inside) factor oblivious Prod.fst (fun _ _ => rfl) work before
  simpa only [erasedEq] using projected

end BeaconcryptCore.Computational.RegistrationNativeKeyPhases

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyPhases.onMeta_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyPhases.onMeta_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyPhases.onMeta_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyPhases.onMeta_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyPhases.erased_commutes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyPhases.erased_commutes
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyPhases.eager_prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyPhases.eager_prepare_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKeyPhases.defer_preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKeyPhases.defer_preparation

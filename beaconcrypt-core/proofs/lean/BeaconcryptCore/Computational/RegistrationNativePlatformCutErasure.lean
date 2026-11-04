-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal
/-! Erasing only the private signing journal preserves every native interpreter value and complete poststate under arbitrary adaptive programs. Extra Ed or trusted serializer capabilities carry the same shared base-monad state and can fail or diverge; they are lifted without inspecting the journal. No codec law, public-key injectivity or source-security premise is used. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure
open RegistrationNativePlatformCutJournal
variable {S : Type} {Value I : Type} {extra : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def liftWorld (work : StateT S m Value) : StateT (State S) m Value :=
  fun before => (fun result => (result.1, (result.2, before.2))) <$> work.run before.1

theorem lifted (work : StateT S m Value) (before : State S) :
    Prod.map id Prod.fst <$> (liftWorld work).run before = work.run before.1 := by
  change (Prod.map id Prod.fst <$> ((fun result => (result.1, (result.2, before.2))) <$> work.run before.1)) = _
  simp only [Functor.map_map, Prod.map, id_eq]
  exact id_map _

variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))

theorem outgoing (query : RegistrationSigningShared.Spec.Domain) (before : State S) :
    Prod.map id Prod.fst <$> (forward impl query).run before =
      (impl query).run before.1 := by
  cases query with
  | hash request =>
      rw [forward, hash_run]
      simp only [Functor.map_map, Prod.map, id_eq]
      exact id_map _
  | sign request payload digest =>
      change Prod.map id Prod.fst <$> ((fun result => (result.1, (result.2, before.2))) <$>
        (impl (.sign request payload digest)).run before.1) = _
      simp only [Functor.map_map, Prod.map, id_eq]
      exact id_map _

def Spec (extra : OracleSpec I) := RegistrationSigningShared.Spec + extra

noncomputable def handler (side : QueryImpl extra (StateT S m)) :
    QueryImpl (Spec extra) (StateT (State S) m)
  | .inl query => forward impl query
  | .inr query => liftWorld (side query)

noncomputable def native (side : QueryImpl extra (StateT S m)) :
    QueryImpl (Spec extra) (StateT S m)
  | .inl query => impl query
  | .inr query => side query

/-- Extra Ed/serializer capabilities can carry arbitrary shared state while erasing only the private signing journal. -/
theorem program (side : QueryImpl extra (StateT S m))
    (work : OracleComp (Spec extra) Value) (before : State S) :
    Prod.map id Prod.fst <$> (simulateQ (handler impl side) work).run before =
      (simulateQ (native impl side) work).run before.1 := by
  apply OracleComp.map_run_simulateQ_eq_of_query_map_eq
  intro query current
  cases query with
  | inl query => exact outgoing impl query current
  | inr query => exact lifted (side query) current
end BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure.lifted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure.lifted

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure.program

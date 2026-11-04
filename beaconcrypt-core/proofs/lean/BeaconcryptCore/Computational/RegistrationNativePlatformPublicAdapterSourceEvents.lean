-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceTrace
/-! Actual source callback boundaries retain original source objects and source primitive poststates. An opening precedes all operation stages; a closing retains the literal Rust result, including failure and divergence. The source log lives beside persistent P and is removed without replacing any source object or backend coordinate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents
open BeaconcryptCore.Refinement
open RegistrationNativePlatformSdkReification (Backend)
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformPublicAdapterSourceRuntime (Objects)
abbrev Spec := RegistrationNativePlatformPublicAdapterLowSpec.Spec
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

inductive Event (n : Nat) (KemSK R P : Type) where
  | stage (actual : RegistrationNativePlatformPublicAdapterSourceTrace.Stage)
  | opened (query : Spec.Domain) (before : Store n KemSK R P)
  | closed (query : Spec.Domain) (reply : RustM (Spec.Range query × Objects R))
      (after : Backend n KemSK × P)

variable {n : Nat} {KemSK R P A : Type}
abbrev Log (n : Nat) (KemSK R P : Type) := List (Event n KemSK R P)
abbrev State (n : Nat) (KemSK R P : Type) := Store n KemSK R (P × Log n KemSK R P)
abbrev Outcome (n : Nat) (KemSK R P A : Type) :=
  RustM (A × Objects R) × (Backend n KemSK × (P × Log n KemSK R P))

def backend (current : Backend n KemSK × (P × Log n KemSK R P)) : Backend n KemSK × P :=
  (current.1,current.2.1)

def store (current : State n KemSK R P) : Store n KemSK R P :=
  {current with backend := backend current.backend}

def outcome (result : Outcome n KemSK R P A) : RustM (A × Objects R) × (Backend n KemSK × P) :=
  (result.1,backend result.2)

def append (before : State n KemSK R P) (event : Event n KemSK R P) : State n KemSK R P :=
  {before with backend := (before.backend.1,(before.backend.2.1,before.backend.2.2 ++ [event]))}

theorem append_store (before : State n KemSK R P) (event : Event n KemSK R P) :
    store (append before event) = store before := rfl

/-- The actual source call is sampled once, after its opening marker. Its closing observes that same Rust reply and full physical poststate. -/
noncomputable def callback (query : Spec.Domain)
    (operation : State n KemSK R P → ProbComp (Outcome n KemSK R P (Spec.Range query)))
    (before : State n KemSK R P) : ProbComp (Outcome n KemSK R P (Spec.Range query)) := do
  let result ← operation (append before (.opened query (store before)))
  pure (result.1,(result.2.1,(result.2.2.1,
    result.2.2.2 ++ [.closed query result.1 (backend result.2)])))

/-- Erasure of callback observations preserves the same physical source operation, including every nonnormal terminal state. -/
theorem callback_erase (query : Spec.Domain)
    (operation : State n KemSK R P → ProbComp (Outcome n KemSK R P (Spec.Range query)))
    (plain : Store n KemSK R P → ProbComp (RustM (Spec.Range query × Objects R) × (Backend n KemSK × P)))
    (law : ∀ before, outcome <$> operation before = plain (store before))
    (before : State n KemSK R P) :
    outcome <$> callback query operation before = plain (store before) := by
  unfold callback
  simp only [map_bind, map_pure]
  have same := law (append before (.opened query (store before)))
  change (fun result : Outcome n KemSK R P (Spec.Range query) =>
    (result.1,(result.2.1,result.2.2.1))) <$> operation _ = _ at same
  simpa only [outcome,backend,bind_pure_comp,append_store] using same

/-- A source program erases only its actual source log. This includes nonnormal Rust results and preserves the terminal backend without executing a source continuation after failure. -/
theorem program {Q : Type} {spec : OracleSpec Q}
    (traced : QueryImpl spec (RegistrationNativePlatformPublicAdapterSourceRuntime.M n KemSK R (P × Log n KemSK R P)))
    (plain : QueryImpl spec (RegistrationNativePlatformPublicAdapterSourceRuntime.M n KemSK R P))
    (queries : ∀ query before,
      outcome <$> RegistrationNativePlatformPublicAdapterSourceRuntime.run (traced query) before =
        RegistrationNativePlatformPublicAdapterSourceRuntime.run (plain query) (store before))
    (work : OracleComp spec A) (before : State n KemSK R P) :
    outcome <$> RegistrationNativePlatformPublicAdapterSourceRuntime.run (simulateQ traced work) before =
      RegistrationNativePlatformPublicAdapterSourceRuntime.run (simulateQ plain work) (store before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
    simp only [simulateQ_pure,RegistrationNativePlatformPublicAdapterSourceRuntime.run_pure,map_pure]
    rfl
  | query_bind query next ih =>
    rw [simulateQ_bind,simulateQ_bind,simulateQ_spec_query,simulateQ_spec_query,
      RegistrationNativePlatformPublicAdapterSourceRuntime.run_bind,
      RegistrationNativePlatformPublicAdapterSourceRuntime.run_bind,map_bind]
    rw [←queries query before,bind_map_left]
    apply bind_congr
    rintro ⟨reply,after⟩
    cases reply with
    | fail error | div => rfl
    | ok pair => exact ih pair.1 (RegistrationNativePlatformPublicAdapterSourceRuntime.join pair.2 after)

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents.append_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents.append_store
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents.callback_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents.callback_erase
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceEvents.program

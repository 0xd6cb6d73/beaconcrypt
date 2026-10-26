import BeaconcryptCore.Computational.PqxdhServerRootPreparation

/-!
An authentication-only KEM controller is an explicit strengthened observation interface. Its descriptors expose public key bytes, ciphertext and a stable creation index, never a KEM secret, selected DH scalar, or identity seed. Both optional results are exposed, including failure. The concrete interpreter executes the exact original native KEM callback before disclosing its reply; erasing only this extra public audit preserves the complete source computation. Allowing arbitrary controller replies is an overapproximation, not a secrecy theorem or a new primitive security contract.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhKemCoordinateController
open PqxdhBeaconPhase2Preparation (Bytes Word32 Ciphertext)
open PqxdhEd25519EufCma (MlKem768PublicKey)

/-- The actual indexed creation descriptor; its second coordinate is an index, not secret key material. -/
abbrev Handle := MlKem768PublicKey × Nat

inductive Request where
  | encapsulate : MlKem768PublicKey → Request
  | decapsulate : Ciphertext → Handle → Request

abbrev Spec : OracleSpec Request
  | .encapsulate _ => Option (Ciphertext × Word32)
  | .decapsulate _ _ => Option Word32

/-- This is additional adversarial knowledge. In particular, successful KEM replies are not silently kept private in this authentication abstraction. -/
structure Observation where
  request : Request
  reply : Spec.Range request

abbrev NativeSpec (Reader E I D X Response : Type) :=
  PqxdhServerRootPreparation.Spec Reader E Word32 + PqxdhBeaconPhase2Preparation.Spec I D Handle X Response
abbrev ControlledSpec (Reader E I D X Response : Type) := Spec + NativeSpec Reader E I D X Response
abbrev State (A : Type) := A × List Observation

variable {Reader E I D X Response A Result : Type}

def sourceQuery : (query : Spec.Domain) → (NativeSpec Reader E I D X Response).Domain
  | .encapsulate key => .inl (.encapsulate key)
  | .decapsulate ciphertext handle => .inr (.decapsulate ciphertext handle)

/-- Every other native parser, conversion, DH, allocation or state callback remains the literal original private interface. -/
def compiler : QueryImpl (NativeSpec Reader E I D X Response) (OracleComp (ControlledSpec Reader E I D X Response))
  | .inl (.encapsulate key) => (ControlledSpec Reader E I D X Response).query (.inl (.encapsulate key))
  | .inr (.decapsulate ciphertext handle) => (ControlledSpec Reader E I D X Response).query (.inl (.decapsulate ciphertext handle))
  | query => (ControlledSpec Reader E I D X Response).query (.inr query)

/-- Controller emulation knows all KEM keys locally. It evaluates the actual primitive and exposes its actual optional reply, retaining every primitive state update and query. -/
def concrete (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp)) :
    QueryImpl Spec (StateT (State A) ProbComp) := fun query state =>
  match query with
  | .encapsulate key =>
      (fun result => (result.1, (result.2, state.2 ++ [⟨.encapsulate key, result.1⟩]))) <$>
        (native (.inl (.encapsulate key))).run state.1
  | .decapsulate ciphertext handle =>
      (fun result => (result.1, (result.2, state.2 ++ [⟨.decapsulate ciphertext handle, result.1⟩]))) <$>
        (native (.inr (.decapsulate ciphertext handle))).run state.1

/-- Ordinary source work changes its actual private state and leaves the auxiliary disclosure history intact. -/
def ordinary (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp)) :
    QueryImpl (NativeSpec Reader E I D X Response) (StateT (State A) ProbComp) := fun query state =>
  (fun result => (result.1, (result.2, state.2))) <$> (native query).run state.1

/-- The abstract controller is supplied separately from ordinary source callbacks. The concrete simulation below selects the exact source-result controller. -/
def impl (controller : QueryImpl Spec (StateT (State A) ProbComp))
    (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp)) :
    QueryImpl (ControlledSpec Reader E I D X Response) (StateT (State A) ProbComp)
  | .inl query => controller query
  | .inr query => ordinary native query

set_option backward.isDefEq.respectTransparency false in
/-- One source request has the same optional result and complete primitive poststate after erasing only the explicitly added KEM disclosure. -/
theorem step_source (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp))
    (query : (NativeSpec Reader E I D X Response).Domain) (state : State A) :
    (fun result => (result.1, result.2.1)) <$>
      ((simulateQ (impl (concrete native) native) (compiler query)).run state) =
        (native query).run state.1 := by
  cases query with
  | inl query =>
      cases query <;> simp [compiler, impl, ordinary, concrete, StateT.run, Functor.map_map]
  | inr query =>
      cases query <;> simp [compiler, impl, ordinary, concrete, StateT.run, Functor.map_map]

/-- Every adaptive native source program and all its private state are preserved by the concrete controller interpretation, including failed optional callbacks. -/
theorem program_source (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp))
    (client : OracleComp (NativeSpec Reader E I D X Response) Result) (state : State A) :
    (fun result => (result.1, result.2.1)) <$>
      ((simulateQ (impl (concrete native) native) (simulateQ compiler client)).run state) =
        (simulateQ native client).run state.1 := by
  have perQuery : ∀ query before,
      Prod.map id Prod.fst <$>
        (((impl (concrete native) native) ∘ₛ compiler) query).run before =
          (native query).run before.1 := by
    intro query before
    simpa only [QueryImpl.compose, Prod.map_def, id_eq] using step_source native query before
  simpa only [QueryImpl.simulateQ_compose, Prod.map_def, id_eq] using
    map_run_simulateQ_eq_of_query_map_eq ((impl (concrete native) native) ∘ₛ compiler) native Prod.fst
      perQuery client state

/-- The same evaluated full continuation receives exactly the original reply and private primitive poststate; only the explicitly strengthened controller transcript is projected away. -/
theorem continuation_source {Final : Type}
    (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp))
    (client : OracleComp (NativeSpec Reader E I D X Response) Result) (state : State A)
    (next : Result × A → ProbComp Final) :
    (((simulateQ (impl (concrete native) native) (simulateQ compiler client)).run state) >>=
      fun result => next (result.1, result.2.1)) =
        ((simulateQ native client).run state.1 >>= next) := by
  rw [← program_source native client state, bind_map_left]

/-- The extra disclosure bookkeeping has the complete original primitive uniform bill on every adaptive source path, including optional failures. -/
theorem uniform_iff (native : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp))
    (client : OracleComp (NativeSpec Reader E I D X Response) Result) (state : State A) (q : Nat) :
    ((simulateQ (impl (concrete native) native) (simulateQ compiler client)).run state).IsTotalQueryBound q ↔
      ((simulateQ native client).run state.1).IsTotalQueryBound q := by
  rw [← program_source native client state]
  simp only [IsTotalQueryBound, isQueryBound_map_iff]

/-- The concrete controller never calls a DH, identity, parser, or other non-KEM callback; agreeing only on the two KEM operations is sufficient for identical disclosed executions. -/
theorem concrete_only_kem
    (native alternative : QueryImpl (NativeSpec Reader E I D X Response) (StateT A ProbComp))
    (sameEncaps : ∀ key, native (.inl (.encapsulate key)) = alternative (.inl (.encapsulate key)))
    (sameDecaps : ∀ ciphertext handle, native (.inr (.decapsulate ciphertext handle)) = alternative (.inr (.decapsulate ciphertext handle))) :
    concrete native = concrete alternative := by
  funext query state
  cases query <;> simp only [concrete, sameEncaps, sameDecaps]

end BeaconcryptCore.Computational.PqxdhKemCoordinateController

/-- info: 'BeaconcryptCore.Computational.PqxdhKemCoordinateController.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCoordinateController.step_source

/-- info: 'BeaconcryptCore.Computational.PqxdhKemCoordinateController.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCoordinateController.program_source

/-- info: 'BeaconcryptCore.Computational.PqxdhKemCoordinateController.continuation_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCoordinateController.continuation_source

/-- info: 'BeaconcryptCore.Computational.PqxdhKemCoordinateController.uniform_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCoordinateController.uniform_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhKemCoordinateController.concrete_only_kem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhKemCoordinateController.concrete_only_kem

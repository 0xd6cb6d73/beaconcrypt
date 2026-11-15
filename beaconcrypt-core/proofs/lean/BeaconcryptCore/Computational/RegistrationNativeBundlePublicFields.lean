-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemBirthOwners

/-! Native publication preserves every stored public prekey, including all failed outgoing signatures and writers. This concrete support receipt lets private scalar reconstruction retain the selected challenge public key without assuming an unrelated key invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeBundlePublicFields
open RegistrationNativeBeaconFrontend
open RegistrationWorldAgreementCompiler (EnvState)
private def metadata {source : RegistrationNativeMldsa.Source} (owner : RegistrationNativeBeaconFrontend.Owner source) := owner.prekeyPublic
open PqxdhServerAuthExperiment (Setup)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}
private abbrev Keys := List (Std.Array U8 32#usize)

private def Keeps (expected : Keys) (work : M n KemSK mlSource Auxiliary Value) : Prop :=
  ∀ owners env result, owners.map metadata = expected →
    result ∈ support ((work.run owners).run env) → result.1.2.map metadata = expected

private theorem pure_keeps (expected : Keys) (value : Value) :
    Keeps expected (pure value : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact prior

private theorem bind_keeps {Next : Type} (expected : Keys) (work : M n KemSK mlSource Auxiliary Value)
    (next : Value → M n KemSK mlSource Auxiliary Next) (first : Keeps expected work)
    (rest : ∀ value, Keeps expected (next value)) : Keeps expected (work >>= next) := by
  intro owners env result prior supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first owners env middle prior reached) continued

private theorem lift_keeps (expected : Keys)
    (work : StateT (EnvState Auxiliary) (OracleComp (Trusted n KemSK)) Value) :
    Keeps expected (StateT.lift work : M n KemSK mlSource Auxiliary Value) := by
  intro owners env result prior supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨middle, _, returned⟩ := supported
  cases returned
  exact prior

private theorem simulate_keeps {Query : Type} {spec : OracleSpec Query} (expected : Keys)
    (implementation : QueryImpl spec (M n KemSK mlSource Auxiliary))
    (law : ∀ query, Keeps expected (implementation query)) (work : OracleComp spec Value) :
    Keeps expected (simulateQ implementation work) := by
  induction work using OracleComp.inductionOn with
  | pure value => exact pure_keeps expected value
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact bind_keeps expected _ _ (law query) ih

private theorem sample_keeps (expected : Keys) (work : ProbComp Value) :
    Keeps expected (sample (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) work) :=
  simulate_keeps expected (fun (query : unifSpec.Domain) => effect (.inl query))
    (fun _ => lift_keeps expected _) work

private theorem set_same (expected : Keys) (index : Nat) (key : Std.Array U8 32#usize)
    (found : expected[index]? = some key) : expected.set index key = expected := by
  obtain ⟨below, selected⟩ := List.getElem?_eq_some_iff.mp found
  rw [← selected]
  exact List.set_getElem_self below

private theorem current_keeps (expected : Keys) (index : Nat) (change : Owner mlSource → Owner mlSource)
    (same : ∀ owner, metadata (change owner) = metadata owner) :
    Keeps expected ((modify fun owners => match owners[index]? with
      | none => owners
      | some current => owners.set index (change current)) : M n KemSK mlSource Auxiliary Unit) := by
  intro owners env result prior supported
  simp only [StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : owners[index]? with
  | none => simpa only [found] using prior
  | some owner =>
      simp only [List.map_set, same, prior]
      apply set_same expected index (metadata owner)
      rw [← prior]
      simp [found]

private theorem phase_keeps (expected : Keys) (index : Nat) (phase : Phase) :
    Keeps expected (updatePhase (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) index phase) :=
  current_keeps expected index (fun owner => { owner with phase }) (fun _ => rfl)

private theorem log_keeps (expected : Keys) (index : Nat) (message : Pqxdh.Bytes)
    (signature : PqxdhEd25519EufCma.Ed25519Signature) :
    Keeps expected (logEd (n := n) (KemSK := KemSK) (mldsaSource := mlSource) (Auxiliary := Auxiliary) index message signature) :=
  current_keeps expected index
    (fun owner => { owner with edHistory := owner.edHistory ++ [.signed message signature] }) (fun _ => rfl)

private theorem outgoing_keeps (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (owner : Owner source) (expected : Keys) (query : RegistrationBeaconInitExecutor.Spec.Domain) :
    Keeps expected (outgoing (n := n) (Auxiliary := Auxiliary) setup source index owner query) := by
  classical
  rcases query with (hashRequest | signRequest) | edRequest
  · exact lift_keeps expected _
  · exact pure_keeps expected (core.option.Option.None : RegistrationSigningShared.SignReply)
  · simp only [outgoing]
    split
    · exact bind_keeps expected _ _ (log_keeps expected index _ _) (fun _ => pure_keeps expected _)
    · exact pure_keeps expected _

private noncomputable def bundled (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) : M n KemSK source Auxiliary (RustM (Option Pqxdh.Bytes)) := do
  let published ← simulateQ (outgoing setup source index owner)
    (RegistrationBeaconInitExecutor.begin wire.encodeInit ⟨owner.pin.binding⟩ (inputs setup owner)
      ⟨PqxdhRootTableInitialization.rootArray (setup.dh.publicKey oneTime)⟩ owner.pin)
  match published with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok finished) => do
      updatePhase index (.initSent finished.pending oneTime)
      let _ ← effect (.inr (.advanceOwner owner.worldOwner .initSent))
      pure (.ok (some finished.encoded))

private theorem bundled_keeps (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat) (owner : Owner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (expected : Keys) :
    Keeps expected (bundled (n := n) (Auxiliary := Auxiliary) setup source wire index owner oneTime) := by
  unfold bundled
  apply bind_keeps expected _ _ (simulate_keeps expected _ (outgoing_keeps setup source index owner expected) _)
  intro published
  cases published with
  | fail error | div => exact pure_keeps expected _
  | ok result => cases result with
    | Err previous => exact pure_keeps expected _
    | Ok finished => exact bind_keeps expected _ _ (phase_keeps expected index _) (fun _ =>
        bind_keeps expected _ _ (lift_keeps expected _) (fun _ => pure_keeps expected _))

/-- Every actual bundle retains the complete original sequence of public prekeys. -/
theorem bundle_metadata (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index : Nat)
    (owners : State source) (env : EnvState Auxiliary)
    (result : (RustM (Option Pqxdh.Bytes) × State source) × EnvState Auxiliary)
    (supported : result ∈ support (((bundle (n := n) setup source wire index).run owners).run env)) :
    result.1.2.map metadata = owners.map metadata := by
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : owners[index]? with
  | none => simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl
  | some owner =>
      rw [found] at supported
      cases phase : owner.phase <;> simp only [phase] at supported
      all_goals try { simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported; cases supported; rfl }
      case fresh =>
        exact (bind_keeps _ _ _ (sample_keeps _ _) (fun oneTime =>
          bundled_keeps setup source wire index owner oneTime _)) owners env result rfl supported
      case freshWithCoins oneTime =>
        exact (bundled_keeps setup source wire index owner oneTime _) owners env result rfl supported


end BeaconcryptCore.Computational.RegistrationNativeBundlePublicFields
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeBundlePublicFields.bundle_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeBundlePublicFields.bundle_metadata

import BeaconcryptCore.Computational.PqxdhJointDhExtractRoot
import BeaconcryptCore.Computational.PqxdhBeaconPhase2Shared

/-!
Actual reached selected-DH references need no secret value to decide the extracted Phase2 metadata admission. The ordinary valid-point/nonzero functional contract discharges only the hidden first and third DH zero checks. Exact raw identity pinning and locally known second/fourth checks remain source operations after the full ordered preparation. This is not a cryptographic authentication premise.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.RepresentationBridge PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhPhase2DhMetadata
open PqxdhJointIdentity PqxdhJointGapDh PqxdhPhase2GapDhSource
open PqxdhBeaconPhase2Preparation (Word32)

/-- The unavailable selected DH value is nonzero because the actual reached public point was admitted; no protocol-origin fact is required. -/
theorem selected_nonzero {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) (point : Word32) (admitted : domain.accepts (peer point) = true) :
    absBytes (materialize dh scalar (.selected (peer point))) ≠ Pqxdh.zero32 := by
  have nonzero := domain.nonzero scalar (peer point)
    (PqxdhPhase2InputBytes.word (materialize dh scalar (.selected (peer point))))
    (PqxdhPhase2GapDhInput.selected_value dh domain scalar point admitted)
  intro zero
  apply nonzero
  apply List.Vector.toList_injective
  exact zero

def knownNonzero {Response : Type} (collected : Inputs Response) : Prop :=
  absBytes collected.second ≠ Pqxdh.zero32 ∧ absBytes collected.fourth ≠ Pqxdh.zero32

set_option backward.isDefEq.respectTransparency false in
/-- Both unavailable checks follow from actual reached point admission; both locally held DH checks remain exact source tests. -/
theorem source_nonzero {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {Response : Type} (collected : Inputs Response)
    (references : References domain collected) :
    Pqxdh.dhNonZero (absBytes (materialize dh scalar collected.first), absBytes collected.second,
      absBytes (materialize dh scalar collected.third), absBytes collected.fourth) ↔ knownNonzero collected := by
  rw [references.1, references.2.1]
  constructor
  · intro all
    exact ⟨all.2.1, all.2.2.2⟩
  · intro known
    exact ⟨selected_nonzero dh domain scalar collected.serverConverted references.2.2.1, known.1,
      selected_nonzero dh domain scalar collected.ephemeral references.2.2.2, known.2⟩

/-- Mathematical realization is confined to the source side of the equality. -/
def realized {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {Response : Type} (collected : Inputs Response) : PqxdhBeaconPhase2Shared.Inputs Response Word32 :=
  ⟨collected.response, collected.ciphertext, collected.ephemeral, collected.server, collected.assigned,
    ⟨materialize dh scalar collected.first, collected.second, materialize dh scalar collected.third,
      collected.fourth, collected.shared⟩⟩

/-- This metadata test contains neither unavailable DH coordinate. Exact raw pinning and both local zero checks remain. -/
noncomputable def admitted {Response : Type} (control : pqxdh.BeaconInitSent)
    (collected : Inputs Response) : Option PqxdhBeaconPhase2Shared.Metadata := by
  classical
  exact if absBytes control.expected_server_binding.identity_public_key = absBytes collected.server then
    if knownNonzero collected then
      some ⟨control.expected_server_binding, collected.assigned, PqxdhBeaconPhase2Shared.associatedData control⟩
    else none
  else none

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual core acceptance and metadata agree at every reached selected-DH input, including changed identities and rejected local DH results. -/
theorem admitted_exact {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {Response : Type} (control : pqxdh.BeaconInitSent)
    (collected : Inputs Response) (references : References domain collected) :
    PqxdhBeaconPhase2Shared.optionalMetadata (PqxdhBeaconPhase2Preparation.normalPrepare control
      (concreteInputs dh scalar collected).finishInputs) = admitted control collected := by
  rw [show concreteInputs dh scalar collected =
    PqxdhBeaconPhase2Shared.concreteInputs id (realized dh scalar collected) from rfl,
    PqxdhBeaconPhase2Shared.admitted_exact]
  simp only [PqxdhBeaconPhase2Shared.admitted, PqxdhBeaconPhase2Shared.nonzero, realized, admitted]
  by_cases known : knownNonzero collected
  · simp only [known, (source_nonzero dh domain scalar collected references).mpr known, ite_true]
  · have hidden := mt (source_nonzero dh domain scalar collected references).mp known
    simp only [known, hidden, ite_false]

/-- Pending simulator state stores actual local replies and metadata, without a DH materializer. -/
structure Prepared (Response : Type) where
  collected : Inputs Response
  metadata : PqxdhBeaconPhase2Shared.Metadata

/-- Full source input and metadata are retained in the mathematical relation, not supplied as simulator data. -/
def ReadyRel {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {Response : Type} (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : Prepared Response) : Prop :=
  PqxdhBeaconPhase2Shared.ReadyRel id original
    (PqxdhBeaconPhase2Shared.prepared (realized dh scalar pending.collected) pending.metadata)

/-- Actual successful preparation establishes every retained source field and the exact extracted input builder. -/
theorem prepared_related {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {Response : Type} (control : pqxdh.BeaconInitSent) (collected : Inputs Response)
    (candidate : pqxdh.BeaconRegistrationCandidate)
    (actual : PqxdhBeaconPhase2Preparation.normalPrepare control
      (concreteInputs dh scalar collected).finishInputs = .Ok candidate) :
    ReadyRel dh scalar ⟨collected.response, collected.ciphertext, collected.ephemeral, candidate⟩
      ⟨collected, PqxdhBeaconPhase2Shared.candidateMetadata candidate⟩ :=
  PqxdhBeaconPhase2Shared.prepared_related id control (realized dh scalar collected) candidate actual

/-- The native logical erasure callback is executed after admission on both outcomes. Its ordinary no-observation law removes unavailable temporary bytes from the executable continuation. -/
theorem afterInputs_continuation {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {I D K X Response Result : Type} {m : Type → Type}
    [Monad m] [LawfulMonad m]
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) m)
    (visit : Word32 → m Unit) (erase : ∀ secrets, aux (.eraseShared secrets) = pure ())
    (control : pqxdh.BeaconInitSent) (collected : Inputs Response) (references : References domain collected)
    (nextNative : Option (PqxdhBeaconPhase2Preparation.Prepared Response) → m Result)
    (nextPending : Option (Prepared Response) → m Result)
    (rejected : nextNative none = nextPending none)
    (accepted : ∀ original metadata, admitted control collected = some metadata → ReadyRel dh scalar original ⟨collected, metadata⟩ →
      nextNative (some original) = nextPending (some ⟨collected, metadata⟩)) :
    (simulateQ (nativeImpl dh scalar aux visit)
      (PqxdhBeaconPhase2Preparation.afterInputs control (concreteInputs dh scalar collected)) >>= nextNative) =
      nextPending ((admitted control collected).map (fun metadata => ⟨collected, metadata⟩)) := by
  simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind, simulateQ_spec_query,
    nativeImpl, erase, pure_bind, simulateQ_pure]
  have metadataEq := (admitted_exact dh domain scalar control collected references).symm
  cases actual : PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs dh scalar collected).finishInputs with
  | Err error =>
      simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
      simpa only [pure_bind, metadataEq, Option.map_none] using rejected
  | Ok candidate =>
      simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
      simpa only [pure_bind, metadataEq, Option.map_some, concreteInputs] using
        accepted _ _ metadataEq (prepared_related dh scalar control collected candidate actual)

/-- Source-shaped preparation uses the existing ordered prefix and only available metadata. Logical temporary erasure has no observable callback effect in the native interpreter. -/
noncomputable def prepare {I D K X Response : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    OracleComp (PrefixSpec I D K X Response) (Option (Prepared Response)) := do
  let collected ← collect identity oneTime kem raw
  pure (collected.bind (fun value => (admitted control value).map (fun metadata => ⟨value, metadata⟩)))

set_option backward.isDefEq.respectTransparency false in
/-- The entire actual preparation and arbitrary complete-state continuation are preserved. Reached references are derived from the source prefix, never assumed of an attacker-selected response. -/
theorem prepare_continuation {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) {I D K X Response A Result : Type}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A ProbComp))
    (visit : Word32 → StateT A ProbComp Unit) (erase : ∀ secrets, aux (.eraseShared secrets) = pure ())
    (control : pqxdh.BeaconInitSent) (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (initial : A)
    (nextNative : Option (PqxdhBeaconPhase2Preparation.Prepared Response) × A → ProbComp Result)
    (nextPending : Option (Prepared Response) × A → ProbComp Result)
    (rejected : ∀ state, nextNative (none, state) = nextPending (none, state))
    (accepted : ∀ original pending state, References domain pending.collected →
      admitted control pending.collected = some pending.metadata → ReadyRel dh scalar original pending →
      nextNative (some original, state) = nextPending (some pending, state)) :
    ((simulateQ (nativeImpl dh scalar aux visit)
      (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)).run initial >>= nextNative) =
      ((simulateQ (prefixImpl domain aux visit) (prepare control identity oneTime kem raw)).run initial >>= nextPending) := by
  rw [PqxdhPhase2GapDhSource.prepare_continuation dh domain scalar aux visit]
  simp only [prepare, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc]
  apply bind_congr_of_forall_mem_support
  rintro ⟨collected, state⟩ reached
  cases collected with
  | none => exact rejected state
  | some collected =>
      have references := collect_references domain aux visit identity oneTime kem raw initial state collected reached
      simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind, simulateQ_spec_query,
        nativeImpl, erase, simulateQ_pure, StateT.run_pure, pure_bind]
      have metadataEq := (admitted_exact dh domain scalar control collected references).symm
      cases actual : PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs dh scalar collected).finishInputs with
      | Err error =>
          simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
          simpa only [metadataEq, Option.bind_some, Option.map_none] using rejected state
      | Ok candidate =>
          simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
          simpa only [metadataEq, Option.bind_some, Option.map_some, concreteInputs] using
            accepted _ _ state references metadataEq (prepared_related dh scalar control collected candidate actual)

/-- Successful secret-free admission retains exact raw pinned identity equality, local DH checks, assigned ID and associated data. -/
theorem admitted_fields {Response : Type} (control : pqxdh.BeaconInitSent) (collected : Inputs Response)
    (metadata : PqxdhBeaconPhase2Shared.Metadata) (accepted : admitted control collected = some metadata) :
    absBytes control.expected_server_binding.identity_public_key = absBytes collected.server ∧
      knownNonzero collected ∧ metadata = ⟨control.expected_server_binding, collected.assigned,
        PqxdhBeaconPhase2Shared.associatedData control⟩ := by
  unfold admitted at accepted
  split at accepted <;> simp_all only [reduceCtorEq]
  split at accepted <;> simp_all

/-- Actual successful admission and ordinary joint public conversion identify the hidden Server coordinate. No identity origin or authentication premise is inserted. -/
theorem pinned_conversion (c : Pqxdh.Crypto) (joint : Primitives)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    (seed : IdentitySeed) {Response : Type} (control : pqxdh.BeaconInitSent)
    (collected : Inputs Response) (metadata : PqxdhBeaconPhase2Shared.Metadata)
    (pin : absBytes control.expected_server_binding.identity_public_key = (joint.publicKeys seed).ed25519.toList)
    (accepted : admitted control collected = some metadata)
    (converted : c.xpkConv (absBytes collected.server) = some (absBytes collected.serverConverted)) :
    peer collected.serverConverted = (joint.publicKeys seed).convertedX25519 := by
  have actualPin := (admitted_fields control collected metadata accepted).1.symm.trans pin
  rw [actualPin] at converted
  apply List.Vector.toList_injective
  exact Option.some.inj (converted.symm.trans (jointPublic_conversion c joint secretOfSeed wiring seed))

/-- Root-input clearing leaves precisely the original public-free metadata; no unavailable DH value survives into the native record tail. -/
theorem cleared_related {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {Response : Type} (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : Prepared Response) (related : ReadyRel dh scalar original pending) :
    PqxdhBeaconPhase2Publication.clearedCandidate original.candidate =
      PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata :=
  PqxdhBeaconPhase2Shared.cleared_related id original
    (PqxdhBeaconPhase2Shared.prepared (realized dh scalar pending.collected) pending.metadata) related

/-- Metadata processing adds no oracle work to the original twelve-callback prefix. The native logical-erasure functional law is separate. -/
theorem prepare_bound {I D K X Response : Type} (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (prepare (X := X) (Response := Response) control identity oneTime kem raw).IsTotalQueryBound 12 := by
  unfold prepare
  exact isTotalQueryBound_bind (collect_bound identity oneTime kem raw) (n₂ := 0) (fun _ => by simp [IsTotalQueryBound, isQueryBound_pure])

/-- The actual interpreted preparation pays all ten local callbacks and both selected-DH call effects, including every rejection. Pure metadata handling adds no oracle request. -/
theorem interpreted_bound {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response A ι : Type} {target : OracleSpec ι}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A (OracleComp target)))
    (visit : Word32 → StateT A (OracleComp target) Unit)
    (predicate : target.Domain → Prop) [DecidablePred predicate] (qAux qVisit : Nat)
    (auxBound : ∀ query state, ((aux query).run state).IsQueryBoundP predicate qAux)
    (visitBound : ∀ input state, ((visit input).run state).IsQueryBoundP predicate qVisit)
    (control : pqxdh.BeaconInitSent) (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (initial : A) :
    ((simulateQ (prefixImpl domain aux visit) (prepare control identity oneTime kem raw)).run initial).IsQueryBoundP
      predicate (10 * qAux + 2 * qVisit) := by
  simp only [prepare, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  exact isQueryBoundP_bind (PqxdhPhase2GapDhSource.interpreted_bound domain aux visit predicate qAux qVisit
    auxBound visitBound identity oneTime kem raw initial) (m := 0) (fun _ _ => isQueryBoundP_pure predicate _ 0)

set_option backward.isDefEq.respectTransparency false in
/-- The same complete source execution also supplies its actual reached public conversion, using only the native callback functional law. Pinning still occurs after decapsulation and all DH calls. -/
theorem prepare_converted_continuation {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) (c : Pqxdh.Crypto) {I D K X Response A Result : Type}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A ProbComp))
    (conversion : ∀ value initial converted final,
      (some converted, final) ∈ support ((aux (.publicConversion value)).run initial) →
        c.xpkConv (absBytes value) = some (absBytes converted))
    (visit : Word32 → StateT A ProbComp Unit) (erase : ∀ secrets, aux (.eraseShared secrets) = pure ())
    (control : pqxdh.BeaconInitSent) (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (initial : A)
    (nextNative : Option (PqxdhBeaconPhase2Preparation.Prepared Response) × A → ProbComp Result)
    (nextPending : Option (Prepared Response) × A → ProbComp Result)
    (rejected : ∀ state, nextNative (none, state) = nextPending (none, state))
    (accepted : ∀ original pending state, References domain pending.collected →
      c.xpkConv (absBytes pending.collected.server) = some (absBytes pending.collected.serverConverted) →
      admitted control pending.collected = some pending.metadata → ReadyRel dh scalar original pending →
      nextNative (some original, state) = nextPending (some pending, state)) :
    ((simulateQ (nativeImpl dh scalar aux visit)
      (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)).run initial >>= nextNative) =
      ((simulateQ (prefixImpl domain aux visit) (prepare control identity oneTime kem raw)).run initial >>= nextPending) := by
  rw [PqxdhPhase2GapDhSource.prepare_continuation dh domain scalar aux visit]
  simp only [prepare, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, pure_bind, bind_assoc]
  apply bind_congr_of_forall_mem_support
  rintro ⟨collected, state⟩ reached
  cases collected with
  | none => exact rejected state
  | some collected =>
      have references := collect_references domain aux visit identity oneTime kem raw initial state collected reached
      have converted := collect_conversion domain c aux conversion visit identity oneTime kem raw initial state collected reached
      simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind, simulateQ_spec_query,
        nativeImpl, erase, simulateQ_pure, StateT.run_pure, pure_bind]
      have metadataEq := (admitted_exact dh domain scalar control collected references).symm
      cases actual : PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs dh scalar collected).finishInputs with
      | Err error =>
          simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
          simpa only [metadataEq, Option.bind_some, Option.map_none] using rejected state
      | Ok candidate =>
          simp only [actual, PqxdhBeaconPhase2Shared.optionalMetadata] at metadataEq
          simpa only [metadataEq, Option.bind_some, Option.map_some, concreteInputs] using
            accepted _ _ state references converted metadataEq (prepared_related dh scalar control collected candidate actual)


end BeaconcryptCore.Computational.PqxdhPhase2DhMetadata

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.selected_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.selected_nonzero

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.source_nonzero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.source_nonzero

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.admitted_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.admitted_exact

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepared_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepared_related

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.afterInputs_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.afterInputs_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepare_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepare_continuation

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.admitted_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.admitted_fields

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.pinned_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.pinned_conversion

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.cleared_related' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.cleared_related

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepare_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepare_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.interpreted_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.interpreted_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepare_converted_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhMetadata.prepare_converted_continuation

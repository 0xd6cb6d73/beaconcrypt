import BeaconcryptCore.Computational.PqxdhPhase2GapDhSource
import BeaconcryptCore.Refinement.PqxdhSurface

/-!
The reached source prefix determines a two-unknown-coordinate root address. Its first coordinate is the selected pinned Server identity's static DH with the selected Beacon prekey; its third is that same prekey's DH with the actual response ephemeral encoding. Every other coordinate remains the actual local source reply. The ordinary Gap-DH matcher recognizes precisely the extracted core's constructed 192-byte input and retains its complete decision history.

Recognition does not supply the root or an Extract output. Such derived outputs require a separate explicitly related-input endpoint and a complete source continuation compiler.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.RepresentationBridge PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2GapDhInput
open PqxdhJointIdentity PqxdhJointGapDh PqxdhPhase2GapDhSource
open PqxdhBeaconPhase2Preparation (Word32)

/-- This private simulator address contains public peers and locally known DH/KEM replies; it contains neither selected secret nor their DH outputs. -/
def address {Response : Type} (publicValue : PublicChallenge) (input : Inputs Response) : TupleAddress :=
  ⟨publicValue.prekey, peer input.ephemeral, PqxdhPhase2InputBytes.word input.second,
    PqxdhPhase2InputBytes.word input.fourth, PqxdhPhase2InputBytes.word input.shared⟩

/-- Public native admission identifies the actual successful output in the private mathematical interpretation. -/
theorem selected_value {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) (input : Word32) (admitted : domain.accepts (peer input) = true) :
    dh.dh scalar (peer input) =
      some (PqxdhPhase2InputBytes.word (materialize dh scalar (.selected (peer input)))) := by
  cases actual : dh.dh scalar (peer input) with
  | none =>
    have available := domain.available scalar (peer input)
    simp [actual, admitted] at available
  | some value =>
    simp [materialize, actual, word, PqxdhPhase2InputBytes.word_rootArray]

/-- The source's two retained prekey replies are exactly the two unavailable coordinates of the existing joint challenge. -/
theorem source_coordinates {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type} (input : Inputs Response)
    (references : References domain input)
    (converted : peer input.serverConverted = (joint.publicKeys seed).convertedX25519) :
    joint.staticDh seed (dh.publicKey scalar) =
      some (PqxdhPhase2InputBytes.word (materialize dh scalar input.first)) ∧
    dh.dh scalar (peer input.ephemeral) =
      some (PqxdhPhase2InputBytes.word (materialize dh scalar input.third)) := by
  constructor
  · rw [dh.agreement, ← converted, references.1]
    exact selected_value dh domain scalar input.serverConverted references.2.2.1
  · rw [references.2.1]
    exact selected_value dh domain scalar input.ephemeral references.2.2.2

/-- The existing Gap-DH address reconstructs exactly the original extracted 192-byte source input, including all actual local values in source order. -/
theorem source_input {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type} (input : Inputs Response)
    (references : References domain input)
    (converted : peer input.serverConverted = (joint.publicKeys seed).convertedX25519)
    (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input (concreteInputs dh scalar input).finishInputs.shared_secrets = ok (.Ok root)) :
    sourceInput joint dh seed scalar (address (challenge joint dh seed scalar) input) = some (absBytes root.bytes) := by
  obtain ⟨first, third⟩ := source_coordinates dh domain seed scalar input references converted
  have bytes := PqxdhPhase2InputBytes.root_input _ root built
  simp only [sourceInput, address, challenge, first, third]
  exact congrArg some bytes.symm

/-- Actual extracted admission and the existing joint-identity conversion law identify the pinned Server coordinate without requiring its seed in the executable prefix. -/
theorem pinned_conversion (c : Pqxdh.Crypto) (joint : Primitives)
    (dh : DhInterface joint) (scalar : ScalarBytes)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring c joint secretOfSeed)
    {count : Nat} (state : PqxdhPhase1AcceptanceOracle.BareState count)
    (server : PqxdhPhase2JointIdentity.Converted) (seed : IdentitySeed)
    (represented : PqxdhPhase2JointIdentity.Represents joint state server seed)
    {Response : Type} (input : Inputs Response) (control : pqxdh.BeaconInitSent)
    (pin : absBytes control.expected_server_binding.identity_public_key = server.publicIdentity.ed25519.toList)
    (candidate : pqxdh.BeaconRegistrationCandidate)
    (prepared : PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs dh scalar input).finishInputs = .Ok candidate)
    (converted : c.xpkConv (absBytes input.server) = some (absBytes input.serverConverted)) :
    peer input.serverConverted = (joint.publicKeys seed).convertedX25519 := by
  have shape := BeaconcryptCore.Refinement.PqxdhSurface.beacon_prepare_finish_success_shape control (concreteInputs dh scalar input).finishInputs
    candidate ((PqxdhBeaconPhase2Preparation.normalPrepare_exact _ _).trans (congrArg ok prepared))
  have actualPin : absBytes input.server = server.publicIdentity.ed25519.toList :=
    (congrArg absBytes shape.1).symm.trans pin
  have jointConversion := PqxdhPhase2JointIdentity.converted_public c joint secretOfSeed wiring state server seed represented
  rw [actualPin] at converted
  rw [represented.2]
  apply List.Vector.toList_injective
  exact Option.some.inj (converted.symm.trans jointConversion)

/-- Executable address recognition uses only the public challenge and retained source prefix. It requests no raw secret or derived root output. -/
def test {Response : Type} (publicValue : PublicChallenge) (input : Inputs Response)
    (candidate : Pqxdh.Bytes) : OracleComp PqxdhJointGapDh.AdversarySpec Bool :=
  testInput (address publicValue input) candidate

/-- The complete matcher continuation recognizes exact source-root equality, retaining both decision attempts and all previous history. -/
theorem test_source {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response Result : Type} (input : Inputs Response)
    (references : References domain input)
    (converted : peer input.serverConverted = (joint.publicKeys seed).convertedX25519)
    (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input (concreteInputs dh scalar input).finishInputs.shared_secrets = ok (.Ok root))
    (candidate : Pqxdh.Bytes) (history : PqxdhJointGapDh.History) (next : Bool → PqxdhJointGapDh.History → ProbComp Result) :
    ((simulateQ (serviceImpl joint dh seed scalar) (test (challenge joint dh seed scalar) input candidate)).run history >>=
      fun result => next result.1 result.2) =
      next (decide (absBytes root.bytes = candidate))
        (testOutcome (joint.staticDh seed (dh.publicKey scalar)) (dh.dh scalar (peer input.ephemeral))
          (address (challenge joint dh seed scalar) input) candidate history).2 := by
  rw [test, testInput_continuation, source_input dh domain seed scalar input references converted root built]
  simp only [Option.some.injEq]
  rfl

/-- A supported source prefix and actual successful extracted preparation discharge the matcher's coordinate premises using the existing joint identity interface. -/
theorem prepared_test (c : Pqxdh.Crypto) (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain dh)
    (scalar : ScalarBytes) (secretOfSeed : IdentitySeed → List.Vector UInt8 64)
    (wiring : SourceWiring c joint secretOfSeed)
    {count : Nat} (state : PqxdhPhase1AcceptanceOracle.BareState count)
    (server : PqxdhPhase2JointIdentity.Converted) (seed : IdentitySeed)
    (represented : PqxdhPhase2JointIdentity.Represents joint state server seed)
    {I D K X Response A Result : Type}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response) (StateT A ProbComp))
    (conversion : ∀ value initial converted final,
      (some converted, final) ∈ support ((aux (.publicConversion value)).run initial) →
        c.xpkConv (absBytes value) = some (absBytes converted))
    (visit : Word32 → StateT A ProbComp Unit) (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes)
    (initial final : A) (input : Inputs Response)
    (reached : (some input, final) ∈ support
      ((simulateQ (prefixImpl domain aux visit) (collect identity oneTime kem raw)).run initial))
    (control : pqxdh.BeaconInitSent)
    (pin : absBytes control.expected_server_binding.identity_public_key = server.publicIdentity.ed25519.toList)
    (prepared : pqxdh.BeaconRegistrationCandidate)
    (admitted : PqxdhBeaconPhase2Preparation.normalPrepare control (concreteInputs dh scalar input).finishInputs = .Ok prepared)
    (candidate : Pqxdh.Bytes) (history : PqxdhJointGapDh.History)
    (next : Bool → PqxdhJointGapDh.History → A → ProbComp Result) :
    ((simulateQ (serviceImpl joint dh seed scalar) (test (challenge joint dh seed scalar) input candidate)).run history >>=
      fun result => next result.1 result.2 final) =
      next (decide (absBytes prepared.root_key_input.bytes = candidate))
        (testOutcome (joint.staticDh seed (dh.publicKey scalar)) (dh.dh scalar (peer input.ephemeral))
          (address (challenge joint dh seed scalar) input) candidate history).2 final := by
  have references := collect_references domain aux visit identity oneTime kem raw initial final input reached
  have converted := collect_conversion domain c aux conversion visit identity oneTime kem raw initial final input reached
  have pinned := pinned_conversion c joint dh scalar secretOfSeed wiring state server seed represented input control pin prepared admitted converted
  have shape := BeaconcryptCore.Refinement.PqxdhSurface.beacon_prepare_finish_success_shape control (concreteInputs dh scalar input).finishInputs
    prepared ((PqxdhBeaconPhase2Preparation.normalPrepare_exact _ _).trans (congrArg ok admitted))
  exact test_source dh domain seed scalar input references pinned prepared.root_key_input shape.2.2.2.1 candidate history
    (fun answer log => next answer log final)

/-- Each candidate recognition costs at most two ordinary anchored decisions and no signing or explicit uniform query; malformed candidates incur neither decision. -/
theorem test_bills {Response : Type} (publicValue : PublicChallenge) (input : Inputs Response) (candidate : Pqxdh.Bytes) :
    (test publicValue input candidate).IsTotalQueryBound 2 ∧
    (test publicValue input candidate).IsQueryBoundP PqxdhJointGapDh.IsSigning 0 ∧
    (test publicValue input candidate).IsQueryBoundP PqxdhJointGapDh.IsUniform 0 := by
  refine ⟨testInput_query_bound _ _, testInput_excludes _ _ _ ?_, testInput_excludes _ _ _ ?_⟩
  · intro side peer candidate
    simp [PqxdhJointGapDh.IsSigning]
  · intro side peer candidate
    simp [PqxdhJointGapDh.IsUniform]

end BeaconcryptCore.Computational.PqxdhPhase2GapDhInput

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.selected_value' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.selected_value

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.source_coordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.source_coordinates

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.source_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.source_input

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.pinned_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.pinned_conversion

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.test_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.test_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.prepared_test' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.prepared_test

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.test_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2GapDhInput.test_bills

import BeaconcryptCore.Computational.RegistrationNativeRelatedFamily
import BeaconcryptCore.Computational.PqxdhJointDhExtractRoot

/-!
Executable root-valued clients of the additional joint-DH Extract family. Source requests contain only public peer encodings and actual locally available coordinates. Root expansion makes one explicitly billed real HMAC call. The whole root-valued service reduces to one ordinary distinguishing bit, preserving all history and cache instrumentation. No smallness, derived-input distribution security, fresh-session selection or whole-source compiler premise is introduced.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.RepresentationBridge PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.RegistrationNativeRelatedRoot
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointIdentity RegistrationNativeRelatedFamily
open PqxdhJointGapDh (DhInterface ScalarBytes PublicChallenge)

/-- The request has neither selected secret nor either unavailable DH output. -/
def beaconMessage {Response : Type} (publicValue : PublicChallenge)
    (collected : PqxdhPhase2GapDhSource.Inputs Response) : Message :=
  ⟨publicValue.prekey, .selected (PqxdhPhase2GapDhSource.peer collected.ephemeral),
    PqxdhPhase2InputBytes.word collected.second, PqxdhPhase2InputBytes.word collected.fourth,
    PqxdhPhase2InputBytes.word collected.shared⟩

/-- Actual pin and ephemeral operands are public; neither selected prekey scalar nor either DH output occurs in this message. -/
def pinnedBeaconMessage {Response : Type} (collected : PqxdhPhase2GapDhSource.Inputs Response) : Message :=
  ⟨PqxdhPhase2GapDhSource.peer collected.serverConverted,
    .pinned (PqxdhPhase2GapDhSource.peer collected.ephemeral),
    PqxdhPhase2InputBytes.word collected.second, PqxdhPhase2InputBytes.word collected.fourth,
    PqxdhPhase2InputBytes.word collected.shared⟩

/-- Ordinary owners can supply their actual locally computed DH values without borrowing either selected secret. -/
def suppliedMessage (first second third fourth kem : DhOutput) : Message :=
  ⟨List.Vector.replicate 32 0, .supplied first third, second, fourth, kem⟩

/-- Server-generated ephemeral material supplies the third coordinate locally, even for an arbitrary admitted prekey without a known scalar. -/
def serverMessage (prekey : PeerEncoding) (second third fourth kem : DhOutput) : Message :=
  ⟨prekey, .known third, second, fourth, kem⟩

/-- This executable descriptor denotes the existing source-shaped two-coordinate input. Peer metadata is not cryptographically injective. -/
theorem beacon_input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) {Response : Type} (collected : PqxdhPhase2GapDhSource.Inputs Response) :
    input joint dh seed scalar (beaconMessage (PqxdhJointGapDh.challenge joint dh seed scalar) collected) =
      PqxdhJointGapDh.sourceInput joint dh seed scalar
        (PqxdhPhase2GapDhInput.address (PqxdhJointGapDh.challenge joint dh seed scalar) collected) := by
  rfl

/-- The prior source callback/identity proofs discharge the descriptor against the exact extracted 192-byte builder. This statement needs no unavailable value in the executable request. -/
theorem beacon_source {joint : Primitives} (dh : DhInterface joint)
    (domain : PqxdhPhase2GapDhSource.PublicDomain dh) (seed : IdentitySeed) (scalar : ScalarBytes)
    {Response : Type} (collected : PqxdhPhase2GapDhSource.Inputs Response)
    (references : PqxdhPhase2GapDhSource.References domain collected)
    (converted : PqxdhPhase2GapDhSource.peer collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (root : pqxdh.RootKeyInput)
    (built : pqxdh.build_root_key_input
      (PqxdhPhase2GapDhSource.concreteInputs dh scalar collected).finishInputs.shared_secrets = ok (.Ok root)) :
    input joint dh seed scalar (beaconMessage (PqxdhJointGapDh.challenge joint dh seed scalar) collected) =
      some (absBytes root.bytes) := by
  rw [beacon_input]
  exact PqxdhPhase2GapDhInput.source_input dh domain seed scalar collected references converted root built

/-- The Server request needs only its ordinary static-DH first reply; all other supplied fields are exact caller-held source values. -/
theorem server_input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (prekey : PeerEncoding) (second third fourth kem : DhOutput) :
    input joint dh seed scalar (serverMessage prekey second third fourth kem) =
      (joint.staticDh seed prekey).map (fun first =>
        PqxdhJointGapDh.assemble ⟨prekey, prekey, second, fourth, kem⟩ first third) := by
  cases actual : joint.staticDh seed prekey <;> simp [input, serverMessage, firstValue, thirdValue, address, actual]

/-- One family request and, on success, one real HMAC expansion; the source caller receives only the optional 32-byte projection. -/
def root (message : Message) : OracleComp Spec (Option RootOutput) := do
  let prk ← Spec.query (.inr (.derive message))
  match prk with
  | none => pure none
  | some value => do
      let block ← Spec.query (.inr (.publicHmac value rootExpandInput))
      pure (some (first32 block))

/-- The retained analysis state charges and records both actual primitive calls. It is not exposed in the root API reply. -/
def rootState (hmac : HmacSha512) (message : Message) (bytes : Pqxdh.Bytes) (state : State) : State :=
  let prk := extract hmac bytes
  let block := hmac.eval prk rootExpandInput
  ⟨state.history ++ [.derive message (some prk), .publicHmac prk rootExpandInput block],
    state.cache.cacheQuery bytes prk⟩

def nativeRoot (source : FixedHkdfSha512NoSaltSource) (bytes : Pqxdh.Bytes) : RootOutput :=
  ⟨Pqxdh.rootSecret source.crypto bytes, Pqxdh.rootSecret_length source.crypto bytes⟩

/-- Actual fixed-HKDF source root and complete callback instrumentation, including rejection. -/
def sourceRoot (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) : StateT State ProbComp (Option RootOutput) := fun state =>
  match input joint dh seed scalar message with
  | none => pure (none, { state with history := state.history ++ [.derive message none] })
  | some bytes => pure (some (nativeRoot source bytes), rootState hmac message bytes state)

set_option backward.isDefEq.respectTransparency false in
/-- The real primitive reduction returns the exact source root, with its optional outcome and complete history/cache before any continuation. -/
theorem root_real (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (message : Message) :
    simulateQ (realImpl hmac joint dh seed scalar) (root message) =
      sourceRoot source hmac joint dh seed scalar message := by
  funext state
  change (simulateQ (realImpl hmac joint dh seed scalar) (root message)).run state =
    (sourceRoot source hmac joint dh seed scalar message).run state
  simp only [root, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, real_derive]
  cases actual : input joint dh seed scalar message <;>
    simp only [pure_bind, simulateQ_pure, StateT.run_pure, simulateQ_bind,
      simulateQ_spec_query, StateT.run_bind, realImpl, public_evaluation]
  all_goals simp [sourceRoot, actual, rootState, nativeRoot,
    sourceRootOutput_eq source hmac correct, expandRoot, StateT.run, List.append_assoc]

inductive RootRequest where
  | sign : Pqxdh.Bytes → RootRequest
  | publicHmac : HmacBlock → Pqxdh.Bytes → RootRequest
  | derive : Message → RootRequest

abbrev RootPrimitive : OracleSpec RootRequest
  | .sign _ => PqxdhEd25519EufCma.Ed25519Signature
  | .publicHmac _ _ => HmacBlock
  | .derive _ => Option RootOutput
abbrev RootSpec := unifSpec + RootPrimitive

/-- The executable reduction has no selected identity seed or prekey scalar. -/
def reduction : QueryImpl RootSpec (OracleComp Spec)
  | .inl coin => Spec.query (.inl coin)
  | .inr (.sign bytes) => Spec.query (.inr (.sign bytes))
  | .inr (.publicHmac key bytes) => Spec.query (.inr (.publicHmac key bytes))
  | .inr (.derive message) => root message

noncomputable def sourceImpl (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes) :
    QueryImpl RootSpec (StateT State ProbComp)
  | .inl coin => realImpl hmac joint dh seed scalar (.inl coin)
  | .inr (.sign bytes) => realImpl hmac joint dh seed scalar (.inr (.sign bytes))
  | .inr (.publicHmac key bytes) => realImpl hmac joint dh seed scalar (.inr (.publicHmac key bytes))
  | .inr (.derive message) => sourceRoot source hmac joint dh seed scalar message

set_option backward.isDefEq.respectTransparency false in
/-- Every real root-valued query has the original source meaning, including the same joint signing and all public fixed evaluations. -/
theorem reduction_step (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) :
    realImpl hmac joint dh seed scalar ∘ₛ reduction = sourceImpl source hmac joint dh seed scalar := by
  funext query
  cases query with
  | inl coin => simp only [QueryImpl.compose, reduction, simulateQ_spec_query, sourceImpl]
  | inr request =>
      cases request <;> simp only [QueryImpl.compose, reduction, simulateQ_spec_query, sourceImpl,
        root_real source hmac correct]

/-- Arbitrary adaptive root/signing/public-evaluation clients retain their complete result and state. No whole-schedule equality is assumed. -/
theorem reduction_complete {Result : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (seed : IdentitySeed) (scalar : ScalarBytes) (client : OracleComp RootSpec Result) (state : State) :
    (simulateQ (realImpl hmac joint dh seed scalar) (simulateQ reduction client)).run state =
      (simulateQ (sourceImpl source hmac joint dh seed scalar) client).run state := by
  rw [← QueryImpl.simulateQ_compose, reduction_step source hmac correct]

noncomputable def sourceGame (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (client : PublicChallenge → OracleComp RootSpec Bool) : ProbComp Bool := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  (simulateQ (sourceImpl source hmac joint dh seed scalar)
    (client (PqxdhJointGapDh.challenge joint dh seed scalar))).run' empty

noncomputable def idealRootGame (hmac : HmacSha512) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp RootSpec Bool) : ProbComp Bool :=
  idealGame hmac joint dh (fun publicValue => simulateQ reduction (client publicValue))

/-- The exact correlated endpoint sampler and entire root client have coefficient-one game equality. This law does not exchange any source generator with a continuation. -/
theorem game_real (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp RootSpec Bool) :
    realGame hmac joint dh (fun publicValue => simulateQ reduction (client publicValue)) =
      sourceGame source hmac joint dh client := by
  simp only [realGame, sourceGame, ← QueryImpl.simulateQ_compose, reduction_step source hmac correct]

/-- The root-service comparison has exactly one explicitly additional family advantage, with no multiplicative loss. This is not an authentication bound or an assertion that the family advantage is small. -/
theorem advantage_exact (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (correct : SourceRootCorrect source hmac) (joint : Primitives) (dh : DhInterface joint)
    (client : PublicChallenge → OracleComp RootSpec Bool) :
    (sourceGame source hmac joint dh client).boolDistance (idealRootGame hmac joint dh client) =
      advantage hmac joint dh (fun publicValue => simulateQ reduction (client publicValue)) := by
  rw [RegistrationNativeRelatedFamily.advantage, game_real source hmac correct]
  rfl


/-- The pin-free descriptor denotes precisely the two actual selected-prekey DH operands. -/
theorem pinned_input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) {Response : Type} (collected : PqxdhPhase2GapDhSource.Inputs Response) :
    input joint dh seed scalar (pinnedBeaconMessage collected) = (do
      let first ← dh.dh scalar (PqxdhPhase2GapDhSource.peer collected.serverConverted)
      let third ← dh.dh scalar (PqxdhPhase2GapDhSource.peer collected.ephemeral)
      pure (PqxdhJointGapDh.assemble (address (pinnedBeaconMessage collected)) first third)) := rfl

/-- Fully supplied ordinary inputs retain the exact source layout and can still alias any other descriptor at the literal byte table. -/
theorem supplied_input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed)
    (scalar : ScalarBytes) (first second third fourth kem : DhOutput) :
    input joint dh seed scalar (suppliedMessage first second third fourth kem) =
      some (PqxdhJointGapDh.assemble (address (suppliedMessage first second third fourth kem)) first third) := rfl


/-- Legacy root-valued source clients use the proved additive message embedding. -/
def legacy : QueryImpl PqxdhJointDhExtractRoot.RootSpec (OracleComp RootSpec)
  | .inl coin => RootSpec.query (.inl coin)
  | .inr (.sign bytes) => RootSpec.query (.inr (.sign bytes))
  | .inr (.publicHmac key bytes) => RootSpec.query (.inr (.publicHmac key bytes))
  | .inr (.derive message) => RootSpec.query (.inr (.derive (Message.ofLegacy message)))

/-- Actual source root replies are identical for old descriptors and their native embedding, independently of either private history/cache. -/
theorem sourceRoot_reply_legacy (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : PqxdhJointDhExtractFamily.Message) (nativeBefore : State)
    (legacyBefore : PqxdhJointDhExtractFamily.State) :
    Prod.fst <$> (sourceRoot source hmac joint dh seed scalar (Message.ofLegacy message)).run nativeBefore =
      Prod.fst <$> (PqxdhJointDhExtractRoot.sourceRoot source hmac joint dh seed scalar message).run legacyBefore := by
  simp only [sourceRoot, PqxdhJointDhExtractRoot.sourceRoot, input_ofLegacy, StateT.run]
  cases PqxdhJointDhExtractFamily.input joint dh seed scalar message <;> rfl

end BeaconcryptCore.Computational.RegistrationNativeRelatedRoot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.beacon_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.beacon_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.beacon_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.beacon_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.server_input' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.server_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.root_real' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.root_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.reduction_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.reduction_step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.reduction_complete' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.reduction_complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.game_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.game_real

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.advantage_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.advantage_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.pinned_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.pinned_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.supplied_input' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.supplied_input

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.sourceRoot_reply_legacy' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRelatedRoot.sourceRoot_reply_legacy

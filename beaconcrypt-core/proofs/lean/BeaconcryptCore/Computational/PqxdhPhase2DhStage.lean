import BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer

/-!
The complete source preparation and related-root continuation share one execution. Native-only analysis reads its already constructed root input to record the same descriptor used by the key-free compiler; this read is never an oracle reply or a simulator input. All rejection timing and complete primitive state are retained.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.RepresentationBridge PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhPhase2DhStage
open PqxdhJointIdentity PqxdhJointGapDh PqxdhPhase2GapDhSource
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointDhExtractRoot PqxdhSecretInputKdf PqxdhJointKdfGame

/-- These offsets are the three source-local coordinates of the exact 192-byte input, not unavailable DH values. -/
theorem read_local (address : TupleAddress) (first third : DhOutput) :
    readDh 64 (assemble address first third) = some address.second ∧
    readDh 128 (assemble address first third) = some address.fourth ∧
    readDh 160 (assemble address first third) = some address.kem := by
  simp [readDh, assemble, List.append_assoc, List.drop_append]
  apply List.Vector.toList_injective
  simp

/-- Native-only instrumentation of the actual constructed input. The executable reduction instead uses its retained local callback replies. -/
def sourceMessage {Response : Type} (publicValue : PublicChallenge)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) : PqxdhJointDhExtractFamily.Message :=
  ⟨publicValue.prekey, .selected (peer original.ephemeral),
    (readDh 64 (absBytes original.candidate.root_key_input.bytes)).getD zeroDh,
    (readDh 128 (absBytes original.candidate.root_key_input.bytes)).getD zeroDh,
    (readDh 160 (absBytes original.candidate.root_key_input.bytes)).getD zeroDh⟩

set_option backward.isDefEq.respectTransparency false in
/-- Exact extracted construction makes the native-only descriptor identical to the key-free source request, without an injectivity or origin premise. -/
theorem source_message {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {Response : Type} (publicValue : PublicChallenge)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    sourceMessage publicValue original = beaconMessage publicValue pending.collected := by
  have bytes := PqxdhPhase2InputBytes.root_input _ original.candidate.root_key_input related.2.2.2.2
  have assembled : absBytes original.candidate.root_key_input.bytes =
      assemble (PqxdhPhase2GapDhInput.address publicValue pending.collected)
        (PqxdhPhase2InputBytes.word (materialize dh scalar pending.collected.first))
        (PqxdhPhase2InputBytes.word (materialize dh scalar pending.collected.third)) := bytes
  simp only [sourceMessage, assembled, (read_local _ _ _).1, (read_local _ _ _).2.1,
    (read_local _ _ _).2.2, Option.getD_some, related.2.2.1, beaconMessage,
    PqxdhBeaconPhase2Shared.prepared, PqxdhPhase2DhMetadata.realized, PqxdhPhase2GapDhInput.address]

/-- Source-only root instrumentation reads the genuine native input and changes no native auxiliary field. -/
def sourceRootReply {Response A : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (publicValue : PublicChallenge) (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (input : pqxdh.RootKeyInput) : StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp (Option Word32) := fun state =>
  pure (some (RawCtxSourceHkdf.rootResponse source.crypto input),
    (rootState hmac (sourceMessage publicValue original) (absBytes input.bytes) state.1, state.2))

/-- The original source tail, with its private root-family instrumentation and unchanged native callbacks. -/
noncomputable def sourceTail {Response A : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (publicValue : PublicChallenge)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (original : PqxdhBeaconPhase2Preparation.Prepared Response) :=
  simulateQ (PqxdhPhase2DhRootConsumer.withRoot (sourceRootReply source hmac publicValue original)
    (PqxdhPhase2DhRootConsumer.nativeImpl native))
    (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter (PqxdhBeaconPhase2Publication.tail decode original))

/-- The source annotation is derived from its own actual input, rather than supplied as a relation in the native callback interface. -/
theorem source_tail {A : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type}
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : References domain pending.collected)
    (converted : peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    sourceTail source hmac (challenge joint dh seed scalar) native decode original =
      simulateQ (PqxdhPhase2DhRootConsumer.impl (sourceImpl source hmac joint dh seed scalar) native)
        (PqxdhPhase2DhRootConsumer.tail (challenge joint dh seed scalar) decode pending) := by
  have same : sourceRootReply source hmac (challenge joint dh seed scalar) original =
      PqxdhPhase2DhRootConsumer.nativeRootReply (A := A) source hmac (challenge joint dh seed scalar) pending := by
    funext input state
    simp only [sourceRootReply, PqxdhPhase2DhRootConsumer.nativeRootReply, source_message dh scalar _ original pending related]
  unfold sourceTail
  rw [same]
  exact PqxdhPhase2DhRootConsumer.tail_source source hmac dh domain seed scalar native decode original pending references converted related

abbrev Spec (I D K X Response : Type) := PrefixSpec I D K X Response + PqxdhPhase2DhRootConsumer.Spec Response

def prefixLift {I D K X Response : Type} :
    QueryImpl (PrefixSpec I D K X Response) (OracleComp (Spec I D K X Response)) :=
  fun query => (Spec I D K X Response).query (.inl query)

def tailLift {I D K X Response : Type} :
    QueryImpl (PqxdhPhase2DhRootConsumer.Spec Response) (OracleComp (Spec I D K X Response)) :=
  fun query => (Spec I D K X Response).query (.inr query)

/-- One executable source-shaped preparation/root/record stage, with no selected secret or DH materializer. -/
noncomputable def stage {I D K X Response : Type} (publicValue : PublicChallenge)
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    OracleComp (Spec I D K X Response) (Option PqxdhBeaconPhase2Publication.Staged) := do
  let pending ← simulateQ prefixLift (PqxdhPhase2DhMetadata.prepare control identity oneTime kem raw)
  match pending with
  | none => pure none
  | some pending => simulateQ tailLift (PqxdhPhase2DhRootConsumer.tail publicValue decode pending)

def impl {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response A : Type}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response)
      (StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp))
    (visit : Word32 → StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp Unit)
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp)) :
    QueryImpl (Spec I D K X Response) (StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp)
  | .inl query => prefixImpl domain aux visit query
  | .inr query => PqxdhPhase2DhRootConsumer.impl family native query

/-- The source side retains real selected DH values internally and executes the original preparation before its original native tail. -/
noncomputable def sourceStage {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {I D K X Response A : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (publicValue : PublicChallenge)
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response)
      (StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp))
    (visit : Word32 → StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp Unit)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp (Option PqxdhBeaconPhase2Publication.Staged) := do
  let prepared ← simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar aux visit)
    (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)
  match prepared with
  | none => pure none
  | some original => sourceTail source hmac publicValue native decode original

set_option backward.isDefEq.respectTransparency false in
/-- One whole source execution supplies its actual references, native conversion, late raw identity pin, exact 192-byte root input and complete optional record tail. No accepted-target honesty or authentication premise occurs. -/
theorem stage_source {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {I D K X Response A : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response)
      (StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp))
    (conversion : ∀ value initial converted final,
      (some converted, final) ∈ support ((aux (.publicConversion value)).run initial) →
        source.crypto.xpkConv (absBytes value) = some (absBytes converted))
    (visit : Word32 → StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp Unit)
    (erase : ∀ secrets, aux (.eraseShared secrets) = pure ())
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (pin : absBytes control.expected_server_binding.identity_public_key = (joint.publicKeys seed).ed25519.toList)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    sourceStage dh scalar source hmac (challenge joint dh seed scalar) aux visit native decode control identity oneTime kem raw =
      simulateQ (impl domain aux visit (sourceImpl source hmac joint dh seed scalar) native)
        (stage (challenge joint dh seed scalar) decode control identity oneTime kem raw) := by
  have preEq : impl domain aux visit (sourceImpl source hmac joint dh seed scalar) native ∘ₛ prefixLift =
      prefixImpl domain aux visit := by
    funext query
    exact simulateQ_spec_query (impl domain aux visit (sourceImpl source hmac joint dh seed scalar) native) _
  have tailEq : impl domain aux visit (sourceImpl source hmac joint dh seed scalar) native ∘ₛ tailLift =
      PqxdhPhase2DhRootConsumer.impl (sourceImpl source hmac joint dh seed scalar) native := by
    funext query
    exact simulateQ_spec_query (impl domain aux visit (sourceImpl source hmac joint dh seed scalar) native) _
  funext initial
  change (sourceStage dh scalar source hmac (challenge joint dh seed scalar) aux visit native decode control identity oneTime kem raw).run initial = _
  simp only [sourceStage, stage, simulateQ_bind, ← QueryImpl.simulateQ_compose, preEq, StateT.run_bind]
  apply PqxdhPhase2DhMetadata.prepare_converted_continuation dh domain scalar source.crypto aux conversion visit erase
    control identity oneTime kem raw initial
  · intro state
    simp only [simulateQ_pure, StateT.run_pure]
    rfl
  · intro original pending state references converted admitted related
    have actualConversion := PqxdhPhase2DhMetadata.pinned_conversion source.crypto joint secretOfSeed wiring seed
      control pending.collected pending.metadata pin admitted converted
    change (sourceTail source hmac (challenge joint dh seed scalar) native decode original).run state =
      (simulateQ (impl domain aux visit (sourceImpl source hmac joint dh seed scalar) native)
        (simulateQ tailLift (PqxdhPhase2DhRootConsumer.tail (challenge joint dh seed scalar) decode pending))).run state
    rw [← QueryImpl.simulateQ_compose, tailEq,
      source_tail source hmac dh domain seed scalar native decode original pending references actualConversion related]

/-- The complete executable stage has at most 12 preparation callbacks, one family request and 55 original native tail callbacks. Logical native erasure has its explicit no-observation equation. -/
theorem stage_bound {I D K X Response : Type} (publicValue : PublicChallenge)
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    (stage (X := X) (Response := Response) publicValue decode control identity oneTime kem raw).IsTotalQueryBound 68 := by
  unfold stage
  apply isTotalQueryBound_bind (n₁ := 12) (n₂ := 56)
  · apply PqxdhBeaconPhase2Bounds.simulate_total prefixLift _ 12
      (PqxdhPhase2DhMetadata.prepare_bound control identity oneTime kem raw)
    intro query
    exact (isQueryBoundP_true_iff _ _).mp
      ((isQueryBoundP_query_iff (spec := Spec I D K X Response) (p := fun _ => True) (.inl query) 1).mpr (by decide))
  · rintro (_ | pending)
    · simp [IsTotalQueryBound, isQueryBound_pure]
    · apply PqxdhBeaconPhase2Bounds.simulate_total tailLift _ 56
        (PqxdhPhase2DhRootConsumer.tail_bound publicValue decode pending)
      intro query
      exact (isQueryBoundP_true_iff _ _).mp
        ((isQueryBoundP_query_iff (spec := Spec I D K X Response) (p := fun _ => True) (.inr query) 1).mpr (by decide))

set_option backward.isDefEq.respectTransparency false in
/-- Every interpreted callback is charged at the actual source position. Accepted and rejected responses have the same bound, including all work before a mismatched raw pin is rejected. -/
theorem stage_uniform {joint : Primitives} {dh : DhInterface joint} (domain : PublicDomain dh)
    {I D K X Response A : Type}
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response)
      (StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp))
    (visit : Word32 → StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp Unit)
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (qAux qVisit qFamily qNative : Nat)
    (auxBound : ∀ query state, ((aux query).run state).IsTotalQueryBound qAux)
    (visitBound : ∀ input state, ((visit input).run state).IsTotalQueryBound qVisit)
    (familyBound : ∀ query state, ((family query).run state).IsTotalQueryBound qFamily)
    (nativeBound : ∀ query state, ((native query).run state).IsTotalQueryBound qNative)
    (publicValue : PublicChallenge) (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (state : PqxdhPhase2DhRootConsumer.State A) :
    ((simulateQ (impl domain aux visit family native)
      (stage publicValue decode control identity oneTime kem raw)).run state).IsTotalQueryBound
      ((10 * qAux + 2 * qVisit) + (qFamily + 55 * qNative)) := by
  have preEq : impl domain aux visit family native ∘ₛ prefixLift = prefixImpl domain aux visit := by
    funext query
    exact simulateQ_spec_query (impl domain aux visit family native) _
  have tailEq : impl domain aux visit family native ∘ₛ tailLift = PqxdhPhase2DhRootConsumer.impl family native := by
    funext query
    exact simulateQ_spec_query (impl domain aux visit family native) _
  simp only [stage, simulateQ_bind, ← QueryImpl.simulateQ_compose, preEq, StateT.run_bind]
  apply isTotalQueryBound_bind
  · exact (isQueryBoundP_true_iff _ _).mp (PqxdhPhase2DhMetadata.interpreted_bound domain aux visit
      (fun _ => True) qAux qVisit (fun query state => (auxBound query state).isQueryBoundP)
      (fun input state => (visitBound input state).isQueryBoundP) control identity oneTime kem raw state)
  · rintro ⟨pending, post⟩
    cases pending with
    | none => simp only [simulateQ_pure, StateT.run_pure]; simp [IsTotalQueryBound, isQueryBound_pure]
    | some pending =>
        change ((simulateQ (impl domain aux visit family native)
          (simulateQ tailLift (PqxdhPhase2DhRootConsumer.tail publicValue decode pending))).run post).IsTotalQueryBound _
        rw [← QueryImpl.simulateQ_compose, tailEq]
        exact PqxdhPhase2DhRootConsumer.tail_uniform family native qFamily qNative familyBound nativeBound publicValue decode pending post

end BeaconcryptCore.Computational.PqxdhPhase2DhStage

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhStage.read_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhStage.read_local

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhStage.source_message' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhStage.source_message

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhStage.source_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhStage.source_tail

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhStage.stage_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhStage.stage_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhStage.stage_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhStage.stage_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhStage.stage_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhStage.stage_uniform

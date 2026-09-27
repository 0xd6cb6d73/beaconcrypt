import BeaconcryptCore.Computational.PqxdhPhase2DhMetadata

/-!
The native post-root continuation consumes rootless admitted metadata. The only unavailable-input operation is a request to the explicit related-DH root service. Its real interpreter returns the actual fixed-HKDF root and keeps the complete private cache/history. This operational consumer asserts no smallness of that additional primitive advantage.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
open BeaconcryptCore.Refinement.RepresentationBridge PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer
open PqxdhJointIdentity PqxdhJointGapDh PqxdhPhase2GapDhSource
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointDhExtractRoot
open PqxdhSecretInputKdf PqxdhJointKdfGame

/-- This is the actual candidate after root processing cleared its copied input. No unavailable input bytes occur in this continuation argument. -/
def cleared {Response : Type} (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    PqxdhBeaconPhase2Preparation.Prepared Response :=
  ⟨pending.collected.response, pending.collected.ciphertext, pending.collected.ephemeral,
    PqxdhBeaconPhase2Shared.clearedMetadata pending.metadata⟩

/-- Continue with the original native initializer, parser, opening, sequence-one check and binding checks. -/
noncomputable def afterRoot {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : Word32) :=
  simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
    (PqxdhBeaconPhase2Publication.afterRoot decode (cleared pending) root)

set_option backward.isDefEq.respectTransparency false in
/-- The entire native post-root program depends on the original metadata and optional source replies, with its temporary root input already cleared. -/
theorem afterRoot_source {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {Response : Type} (decode : RawCtxReceive.FrameDecoder)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) (root : Word32) :
    simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.afterRoot decode original root) = afterRoot decode pending root := by
  have responseEq : original.response = pending.collected.response := related.1
  unfold afterRoot PqxdhBeaconPhase2Publication.afterRoot
  rw [PqxdhPhase2DhMetadata.cleared_related dh scalar original pending related, responseEq]
  have clearedEq (metadata : PqxdhBeaconPhase2Shared.Metadata) :
      PqxdhBeaconPhase2Publication.clearedCandidate (PqxdhBeaconPhase2Shared.clearedMetadata metadata) =
      PqxdhBeaconPhase2Shared.clearedMetadata metadata := by
    unfold PqxdhBeaconPhase2Publication.clearedCandidate PqxdhBeaconPhase2Shared.clearedMetadata
    congr
  simp only [cleared, clearedEq]
  congr 2
  funext kernel
  congr 1
  funext raw
  cases raw <;> rfl

/-- The vector-valued fixed-HKDF root is exactly the native 32-byte wrapper on that same full input. -/
theorem native_root (source : FixedHkdfSha512NoSaltSource) (input : pqxdh.RootKeyInput) :
    PqxdhRootTableInitialization.rootArray (nativeRoot source (absBytes input.bytes)) =
      RawCtxSourceHkdf.rootResponse source.crypto input := by
  rfl

/-- The reduction sends only the public challenge and actual locally available source coordinates. -/
def root {Response : Type} (publicValue : PublicChallenge)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) : OracleComp RootSpec (Option Word32) :=
  Option.map PqxdhRootTableInitialization.rootArray <$>
    (RootSpec.query (.inr (.derive (beaconMessage publicValue pending.collected))) : OracleComp RootSpec _)

set_option backward.isDefEq.respectTransparency false in
/-- The actual reached descriptor returns the precise native fixed-HKDF root and complete private instrumentation at the extracted 192-byte address. -/
theorem root_source (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type}
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : References domain pending.collected)
    (converted : peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending)
    (state : PqxdhJointDhExtractFamily.State) :
    (simulateQ (sourceImpl source hmac joint dh seed scalar)
      (root (challenge joint dh seed scalar) pending)).run state =
      pure (some (RawCtxSourceHkdf.rootResponse source.crypto original.candidate.root_key_input),
        rootState hmac (beaconMessage (challenge joint dh seed scalar) pending.collected)
          (absBytes original.candidate.root_key_input.bytes) state) := by
  have inputEq := beacon_source dh domain seed scalar pending.collected references converted
    original.candidate.root_key_input related.2.2.2.2
  simp only [root, simulateQ_map, simulateQ_spec_query, sourceImpl]
  rw [StateT.run_map]
  change (fun result => (Option.map PqxdhRootTableInitialization.rootArray result.1, result.2)) <$>
    (sourceRoot source hmac joint dh seed scalar (beaconMessage (challenge joint dh seed scalar) pending.collected)).run state = _
  simp only [sourceRoot, inputEq, StateT.run, map_pure, Option.map_some, native_root]

/-- The source root callback is singled out at its actual position; every other native callback is unchanged. -/
def withRoot {Response : Type} {m : Type → Type} [Monad m]
    (rootReply : pqxdh.RootKeyInput → m (Option Word32))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m
  | .inr (.root input) => rootReply input
  | .inr (.initial request) => native (.inr (.initial request))
  | .inr (.application response) => native (.inr (.application response))
  | .inl query => native (.inl query)

/-- Every expanded raw callback retains its complete effect and optional reply across the root-only replacement. -/
theorem raw_unchanged {Response Result : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (rootReply : pqxdh.RootKeyInput → m (Option Word32))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (work : OracleComp RawCtxSourceOpen.NativeSpec Result) :
    simulateQ (withRoot rootReply native) (simulateQ PqxdhBeaconPhase2Publication.nativeRawLift work) =
      simulateQ native (simulateQ PqxdhBeaconPhase2Publication.nativeRawLift work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1

/-- The actual post-root source program performs no root callback. All typed64, application and raw-receive effects are retained. -/
theorem afterRoot_unchanged {Response : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (rootReply : pqxdh.RootKeyInput → m (Option Word32))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (decode : RawCtxReceive.FrameDecoder) (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (rootValue : Word32) :
    simulateQ (withRoot rootReply native) (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.afterRoot decode original rootValue)) =
      simulateQ native (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
        (PqxdhBeaconPhase2Publication.afterRoot decode original rootValue)) := by
  unfold PqxdhBeaconPhase2Publication.afterRoot PqxdhBeaconPhase2Publication.initialRun
  simp only [simulateQ_bind, simulateQ_spec_query,
    PqxdhBeaconPhase2Publication.nativeTailAdapter, bind_assoc, pure_bind]
  apply bind_congr
  intro response
  apply bind_congr
  intro raw
  cases raw with
  | none => rfl
  | some raw =>
      simp only [simulateQ_bind, simulateQ_pure]
      rw [PqxdhBeaconPhase2Bounds.native_raw_lift, raw_unchanged rootReply native]

set_option backward.isDefEq.respectTransparency false in
/-- The original native tail issues its exact root input once and retains every optional result before the untouched source continuation. -/
theorem tail_root {Response : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (rootReply : pqxdh.RootKeyInput → m (Option Word32))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) m)
    (decode : RawCtxReceive.FrameDecoder) (original : PqxdhBeaconPhase2Preparation.Prepared Response) :
    simulateQ (withRoot rootReply native) (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.tail decode original)) =
      (rootReply original.candidate.root_key_input >>= fun value => match value with
        | none => pure none
        | some value => simulateQ native (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
            (PqxdhBeaconPhase2Publication.afterRoot decode original value))) := by
  have rootEq : simulateQ (withRoot rootReply native)
      (PqxdhBeaconPhase2Publication.nativeTailAdapter (.inr (.root original.candidate.root_key_input))) =
      rootReply original.candidate.root_key_input := simulateQ_spec_query (withRoot rootReply native) _
  simp only [PqxdhBeaconPhase2Publication.tail, simulateQ_bind, simulateQ_spec_query, rootEq]
  apply bind_congr
  intro value
  cases value with
  | none => simp only [simulateQ_pure]
  | some value => exact afterRoot_unchanged rootReply native decode original value

abbrev State (A : Type) := PqxdhJointDhExtractFamily.State × A
abbrev Spec (Response : Type) := RootSpec + PqxdhBeaconPhase2Publication.NativeTailSpec Response

def rootLift {Response : Type} : QueryImpl RootSpec (OracleComp (Spec Response)) :=
  fun query => (Spec Response).query (.inl query)

def nativeLift {Response : Type} :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (OracleComp (Spec Response)) :=
  fun query => (Spec Response).query (.inr query)

/-- The executable complete tail has no selected seed, prekey scalar or unavailable root-input byte. -/
noncomputable def tail {Response : Type} (publicValue : PublicChallenge)
    (decode : RawCtxReceive.FrameDecoder) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    OracleComp (Spec Response) (Option PqxdhBeaconPhase2Publication.Staged) := do
  let value ← simulateQ rootLift (root publicValue pending)
  match value with
  | none => pure none
  | some value => simulateQ nativeLift (afterRoot decode pending value)

/-- The shared source interpreter preserves the entire native auxiliary state at each family query. -/
def familyImpl {A : Type}
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp)) :
    QueryImpl RootSpec (StateT (State A) ProbComp) := fun query state =>
  (fun result => (result.1, (result.2, state.2))) <$> (family query).run state.1

/-- Native operations retain the full private root-service cache/history, including unrelated entries. -/
def nativeImpl {Response A : Type}
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp)) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT (State A) ProbComp) := fun query state =>
  (fun result => (result.1, (state.1, result.2))) <$> (native query).run state.2

def impl {Response A : Type}
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp)) :
    QueryImpl (Spec Response) (StateT (State A) ProbComp)
  | .inl query => familyImpl family query
  | .inr query => nativeImpl native query

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary adaptive family work retains every auxiliary field and the full family poststate before its continuation. -/
theorem family_complete {A Result : Type}
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (work : OracleComp RootSpec Result) (state : State A) :
    (simulateQ (familyImpl family) work).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (simulateQ family work).run state.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change (((fun result => (result.1, (result.2, state.2))) <$> (family query).run state.1) >>= fun reply =>
      (simulateQ (familyImpl family) (next reply.1)).run reply.2) = _
    simp only [bind_map_left, ih, map_bind]

/-- Native root evaluation with explicit analysis instrumentation. Temporary copied input clearing is consumed by the unchanged post-root continuation. -/
def nativeRootReply {Response A : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (publicValue : PublicChallenge) (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (input : pqxdh.RootKeyInput) : StateT (State A) ProbComp (Option Word32) := fun state =>
  pure (some (RawCtxSourceHkdf.rootResponse source.crypto input),
    (rootState hmac (beaconMessage publicValue pending.collected) (absBytes input.bytes) state.1, state.2))

set_option backward.isDefEq.respectTransparency false in
/-- The reached root call matches native evaluation and its entire private instrumentation before any remaining source or adversary work. -/
theorem root_complete {A : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type}
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : References domain pending.collected)
    (converted : peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    simulateQ (familyImpl (A := A) (sourceImpl source hmac joint dh seed scalar))
      (root (challenge joint dh seed scalar) pending) =
      nativeRootReply source hmac (challenge joint dh seed scalar) pending original.candidate.root_key_input := by
  funext state
  change (simulateQ (familyImpl (A := A) (sourceImpl source hmac joint dh seed scalar))
    (root (challenge joint dh seed scalar) pending)).run state = _
  rw [family_complete, root_source source hmac dh domain seed scalar original pending references converted related]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete original native tail and its executable related-root client are equal in the same full effect state, before arbitrary continuation. Neither successful opening nor authentication is assumed. -/
theorem tail_source {A : Type} (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type}
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : References domain pending.collected)
    (converted : peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    simulateQ (withRoot (nativeRootReply source hmac (challenge joint dh seed scalar) pending) (nativeImpl native))
      (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter (PqxdhBeaconPhase2Publication.tail decode original)) =
      simulateQ (impl (sourceImpl source hmac joint dh seed scalar) native)
        (tail (challenge joint dh seed scalar) decode pending) := by
  have familyEq : impl (sourceImpl source hmac joint dh seed scalar) native ∘ₛ rootLift =
      familyImpl (A := A) (sourceImpl source hmac joint dh seed scalar) := by
    funext query
    exact simulateQ_spec_query (impl (sourceImpl source hmac joint dh seed scalar) native) _
  have nativeEq : impl (sourceImpl source hmac joint dh seed scalar) native ∘ₛ nativeLift =
      nativeImpl native := by
    funext query
    exact simulateQ_spec_query (impl (sourceImpl source hmac joint dh seed scalar) native) _
  rw [tail_root]
  simp only [tail, simulateQ_bind, ← QueryImpl.simulateQ_compose, familyEq]
  rw [root_complete source hmac dh domain seed scalar original pending references converted related]
  apply bind_congr
  intro value
  cases value with
  | none => simp only [simulateQ_pure]
  | some value =>
      rw [← QueryImpl.simulateQ_compose, nativeEq]
      change simulateQ (nativeImpl native ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter)
        (PqxdhBeaconPhase2Publication.afterRoot decode original value) = _
      rw [QueryImpl.simulateQ_compose, afterRoot_source dh scalar decode original pending related value]

/-- The key-free typed root client asks exactly one root-valued service question; its underlying Extract and real Expand calls remain separately billed. -/
theorem root_bound {Response : Type} (publicValue : PublicChallenge)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) : (root publicValue pending).IsTotalQueryBound 1 := by
  simp only [root, IsTotalQueryBound, isQueryBound_map_iff]
  exact (isQueryBoundP_true_iff _ _).mp
    ((isQueryBoundP_query_iff (spec := RootSpec) (p := fun _ => True)
      (.inr (.derive (beaconMessage publicValue pending.collected))) 1).mpr (by decide))

/-- The compiled tail keeps the original native cap of 55 post-root callbacks and one explicit root-valued query. Rejected raw sequences are still processed at their source position. -/
theorem tail_bound {Response : Type} (publicValue : PublicChallenge)
    (decode : RawCtxReceive.FrameDecoder) (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    (tail publicValue decode pending).IsTotalQueryBound 56 := by
  unfold tail
  apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 55)
  · apply PqxdhBeaconPhase2Bounds.simulate_total rootLift _ 1 (root_bound publicValue pending)
    intro query
    exact (isQueryBoundP_true_iff _ _).mp
      ((isQueryBoundP_query_iff (spec := Spec Response) (p := fun _ => True) (.inl query) 1).mpr (by decide))
  · rintro (_ | value)
    · simp [IsTotalQueryBound, isQueryBound_pure]
    · apply PqxdhBeaconPhase2Bounds.simulate_total nativeLift _ 55
        (PqxdhBeaconPhase2Bounds.native_afterRoot_bound decode (cleared pending) value)
      intro query
      exact (isQueryBoundP_true_iff _ _).mp
        ((isQueryBoundP_query_iff (spec := Spec Response) (p := fun _ => True) (.inr query) 1).mpr (by decide))

/-- Lifting root-family work counts only family calls; unrelated native calls are absent. -/
theorem rootLift_bills {Response Result : Type} (work : OracleComp RootSpec Result) (q : Nat)
    (bounded : work.IsTotalQueryBound q) (family : Bool) :
    (simulateQ (rootLift (Response := Response)) work).IsQueryBoundP (fun query => query.isLeft = family)
      (if family then q else 0) := by
  cases family with
  | false =>
      apply RawCtxSourceOpen.simulate_bound rootLift (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
      intro query
      exact (isQueryBoundP_query_iff (spec := Spec Response) (p := fun query => query.isLeft = false) (.inl query) 0).mpr (by simp)
  | true =>
      apply RawCtxSourceOpen.simulate_bound rootLift (fun _ => True) _ work q bounded.isQueryBoundP
      intro query
      exact (isQueryBoundP_query_iff (spec := Spec Response) (p := fun query => query.isLeft = true) (.inl query) 1).mpr (by simp)

/-- Lifting actual native work counts only native calls and cannot issue an extra private family request. -/
theorem nativeLift_bills {Response Result : Type}
    (work : OracleComp (PqxdhBeaconPhase2Publication.NativeTailSpec Response) Result) (q : Nat)
    (bounded : work.IsTotalQueryBound q) (family : Bool) :
    (simulateQ nativeLift work).IsQueryBoundP (fun query => query.isLeft = family) (if family then 0 else q) := by
  cases family with
  | false =>
      apply RawCtxSourceOpen.simulate_bound nativeLift (fun _ => True) _ work q bounded.isQueryBoundP
      intro query
      exact (isQueryBoundP_query_iff (spec := Spec Response) (p := fun query => query.isLeft = false) (.inr query) 1).mpr (by simp)
  | true =>
      apply RawCtxSourceOpen.simulate_bound nativeLift (fun _ => False) _ work 0 (isQueryBoundP_false work 0)
      intro query
      exact (isQueryBoundP_query_iff (spec := Spec Response) (p := fun query => query.isLeft = true) (.inr query) 0).mpr (by simp)

/-- Every optional tail path bills at most one family call and 55 native calls, with no success filtering. The family call expands into one Extract and one real HMAC call. -/
theorem tail_bills {Response : Type} (publicValue : PublicChallenge) (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (family : Bool) :
    (tail publicValue decode pending).IsQueryBoundP (fun query => query.isLeft = family)
      ((if family then 1 else 0) + (if family then 0 else 55)) := by
  unfold tail
  apply isQueryBoundP_bind (rootLift_bills (root publicValue pending) 1 (root_bound publicValue pending) family)
  rintro (_ | value) _
  · exact isQueryBoundP_pure _ _ _
  · exact nativeLift_bills (afterRoot decode pending value) 55
      (PqxdhBeaconPhase2Bounds.native_afterRoot_bound decode (cleared pending) value) family

set_option backward.isDefEq.respectTransparency false in
/-- Both full stateful interpreters are billed. The endpoint allowance includes all family work, and each native allowance includes its real local and shared-oracle randomness. -/
theorem tail_uniform {Response A : Type}
    (family : QueryImpl RootSpec (StateT PqxdhJointDhExtractFamily.State ProbComp))
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (qFamily qNative : Nat)
    (familyBound : ∀ query state, ((family query).run state).IsTotalQueryBound qFamily)
    (nativeBound : ∀ query state, ((native query).run state).IsTotalQueryBound qNative)
    (publicValue : PublicChallenge) (decode : RawCtxReceive.FrameDecoder)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (state : State A) :
    ((simulateQ (impl family native) (tail publicValue decode pending)).run state).IsTotalQueryBound
      (qFamily + 55 * qNative) := by
  have structural := FinitePartitionQueryBounds.weighted_bound (fun query : (Spec Response).Domain => query.isLeft)
    (fun selected => if selected then qFamily else qNative) (fun selected => if selected then 1 else 55)
    (impl family native) (fun _ => True) (tail publicValue decode pending)
    (by intro selected; cases selected with
        | false => exact tail_bills publicValue decode pending false
        | true => exact tail_bills publicValue decode pending true)
  have step : ∀ query state, ((impl family native query).run state).IsQueryBoundP (fun _ => True)
      ((fun selected => if selected then qFamily else qNative) query.isLeft) := by
    intro query state
    cases query with
    | inl query =>
        simpa [impl, familyImpl, StateT.run, IsQueryBoundP, isQueryBound_map_iff] using (familyBound query state.1).isQueryBoundP (p := fun _ => True)
    | inr query =>
        simpa [impl, nativeImpl, StateT.run, IsQueryBoundP, isQueryBound_map_iff] using (nativeBound query state.2).isQueryBoundP (p := fun _ => True)
  apply (isQueryBoundP_true_iff _ _).mp
  simpa [Nat.mul_comm, Nat.add_comm] using structural step state

end BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.afterRoot_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.afterRoot_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.native_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.native_root

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.root_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.root_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.raw_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.raw_unchanged

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.afterRoot_unchanged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.afterRoot_unchanged

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_root' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_root

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.family_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.family_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.root_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.root_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_source

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.root_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.root_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.rootLift_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.rootLift_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.nativeLift_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.nativeLift_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_bills

/-- info: 'BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2DhRootConsumer.tail_uniform

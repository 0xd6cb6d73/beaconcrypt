import BeaconcryptCore.Computational.PqxdhLivePhase1Bundle

/-!
A live bundle uses the existing joint identity service at its actual owner handle. Local one-time generation and serialization keep all prior joint state. The three source signatures append to the full prior history even when the later writer fails; no exact-three-entry premise is introduced.
-/

open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLiveJointSigning
open PqxdhJointIdentity PqxdhDynamicIdentityPool PqxdhJointPhase1SourceWriter
open PqxdhEd25519EufCma PqxdhBeaconPhase1Publication

variable {I D K A : Type}

abbrev State (A : Type) := SourceState × A

def impl (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp)) :
    QueryImpl (PqxdhLivePhase1Bundle.Spec D) (StateT (State A) ProbComp) :=
  fun query state => match query with
  | .inl request =>
      (fun result => (result.1, (state.1, result.2))) <$> (generate request).run state.2
  | .inr (.inl request) =>
      (fun result => (result.1, (result.2, state.2))) <$> (lazyImpl primitives request).run state.1
  | .inr (.inr request) =>
      (fun result => (result.1, (state.1, result.2))) <$> (writer request).run state.2

def joint {Result : Type} (work : OracleComp DynamicSpec Result) :
    OracleComp (PqxdhLivePhase1Bundle.Spec D) Result :=
  simulateQ (fun request => ((PqxdhLivePhase1Bundle.Spec D).query (.inr (.inl request)) :
    OracleComp (PqxdhLivePhase1Bundle.Spec D) _)) work

set_option backward.isDefEq.respectTransparency false in
/-- All joint requests preserve the complete local generation/serialization state while keeping the original service's full seed and observation history. -/
theorem joint_complete {Result : Type} (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (work : OracleComp DynamicSpec Result) (state : State A) :
    (simulateQ (impl primitives generate writer) (joint work)).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (simulateQ (lazyImpl primitives) work).run state.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [joint, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change (((fun result => (result.1, (result.2, state.2))) <$>
      (lazyImpl primitives query).run state.1) >>= fun reply =>
      (simulateQ (impl primitives generate writer) (joint (next reply.1))).run reply.2) = _
    simp only [bind_map_left, ih, map_bind]

set_option backward.isDefEq.respectTransparency false in
/-- The live owner's three actual signatures retain every prior joint observation and the whole private local state. -/
theorem signing_complete (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (index : Nat) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (state : State A) (seed : IdentitySeed) (created : state.1.seeds[index]? = some seed) :
    (simulateQ (impl primitives generate writer)
      (PqxdhLivePhase1Bundle.signing index identity keys)).run state =
      pure (some (signedCandidate primitives seed identity keys),
        (signedState primitives seed index keys state.1, state.2)) := by
  simpa only [PqxdhLivePhase1Bundle.signing, joint, signingProgram_created primitives index identity keys state.1 seed created, map_pure] using
    joint_complete primitives generate writer (signingProgram index identity keys) state

def serialization {Result : Type} (work : OracleComp WriterSpec Result) :
    OracleComp (PqxdhLivePhase1Bundle.Spec D) Result :=
  simulateQ (fun request => ((PqxdhLivePhase1Bundle.Spec D).query (.inr (.inr request)) :
    OracleComp (PqxdhLivePhase1Bundle.Spec D) _)) work

set_option backward.isDefEq.respectTransparency false in
/-- Every optional serialization outcome retains the full earlier joint signing history. -/
theorem serialization_complete {Result : Type} (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (work : OracleComp WriterSpec Result) (state : State A) :
    (simulateQ (impl primitives generate writer) (serialization work)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (simulateQ writer work).run state.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [serialization, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    change (((fun result => (result.1, (state.1, result.2))) <$>
      (writer query).run state.2) >>= fun reply =>
      (simulateQ (impl primitives generate writer) (serialization (next reply.1))).run reply.2) = _
    simp only [bind_map_left, ih, map_bind]

set_option backward.isDefEq.respectTransparency false in
/-- The original native writer and publication path keep all earlier signatures even when serialization fails. -/
theorem writing_complete (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (identity : Aeneas.Std.Array Aeneas.Std.U8 32#usize) (candidate : Phase1Candidate)
    (generated : Option D) (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) :
    (simulateQ (impl primitives generate writer)
      (PqxdhLivePhase1Bundle.writing identity candidate generated native)).run state =
      (fun result => (result.1, (state.1, result.2))) <$>
        (simulateQ writer (afterSigning identity candidate generated native)).run state.2 := by
  simpa only [PqxdhLivePhase1Bundle.writing, serialization] using
    serialization_complete primitives generate writer (afterSigning identity candidate generated native) state

/-- The mathematical source interpreter applies the actual signer and native optional writer, preserving all prior service state. The executable bundle does not receive this seed. -/
def sourceAfter (primitives : Primitives) (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K) (generated : Option D)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed) :
    ProbComp ((Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) × State A) :=
  match prepare native generated with
  | none => pure ((none, native), state)
  | some prepared =>
      let index := projection.index native.beacon.identity
      let identity := projection.identity native.beacon.identity
      let keys : Phase1KeyTuple := ⟨projection.dh prepared.prekey, projection.dh prepared.oneTime, projection.kem prepared.kem⟩
      let candidate := signedCandidate primitives seed identity keys
      (fun result => (result.1, (signedState primitives seed index keys state.1, result.2))) <$>
        (simulateQ writer (afterSigning (PqxdhLivePhase1Bundle.identityArray identity)
          candidate generated native)).run state.2

set_option backward.isDefEq.respectTransparency false in
/-- Source preparation, actual three-signature history and optional writer/publication are one evaluated operation on the live created handle. -/
theorem afterGenerated_source (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K) (generated : Option D)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed)
    (created : state.1.seeds[projection.index native.beacon.identity]? = some seed) :
    (simulateQ (impl primitives generate writer)
      (PqxdhLivePhase1Bundle.afterGenerated projection generated native)).run state =
      sourceAfter primitives writer projection generated native state seed := by
  unfold PqxdhLivePhase1Bundle.afterGenerated sourceAfter
  cases prepared : prepare native generated
  all_goals simp only [simulateQ_pure, StateT.run_pure, simulateQ_bind, StateT.run_bind]
  rw [signing_complete primitives generate writer _ _ _ state seed created, pure_bind, writing_complete]

/-- A local one-time generator cannot change any prior joint identity or signing observation. -/
theorem generation_complete (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp)) (state : State A) :
    (impl primitives generate writer (.inl ())).run state =
      (fun result => (result.1, (state.1, result.2))) <$> (generate ()).run state.2 := rfl

def sourceBundle (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed) :
    ProbComp ((Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) × State A) :=
  match native.beacon.phase with
  | .fresh _ _ _ => do
      let generated ← (generate ()).run state.2
      sourceAfter primitives writer projection generated.1 native (state.1, generated.2) seed
  | .freshWithCoins _ _ _ _ => sourceAfter primitives writer projection none native state seed
  | _ => pure ((none, native), state)

set_option backward.isDefEq.respectTransparency false in
/-- The complete live bundle at an actually created handle uses the source generator position, all three real signatures and the optional source writer with full retained state. -/
theorem bundle_source (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed)
    (created : state.1.seeds[projection.index native.beacon.identity]? = some seed) :
    (simulateQ (impl primitives generate writer) (PqxdhLivePhase1Bundle.bundle projection native)).run state =
      sourceBundle primitives generate writer projection native state seed := by
  cases phase : native.beacon.phase <;>
    simp only [PqxdhLivePhase1Bundle.bundle, sourceBundle, phase, simulateQ_pure,
      StateT.run_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      generation_complete, bind_map_left]
  all_goals first
    | exact afterGenerated_source primitives generate writer projection none native state seed created
    | exact bind_congr fun generated => afterGenerated_source primitives generate writer projection generated.1 native (state.1, generated.2) seed created

set_option backward.isDefEq.respectTransparency false in
/-- The created-handle source preparation samples only through its actual writer; deterministic signing still has its separately counted three service calls. -/
theorem sourceAfter_uniform (primitives : Primitives)
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K) (generated : Option D)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed) (qWriter : Nat)
    (writerBound : ∀ candidate auxiliary, ((writer candidate).run auxiliary).IsTotalQueryBound qWriter) :
    (sourceAfter primitives writer projection generated native state seed).IsTotalQueryBound qWriter := by
  cases prepared : prepare native generated <;>
    simp only [sourceAfter, prepared, afterSigning,
      simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      IsTotalQueryBound, isQueryBound_map_iff, isQueryBound_pure]
  change IsTotalQueryBound _ (qWriter + 0)
  apply isTotalQueryBound_bind (writerBound _ _)
  rintro ⟨_ | bytes, auxiliary⟩ <;> simp [IsTotalQueryBound, isQueryBound_pure]

set_option backward.isDefEq.respectTransparency false in
/-- The native bundle bills its real local generator and writer randomness. The existing bundle service ledger separately counts its three joint signing requests. -/
theorem bundle_uniform (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed) (qGenerate qWriter : Nat)
    (created : state.1.seeds[projection.index native.beacon.identity]? = some seed)
    (generateBound : ∀ auxiliary, ((generate ()).run auxiliary).IsTotalQueryBound qGenerate)
    (writerBound : ∀ candidate auxiliary, ((writer candidate).run auxiliary).IsTotalQueryBound qWriter) :
    ((simulateQ (impl primitives generate writer) (PqxdhLivePhase1Bundle.bundle projection native)).run state).IsTotalQueryBound (qGenerate + qWriter) := by
  rw [bundle_source primitives generate writer projection native state seed created]
  cases phase : native.beacon.phase <;> simp only [sourceBundle, phase]
  all_goals first
    | exact isTotalQueryBound_bind (generateBound _) (fun generated =>
        sourceAfter_uniform primitives writer projection generated.1 native (state.1, generated.2) seed qWriter writerBound)
    | exact (sourceAfter_uniform primitives writer projection none native state seed qWriter writerBound).mono (Nat.le_add_left qWriter qGenerate)
    | simp [IsTotalQueryBound, isQueryBound_pure]

set_option backward.isDefEq.respectTransparency false in
/-- Signing and optional publication preserve every created identity seed, including the owner needed by later operations. -/
theorem sourceAfter_seeds (primitives : Primitives)
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K) (generated : Option D)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed)
    (result : (Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) × State A)
    (actual : result ∈ support (sourceAfter primitives writer projection generated native state seed)) :
    result.2.1.seeds = state.1.seeds := by
  cases prepared : prepare native generated <;> simp only [sourceAfter, prepared] at actual
  · simp only [mem_support_pure_iff] at actual
    subst result
    rfl
  · simp only [support_map, Set.mem_image] at actual
    obtain ⟨value, _, rfl⟩ := actual
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every supported complete bundle outcome preserves the full identity pool, so the live created-handle invariant survives even a failed writer. -/
theorem bundle_seeds (primitives : Primitives)
    (generate : QueryImpl (PqxdhLivePhase1Bundle.GenerateSpec D) (StateT A ProbComp))
    (writer : QueryImpl WriterSpec (StateT A ProbComp))
    (projection : PqxdhLivePhase1Bundle.Public I D K)
    (native : PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K))
    (state : State A) (seed : IdentitySeed)
    (created : state.1.seeds[projection.index native.beacon.identity]? = some seed)
    (result : (Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := D) (K := K)) × State A)
    (actual : result ∈ support ((simulateQ (impl primitives generate writer)
      (PqxdhLivePhase1Bundle.bundle projection native)).run state)) :
    result.2.1.seeds = state.1.seeds := by
  rw [bundle_source primitives generate writer projection native state seed created] at actual
  cases phase : native.beacon.phase <;> simp only [sourceBundle, phase] at actual
  all_goals first
    | exact sourceAfter_seeds primitives writer projection none native state seed result actual
    | (simp only [mem_support_pure_iff] at actual; subst result; rfl)
    | (simp only [mem_support_bind_iff] at actual
       obtain ⟨generated, _, actual⟩ := actual
       exact sourceAfter_seeds primitives writer projection generated.1 native (state.1, generated.2) seed result actual)

end BeaconcryptCore.Computational.PqxdhLiveJointSigning

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.joint_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.joint_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.signing_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.signing_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.serialization_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.serialization_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.writing_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.writing_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.afterGenerated_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.afterGenerated_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.generation_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.generation_complete

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.bundle_source

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.sourceAfter_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.sourceAfter_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.bundle_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.bundle_uniform

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.sourceAfter_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.sourceAfter_seeds

/-- info: 'BeaconcryptCore.Computational.PqxdhLiveJointSigning.bundle_seeds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLiveJointSigning.bundle_seeds

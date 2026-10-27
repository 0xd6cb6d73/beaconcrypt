import BeaconcryptCore.Computational.PqxdhServerAuthCtxNative

/-! Query accounting for the concrete ordinary tail compiler counts every attempted commitment, including the paths on which a frame writer or later response writer fails. Deterministic native and codec work remains computation. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds
open PqxdhJointKdfGame
open PqxdhServerAuthExperiment (Codec Checks)
open PqxdhServerAuthCtxNative

variable {Reader Response : Type}

def registrationHash (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) : Prop :=
  PqxdhServerRegistrationPublication.leftPredicate (RawCtxSourceSeal.category .hash) query = true

instance : DecidablePred registrationHash := fun query => inferInstanceAs (Decidable
  (PqxdhServerRegistrationPublication.leftPredicate (RawCtxSourceSeal.category .hash) query = true))

/-- Each concrete known native hash forwards exactly one component hash request; all other registration callbacks contribute zero. -/
theorem registration_hash_step {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) (state : A) :
    ((registration source codec checks query).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (if registrationHash query then 1 else 0) := by
  rcases query with (request | (input | (bytes | frame))) | callback
  all_goals simp only [registration, RawCtxMixedOwner.sendLift, simulateQ_spec_query]
  · simp [native, PqxdhServerAuthCtxAmbient.native, StateT.run_lift, bind_pure_comp, registrationHash,
      PqxdhServerRegistrationPublication.leftPredicate, RawCtxSourceSeal.category]
  · simp [native, PqxdhServerAuthCtxAmbient.native, StateT.run_lift, bind_pure_comp, registrationHash,
      PqxdhServerRegistrationPublication.leftPredicate, RawCtxSourceSeal.category]
  · simp [native, PqxdhServerAuthCtxAmbient.native, StateT.run_lift, bind_pure_comp, registrationHash,
      PqxdhServerRegistrationPublication.leftPredicate, RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind,
      PqxdhServerAuthCtxAmbient.hash,
      AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxQueryBounds.SourceHash]
  · simp [native, PqxdhServerAuthCtxAmbient.native, StateT.run_lift, bind_pure_comp, registrationHash,
      PqxdhServerRegistrationPublication.leftPredicate, RawCtxSourceSeal.category]
  · cases callback <;> simp [aux, registrationHash, PqxdhServerRegistrationPublication.leftPredicate]

/-- Every adaptive native registration program retains its attempted-hash allowance through the concrete compiler and complete local state. -/
theorem registration_hash {A Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks)
    (work : OracleComp PqxdhServerRegistrationPublication.NativeSpec Result) (bound : Nat)
    (bounded : work.IsQueryBoundP registrationHash bound) (state : A) :
    ((simulateQ (registration source codec checks) work).run state).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute bound :=
  bounded.simulateQ_run_StateT_of_step (registration_hash_step source codec checks) state

/-- The actual ordinary tail makes at most one component hash per reached source seal callback; KDF and auxiliary callbacks make none. -/
theorem nativeTail_hash {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : A) :
    ((nativeTail source codec checks query).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (if PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0) := by
  have single : (liftM (PqxdhServerRegistrationPublication.TailSpec.query query) : OracleComp PqxdhServerRegistrationPublication.TailSpec _).IsQueryBoundP
      (fun request => PqxdhServerRegistrationPublication.callKind request = .seal)
      (if PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0) :=
    (isQueryBoundP_query_iff _ _ _).2 (by intro hit; simp [hit])
  have expanded := PqxdhServerRegistrationPublication.native_seal_bound _ _ single .hash
  simp only [simulateQ_spec_query] at expanded
  exact registration_hash source codec checks (PqxdhServerRegistrationPublication.nativeAdapter query) _
    (IsQueryBoundP.of_imp (fun _ hit => hit) expanded) state

/-- Successful-seal logging inserts no query, including paths that later fail to write the response. -/
theorem tail_hash (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : List RawCtxSourceSend.SealContext) :
    ((tail source codec checks query).run state).IsQueryBoundP AdaptiveCtxDynamicKnownBounds.HashRoute
      (if PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0) := by
  rcases query with (request | input) | callback
  · exact nativeTail_hash source codec checks _ state
  · simp only [tail, StateT.run_bind]
    have before := nativeTail_hash source codec checks (.inl (.inr input)) state
    have after : ∀ result : Option Pqxdh.Bytes × List RawCtxSourceSend.SealContext,
        ((if result.1.isSome then do
            modify fun contexts => contexts ++ [input.context]
            pure result.1
          else pure result.1 : Local (List RawCtxSourceSend.SealContext) (Option Pqxdh.Bytes)).run result.2).IsQueryBoundP
          AdaptiveCtxDynamicKnownBounds.HashRoute 0 := by
      rintro ⟨result, current⟩
      cases result <;> trivial
    simpa only [Nat.add_zero] using isQueryBoundP_bind before (fun result _ => after result)
  · exact nativeTail_hash source codec checks _ state

/-- The complete concrete ordinary builder forwards at most one attempted commitment request, with no success premise or omitted writer-failure path. -/
theorem build_hash (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (state : List RawCtxSourceSend.SealContext) :
    ((simulateQ (tail source codec checks)
      (PqxdhServerRegistrationPublication.build source pending root payload () server)).run state).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.HashRoute 1 :=
  (PqxdhServerRegistrationPublication.build_bound source pending root payload () server .seal).simulateQ_run_StateT_of_step
    (tail_hash source codec checks) state

/-- The concrete ordinary registration compiler issues only shared hash requests. Known KDF, AEAD and codec work remains actual local computation. -/
theorem registration_only_hash {A : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) (state : A) :
    ((registration source codec checks query).run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
  rcases query with (request | (input | (bytes | frame))) | callback
  all_goals simp only [registration, RawCtxMixedOwner.sendLift, simulateQ_spec_query]
  all_goals try cases callback
  all_goals simp only [native, PqxdhServerAuthCtxAmbient.native, aux, StateT.run_lift, bind_pure_comp,
    PqxdhServerAuthCtxAmbient.hash]
  all_goals try trivial
  simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  simp [AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxQueryBounds.SourceHash]

/-- Any adaptive ordinary native registration program has no component query outside shared hashing. -/
theorem registration_program_only_hash {A Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response) (checks : Checks)
    (work : OracleComp PqxdhServerRegistrationPublication.NativeSpec Result) (state : A) :
    ((simulateQ (registration source codec checks) work).run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
  exact (isQueryBoundP_false work 0).simulateQ_run_StateT_of_step
    (fun query state => by simpa only [ite_false] using registration_only_hash source codec checks query state) state

/-- The successful-seal log cannot add selected seal, selected raw or explicit coin requests to the ordinary native tail. -/
theorem tail_only_hash (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) (checks : Checks)
    (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (state : List RawCtxSourceSend.SealContext) :
    ((tail source codec checks query).run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
  have base := fun request (current : List RawCtxSourceSend.SealContext) => registration_program_only_hash source codec checks
    (PqxdhServerRegistrationPublication.nativeAdapter request) current
  rcases query with (request | input) | callback
  · exact base (.inl (.inl request)) state
  · simp only [tail, StateT.run_bind]
    refine isQueryBoundP_bind (m := 0) (base (.inl (.inr input)) state) ?_
    rintro ⟨reply, after⟩ _
    cases reply <;> trivial
  · exact base (.inr callback) state

/-- Complete ordinary builders make no component requests other than the separately counted shared hashes. -/
theorem build_only_hash (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (state : List RawCtxSourceSend.SealContext) :
    ((simulateQ (tail source codec checks)
      (PqxdhServerRegistrationPublication.build source pending root payload () server)).run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
  exact (isQueryBoundP_false _ 0).simulateQ_run_StateT_of_step
    (fun query state => by simpa only [ite_false] using tail_only_hash source codec checks query state) state

/-- The literal ordinary receive adapter forwards each attempted hash once and adds no hash for a known KDF or AEAD opening. -/
theorem receive_hash_step {A : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (state : A) :
    ((simulateQ (native source writer) (RawCtxMixedOwner.receiveLift query)).run state).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute
      (if RawCtxSourceOpen.openingPredicate Sum.isLeft query = true then 1 else 0) := by
  rcases query with request | (bytes | input)
  all_goals simp [RawCtxMixedOwner.receiveLift, native, PqxdhServerAuthCtxAmbient.native,
    StateT.run_lift, bind_pure_comp, PqxdhServerAuthCtxAmbient.hash,
    RawCtxSourceOpen.openingPredicate, AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxQueryBounds.SourceHash]

/-- Every adaptive ordinary receive program preserves its actual attempted-hash budget and complete local state. -/
theorem receive_hash {A Result : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RawCtxSourceOpen.NativeSpec Result) (bound : Nat)
    (bounded : work.IsQueryBoundP (fun query => RawCtxSourceOpen.openingPredicate Sum.isLeft query = true) bound)
    (state : A) :
    ((simulateQ (native source writer ∘ₛ RawCtxMixedOwner.receiveLift) work).run state).IsQueryBoundP
      AdaptiveCtxDynamicKnownBounds.HashRoute bound :=
  bounded.simulateQ_run_StateT_of_step (receive_hash_step source writer) state

/-- The complete actual ordinary Beacon post-root continuation has at most one attempted component hash, including arbitrary raw/parser/sequence/opening failures. -/
theorem beacon_after_hash (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (prepared : PqxdhPhase2DhMetadata.Prepared Response) (root : Std.Array Std.U8 32#usize) (state : Unit) :
    ((simulateQ (beacon source codec)
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead prepared root)).run state).IsQueryBoundP
        AdaptiveCtxDynamicKnownBounds.HashRoute 1 := by
  unfold PqxdhPhase2DhRootConsumer.afterRoot PqxdhBeaconPhase2Publication.afterRoot
    PqxdhBeaconPhase2Publication.initialRun
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query,
    PqxdhBeaconPhase2Publication.nativeTailAdapter, beacon]
  cases found : codec.application (PqxdhPhase2DhRootConsumer.cleared prepared).response with
  | none => simp only [simulateQ_pure]; trivial
  | some raw =>
      simp only [bind_pure_comp, simulateQ_map, PqxdhBeaconPhase2Bounds.native_raw_lift,
        StateT.run_map, isQueryBoundP_map_iff]
      rw [← QueryImpl.simulateQ_compose]
      have handler : beacon source codec ∘ₛ PqxdhBeaconPhase2Publication.nativeRawLift =
          native source codec.frameWrite ∘ₛ RawCtxMixedOwner.receiveLift := by
        funext query
        simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeRawLift,
          simulateQ_spec_query, beacon]
      rw [handler]
      exact receive_hash source codec.frameWrite _ 1 (RawCtxSourceOpen.raw_primitive_bounds codec.frameRead raw _).1 state

/-- Every ordinary Beacon callback uses only shared hashes at the component interface; actual known-key opening and deterministic HKDF remain local. -/
theorem beacon_only_hash (source : FixedHkdfSha512NoSaltSource) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) (state : Unit) :
    ((beacon source codec query).run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
  rcases query with (request | (bytes | input)) | (root | request | response)
  all_goals simp only [beacon, RawCtxMixedOwner.receiveLift, simulateQ_spec_query,
    native, PqxdhServerAuthCtxAmbient.native, StateT.run_lift, bind_pure_comp, PqxdhServerAuthCtxAmbient.hash]
  all_goals try trivial
  simp only [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
  simp [AdaptiveCtxDynamicKnownBounds.HashRoute, AdaptiveCtxQueryBounds.SourceHash]

/-- Complete adaptive ordinary Beacon programs make no component call outside shared hashing, regardless of parser/opening outcomes. -/
theorem beacon_program_only_hash {Result : Type} (source : FixedHkdfSha512NoSaltSource)
    (codec : Codec Reader Response)
    (work : OracleComp (PqxdhBeaconPhase2Publication.NativeTailSpec Response) Result) (state : Unit) :
    ((simulateQ (beacon source codec) work).run state).IsQueryBoundP
      (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0 := by
  exact (isQueryBoundP_false work 0).simulateQ_run_StateT_of_step
    (fun query state => by simpa only [ite_false] using beacon_only_hash source codec query state) state

/-- The hash-only certificate explicitly gives zero selected seal, selected raw and explicit uniform calls. The hash budget and all deterministic work remain separate. -/
theorem only_hash_other {Result : Type} (work : OracleComp AdaptiveCtxDynamicKnownKeys.Spec Result)
    (bounded : work.IsQueryBoundP (fun query => ¬ AdaptiveCtxDynamicKnownBounds.HashRoute query) 0) :
    work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0 ∧
      work.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxReceive.IsRawQuery) 0 ∧
      work.IsQueryBoundP AdaptiveCtxDynamicKnownBounds.UniformRoute 0 := by
  refine ⟨bounded.of_imp ?_, bounded.of_imp ?_, bounded.of_imp ?_⟩
  · rintro (((coin | (hash | sealing)) | raw) | known) hit
    all_goals simp_all [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxDynamicKnownBounds.HashRoute,
      AdaptiveCtxQueryBounds.SourceSeal, AdaptiveCtxQueryBounds.SourceHash]
  · rintro (((coin | (hash | sealing)) | raw) | known) hit
    all_goals simp_all [AdaptiveCtxDynamicKnownBounds.TargetClass, AdaptiveCtxDynamicKnownBounds.HashRoute,
      AdaptiveCtxReceive.IsRawQuery, AdaptiveCtxQueryBounds.SourceHash]
  · rintro (((coin | (hash | sealing)) | raw) | known) hit
    all_goals simp_all [AdaptiveCtxDynamicKnownBounds.UniformRoute, AdaptiveCtxDynamicKnownBounds.HashRoute,
      AdaptiveCtxQueryBounds.SourceUniform, AdaptiveCtxQueryBounds.SourceHash,
      AdaptiveCtxSharedReplayBounds.ModeHash, AdaptiveCtxQueryBounds.SourceWork]

end BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_hash_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.nativeTail_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.nativeTail_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.tail_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.tail_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.build_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.build_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_only_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_only_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_program_only_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.registration_program_only_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.tail_only_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.tail_only_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.build_only_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.build_only_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.receive_hash_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.receive_hash_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.receive_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.receive_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.beacon_after_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.beacon_after_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.beacon_only_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.beacon_only_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.beacon_program_only_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.beacon_program_only_hash
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.only_hash_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxNativeBounds.only_hash_other

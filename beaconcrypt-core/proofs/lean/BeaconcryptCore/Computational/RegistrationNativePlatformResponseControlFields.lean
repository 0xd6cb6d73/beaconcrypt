import BeaconcryptCore.Computational.RegistrationNativePlatformResponseBranchFields
/-! Successful current moved-token completion returns bytes from the actual stateful source response writer with its exact stored Ready ciphertext and configured Server identity. Allocation, occupancy, seal and publication failures remain in the literal source body. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformResponseControlFields
open RegistrationNativePlatformBoundCompiler (PublicState)
open RegistrationNativeSecretWordMessage (Message ServerReady ServerState)
open RegistrationNativePlatformSecretWordBuildControl
variable {n : Nat} {Platform E : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (reservePackets : Usize → StateT Platform ProbComp (core.result.Result Unit E))
    (reservePeer : StateT Platform ProbComp Bool)
local notation "writer" => RegistrationNativePlatformConcreteSource.writer reservePackets
local notation "reserveSource" => RegistrationNativePlatformSecretWordBuild.liftEffects
  (RegistrationNativePlatformBoundCompiler.liftPlatform (n := n) (RegistrationNativePlatformEffectCompiler.compile reservePeer))
local notation "serviceSource" => RegistrationNativePlatformSecretWordBuild.service (n := n) source view failure allocation erased helper sign writer
local notation "presenceSource" => (fun keyId => RegistrationNativePlatformSecretWordBuild.liftEffects
  (RegistrationNativePlatformEffectCompiler.effect (n := n) (Platform := PublicState Platform) (Sum.inr (PqxdhRecordLiftInterface.Capability.peerPresent keyId))))
local notation "pinSource" => (fun current => RegistrationNativePlatformSecretWordBuild.liftEffects
  (RegistrationNativePlatformServerRestrictedService.pin (n := n) (Platform := Platform) current))

omit primitive in
private theorem pure_apply {S A : Type} {m : Type → Type} [Monad m] (value : A) (before : S) :
    (pure value : StateT S m A) before = pure (value,before) := rfl

omit primitive in
private theorem bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (work : StateT S m A) (next : A → StateT S m B) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

omit primitive in
private def Fields (ciphertext : Std.Array U8 1088#usize) (identity : Std.Array U8 32#usize) (bytes : alloc.vec.Vec U8) : Prop :=
  RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse ciphertext (TranscriptAuthParts.absSlice bytes) ∧
  RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse identity (TranscriptAuthParts.absSlice bytes)

omit primitive in
private theorem lookup_fields (control : pqxdh.ServerState) (current : session.ServerAuthenticationPin)
    (ready : ServerReady) (application : Slice U8) (lookup : peer.CompletionLookup)
    (begun : peer.begin_completion_lookup control current (RegistrationNativeSecretWordServerMaterial.token ready) application=.ok (.Ok lookup))
    (occupied : Bool) (initial : registration.ServerInitialKdf) (resumed : lookup.resume occupied=.ok (.Ok initial)) :
    initial.candidate.kem_ciphertext=ready.agreement.pending.kem_ciphertext ∧
    initial.candidate.server_identity_public_key=current.binding.identity_public_key := by
  obtain ⟨next,nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  cases next with
  | Err previous => simp [peer.begin_completion_lookup,nextRun] at begun
  | Ok allocated =>
    have looked := BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_begin_next control current
      (RegistrationNativeSecretWordServerMaterial.token ready) application allocated nextRun
    rw [looked] at begun
    cases begun
    have initialized : registration.begin_server_completion control current (if occupied then .Occupied else .Available)
        (RegistrationNativeSecretWordServerMaterial.token ready).agreement application = .ok (.Ok initial) :=
      (BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_resume
        (peer.CompletionLookup.mk control current (RegistrationNativeSecretWordServerMaterial.token ready) application allocated) occupied).symm.trans resumed
    exact ⟨RegistrationNativeResponseCipherCandidate.initial_ciphertext _ _ _ _ _ _ initialized,
      RegistrationNativeResponseCandidate.initial_identity _ _ _ _ _ _ initialized⟩

private theorem after_result (control : pqxdh.ServerState) (reference : Message)
    (action : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState))
    (ciphertext : Std.Array U8 1088#usize) (identity : Std.Array U8 32#usize)
    (initialFields : ∀ initial, action=.ok (.Ok initial) → initial.candidate.kem_ciphertext=ciphertext ∧ initial.candidate.server_identity_public_key=identity)
    (before after : ServerState) (previous next : PublicState Platform) (keyId : U64) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some (keyId,bytes)),after),next) ∈ support
      (((afterResult reserveSource serviceSource control reference action).run before).run previous)) : Fields ciphertext identity bytes := by
  cases action with
  | fail error | div => simp [afterResult] at supported
  | ok result => cases result with
    | Err previousControl => simp [afterResult] at supported
    | Ok initial =>
      have fields := initialFields initial rfl
      simp only [afterResult,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,mem_support_bind_iff] at supported
      obtain ⟨admitted,_reserved,continued⟩ := supported
      cases allowed : admitted.1 with
      | false => simp [allowed] at continued
      | true =>
        simp only [allowed,ite_true,StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,mem_support_bind_iff] at continued
        obtain ⟨published,called,returned⟩ := continued
        simp only [StateT.run,pure_apply,mem_support_pure_iff] at returned
        have same := congrArg (fun result => result.1.1) returned
        cases actual : published.1 with
        | fail error | div => simp [actual,finish] at same
        | ok value => cases value with
          | Err control => simp [actual,finish] at same
          | Ok peer =>
            simp only [actual,finish] at same
            have encoding : peer.encoded=bytes := (congrArg Prod.snd (Option.some.inj (RustM.ok.inj same))).symm
            have encoded := RegistrationNativePlatformResponseBranchFields.service source view failure allocation erased helper sign reservePackets
              control initial reference peer admitted.2 published.2 (by simpa only [←actual,Prod.mk.eta] using called)
            change RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
              initial.candidate.kem_ciphertext (TranscriptAuthParts.absSlice peer.encoded) ∧
              RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
              initial.candidate.server_identity_public_key (TranscriptAuthParts.absSlice peer.encoded) at encoded
            rw [fields.1,fields.2,encoding] at encoded
            exact encoded

private theorem after_pin (control : pqxdh.ServerState) (ready : ServerReady) (application : Slice U8)
    (current : RustM (core.option.Option session.ServerAuthenticationPin)) (identity : Std.Array U8 32#usize)
    (pinFields : ∀ pin, current=.ok (.Some pin) → pin.binding.identity_public_key=identity)
    (before after : ServerState) (previous next : PublicState Platform) (keyId : U64) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some (keyId,bytes)),after),next) ∈ support
      (((afterPin reserveSource presenceSource serviceSource control ready application current).run before).run previous)) :
    Fields ready.agreement.pending.kem_ciphertext identity bytes := by
  cases current with
  | fail error | div => simp [afterPin,StateT.run,pure_apply] at supported
  | ok optional => cases optional with
    | none => simp [afterPin,StateT.run,pure_apply] at supported
    | some pin =>
      have pinEq := pinFields pin rfl
      simp only [afterPin,StateT.run] at supported
      cases begun : peer.begin_completion_lookup control pin (RegistrationNativeSecretWordServerMaterial.token ready) application with
      | fail error | div => simp [begun,pure_apply] at supported
      | ok optional => cases optional with
        | Err previousControl => simp [begun,pure_apply] at supported
        | Ok lookup =>
          simp only [begun] at supported
          cases requested : lookup.request with
          | fail error | div => simp [requested,pure_apply] at supported
          | ok allocated =>
            simp only [requested] at supported
            split at supported
            · rw [bind_apply,mem_support_bind_iff] at supported
              obtain ⟨occupied,_asked,continued⟩ := supported
              apply after_result source view failure allocation erased helper sign reservePackets reservePeer control ready.reference _
                ready.agreement.pending.kem_ciphertext identity ?_ before after occupied.2 next keyId bytes continued
              intro admitted initialEq
              cases resumed : lookup.resume occupied.1 with
              | fail error =>
                  rw [resumed] at initialEq
                  change (RustM.fail error : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) = .ok (.Ok admitted) at initialEq
                  cases initialEq
              | div =>
                  rw [resumed] at initialEq
                  change (RustM.div : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) = .ok (.Ok admitted) at initialEq
                  cases initialEq
              | ok selected => cases selected with
                | Err previousControl =>
                    rw [resumed] at initialEq
                    change (RustM.ok (.Err previousControl) : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) = .ok (.Ok admitted) at initialEq
                    cases initialEq
                | Ok initial =>
                  rw [resumed] at initialEq
                  change (RustM.ok (.Ok (RegistrationBoundKeySchedule.publicInitial initial)) : RustM (core.result.Result RegistrationBoundKeySchedule.PublicInitial pqxdh.ServerState)) = .ok (.Ok admitted) at initialEq
                  cases initialEq
                  have fields := lookup_fields control pin ready application lookup begun occupied.1 initial resumed
                  exact ⟨fields.1,fields.2.trans pinEq⟩
            · simp [pure_apply] at supported


omit primitive in
private theorem pin_fields (current : session.ServerAuthenticationPin)
    (before after : PublicState Platform) (returned : RustM (core.option.Option session.ServerAuthenticationPin))
    (supported : (returned,after) ∈ support ((pinSource current).run before))
    (pin : session.ServerAuthenticationPin) (equal : returned=.ok (.Some pin)) :
    pin.binding.identity_public_key=current.binding.identity_public_key := by
  have possible := PqxdhDeploymentEnvironment.support_simulateQ_subset
    (RegistrationNativePlatformSecretWordBuild.embed (n := n))
    ((RegistrationNativePlatformServerRestrictedService.pin current).run before) supported
  change (returned,after) ∈ support (do
    let digest ← ((RegistrationNativePlatformEffectCompiler.Spec n).query (.inl (.inr (.hash (PqxdhRefinement.absBytes current.public_key)))) : OracleComp (RegistrationNativePlatformEffectCompiler.Spec n) _)
    pure (.ok (.Some ⟨current.binding,current.public_key,RegistrationAuthenticationShared.digestArray digest⟩),before)) at possible
  rw [mem_support_bind_iff] at possible
  obtain ⟨digest,_drawn,same⟩ := possible
  rw [mem_support_pure_iff] at same
  have selected := equal.symm.trans (congrArg Prod.fst same)
  have pinSame := Option.some.inj (RustM.ok.inj selected)
  rw [pinSame]

/-- Successful current source completion encodes the same consumed Ready ciphertext and the pre-call Server identity, through its actual stateful writer. -/
theorem complete (ready : ServerReady) (application : Slice U8)
    (before after : ServerState) (previous next : PublicState Platform) (keyId : U64) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some (keyId,bytes)),after),next) ∈ support
      (((RegistrationNativePlatformSecretWordBuildControl.complete pinSource reserveSource presenceSource serviceSource ready application).run before).run previous)) :
    RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
      ready.agreement.pending.kem_ciphertext (TranscriptAuthParts.absSlice bytes) ∧
    RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
      before.pin.binding.identity_public_key (TranscriptAuthParts.absSlice bytes) := by
  simp only [RegistrationNativePlatformSecretWordBuildControl.complete, StateT.run,
    bind_apply,mem_support_bind_iff] at supported
  obtain ⟨current,hashed,continued⟩ := supported
  exact after_pin source view failure allocation erased helper sign reservePackets reservePeer
    before.control ready application current.1 before.pin.binding.identity_public_key
    (fun pin equal => pin_fields before.pin previous current.2 current.1 hashed pin equal)
    before after current.2 next keyId bytes continued

/-- An actual successful moved-token build binds its encoded response to the exact stored Ready and original Server identity. Rejected pin, reserve, occupancy, allocation, seal and publication paths remain literal source paths. -/
theorem body (handle : Nat) (application : Option (Slice U8))
    (before after : ServerState) (previous next : PublicState Platform) (keyId : U64) (bytes : alloc.vec.Vec U8)
    (supported : ((.ok (some (keyId,bytes)),after),next) ∈ support
      (((RegistrationNativePlatformSecretWordBuild.body (n := n) source view failure allocation erased helper sign writer reservePeer handle application).run before).run previous)) :
    ∃ ready, before.sessions[handle]?=some (some ready) ∧
      RegistrationNativeResponseCiphertext.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
        ready.agreement.pending.kem_ciphertext (TranscriptAuthParts.absSlice bytes) ∧
      RegistrationNativeResponseIdentity.EncodedFrom RegistrationNativePlatformConcreteSource.wire.encodeResponse
        before.pin.binding.identity_public_key (TranscriptAuthParts.absSlice bytes) := by
  simp only [RegistrationNativePlatformSecretWordBuild.body,RegistrationNativePlatformSecretWordBuildControl.build,
    RegistrationNativeSecretWordServerMaterial.take,StateT.run] at supported
  cases stored : before.sessions[handle]? with
  | none => simp [stored,StateT.monad_pure_def,StateT.pure] at supported
  | some entry => cases entry with
    | none => simp [stored,StateT.monad_pure_def,StateT.pure] at supported
    | some ready =>
      simp only [stored] at supported
      cases application with
      | none => simp [StateT.monad_pure_def,StateT.pure] at supported
      | some application =>
          exact ⟨ready,rfl,complete source view failure allocation erased helper sign reservePackets reservePeer ready application
            {before with sessions:=before.sessions.set handle none} after previous next keyId bytes supported⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformResponseControlFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseControlFields.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseControlFields.complete

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformResponseControlFields.body' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformResponseControlFields.body

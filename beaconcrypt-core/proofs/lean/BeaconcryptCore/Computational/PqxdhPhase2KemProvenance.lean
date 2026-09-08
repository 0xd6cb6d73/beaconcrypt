import BeaconcryptCore.Computational.PqxdhPhase2KemHandles
import BeaconcryptCore.Computational.PqxdhGeneratedBeaconState
import BeaconcryptCore.Computational.PqxdhPhase2LiveFinish

/-!
The selected KEM handle is identified by its original generation, not public-key byte equality. A reached-state predicate records that every generated handle is the designated original index/public key; earlier objects keep their complete disjoint payloads. The Option encoding is invertible on this predicate. No secret key, honest accepted candidate, or primitive security premise is introduced.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPhase2KemProvenance
open PqxdhGeneratedBeaconState (KemHandle)
open PqxdhStatefulPhase1EufCma (TargetKemPublicKey)
variable {I D K : Type}

def encode : KemHandle K → Option K
  | .existing key => some key
  | .generated _ _ => none

def decode (index : Nat) (publicKey : TargetKemPublicKey) : Option K → KemHandle K
  | some key => .existing key
  | none => .generated index publicKey

def Key (index : Nat) (publicKey : TargetKemPublicKey) : KemHandle K → Prop
  | .existing _ => True
  | .generated actual actualKey => actual = index ∧ actualKey = publicKey

/-- Earlier payloads and the original selected generator are represented reversibly, without public-key comparisons. -/
theorem decode_encode (index : Nat) (publicKey : TargetKemPublicKey) (key : KemHandle K)
    (valid : Key index publicKey key) : decode index publicKey (encode key) = key := by
  cases key with
  | existing key => rfl
  | generated actual actualKey =>
    obtain ⟨rfl, rfl⟩ := valid
    rfl

def Phase {Kernel : Type} (predicate : K → Prop) : RawCtxBeaconLifecycle.Phase D K Kernel → Prop
  | .fresh _ _ key | .freshWithCoins _ _ _ key | .initSent _ _ _ key => predicate key
  | .established _ _ _ | .aborted _ => True

def Owner (index : Nat) (publicKey : TargetKemPublicKey)
    (state : RawCtxBeaconLifecycle.State I D (KemHandle K)) : Prop :=
  Phase (Key index publicKey) state.beacon.phase

/-- The selected/prior encoding reconstructs every retained native owner field on valid provenance. -/
theorem owner_inverse (index : Nat) (publicKey : TargetKemPublicKey)
    (state : RawCtxBeaconLifecycle.State I D (KemHandle K)) (valid : Owner index publicKey state) :
    PqxdhBeaconPhase1Publication.mapState id (decode index publicKey)
      (PqxdhBeaconPhase1Publication.mapState id encode state) = state := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk identity keyId serverIdentity phase =>
      cases phase <;> simp only [Owner, Phase] at valid
      all_goals simp only [PqxdhBeaconPhase1Publication.mapState, PqxdhBeaconPhase1Publication.mapPhase, id_eq]
      all_goals first | rfl | rw [decode_encode index publicKey _ valid]

/-- Every previously retained object preserves its complete existing KEM payload, even when public bytes coincide with the new target. -/
theorem existing_valid (index : Nat) (publicKey : TargetKemPublicKey)
    (state : RawCtxBeaconLifecycle.State I D K) :
    Owner index publicKey (PqxdhBeaconPhase1Publication.mapState id KemHandle.existing state) := by
  cases h : state.beacon.phase <;> simp only [Owner, PqxdhBeaconPhase1Publication.mapState, h, PqxdhBeaconPhase1Publication.mapPhase, Phase, Key]

/-- The actual fresh source owner has exactly the designated generated handle. -/
theorem fresh_valid {ι : Type} {baseSpec : OracleSpec ι}
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (index : Nat) (identity : PqxdhJointIdentity.PublicIdentity)
    (generated : PqxdhPrivateKemSource.Generated setup Unit) (binding : pqxdh.ServerBinding) :
    Owner index generated.target (PqxdhGeneratedBeaconState.fresh (I := I) (K := K) setup index identity generated binding) := by
  exact ⟨rfl, rfl⟩

/-- Actual Phase1 preparation selects the original retained KEM handle on every successful branch. -/
theorem prepare_valid (index : Nat) (publicKey : TargetKemPublicKey)
    (state : RawCtxBeaconLifecycle.State I D (KemHandle K)) (valid : Owner index publicKey state)
    (generated : Option D) (prepared : PqxdhBeaconPhase1Publication.Prepared D (KemHandle K))
    (selected : PqxdhBeaconPhase1Publication.prepare state generated = some prepared) :
    Key index publicKey prepared.kem := by
  cases h : state.beacon.phase <;> simp only [PqxdhBeaconPhase1Publication.prepare, h] at selected
  case fresh control prekey kem =>
    cases generated with
    | none => cases selected
    | some oneTime =>
      cases selected
      simpa only [Owner, h, Phase] using valid
  case freshWithCoins control prekey oneTime kem =>
    cases selected
    simpa only [Owner, h, Phase] using valid
  all_goals cases selected

/-- Every actual writer result preserves selected/prior KEM provenance, with its complete auxiliary state left unconstrained. -/
theorem afterSigning_valid {A : Type}
    (writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec (StateT A ProbComp))
    (index : Nat) (publicKey : TargetKemPublicKey)
    (identity : Std.Array Std.U8 32#usize) (bundle : PqxdhEd25519EufCma.Phase1Candidate)
    (generated : Option D) (state : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Owner index publicKey state) (auxiliary : A)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D (KemHandle K)) × A)
    (supported : result ∈ support ((simulateQ writer
      (PqxdhBeaconPhase1Publication.afterSigning identity bundle generated state)).run auxiliary)) :
    Owner index publicKey result.1.2 := by
  cases selected : PqxdhBeaconPhase1Publication.prepare state generated with
  | none =>
    simp only [PqxdhBeaconPhase1Publication.afterSigning, selected, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact valid
  | some prepared =>
    simp only [PqxdhBeaconPhase1Publication.afterSigning, selected, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨written, _, supported⟩ := supported
    cases reply : written.1 <;> simp only [reply, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    all_goals subst result
    · exact valid
    · exact prepare_valid index publicKey state valid generated prepared selected

/-- An active Phase2 attempt disposes of its retained KEM material on both publication and terminal abort. -/
theorem finish_valid (index : Nat) (publicKey : TargetKemPublicKey)
    (control : pqxdh.BeaconInitSent) (state : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    Owner index publicKey (PqxdhBeaconPhase2Publication.finish control state staged).2 := by
  cases staged with
  | none => trivial
  | some staged =>
    simp only [PqxdhBeaconPhase2Publication.finish]
    split_ifs <;> trivial

/-- Complete Phase2 interpretation preserves provenance for every optional reply and auxiliary outcome. -/
theorem owner_valid {A X Response ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.FullSpec I D (KemHandle K) X Response)
      (StateT A (OracleComp base)))
    (index : Nat) (publicKey : TargetKemPublicKey) (decodeFrame : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Owner index publicKey state) (auxiliary : A)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D (KemHandle K)) × A)
    (supported : result ∈ support ((simulateQ handler
      (PqxdhBeaconPhase2Publication.owner decodeFrame raw state)).run auxiliary)) :
    Owner index publicKey result.1.2 := by
  cases active : state.beacon.phase
  all_goals simp only [PqxdhBeaconPhase2Publication.owner, active, simulateQ_pure,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  case initSent control prekey oneTime kem =>
    rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨prepared, _, supported⟩ := supported
    cases reply : prepared.1 <;> simp only [reply, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at supported
    · subst result
      exact finish_valid index publicKey control state none
    · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨staged, _, supported⟩ := supported
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact finish_valid index publicKey control state staged.1
  all_goals subst result; exact valid

/-- The actual native raw opening expansion preserves the same complete owner's KEM provenance. -/
theorem native_valid {A X Response ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (KemHandle K) X Response)
      (StateT A (OracleComp base)))
    (index : Nat) (publicKey : TargetKemPublicKey) (decodeFrame : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Owner index publicKey state) (auxiliary : A)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D (KemHandle K)) × A)
    (supported : result ∈ support ((simulateQ handler
      (PqxdhBeaconPhase2Publication.nativeOwner decodeFrame raw state)).run auxiliary)) :
    Owner index publicKey result.1.2 := by
  apply owner_valid (handler ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter)
    index publicKey decodeFrame raw state valid auxiliary result
  simpa only [PqxdhBeaconPhase2Publication.nativeOwner, QueryImpl.simulateQ_compose] using supported

/-- Provenance depends only on the actual retained private role fields, not the evolving established kernel. -/
theorem retained_valid (index : Nat) (publicKey : TargetKemPublicKey)
    (before after : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Owner index publicKey before)
    (retained : RawCtxBeaconLifecycle.retained after = RawCtxBeaconLifecycle.retained before) :
    Owner index publicKey after := by
  have same := congrArg (fun fields => fields.2.2.2) retained
  change RawCtxBeaconLifecycle.phaseFields after.beacon.phase = RawCtxBeaconLifecycle.phaseFields before.beacon.phase at same
  have fields (phase : RawCtxBeaconLifecycle.Phase D (KemHandle K) ratchet.concrete.ConcreteRatchetKernel) :
      Phase (Key index publicKey) phase = Phase (Key index publicKey) (RawCtxBeaconLifecycle.phaseFields phase) := by
    cases phase <;> rfl
  change Phase (Key index publicKey) after.beacon.phase
  rw [fields, same, ← fields]
  exact valid

/-- The actual adaptive send/raw continuation preserves retained KEM provenance through rejected calls, failed openings and successful publications. -/
theorem records_valid {A Result ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT A (OracleComp base)))
    (index : Nat) (publicKey : TargetKemPublicKey) (decodeFrame : RawCtxReceive.FrameDecoder)
    (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (qRaw : Nat) (rawBound : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Owner index publicKey state) (auxiliary : A)
    (result : Result × (RawCtxBeaconLifecycle.State I D (KemHandle K) × A))
    (supported : result ∈ support ((simulateQ (RawCtxBeaconLifecycle.sourceImpl impl decodeFrame) client).run (state, auxiliary))) :
    Owner index publicKey result.2.1 := by
  exact retained_valid index publicKey state result.2.1 valid
    (RawCtxBeaconLifecycle.source_schedule impl decodeFrame client qRaw rawBound (state, auxiliary) result supported).2

/-- Extending the actual session family derives provenance for every previous owner and the new designated owner. -/
theorem extend_valid {ι : Type} {baseSpec : OracleSpec ι} {M P A : Type} {S B : Nat}
    {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (index : Nat) (publicKey : TargetKemPublicKey) (beacon : PqxdhGeneratedBeaconState.Beacon setup I K)
    (valid : Owner index publicKey beacon)
    (state : PqxdhGeneratedBeaconState.InitialState setup M P I K A S B) :
    ∀ position, Owner index publicKey ((PqxdhGeneratedBeaconState.extend beacon state).roles.1.2 position) := by
  intro position
  refine Fin.cases ?_ (fun prior => ?_) position
  · exact valid
  · simpa only [PqxdhGeneratedBeaconState.extend, Fin.cons_succ, PqxdhGeneratedBeaconState.existing,
      Owner, PqxdhBeaconPhase1Publication.mapState] using
      existing_valid index publicKey (state.roles.1.2 prior)

/-- From the supplied Generated output, the actual start/writer/publication execution derives the complete reached family invariant. -/
theorem start_valid {ι : Type} {baseSpec : OracleSpec ι} {M P A : Type} {S B : Nat}
    (setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec)
    (writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (index : Nat) (identity : PqxdhJointIdentity.PublicIdentity)
    (generated : PqxdhPrivateKemSource.Generated setup Unit) (binding : pqxdh.ServerBinding)
    (bundle : PqxdhEd25519EufCma.Phase1Candidate)
    (state : PqxdhGeneratedBeaconState.InitialState setup M P I K A S B)
    (result : Option Pqxdh.Bytes × PqxdhGeneratedBeaconState.State setup M P I K A S (B + 1))
    (supported : result ∈ support (PqxdhGeneratedBeaconState.start setup writer index identity generated binding bundle state)) :
    ∀ position, Owner index generated.target (result.2.roles.1.2 position) := by
  unfold PqxdhGeneratedBeaconState.start at supported
  obtain ⟨inner, innerSupported, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  have fresh := fresh_valid (I := I) (K := K) setup index identity generated binding
  have newOwner := afterSigning_valid writer index generated.target
    (PqxdhRootTableInitialization.rootArray identity.ed25519) bundle (some (.inr generated.after))
    (PqxdhGeneratedBeaconState.fresh setup index identity generated binding) fresh state.primitive inner innerSupported
  intro position
  by_cases selected : position = 0
  · subst position
    simpa only [PqxdhGeneratedBeaconState.reinstall, Function.update_self] using newOwner
  · simpa only [PqxdhGeneratedBeaconState.reinstall, Function.update_of_ne selected] using
      extend_valid index generated.target (PqxdhGeneratedBeaconState.fresh setup index identity generated binding)
        fresh state position

/-- Actual indexed record and public calls preserve every owner's original KEM provenance through the shared primitive state. -/
theorem role_step_valid {M P A : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (index : Nat) (publicKey : TargetKemPublicKey)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (state : RawCtxProtocolRoles.State M P I D (KemHandle K) S B × RawCtxSharedPrimitive.SharedState A)
    (valid : ∀ position, Owner index publicKey (state.1.2 position))
    (result : (RawCtxProtocolRoles.SourceSpec S B).Range query ×
      (RawCtxProtocolRoles.State M P I D (KemHandle K) S B × RawCtxSharedPrimitive.SharedState A))
    (supported : result ∈ support ((RawCtxProtocolRoles.sourceImpl source writer S B senderId route decodeFrame query).run state)) :
    ∀ position, Owner index publicKey (result.2.1.2 position) := by
  rcases query with server | (beacon | publicQuery)
  all_goals simp only [RawCtxProtocolRoles.sourceImpl, StateT.run, bind_pure_comp, support_map] at supported
  all_goals obtain ⟨original, originalSupport, rfl⟩ := supported
  case inr.inl =>
    simp only [RawCtxRoleFamily.sourceFamily, bind_pure_comp, support_map] at originalSupport
    obtain ⟨localResult, localSupport, rfl⟩ := originalSupport
    have preserved := RawCtxBeaconLifecycle.source_step _ decodeFrame beacon.2 _ localResult localSupport
    have localValid := retained_valid index publicKey _ localResult.2.1 (valid beacon.1) preserved.2
    intro position
    by_cases same : position = beacon.1
    · subst position
      simpa only [Function.update_self] using localValid
    · simpa only [Function.update_of_ne same] using valid position
  all_goals exact valid

/-- The actual public and live-reveal interface preserves every owner's retained KEM generation provenance. -/
theorem source_step_valid {M P A : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (index : Nat) (publicKey : TargetKemPublicKey)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (state : PqxdhRegistrationProtocolState.State M P I D (KemHandle K) A S B)
    (valid : ∀ position, Owner index publicKey (state.roles.1.2 position))
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query ×
      PqxdhRegistrationProtocolState.State M P I D (KemHandle K) A S B)
    (supported : result ∈ support ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decodeFrame query).run state)) :
    ∀ position, Owner index publicKey (result.2.roles.1.2 position) := by
  cases query with
  | inl request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, bind_pure_comp, support_map, Functor.map_map] at supported
    obtain ⟨original, originalSupport, rfl⟩ := supported
    exact role_step_valid source writer senderId route decodeFrame index publicKey request _ valid original originalSupport
  | inr request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact valid

/-- Every original adaptive record/public/reveal/finish schedule retains the proved original-generation invariant for the complete owner family. -/
theorem live_valid {M P A X Response Result : Type} {S B : Nat}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (KemHandle K) X Response)
      (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (index : Nat) (publicKey : TargetKemPublicKey)
    (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result)
    (state : PqxdhRegistrationProtocolState.State M P I D (KemHandle K) A S B)
    (valid : ∀ position, Owner index publicKey (state.roles.1.2 position))
    (result : Result × PqxdhRegistrationProtocolState.State M P I D (KemHandle K) A S B)
    (supported : result ∈ support ((simulateQ
      (PqxdhPhase2LiveFinish.sourceImpl source writer senderId route decodeFrame native) client).run state)) :
    ∀ position, Owner index publicKey (result.2.roles.1.2 position) := by
  apply PqxdhPhase2LiveFinish.live_invariant
    (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decodeFrame) native decodeFrame
    (fun current => ∀ position, Owner index publicKey (current.roles.1.2 position))
    ?_ ?_ client state valid result supported
  · intro query before after beforeValid present
    exact source_step_valid source writer senderId route decodeFrame index publicKey query before beforeValid after present
  · intro selected raw before after beforeValid present position
    have changed := native_valid native index publicKey decodeFrame raw (before.roles.1.2 selected)
      (beforeValid selected) before.primitive after present
    by_cases same : position = selected
    · subst position
      simpa only [PqxdhPhase2LiveFinish.install, Function.update_self] using changed
    · simpa only [PqxdhPhase2LiveFinish.install, Function.update_of_ne same] using beforeValid position

/-- On reached provenance, selected/prior native execution reconstructs the exact original result and complete auxiliary poststate. -/
theorem native_encoded_run {A X Response : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (KemHandle K) X Response) (StateT A m))
    (index : Nat) (publicKey : TargetKemPublicKey) (decodeFrame : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Owner index publicKey state) (auxiliary : A) :
    (fun result => ((result.1.1, PqxdhBeaconPhase1Publication.mapState id (decode index publicKey) result.1.2), result.2)) <$>
      (simulateQ (handler ∘ₛ PqxdhPhase2KemHandles.native (decode index publicKey))
        (PqxdhBeaconPhase2Publication.nativeOwner decodeFrame raw
          (PqxdhBeaconPhase1Publication.mapState id encode state))).run auxiliary =
      (simulateQ handler (PqxdhBeaconPhase2Publication.nativeOwner decodeFrame raw state)).run auxiliary := by
  rw [PqxdhPhase2KemHandles.native_owner_run, owner_inverse index publicKey state valid]

end BeaconcryptCore.Computational.PqxdhPhase2KemProvenance

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.decode_encode' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.decode_encode

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.owner_inverse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.owner_inverse

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.existing_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.existing_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.fresh_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.fresh_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.prepare_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.prepare_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.afterSigning_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.afterSigning_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.finish_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.finish_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.owner_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.owner_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.native_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.native_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.retained_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.retained_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.records_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.records_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.extend_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.extend_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.start_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.start_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.role_step_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.role_step_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.source_step_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.source_step_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.live_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.live_valid

/--
info: 'BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.native_encoded_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPhase2KemProvenance.native_encoded_run

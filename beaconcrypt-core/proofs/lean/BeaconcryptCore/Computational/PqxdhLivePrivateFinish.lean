import BeaconcryptCore.Computational.PqxdhLivePhase2PrivateRoot
import BeaconcryptCore.Computational.PqxdhPhase2LiveFinish

/-!
Actual live finish requests execute the native owner through the private challenge-root router and publish its complete owner and primitive poststate. The public continuation receives only the original optional byte reply. Indexed KEM decapsulation observations, local callback state and the joint identity history stay in interpreter state.
-/
open OracleComp OracleSpec CoreModels Aeneas
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLivePrivateFinish
open PqxdhLivePhase2PrivateRoot PqxdhKemIndCca PqxdhJointIdentity PqxdhJointKdfGame
open PqxdhPrivateKemSource PqxdhChallengeSecretRouting
open PqxdhLivePhase2Aux (Identity LocalSpec)
open PqxdhPhase2DecapsulationRouting (Shared)
open PqxdhLiveKemRouting (Handle PrivateKeys)
variable {ι KemSK M P D A Response : Type} {baseSpec : OracleSpec ι} {S B : Nat}

abbrev Live (M P D A : Type) (S B : Nat) :=
  PqxdhRegistrationProtocolState.State M P Identity D Handle A S B

/-- The interpreter retains all original owners, registration controls, shared cache and joint history, plus only its private added attempt log. -/
abbrev State (M P D A : Type) (S B : Nat) :=
  Live M P D A S B × PqxdhDynamicIdentityPool.SourceState × List (DecapsulationEvent Shared)

/-- Installation is the original source operation. The decoded selected/other handle is public creation provenance, not secret-key material. -/
def install (selected : Nat) (target : MlKem768PublicKey) (index : Fin B)
    (before : State M P D A S B)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected))) ×
      (AuxState A × List (DecapsulationEvent Shared))) : Option Pqxdh.Bytes × State M P D A S B :=
  (result.1.1,
    PqxdhPhase2LiveFinish.install index before.1
      (PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2) result.2.1.1,
    result.2.1.2, before.2.2 ++ result.2.2)

/-- Each complete attempt starts its own private decapsulation log and appends it once after the actual optional owner result. No selected-secret or supplied shared-secret argument occurs here. -/
noncomputable def finish (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (target : MlKem768PublicKey)
    (keys : PrivateKeys KemSK) (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (State M P D A S B) (OracleComp (LocalPostSpec baseSpec)))
  | .finish index raw => fun before => install selected target index before <$>
      privateOwner primitives kem selected keys source callbacks challenge read raw
        (PqxdhBeaconPhase1Publication.mapState id (encode selected) (before.1.roles.1.2 index))
        ((before.1.primitive, before.2.1), [])

/-- Original record, public primitive and current-chain/skipped-key reveal operations keep the full native state and their ordinary optional replies. -/
noncomputable def old (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (State M P D A S B) (OracleComp (LocalPostSpec baseSpec))) := fun query before =>
  simulateQ PqxdhBeaconPhase2Routed.publicLift (ccaCoins ((fun result => (result.1, result.2, before.2)) <$>
    (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route read query).run before.1))

/-- One adaptive original API schedule includes every native finish, record/public request and original chain disclosure. Identity, root and KEM disclosure scheduling is supplied separately by the common experiment. -/
noncomputable def service (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (target : MlKem768PublicKey)
    (keys : PrivateKeys KemSK) (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext) :
    QueryImpl (PqxdhPhase2LiveFinish.Spec S B)
      (StateT (State M P D A S B) (OracleComp (LocalPostSpec baseSpec)))
  | .inl query => old source writer senderId route read query
  | .inr query => finish primitives kem selected target keys source callbacks challenge read query

/-- Mathematical source comparison restores the original private pool and its complete ordered observation history. The public API does not receive this value. -/
def restored (pool : PqxdhLiveKemBirth.Pool KemSK) (supplied : MlKemSharedSecret)
    (before : State M P D A S B) : Live M P D A S B × PqxdhLiveKemBirth.State KemSK :=
  (before.1, (restorePrivate pool supplied ((before.1.primitive, before.2.1), before.2.2)).2)

/-- The direct source finish calls the actual indexed native callback interpreter before the original complete-owner installation. -/
noncomputable def sourceFinish (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (read : RawCtxReceive.FrameDecoder) : QueryImpl (PqxdhPhase2LiveFinish.FinishSpec B)
      (StateT (Live M P D A S B × PqxdhLiveKemBirth.State KemSK) ProbComp)
  | .finish index raw => fun before =>
      (fun result => (result.1.1,
        PqxdhPhase2LiveFinish.install index before.1 result.1.2 result.2.1, result.2.2)) <$>
        (simulateQ (PqxdhLivePhase2Aux.dispatch source
          (PqxdhLivePhase2Aux.direct baseImpl primitives kem source callbacks))
          (PqxdhBeaconPhase2Publication.nativeOwner read raw (before.1.roles.1.2 index))).run
            (before.1.primitive, before.2)

/-- Original source requests preserve the indexed KEM pool while executing the same complete record/public/reveal state transition. -/
noncomputable def sourceOld (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (RawCtxProtocolReveals.SourceSpec S B)
      (StateT (Live M P D A S B × PqxdhLiveKemBirth.State KemSK) ProbComp) := fun query before =>
  (fun result => (result.1, result.2, before.2)) <$>
    (PqxdhRegistrationProtocolState.sourceImpl source writer senderId route read query).run before.1

/-- The source comparison includes the same raw network schedules and private state, without exposing the interpreter to the public continuation. -/
noncomputable def sourceService (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) :
    QueryImpl (PqxdhPhase2LiveFinish.Spec S B)
      (StateT (Live M P D A S B × PqxdhLiveKemBirth.State KemSK) ProbComp)
  | .inl query => sourceOld source writer senderId route read query
  | .inr query => sourceFinish baseImpl primitives kem source callbacks read query


/-- Appending the new attempt log restores exactly the source pool already containing every earlier attempt. No previous observation is removed or replayed. -/
theorem restore_append (pool : PqxdhLiveKemBirth.Pool KemSK) (supplied : MlKemSharedSecret)
    (initial final : AuxState A) (earlier later : List (DecapsulationEvent Shared)) :
    (restorePrivate pool supplied (final, earlier ++ later)).2 =
      (restorePrivate (restorePrivate pool supplied (initial, earlier)).2.2 supplied (final, later)).2 := by
  simp only [restorePrivate, restore, restorePool, observations, List.map_append, List.append_assoc]

/-- Complete original state installation commutes with restoring the private source pool and cumulative optional attempt history. -/
theorem restored_install (pool : PqxdhLiveKemBirth.Pool KemSK) (supplied : MlKemSharedSecret)
    (selected : Nat) (target : MlKem768PublicKey) (index : Fin B) (before : State M P D A S B)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected))) ×
      (AuxState A × List (DecapsulationEvent Shared))) :
    restored pool supplied (install selected target index before result).2 =
      (PqxdhPhase2LiveFinish.install index before.1
        (PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2) result.2.1.1,
        (restorePrivate (restored pool supplied before).2.2 supplied result.2).2) := by
  exact Prod.ext rfl (restore_append pool supplied (before.1.primitive, before.2.1)
    result.2.1 before.2.2 result.2.2)


set_option backward.isDefEq.respectTransparency false in
/-- One actual indexed finish, including all prior decapsulation history and original whole-owner publication, equals its ordinary challenge-root interpretation. The executable finish requires no selected-secret argument; the mathematical source comparison supplies that secret to the primitive interpreter. Arbitrary input aliases are not excluded. -/
theorem finish_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (read : RawCtxReceive.FrameDecoder) (index : Fin B) (raw : Pqxdh.Bytes)
    (before : State M P D A S B)
    (valid : PqxdhLiveKemOwnership.Owner pool (before.1.roles.1.2 index)) :
    (fun result => (result.1, restored pool supplied result.2)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (actualImpl source kem secret challenge)
          ((finish primitives kem selected target (PqxdhLiveKemRouting.redact selected pool)
            source callbacks challenge read (.finish index raw)).run before)) =
      (sourceFinish baseImpl primitives kem source callbacks read (.finish index raw)).run
        (restored pool supplied before) := by
  have complete := privateOwner_source baseImpl primitives kem (restored pool supplied before).2.2
    selected target secret present source callbacks challenge supplied agreement read raw
    (before.1.roles.1.2 index) valid (before.1.primitive, before.2.1)
  rw [show PqxdhLiveKemRouting.redact selected (restored pool supplied before).2.2 =
    PqxdhLiveKemRouting.redact selected pool from rfl] at complete
  have published := congrArg (fun work =>
    (fun result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Identity D Handle) ×
        (PqxdhLivePhase2Aux.SharedState A × PqxdhLiveKemBirth.State KemSK) =>
      (result.1.1, PqxdhPhase2LiveFinish.install index before.1 result.1.2 result.2.1, result.2.2)) <$> work) complete
  simpa only [finish, sourceFinish, StateT.run, simulateQ_map, Functor.map_map,
    restored_install, install, restored, restorePrivate, restore,
    restorePool, observations, List.map_append, List.append_assoc, PqxdhPhase2LiveFinish.FinishSpec] using published


set_option backward.isDefEq.respectTransparency false in
/-- Original record/public/reveal execution keeps every optional reply and current native state after restoring the private pool. Real public HKDF and original raw operations are unchanged. -/
theorem old_source (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (secret : KemSK)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (before : State M P D A S B) :
    (fun result => (result.1, restored pool supplied result.2)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (actualImpl source kem secret challenge)
          ((old source writer senderId routeFrame read query).run before)) =
      (sourceOld source writer senderId routeFrame read query).run (restored pool supplied before) := by
  simp only [old, StateT.run]
  rw [← QueryImpl.simulateQ_compose (actualImpl source kem secret challenge) PqxdhBeaconPhase2Routed.publicLift,
    PqxdhBeaconPhase2Routed.publicLift_actual, evaluated_coins]
  simp only [sourceOld, Functor.map_map, restored, restorePrivate, restore]
  rfl


/-- The checked step comparison covers the actual original API request, including inactive finishes and every raw/public/reveal rejection. -/
theorem step_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (query : (PqxdhPhase2LiveFinish.Spec S B).Domain) (before : State M P D A S B)
    (valid : ∀ index, PqxdhLiveKemOwnership.Owner pool (before.1.roles.1.2 index)) :
    (fun result => (result.1, restored pool supplied result.2)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (actualImpl source kem secret challenge)
          ((service primitives kem selected target (PqxdhLiveKemRouting.redact selected pool)
            source callbacks writer senderId routeFrame read challenge query).run before)) =
      (sourceService baseImpl primitives kem source callbacks writer senderId routeFrame read query).run
        (restored pool supplied before) := by
  cases query with
  | inl query => exact old_source baseImpl kem pool secret source writer senderId routeFrame read challenge supplied query before
  | inr query =>
    cases query with
    | finish index raw =>
      exact finish_source baseImpl primitives kem pool selected target secret present
        source callbacks challenge supplied agreement read index raw before (valid index)


/-- Terminal native publication erases retained KEM material on both success and failure, independently of all cryptographic callback results. -/
theorem finish_owned {I K : Type} (predicate : K → Prop)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (owner : RawCtxBeaconLifecycle.State I D K)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    PqxdhPhase2KemProvenance.Phase predicate (PqxdhBeaconPhase2Publication.finish control owner staged).2.beacon.phase := by
  cases staged with
  | none => trivial
  | some staged => simp only [PqxdhBeaconPhase2Publication.finish]; split_ifs <;> trivial

/-- The literal source-shaped opaque owner preserves every predicate of its retained KEM handle, including actual indexed ownership, for all optional primitive replies. -/
theorem shared_owned {I K X : Type} (predicate : K → Prop)
    (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : RawCtxBeaconLifecycle.State I D K)
    (valid : PqxdhPhase2KemProvenance.Phase predicate owner.beacon.phase)
    (result : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D K)
    (supported : result ∈ support (PqxdhBeaconPhase2Shared.owner (X := X) (Response := Response) (Shared := Shared) read raw owner)) :
    PqxdhPhase2KemProvenance.Phase predicate result.2.beacon.phase := by
  cases active : owner.beacon.phase
  all_goals simp only [PqxdhBeaconPhase2Shared.owner, active, mem_support_pure_iff] at supported
  case initSent control prekey oneTime kem =>
    rw [mem_support_bind_iff] at supported
    obtain ⟨prepared, _, supported⟩ := supported
    cases reply : prepared with
    | none =>
      simp only [reply, mem_support_pure_iff] at supported
      subst result
      exact finish_owned predicate control owner none
    | some prepared =>
      simp only [reply, mem_support_bind_iff] at supported
      obtain ⟨staged, _, supported⟩ := supported
      obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
      exact finish_owned predicate control owner staged
  all_goals subst result; exact valid


/-- Changing only the private KEM handle representation transports exactly the predicate of that retained field. -/
theorem map_owned {I K L : Type} (predicate : L → Prop) (convert : K → L)
    (owner : RawCtxBeaconLifecycle.State I D K) :
    PqxdhPhase2KemProvenance.Phase predicate (PqxdhBeaconPhase1Publication.mapState id convert owner).beacon.phase =
      PqxdhPhase2KemProvenance.Phase (fun key => predicate (convert key)) owner.beacon.phase := by
  cases owner with
  | mk beacon attempts =>
    cases beacon with
    | mk identity keyId serverIdentity phase => cases phase <;> rfl

/-- Source-created retained handles remain owned after the literal private native attempt, independently of every opaque-root and optional primitive reply. -/
theorem private_owned (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (challenge : MlKem768Ciphertext) (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : RawCtxBeaconLifecycle.State Identity D Handle) (valid : PqxdhLiveKemOwnership.Owner pool owner)
    (state : AuxState A × List (DecapsulationEvent Shared))
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Identity D (Option (OtherHandle selected))) ×
      (AuxState A × List (DecapsulationEvent Shared)))
    (supported : result ∈ support (privateOwner primitives kem selected (PqxdhLiveKemRouting.redact selected pool)
      source callbacks challenge read raw (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner) state)) :
    PqxdhLiveKemOwnership.Owner pool (PqxdhBeaconPhase1Publication.mapState id (decode selected target) result.1.2) := by
  have original := support_simulateQ_run'_subset
    (logged selected (PqxdhBeaconPhase2Routed.handles source challenge
      (auxiliary primitives kem selected (PqxdhLiveKemRouting.redact selected pool) source callbacks)))
    (PqxdhBeaconPhase2Shared.owner read raw (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner)) state
  have pureSupport := original (show result.1 ∈ support ((simulateQ
      (logged selected (PqxdhBeaconPhase2Routed.handles source challenge
        (auxiliary primitives kem selected (PqxdhLiveKemRouting.redact selected pool) source callbacks)))
      (PqxdhBeaconPhase2Shared.owner read raw (PqxdhBeaconPhase1Publication.mapState id (encode selected) owner))).run' state) from by
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem _ supported)
  change PqxdhPhase2KemProvenance.Phase (PqxdhLiveKemRouting.Known pool) _
  rw [map_owned]
  apply shared_owned _ read raw _ _ result.1 pureSupport
  rw [← map_owned, owner_inverse pool selected target secret present owner valid]
  exact valid


/-- Record processing may evolve the established kernel but preserves the exact retained KEM field used by the ownership relation. -/
theorem retained_owned {I K : Type} (predicate : K → Prop)
    (before after : RawCtxBeaconLifecycle.State I D K)
    (valid : PqxdhPhase2KemProvenance.Phase predicate before.beacon.phase)
    (retained : RawCtxBeaconLifecycle.retained after = RawCtxBeaconLifecycle.retained before) :
    PqxdhPhase2KemProvenance.Phase predicate after.beacon.phase := by
  have same := congrArg (fun fields => fields.2.2.2) retained
  change RawCtxBeaconLifecycle.phaseFields after.beacon.phase = RawCtxBeaconLifecycle.phaseFields before.beacon.phase at same
  have fields (phase : RawCtxBeaconLifecycle.Phase D K beaconcrypt_core.ratchet.concrete.ConcreteRatchetKernel) :
      PqxdhPhase2KemProvenance.Phase predicate phase =
        PqxdhPhase2KemProvenance.Phase predicate (RawCtxBeaconLifecycle.phaseFields phase) := by
    cases phase <;> rfl
  rw [fields, same, ← fields]
  exact valid


/-- Every actual indexed record/public call preserves the retained handles of every Beacon, including inactive and failed receive branches. -/
theorem role_owned (pool : PqxdhLiveKemBirth.Pool KemSK)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (state : RawCtxProtocolRoles.State M P Identity D Handle S B × PqxdhLivePhase2Aux.SharedState A)
    (valid : ∀ position, PqxdhLiveKemOwnership.Owner pool (state.1.2 position))
    (result : (RawCtxProtocolRoles.SourceSpec S B).Range query ×
      (RawCtxProtocolRoles.State M P Identity D Handle S B × PqxdhLivePhase2Aux.SharedState A))
    (supported : result ∈ support ((RawCtxProtocolRoles.sourceImpl source writer S B senderId routeFrame read query).run state)) :
    ∀ position, PqxdhLiveKemOwnership.Owner pool (result.2.1.2 position) := by
  rcases query with server | (beacon | publicQuery)
  all_goals simp only [RawCtxProtocolRoles.sourceImpl, StateT.run, bind_pure_comp, support_map] at supported
  all_goals obtain ⟨original, originalSupport, rfl⟩ := supported
  case inr.inl =>
    simp only [RawCtxRoleFamily.sourceFamily, bind_pure_comp, support_map] at originalSupport
    obtain ⟨localResult, localSupport, rfl⟩ := originalSupport
    have preserved := RawCtxBeaconLifecycle.source_step _ read beacon.2 _ localResult localSupport
    have localValid := retained_owned (PqxdhLiveKemRouting.Known pool) _ localResult.2.1 (valid beacon.1) preserved.2
    intro position
    by_cases same : position = beacon.1
    · subst position
      simpa only [Function.update_self, PqxdhLiveKemOwnership.Owner] using localValid
    · simpa only [Function.update_of_ne same] using valid position
  all_goals exact valid


/-- The original record/public/current-chain/skipped-key API preserves actual indexed KEM ownership in every live Beacon field. -/
theorem original_owned (pool : PqxdhLiveKemBirth.Pool KemSK)
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Aeneas.Std.U64) (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain) (state : Live M P D A S B)
    (valid : ∀ position, PqxdhLiveKemOwnership.Owner pool (state.roles.1.2 position))
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query × Live M P D A S B)
    (supported : result ∈ support ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId routeFrame read query).run state)) :
    ∀ position, PqxdhLiveKemOwnership.Owner pool (result.2.roles.1.2 position) := by
  cases query with
  | inl request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, bind_pure_comp, support_map, Functor.map_map] at supported
    obtain ⟨original, originalSupport, rfl⟩ := supported
    exact role_owned pool source writer senderId routeFrame read request _ valid original originalSupport
  | inr request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact valid


/-- Interpretation can only choose replies from the original program's complete reply support. -/
theorem support_interpretation {κ μ Result : Type} {input : OracleSpec κ} {output : OracleSpec μ}
    (impl : QueryImpl input (OracleComp output)) (work : OracleComp input Result) :
    support (simulateQ impl work) ⊆ support work := by
  have kept := support_simulateQ_run'_subset (impl.liftTarget (StateT Unit (OracleComp output))) work ()
  simpa [simulateQ_liftTarget, StateT.run'_eq, liftM_run_StateT] using kept

set_option backward.isDefEq.respectTransparency false in
/-- Every concrete private compiled request preserves the ownership supplied by actual indexed creation. This is an operational invariant, not an authentication or freshness premise. -/
theorem step_owned (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext)
    (query : (PqxdhPhase2LiveFinish.Spec S B).Domain) (before : State M P D A S B)
    (valid : ∀ index, PqxdhLiveKemOwnership.Owner pool (before.1.roles.1.2 index))
    (result : (PqxdhPhase2LiveFinish.Spec S B).Range query × State M P D A S B)
    (supported : result ∈ support ((service primitives kem selected target (PqxdhLiveKemRouting.redact selected pool)
      source callbacks writer senderId routeFrame read challenge query).run before)) :
    ∀ index, PqxdhLiveKemOwnership.Owner pool (result.2.1.roles.1.2 index) := by
  cases query with
  | inl query =>
    have original := support_interpretation _ _ supported
    have coins := support_interpretation _ _ original
    rw [support_map] at coins
    obtain ⟨actual, actualSupport, rfl⟩ := coins
    exact original_owned pool source writer senderId routeFrame read query before.1 valid actual actualSupport
  | inr query =>
    cases query with
    | finish index raw =>
      simp only [service, finish, StateT.run, support_map] at supported
      obtain ⟨actual, actualSupport, rfl⟩ := supported
      have changed := private_owned primitives kem pool selected target secret present source callbacks challenge
        read raw (before.1.roles.1.2 index) (valid index) _ actual actualSupport
      intro other
      by_cases same : other = index
      · subst other
        simpa only [install, PqxdhPhase2LiveFinish.install, Function.update_self] using changed
      · simpa only [install, PqxdhPhase2LiveFinish.install, Function.update_of_ne same] using valid other


/-- Mathematical real-source evaluation is the original ambient primitive interpretation and the actual private challenge-root interpreter. -/
noncomputable def evaluation (source : FixedHkdfSha512NoSaltSource) (baseImpl : QueryImpl baseSpec ProbComp)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (secret : KemSK) (challenge : MlKem768Ciphertext) :=
  PqxdhInitializerSecrecy.kemAmbientImpl baseImpl ∘ₛ actualImpl source kem secret challenge

set_option backward.isDefEq.respectTransparency false in
/-- The entire adaptive original record/public/reveal/finish schedule has the same optional replies, complete live owners, shared cache, joint state and ordered KEM history. Initial indexed ownership is preserved by the concrete source program itself. -/
theorem schedule_source {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result) (before : State M P D A S B)
    (valid : ∀ index, PqxdhLiveKemOwnership.Owner pool (before.1.roles.1.2 index)) :
    (fun result => (result.1, restored pool supplied result.2)) <$>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
        (simulateQ (actualImpl source kem secret challenge)
          ((simulateQ (service primitives kem selected target (PqxdhLiveKemRouting.redact selected pool)
            source callbacks writer senderId routeFrame read challenge) client).run before)) =
      (simulateQ (sourceService baseImpl primitives kem source callbacks writer senderId routeFrame read) client).run
        (restored pool supplied before) := by
  have complete := map_run_simulateQ_eq_of_query_map_eq_inv'
    ((evaluation source baseImpl kem secret challenge).mapStateTBase
      (service primitives kem selected target (PqxdhLiveKemRouting.redact selected pool)
        source callbacks writer senderId routeFrame read challenge))
    (sourceService baseImpl primitives kem source callbacks writer senderId routeFrame read)
    (fun state => ∀ index, PqxdhLiveKemOwnership.Owner pool (state.1.roles.1.2 index))
    (restored pool supplied)
    (by
      intro query state owned result supported
      exact step_owned primitives kem pool selected target secret present source callbacks writer senderId
        routeFrame read challenge query state owned result (support_interpretation _ _ supported))
    (by
      intro query state owned
      simpa only [QueryImpl.mapStateTBase, StateT.run, StateT.mk, evaluation, QueryImpl.simulateQ_compose, Prod.map_def, id_eq] using
        step_source baseImpl primitives kem pool selected target secret present source callbacks writer senderId
          routeFrame read challenge supplied agreement query state owned) client before valid
  simpa only [← QueryImpl.simulateQ_mapStateTBase_run, evaluation, QueryImpl.simulateQ_compose, Prod.map_def, id_eq] using complete


/-- The actual public continuation sees only original API replies and its own final decision; all role, joint and private attempt state stays in this executable wrapper. No selected-secret or candidate argument is required. -/
noncomputable def post {Result : Type} (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat) (target : MlKem768PublicKey)
    (keys : PrivateKeys KemSK) (source : FixedHkdfSha512NoSaltSource)
    (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder) (challenge : MlKem768Ciphertext)
    (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result) (before : State M P D A S B) :=
  Prod.fst <$> (simulateQ (service primitives kem selected target keys source callbacks writer senderId routeFrame read challenge)
    client).run before

/-- The actual public source continuation is simulated by ordinary blocked one-key CCA calls and private use of the one supplied shared secret. The original adaptive client supplies the final observation. -/
theorem post_source {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (agreement : kem.decaps secret challenge = pure (some supplied))
    (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result) (before : State M P D A S B)
    (valid : ∀ index, PqxdhLiveKemOwnership.Owner pool (before.1.roles.1.2 index)) :
    Prod.fst <$> (simulateQ (sourceService baseImpl primitives kem source callbacks writer senderId routeFrame read) client).run
      (restored pool supplied before) =
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (publicImpl kem secret challenge) (simulateQ (route source challenge supplied)
        (post primitives kem selected target (PqxdhLiveKemRouting.redact selected pool) source callbacks
          writer senderId routeFrame read challenge client before))) := by
  have complete := congrArg (Functor.map Prod.fst)
    (schedule_source baseImpl primitives kem pool selected target secret present source callbacks writer senderId
      routeFrame read challenge supplied agreement client before valid)
  simp only [Functor.map_map] at complete
  simpa only [route_complete source kem secret challenge supplied agreement, post, simulateQ_map] using complete.symm

/-- Ordinary functional recipient correctness on actual generation and encapsulation support supplies the exact private routing agreement for the complete original public continuation. -/
theorem supported_post {Result : Type} (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (functional : FunctionalDecapsulation kem)
    (correct : MlKem768RecipientCorrectness kem
      (PqxdhInitializerSecrecy.runtimeOfImpl (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)))
    (pool : PqxdhLiveKemBirth.Pool KemSK) (selected : Nat) (target : MlKem768PublicKey) (secret : KemSK)
    (present : pool.keys[selected]? = some (target, secret))
    (source : FixedHkdfSha512NoSaltSource) (callbacks : QueryImpl (LocalSpec D Response) (StateT A ProbComp))
    (writer : RawCtxMixedShared.Writer) (senderId : M → Aeneas.Std.U64)
    (routeFrame : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)
    (challenge : MlKem768Ciphertext) (supplied : MlKemSharedSecret)
    (generated : (target, secret) ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) kem.keygen))
    (encapsulated : (challenge, supplied) ∈ support
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl) (kem.encaps target)))
    (client : OracleComp (PqxdhPhase2LiveFinish.Spec S B) Result) (before : State M P D A S B)
    (valid : ∀ index, PqxdhLiveKemOwnership.Owner pool (before.1.roles.1.2 index)) :
    Prod.fst <$> (simulateQ (sourceService baseImpl primitives kem source callbacks writer senderId routeFrame read) client).run
      (restored pool supplied before) =
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl baseImpl)
      (simulateQ (publicImpl kem secret challenge) (simulateQ (route source challenge supplied)
        (post primitives kem selected target (PqxdhLiveKemRouting.redact selected pool) source callbacks
          writer senderId routeFrame read challenge client before))) :=
  post_source baseImpl primitives kem pool selected target secret present source callbacks writer senderId routeFrame read
    challenge supplied (honest_decapsulation_program baseImpl kem functional correct generated encapsulated) client before valid

end BeaconcryptCore.Computational.PqxdhLivePrivateFinish

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.restore_append' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.restore_append
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.restored_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.restored_install
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.finish_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.old_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.old_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.step_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.step_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.finish_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.finish_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.shared_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.shared_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.map_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.map_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.private_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.private_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.retained_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.retained_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.role_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.role_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.original_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.original_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.support_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.support_interpretation
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.step_owned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.step_owned
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.schedule_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.schedule_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.post_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.post_source
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePrivateFinish.supported_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePrivateFinish.supported_post

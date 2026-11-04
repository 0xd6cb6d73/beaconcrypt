-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxCompletion
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxBirthdayBudget
import BeaconcryptCore.Computational.RegistrationNativePlatformQueryBounds
/-! Literal physical CTX leaf bounds preserve native and external coin trees. Both Env hashing and ordinary native commitment hashing count their actual shared backend request; unrelated primitive work contributes zero CTX requests. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativePlatformCtxBackend (Spec)
open RegistrationNativePlatformCtxBirthdayBudget (IsHash)
open RegistrationNativePlatformCtxRunner (M)
variable {n : Nat} {I KemSK Reader Response Auxiliary Platform E Local A B : Type} {base : OracleSpec I}

def Bounded (work : M Local Platform A) (cap : Nat) : Prop :=
  ∀ before previous, ((work.run before).run previous).IsQueryBoundP IsHash cap

theorem coins (work : ProbComp A) :
    (simulateQ RegistrationNativePlatformCtxBackend.coin work).IsQueryBoundP IsHash 0 := by
  apply (isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
  intro query _
  simp only [RegistrationNativePlatformCtxBackend.coin, isQueryBoundP_query_iff, IsHash]
  exact fun impossible => impossible.elim

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) : (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Public platform randomness never produces a shared hash request or changes private state. -/
theorem public_work (work : StateT Platform ProbComp A) :
    Bounded (RegistrationNativePlatformCtxRunner.publicWork (Local := Local) work) 0 := by
  intro before previous
  simp only [RegistrationNativePlatformCtxRunner.publicWork, StateT.run, isQueryBoundP_map_iff]
  exact coins _

theorem private_work (work : StateT Local (OracleComp Spec) A) (cap : Nat)
    (bounded : ∀ before, (work.run before).IsQueryBoundP IsHash cap) :
    Bounded (Platform := Platform) (RegistrationNativePlatformCtxRunner.privateWork work) cap := by
  intro before previous
  change (do let result ← work.run before; pure (result, previous)).IsQueryBoundP IsHash cap
  simpa only [bind_pure_comp, isQueryBoundP_map_iff] using bounded before

private theorem pure_bound (value : A) (cap : Nat) : Bounded (pure value : M Local Platform A) cap := by
  intro before previous
  simp only [StateT.run_pure, isQueryBoundP_pure]

private theorem bind_bound (work : M Local Platform A) (next : A → M Local Platform B)
    (first later : Nat) (bounded : Bounded work first) (rest : ∀ value, Bounded (next value) later) :
    Bounded (work >>= next) (first + later) := by
  intro before previous
  rw [StateT.run_bind, StateT.run_bind]
  exact isQueryBoundP_bind (bounded before previous) (fun result _ => rest result.1.1 result.1.2 result.2)

/-- Every physical Env request has at most its one literal CTX call, independently of returned digest and draw receipt. -/
theorem effects (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformCtxLocal.effects query).run before).IsQueryBoundP IsHash 1 := by
  cases query with
  | inl coin =>
    simp only [RegistrationNativePlatformCtxLocal.effects, RegistrationNativePlatformCtxEffects.program,
      StateT.run, isQueryBoundP_map_iff]
    exact (coins _).mono (by decide)
  | inr query => cases query <;> first
    | simp only [RegistrationNativePlatformCtxLocal.effects, RegistrationNativePlatformCtxEffects.program,
        StateT.run, RegistrationNativePlatformCtxBackend.hash, isQueryBoundP_map_iff,
        isQueryBoundP_query_bind_iff, IsHash, ite_true]
      exact ⟨by decide, fun _ => by trivial⟩
    | simp only [RegistrationNativePlatformCtxLocal.effects, RegistrationNativePlatformCtxEffects.program,
        StateT.run, isQueryBoundP_map_iff]
      exact (coins _).mono (by decide)

/-- Every actual native record primitive has at most one backend CTX request; the hashing branch includes its exact native counter update. -/
theorem primitive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformCtxLocal.record setup codec query).run before).IsQueryBoundP IsHash 1 := by
  rcases query with request | input | opening | bytes | frame
  all_goals first
    | simp only [RegistrationNativePlatformCtxLocal.record, RegistrationNativePlatformCtxPrimitives.program,
        StateT.run, isQueryBoundP_map_iff]
      exact (coins _).mono (by decide)
    | simp only [RegistrationNativePlatformCtxLocal.record, RegistrationNativePlatformCtxPrimitives.program,
        StateT.run, RegistrationNativePlatformCtxBackend.hash, isQueryBoundP_map_iff,
        isQueryBoundP_query_bind_iff, IsHash, ite_true]
      exact ⟨by decide, fun _ => by trivial⟩

private theorem shared (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : MldsaSharedNative.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformCtxLocal.shared setup codec query).run before).IsQueryBoundP IsHash 1 := by
  cases query with
  | inl query => exact effects (.inr (.hash query.2)) before
  | inr query => exact primitive setup codec query before

private theorem callbacks (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RegistrationRecordPrimitives.Spec.Domain) :
    (RegistrationRecordPrimitives.callbacks source query).IsTotalQueryBound 1 := by
  cases query with
  | rootKdf request | initialKdf request => trivial
  | ratchetKdf request | «seal» request | openAead request =>
    simp only [RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift]
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨by decide, fun _ => by trivial⟩
  | hash transcript =>
    simp only [RegistrationRecordPrimitives.callbacks, RegistrationAuthenticationShared.callbacks, MldsaSharedNative.authLift]
    rw [isTotalQueryBound_query_bind_iff]
    exact ⟨by decide, fun _ => by trivial⟩
  | write request => cases request with
    | Raw parts => trivial
    | Frame parts sequence sender =>
      simp only [RegistrationRecordPrimitives.callbacks, MldsaSharedNative.recordLift]
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨by decide, fun _ => by trivial⟩

/-- The actual source record adapter contributes at most one physical CTX request, including every optional failure. -/
theorem records (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RegistrationRecordPrimitives.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformCtxLocal.records setup codec query).run before).IsQueryBoundP IsHash 1 := by
  simp only [RegistrationNativePlatformCtxLocal.records, StateT.run, isQueryBoundP_map_iff]
  apply ((isQueryBoundP_true_iff _ _).mpr (callbacks setup.source query)).simulateQ_run_of_step
  · intro request _ current
    exact shared setup codec request current
  · intro request impossible
    exact (impossible trivial).elim

/-- Source signing and its explicit hash request each use at most one physical CTX call; sampler coins stay separate. -/
theorem outgoing (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationSigningShared.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformCtxSigning.outgoing sign query).run before).IsQueryBoundP IsHash 1 := by
  cases query with
  | hash request => exact effects _ before
  | sign request payload digest =>
    simp only [RegistrationNativePlatformCtxSigning.outgoing, StateT.run, isQueryBoundP_map_iff]
    exact (coins _).mono (by decide)
section Seal
variable [sealPrimitive : AdapterSealPrimitive.Operations]

/-- Actual source AEAD work never calls the shared CTX oracle; its private sampler remains explicit. -/
theorem aead (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealPrimitive.Error)
    (plaintext : Slice U8) (associated : core.option.Option (Slice U8))
    (nonce : sealPrimitive.Nonce) (key : sealPrimitive.Key)
    (before : RegistrationWorldAgreement.State n Auxiliary) :
    ((RegistrationNativePlatformCtxSeal.aead setup codec view failure plaintext associated nonce key).run before).IsQueryBoundP IsHash 0 := by
  simp only [RegistrationNativePlatformCtxSeal.aead, RegistrationNativePlatformCtxLocal.record,
    RegistrationNativePlatformCtxPrimitives.program, StateT.run, isQueryBoundP_map_iff]
  exact coins _

private theorem seal_handler (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (query : (AdapterSealNative.Spec E).Domain) :
    Bounded (RegistrationNativePlatformCtxSeal.handler (n := n) (Auxiliary := Auxiliary) setup codec view failure allocation query) 0 := by
  cases query with
  | reserve buffer capacity => exact public_work _
  | aead plaintext associated nonce key =>
    exact private_work _ 0 (aead setup codec view failure plaintext associated nonce key)

/-- Prefix reservation, detached sealing and the source request marker contribute zero CTX calls on all source outcomes. -/
theorem sealing (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : sealPrimitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (request : record_effects.AeadSealRequest) :
    Bounded (RegistrationNativePlatformCtxSeal.sealing (n := n) (Auxiliary := Auxiliary) setup codec view failure allocation request) 0 := by
  unfold RegistrationNativePlatformCtxSeal.sealing
  apply bind_bound _ _ 0 0
  · intro before previous
    apply RegistrationNativePlatformQueryBounds.simulate_bound (fun _ => False) IsHash _ _ _ 0 (isQueryBoundP_false _ 0) before previous
    intro query current prior
    exact seal_handler setup codec view failure allocation query current prior
  · intro result before previous
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, isQueryBoundP_pure]
end Seal

/-- Mutable commitment hashing retains its enclosing RustM reply and contributes one physical CTX call. -/
theorem hash (setup : Setup base KemSK) (codec : Codec Reader Response)
    (erased transcript : commitment.CommitmentTranscript) :
    Bounded (RegistrationNativePlatformCtxSeal.hash (n := n) (Auxiliary := Auxiliary) setup codec erased transcript : M _ Platform _) 1 := by
  apply private_work
  intro before
  simp only [bind_pure_comp]
  exact records setup codec (.hash transcript) before

/-- Raw source writing keeps all allocator/serializer and RustM outcomes while calling no CTX oracle. -/
theorem write (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (request : record_effects.RecordWriteRequest) :
    Bounded (RegistrationNativePlatformCtxWriters.write (n := n) (Auxiliary := Auxiliary) helper request) 0 := by
  intro before previous
  simp only [RegistrationNativePlatformCtxWriters.write, StateT.run, isQueryBoundP_map_iff]
  exact coins _

/-- The actual response serializer contributes no shared CTX query. -/
theorem encode (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (view : registration.SignedResponseView) :
    Bounded (RegistrationNativePlatformCtxWriters.encode (n := n) (Auxiliary := Auxiliary) writer view) 0 :=
  public_work _

end BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.coins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.private_work' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.private_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.public_work' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.public_work

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.effects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.primitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.records

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.outgoing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.outgoing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.aead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.aead

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.sealing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.hash

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.write' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.write

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.encode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxLeafHashBounds.encode

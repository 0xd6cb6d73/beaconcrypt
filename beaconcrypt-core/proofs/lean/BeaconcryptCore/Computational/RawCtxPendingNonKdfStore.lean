import BeaconcryptCore.Computational.RawCtxPendingSelectiveFamily
import BeaconcryptCore.Computational.RawCtxSelectiveChainDepth

/-!
The actual enriched family prefix retains its full private KDF table and cursor through every non-KDF callback. Opening and sealing keep all their original shared commitment, AEAD, writer and optional rejection effects; public HKDF remains real; live reads return their original optional value. No fresh-miss or cache-consistency premise is required. This exact full-Store invariant supports the chronological predecessor scan, including cached predecessor requests, rather than treating a zero sampling cost as absence of state effects.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingNonKdfStore
open PqxdhJointKdfGame RawCtxSelectiveChainGame

/-- The exact inner opening program never invokes a ratchet KDF. -/
theorem open_zero (input : RawCtxWholeOwner.OpenInput) :
    (RawCtxMixedOwner.receiveAdapter (.inr input)).IsQueryBoundP (fun query => query.isLeft = true) 0 := by
  change (simulateQ RawCtxMixedOwner.receiveLift
    (simulateQ RawCtxSourceOpen.openLift (RawCtxSourceOpen.openInput input))).IsQueryBoundP _ 0
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp only [QueryImpl.apply_compose, RawCtxSourceOpen.openLift]
  all_goals exact (isQueryBoundP_query_iff _ _ _).mpr (by simp)

/-- The exact inner sealing program never invokes a ratchet KDF. -/
theorem seal_zero (input : RawCtxSourceSend.SealInput) :
    (RawCtxMixedOwner.sendAdapter (.inr input)).IsQueryBoundP (fun query => query.isLeft = true) 0 := by
  change (simulateQ RawCtxMixedOwner.sendLift
    (simulateQ RawCtxSourceSeal.sealLift (RawCtxSourceSeal.sealInput input))).IsQueryBoundP _ 0
  rw [← QueryImpl.simulateQ_compose]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  rcases query with aead | (hash | writer)
  all_goals simp only [QueryImpl.apply_compose, RawCtxSourceSeal.sealLift]
  all_goals exact (isQueryBoundP_query_iff _ _ _).mpr (by simp)

/-- The actual optional opening adapter has no private derivation in either its missing-material or executed branch. -/
theorem receive_zero (pending : ReceiveOpen RawCtxWholeOwner.OpenContext) :
    (simulateQ RawCtxMixedOwner.receiveAdapter (RawCtxWholeOwner.adapter (.inr pending))).IsQueryBoundP
      (fun query => query.isLeft = true) 0 := by
  simp only [RawCtxWholeOwner.adapter]
  split
  · simp
  · simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, isQueryBoundP_map_iff]
    exact open_zero _

/-- Sealing forwards only its actual AEAD, commitment and writer calls after the source material was already derived. -/
theorem send_zero (pending : SendSeal RawCtxSourceSend.SealContext) :
    (simulateQ RawCtxMixedOwner.sendAdapter (RawCtxSourceSend.adapter (.inr pending))).IsQueryBoundP
      (fun query => query.isLeft = true) 0 := by
  simp only [RawCtxSourceSend.adapter, bind_pure_comp, simulateQ_map, simulateQ_spec_query, isQueryBoundP_map_iff]
  exact seal_zero _

/-- Every non-KDF native primitive retains the entire private table and cursor while executing its original shared-state effect. -/
theorem native_other {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (RawCtxMixedOwner.SealAeadSpec + (RawCtxMixedOwner.OpenAeadSpec + (RawCtxMixedOwner.HashSpec + RawCtxMixedOwner.WriterSpec))).Domain)
    (state : RawCtxPendingSelectiveFamily.State Auxiliary) :
    (((RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift) (.inr query)).run state) =
      (fun result => (result.1, (result.2, state.2))) <$>
        ((RawCtxProtocolBackend.backend source writer (.inr (.inl (.inr query)))).run state.1) := by
  simp [RawCtxPendingSelectiveFamily.backend, QueryImpl.compose, RawCtxServerServices.nativeLift,
    RawCtxSelectiveKdfFamily.compiler, handler, OracleSpec.query, StateT.run]

set_option backward.isDefEq.respectTransparency false in
/-- A complete native program with no private derivation preserves the original full table and cursor under every supported primitive reply. -/
theorem native_store {Auxiliary Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (client : OracleComp RawCtxMixedOwner.NativeSpec Result)
    (bounded : client.IsQueryBoundP (fun query => query.isLeft = true) 0)
    (state : RawCtxPendingSelectiveFamily.State Auxiliary)
    (result : Result × RawCtxPendingSelectiveFamily.State Auxiliary)
    (supported : result ∈ support ((simulateQ
      (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift) client).run state)) :
    result.2.2 = state.2 := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simpa only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] using congrArg (fun pair => pair.2.2) (by exact supported : result = (value, state))
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      cases query with
      | inl request => simpa using bounded.1
      | inr query =>
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨reply, head, tail⟩ := supported
          rw [native_other] at head
          simp only [support_map, Set.mem_image] at head
          obtain ⟨primitive, _, rfl⟩ := head
          exact ih primitive.1 (bounded.2 primitive.1) (primitive.2, state.2) result tail

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual opening callback preserves the private table and cursor, including missing material and rejected opening. -/
theorem receive_store {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (opening : RawCtxInterpretedOpening.Opening RatchetChain RatchetChain RatchetMaterial RawCtxWholeOwner.OpenContext)
    (state : RawCtxPendingSelectiveFamily.State Auxiliary)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxPendingSelectiveFamily.State Auxiliary)
    (supported : result ∈ support ((RawCtxPendingNativeCalls.receive
      (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift) (.inr opening)).run state)) :
    result.2.2 = state.2 := by
  simp only [RawCtxPendingNativeCalls.receive, QueryImpl.apply_compose, RawCtxInterpretedReceive.nativeAdapter,
    _root_.simulateQ_spec_query, QueryImpl.simulateQ_compose] at supported
  apply native_store source writer stage _ (receive_zero (RawCtxInterpretedOpening.toNative opening)) state result
  simpa only [QueryImpl.simulateQ_compose] using supported

set_option backward.isDefEq.respectTransparency false in
/-- The complete actual sealing callback preserves the private table and cursor through optional AEAD and writer failure. -/
theorem send_store {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (sealing : RawCtxInterpretedSend.Seal RatchetMaterial RawCtxSourceSend.SealContext)
    (state : RawCtxPendingSelectiveFamily.State Auxiliary)
    (result : Option RawCtxSourceSend.Encrypted × RawCtxPendingSelectiveFamily.State Auxiliary)
    (supported : result ∈ support ((RawCtxPendingNativeCalls.send
      (RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.nativeLift) (.inr sealing)).run state)) :
    result.2.2 = state.2 := by
  simp only [RawCtxPendingNativeCalls.send, QueryImpl.apply_compose, RawCtxInterpretedSend.nativeAdapter,
    _root_.simulateQ_spec_query, QueryImpl.simulateQ_compose] at supported
  apply native_store source writer stage _ (send_zero (RawCtxInterpretedSend.nativeSeal sealing)) state result
  simpa only [QueryImpl.simulateQ_compose] using supported

/-- Every public service retains the entire private KDF table and cursor; its original shared backend still executes. -/
theorem public_other {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : RawCtxServerServices.PublicSpec.Domain) (state : RawCtxPendingSelectiveFamily.State Auxiliary) :
    (((RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift) query).run state) =
      (fun result => (result.1, (result.2, state.2))) <$>
        (((RawCtxProtocolBackend.backend source writer ∘ₛ RawCtxServerServices.publicLift) query).run state.1) := by
  rcases query with coin | (hash | hkdf)
  all_goals simp [RawCtxPendingSelectiveFamily.backend, QueryImpl.compose, RawCtxServerServices.publicLift,
    RawCtxSelectiveKdfFamily.compiler, handler, OracleSpec.query, StateT.run]

/-- Every supported public reply preserves the private table and cursor, including real HKDF and commitment-cache effects. -/
theorem public_store {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : RawCtxServerServices.PublicSpec.Domain) (state : RawCtxPendingSelectiveFamily.State Auxiliary)
    (result : RawCtxServerServices.PublicSpec.Range query × RawCtxPendingSelectiveFamily.State Auxiliary)
    (supported : result ∈ support (((RawCtxPendingSelectiveFamily.backend source writer stage ∘ₛ RawCtxServerServices.publicLift) query).run state)) :
    result.2.2 = state.2 := by
  rw [public_other] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every supported original non-KDF pending callback preserves the complete private table and cursor, including raw opening, sealing, public services and optional live reads. -/
theorem callback_store {Auxiliary : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
    (query : (RawCtxPendingSelectiveFamily.Spec serverCount beaconCount).Domain)
    (notKdf : RawCtxSelectedFamilyContext.queryAddress query = none)
    (state : RawCtxPendingSelectiveFamily.State Auxiliary)
    (result : (RawCtxPendingSelectiveFamily.Spec serverCount beaconCount).Range query × RawCtxPendingSelectiveFamily.State Auxiliary)
    (supported : result ∈ support ((RawCtxPendingSelectiveFamily.handler source writer stage query).run state)) :
    result.2.2 = state.2 := by
  cases query with
  | inr read =>
      simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
        RawCtxPendingFamilyLiveQueries.handler, RawCtxGenericFamilyRead.nativeReader, StateT.run_pure,
        mem_support_pure_iff] at supported
      exact congrArg (fun pair => pair.2.2) supported
  | inl query =>
      rcases query with (request | opening) | ((request | sealing) | publicQuery)
      · cases notKdf
      · simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
          RawCtxPendingFamilyLiveQueries.handler, RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose,
          RawCtxPendingOwnerQueries.erase, _root_.simulateQ_spec_query, RawCtxPendingNativeCalls.original] at supported
        exact receive_store source writer stage _ state result supported
      · cases notKdf
      · simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
          RawCtxPendingFamilyLiveQueries.handler, RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose,
          RawCtxPendingOwnerQueries.erase, _root_.simulateQ_spec_query, RawCtxPendingNativeCalls.original] at supported
        exact send_store source writer stage _ state result supported
      · simp only [RawCtxPendingSelectiveFamily.handler, RawCtxPendingFamilyNative.handler,
          RawCtxPendingFamilyLiveQueries.handler, RawCtxPendingNativeCalls.pending, QueryImpl.apply_compose,
          RawCtxPendingOwnerQueries.erase, _root_.simulateQ_spec_query, RawCtxPendingNativeCalls.original] at supported
        exact public_store source writer stage publicQuery state result supported

end BeaconcryptCore.Computational.RawCtxPendingNonKdfStore

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.open_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.open_zero
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.seal_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.seal_zero
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.receive_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.receive_zero
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.send_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.send_zero
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.native_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.native_other
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.native_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.native_store
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.receive_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.receive_store
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.send_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.send_store
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.public_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.public_other
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.public_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.public_store
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.callback_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNonKdfStore.callback_store

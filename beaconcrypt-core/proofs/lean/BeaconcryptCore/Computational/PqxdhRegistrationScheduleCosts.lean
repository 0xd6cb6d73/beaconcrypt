-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleSurface
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceServices

/-! Explicit source construction and callback bills retain primitive randomness and interpreted base work. Counts measure oracle calls; deterministic validation, indexing, serialization and bookkeeping remain actual local computations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhServerAuthSourceCosts
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A Result : Type}

/-- The actual post-admission constructor spends two 32-byte draws plus the entire declared KEM generation and base-interpreter bill. No future owner's draws are reserved. -/
theorem create_uniform (setup : Setup baseSpec KemSK) (caps : KemCaps) (bounded : KemBound setup caps)
    (pin : Word32) (keyId : Std.U64) (state : State KemSK) :
    ((create setup pin keyId).run state).IsTotalQueryBound (64 + caps.keygenCost) := by
  change (create setup pin keyId state).IsTotalQueryBound _
  rw [create_source]
  apply (isTotalQueryBound_bind sampleSeed_uniform_bound (n₂ := 32 + caps.keygenCost) ?_).mono (by omega)
  intro identity
  apply isTotalQueryBound_bind sampleScalar_uniform
  intro prekey
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    keygen_uniform setup caps bounded

/-- Runtime initialization is charged on every raw creation attempt, including wrong-width pins; accepted creation then pays both native 32-byte generators and all KEM/base work. -/
theorem rawCreate_uniform (setup : Setup baseSpec KemSK) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool)
    (qInit : Nat) (initBound : ∀ runtime, (ensureInit.run runtime).IsTotalQueryBound qInit)
    (bytes : Pqxdh.Bytes) (keyId : Std.U64) (state : A × State KemSK) :
    ((rawCreate setup checks ensureInit bytes keyId).run state).IsTotalQueryBound
      (qInit + 64 + caps.keygenCost) := by
  simp only [rawCreate, StateT.run]
  apply (isTotalQueryBound_bind (initBound state.1) (n₂ := 64 + caps.keygenCost) ?_).mono (by omega)
  rintro ⟨ready, runtime⟩
  cases ready <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · trivial
  · cases parsed : parsePin checks bytes
    · trivial
    · simpa only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
        create_uniform setup caps bounded _ keyId state.2

/-- The literal source root consumes at most one 64-byte Extract-table draw; real Expand and complete existing tables/state remain in the same program. -/
theorem sourceRoot_uniform (hmac : PqxdhSecretInputKdf.HmacSha512) (input : pqxdh.RootKeyInput)
    (state : NativeState KemSK) :
    ((sourceRoot hmac input).run state).IsTotalQueryBound 64 := by
  simpa only [sourceRoot, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    PqxdhServerAuthEntryFactor.extract_table_uniform (absBytes input.bytes) state.1.cache

/-- Every actual preparation callback retains its complete optional decapsulation bill. Parsing, DH, conversion and getters are the original deterministic primitive/source contracts. -/
theorem preparation_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (PqxdhBeaconPhase2Preparation.Spec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain) :
    (preparation setup codec query).IsTotalQueryBound caps.decapsCost := by
  cases query <;> try trivial
  exact decaps_uniform setup caps bounded _ _

/-- Every actual native tail callback pays the reached shared hash or Extract-table sample. Real ratchet HKDF, AEAD opening, initializer and optional getter work stay in the source program. -/
theorem tail_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) (state : NativeState KemSK) :
    ((sourceBeaconTail setup codec query).run state).IsTotalQueryBound 64 := by
  rcases query with query | (input | request | response)
  · simp only [sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot, beaconNative, nativeCtx,
      StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
    simpa only [StateT.run, IsTotalQueryBound] using
      (RawCtxSharedPrimitive.native_uniform_step setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source)
        0 (RawCtxSourceHkdf.kdf_uniform setup.source) query ((), state.2.ctx)).mono
        (show (if query.isLeft then 0 else if RawCtxSourceOpen.openingPredicate Sum.isLeft query then 64 else 0) ≤ 64 by
          split_ifs <;> omega)
  · exact sourceRoot_uniform setup.hmac input state
  · trivial
  · trivial

/-- The concrete callback family charges all optional KEM/base work and both shared primitive tables; no unspecified ambient callback is assigned a zero allowance. -/
theorem callbacks_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain)
    (state : NativeState KemSK) :
    ((callbacks setup codec query).run state).IsTotalQueryBound (max 64 caps.decapsCost) := by
  rcases query with query | query
  · simpa only [callbacks, nativeCoins, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
      (preparation_uniform setup codec caps bounded query).mono (Nat.le_max_right 64 caps.decapsCost)
  · exact (tail_uniform setup codec query state).mono (Nat.le_max_left 64 caps.decapsCost)

/-- The full literal owner attempt charges all 69 possible callbacks, including preparation and opening work before final sequence/binding rejection. This conservative bound retains complete source and cache state. -/
theorem owner_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps) (raw : Pqxdh.Bytes)
    (owner : Owner KemSK) (state : NativeState KemSK) :
    ((simulateQ (callbacks setup codec) (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state).IsTotalQueryBound (69 * max 64 caps.decapsCost) := by
  exact (isQueryBoundP_true_iff _ _).mp
    (PqxdhBeaconPhase2Bounds.native_interpreted_bound (callbacks setup codec) (fun _ => True)
      (max 64 caps.decapsCost) (fun query current => (callbacks_uniform setup codec caps bounded query current).isQueryBoundP)
      codec.frameRead raw owner state)

/-- Every public finish attempt retains the complete owner bill; missing or future slots are ordinary zero-draw rejection branches. Reinstallation adds no oracle query and preserves all previous effects. -/
theorem finish_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (caps : KemCaps) (bounded : KemBound setup caps) (index : Nat) (raw : Pqxdh.Bytes)
    (state : State KemSK) :
    ((finish setup codec index raw).run state).IsTotalQueryBound (69 * max 64 caps.decapsCost) := by
  cases found : state.owners[index]? with
  | none =>
      rw [finish_missing setup codec index raw state found]
      trivial
  | some owner =>
      simpa only [StateT.run, finish_source setup codec index raw state owner found,
        IsTotalQueryBound, isQueryBound_map_iff] using
        owner_uniform setup codec caps bounded raw owner state.shared

set_option backward.isDefEq.respectTransparency false in
/-- After the optional one-time draw, the actual three signatures and optional writer retain all source work without issuing a uniform-oracle call. This is a functional primitive/query-interface fact, not zero runtime. -/
theorem bundle_after_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (generated : Option ScalarBytes) (owner : Owner KemSK) :
    (simulateQ (bundleCallbacks setup codec owner.beacon.identity)
      (PqxdhLivePhase1Bundle.afterGenerated (projection setup index) generated owner)).IsTotalQueryBound 0 := by
  unfold PqxdhLivePhase1Bundle.afterGenerated
  split
  · trivial
  · simp only [PqxdhLivePhase1Bundle.signing, PqxdhJointPhase1SourceWriter.signingProgram,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bundleCallbacks, pure_bind]
    simp only [Option.map_some, PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning]
    split <;> simp only [simulateQ_bind, simulateQ_spec_query, simulateQ_pure, bundleCallbacks, pure_bind]
    all_goals first
      | trivial
      | (split <;> simp only [simulateQ_pure] <;> trivial)

set_option backward.isDefEq.respectTransparency false in
/-- One full actual bundle attempt draws at most one 32-byte one-time scalar. Retained-coin and terminal branches keep their actual lower costs; failed writers do not remove the attempt. -/
theorem bundle_program_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (owner : Owner KemSK) :
    (simulateQ (bundleCallbacks setup codec owner.beacon.identity)
      (PqxdhLivePhase1Bundle.bundle (projection setup index) owner)).IsTotalQueryBound 32 := by
  cases phase : owner.beacon.phase <;> simp only [PqxdhLivePhase1Bundle.bundle, phase, simulateQ_pure]
  case fresh =>
    simp only [simulateQ_bind, simulateQ_spec_query, bundleCallbacks]
    apply (isTotalQueryBound_bind (n₁ := 32) (n₂ := 0) ?_ ?_).mono (by omega)
    · simpa only [IsTotalQueryBound, isQueryBound_map_iff] using sampleScalar_uniform
    · exact fun generated => bundle_after_uniform setup codec index generated owner
  case freshWithCoins => exact (bundle_after_uniform setup codec index none owner).mono (Nat.zero_le 32)
  case initSent => trivial
  case established => trivial
  case aborted => trivial

/-- Every public bundle attempt keeps the actual source optional writer and complete owner reinstallation; repeated failed attempts each retain their own possible 32-byte draw. -/
theorem bundle_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (state : State KemSK) :
    ((bundle setup codec index).run state).IsTotalQueryBound 32 := by
  cases found : state.owners[index]? with
  | none =>
      simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind, found, StateT.run_pure]
      trivial
  | some owner =>
      simpa only [StateT.run, bundle_source setup codec index state owner found,
        IsTotalQueryBound, isQueryBound_map_iff] using bundle_program_uniform setup codec index owner

/-- Actual Server root evaluation retains its full family history and touch while drawing at most one 64-byte Extract value. -/
theorem server_root_uniform (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes Word32)
    (original : pqxdh.PendingServerRegistration) (state : NativeState KemSK) :
    ((loggedRoot hmac index input original).run state).IsTotalQueryBound 64 := by
  simp only [loggedRoot, StateT.run_bind, StateT.run_pure]
  apply (isTotalQueryBound_bind (n₁ := 64) (n₂ := 0) ?_ ?_).mono (by omega)
  · simpa only [romRoot, romRootBytes, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
      PqxdhServerAuthEntryFactor.extract_table_uniform (absBytes original.root_key_input.bytes) state.1.cache
  · intro result
    simp only [nativeTouch, localState, StateT.run, pure_bind]
    trivial

/-- Native acceptance rejection retains its diagnostics; successful root/consumption work has one Extract-table allowance. -/
theorem server_client_uniform (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes Word32) (state : NativeState KemSK) :
    ((nativeClient hmac index control binding input).run state).IsTotalQueryBound 64 := by
  unfold nativeClient
  split <;> try trivial
  simp only [StateT.run_bind, StateT.run_pure]
  apply (isTotalQueryBound_bind (server_root_uniform hmac index input _ state) (n₂ := 0) ?_).mono (by omega)
  intro result
  simp only [nativeConsume, localState, StateT.run, pure_bind]
  trivial

/-- Each actual raw Server accept pays its entire prefix, possible encapsulation/base work and reached root draw, even when it rejects or allocates only a failed attempt index. -/
theorem accept_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (seed : IdentitySeed) (scalar : ScalarBytes)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeAccept setup codec checks seed scalar raw).run state).IsTotalQueryBound (96 + caps.encapsCost) := by
  simp only [nativeAccept, StateT.run_bind]
  simp only [StateT.run, nativeGet, localState, nativeCoins, nativeSet, pure_bind, bind_map_left]
  have prefixBound : ((nativePrefix setup codec checks seed raw).run state.2.server.consumed).IsTotalQueryBound
      (32 + caps.encapsCost) := by
    simpa only [native_prefix, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using
      server_prefix_uniform setup codec checks caps bounded raw state.2.server.consumed
  apply (isTotalQueryBound_bind prefixBound (n₂ := 64) ?_).mono (by omega)
  rintro ⟨collected, consumed⟩
  cases collected with
  | none => trivial
  | some input =>
      change ((nativeClient setup.hmac state.2.sessions state.2.server.control
        (binding setup (challenge setup.joint setup.dh seed scalar)) input >>= _).run _).IsTotalQueryBound 64
      simp only [StateT.run_bind]
      apply (isTotalQueryBound_bind (server_client_uniform setup.hmac state.2.sessions state.2.server.control
        (binding setup (challenge setup.joint setup.dh seed scalar)) input _) (n₂ := 0) ?_).mono (by omega)
      intro result
      split <;> trivial

/-- Actual response construction pays the complete native hash/tail work before either writer can fail; missing or spent pending slots remain ordinary rejection. -/
theorem build_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeBuild setup codec checks index payload).run state).IsTotalQueryBound 64 := by
  simp only [nativeBuild, StateT.run_bind]
  simp only [StateT.run, nativeGet, localState, pure_bind]
  cases found : state.2.pending index with
  | none => trivial
  | some token =>
      change ((nativeCoins _ >>= _).run state).IsTotalQueryBound 64
      simp only [StateT.run_bind, StateT.run_pure]
      simp only [StateT.run, nativeCoins, nativeSet, localState, map_pure, bind_pure_comp]
      simpa only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
        PqxdhServerAuthTailCosts.build_uniform setup codec checks token.pending token.root payload state.2.server ([], state.2.ctx)

/-- The public HMAC callback keeps off-domain evaluation real and charges one possible shared Extract-table draw on the admitted slice. -/
theorem public_hmac_uniform (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
    (state : PqxdhJointDhExtractFamily.State) :
    ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar
      (.inr (.publicHmac key message))).run state).IsTotalQueryBound 64 := by
  simp only [PqxdhExtractRomFamily.romImpl, StateT.run]
  split
  · simpa only [bind_pure_comp, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
      PqxdhServerAuthEntryFactor.extract_table_uniform message state.cache
  · trivial

/-- The public API adds its actual same-run adversary touch without another draw, retaining all family and protocol state. -/
theorem hmac_uniform (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeHmac setup seed scalar key message).run state).IsTotalQueryBound 64 := by
  by_cases slice : key = PqxdhSecretInputKdf.zeroSalt ∧ message.length = 192
  all_goals simp only [nativeHmac, slice, and_self, ite_true, ite_false, StateT.run_bind]
  all_goals simp only [StateT.run, nativeTouch, localState, pure_bind, PqxdhServerRelatedRootConsumer.familyImpl,
    (PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).2.2]
  all_goals simpa only [StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    public_hmac_uniform setup seed scalar key message state.1

/-- Every public CTX hash preserves its real shared cache and costs at most one 64-byte digest draw. -/
theorem hash_uniform (bytes : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeHash bytes).run state).IsTotalQueryBound 64 := by
  simpa only [nativeHash, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.2.ctx

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.create_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.create_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.rawCreate_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.rawCreate_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.sourceRoot_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.sourceRoot_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.preparation_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.preparation_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.tail_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.tail_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.callbacks_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.callbacks_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.owner_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.owner_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_after_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_after_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_program_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_program_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_root_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_root_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.server_client_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.accept_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.accept_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.build_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.build_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.public_hmac_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.public_hmac_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.hmac_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.hmac_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.hash_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.hash_uniform

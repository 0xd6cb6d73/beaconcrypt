import BeaconcryptCore.Computational.PqxdhServerAuthJointIdentityDhBudget
import BeaconcryptCore.Computational.PqxdhServerAuthEntryResourceServices

/-! Explicit uniform costs of the literal native callbacks. The primitive programs and all interpreted base calls are retained; deterministic operations are not asserted to have zero running time. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts
open PqxdhJointIdentity PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhServerAuthSourceCosts PqxdhServerAuthTailCosts
open PqxdhJointGapDh (ScalarBytes PublicChallenge)
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- One restricted Extract table read costs at most 64 byte draws on a miss and zero on a hit. -/
theorem extract_table_uniform (bytes : Pqxdh.Bytes) (cache : HmacOracle.QueryCache) :
    ((HmacOracle.randomOracle bytes).run cache).IsTotalQueryBound 64 :=
  PqxdhServerAuthEntryFactor.extract_table_uniform bytes cache

/-- Actual root derivation pays the same 64-byte table allowance and keeps real Expand plus both original history entries. -/
theorem root_bytes_uniform {A : Type} (hmac : HmacSha512)
    (message : PqxdhJointDhExtractFamily.Message) (bytes : Pqxdh.Bytes)
    (state : PqxdhServerRelatedRootConsumer.State A) :
    ((romRootBytes hmac message bytes).run state).IsTotalQueryBound 64 := by
  simp only [romRootBytes, StateT.run, IsTotalQueryBound, isQueryBound_map_iff]
  exact extract_table_uniform bytes state.1.cache

set_option backward.isDefEq.respectTransparency false in
/-- The actual Beacon root callback retains its source observation and 32-byte wrapper without additional draws. -/
theorem beacon_root_uniform (hmac : HmacSha512) (publicValue : PublicChallenge)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (input : pqxdh.RootKeyInput)
    (state : NativeState KemSK) :
    ((nativeBeaconRoot hmac publicValue original input).run state).IsTotalQueryBound 64 := by
  rw [nativeBeaconRoot, StateT.run_bind]
  simp only [nativeTouch, PqxdhServerAuthNative.localState, StateT.run, pure_bind]
  change ((romRootReply (A := GameState KemSK) hmac publicValue original input).run _).IsTotalQueryBound 64
  simp only [romRootReply, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
  exact root_bytes_uniform _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The literal original post-root initializer/application/raw-receive program has one CTX miss allowance. Every real KDF and AEAD operation, including future-path derivations before rejection, is retained. -/
theorem after_root_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (root : Std.Array Std.U8 32#usize)
    (state : RawCtxSharedPrimitive.SharedState Unit) :
    ((simulateQ (beaconNative setup codec)
      (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
        (PqxdhBeaconPhase2Publication.afterRoot codec.frameRead original root))).run state).IsTotalQueryBound 64 := by
  unfold PqxdhBeaconPhase2Publication.afterRoot PqxdhBeaconPhase2Publication.initialRun
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query,
    PqxdhBeaconPhase2Publication.nativeTailAdapter, beaconNative]
  cases found : codec.application original.response with
  | none => simp only [simulateQ_pure]; trivial
  | some raw =>
    simp only [bind_pure_comp, simulateQ_map, PqxdhBeaconPhase2Bounds.native_raw_lift,
      StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
    rw [← QueryImpl.simulateQ_compose]
    have handler : beaconNative setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeRawLift =
        RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) := by
      funext query
      simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeRawLift,
        simulateQ_spec_query, beaconNative]
    rw [handler]
    change ((simulateQ (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source))
      (simulateQ RawCtxSourceOpen.nativeAdapter _)).run state).IsTotalQueryBound 64
    exact RawCtxSharedPrimitive.native_uniform_bound setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source)
      0 (RawCtxSourceHkdf.kdf_uniform setup.source) _ 51 1
      (RawCtxKdfBudget.raw_bound codec.frameRead raw _) (RawCtxSourceOpen.raw_primitive_bounds codec.frameRead raw _).1 state

set_option backward.isDefEq.respectTransparency false in
/-- Lifting the complete shared-cache program retains the same full native state and every underlying uniform computation. -/
theorem simulate_native_ctx {κ Result : Type} {spec : OracleSpec κ}
    (impl : QueryImpl spec (StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp))
    (work : OracleComp spec Result) :
    simulateQ (fun query => nativeCtx (KemSK := KemSK) (impl query)) work =
      nativeCtx (simulateQ impl work) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
    funext state
    simp [nativeCtx]
    rfl
  | query_bind query next ih =>
    rw [simulateQ_query_bind]
    simp only [ih]
    funext state
    change (nativeCtx (impl query) >>= fun value => nativeCtx (simulateQ impl (next value))).run state =
      (nativeCtx (simulateQ impl (spec.query query >>= next))).run state
    rw [StateT.run_bind]
    simp only [simulateQ_spec_query, nativeCtx, StateT.run, simulateQ_bind,
      bind_map_left]
    have expand : (impl query >>= fun value => simulateQ impl (next value)) ((), state.2.ctx) =
        ((impl query).run ((), state.2.ctx) >>= fun result => (simulateQ impl (next result.1)).run result.2) := rfl
    rw [expand, map_bind]
    exact bind_congr fun ⟨value, (), cache⟩ => rfl

/-- Lifting a whole CTX program adds no uniform query and retains every other native state coordinate. -/
theorem ctx_uniform {Result : Type}
    (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp Result)
    (count : Nat) (bounded : ∀ state, (work.run state).IsTotalQueryBound count)
    (state : NativeState KemSK) :
    ((nativeCtx work).run state).IsTotalQueryBound count := by
  simpa only [nativeCtx, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    bounded ((), state.2.ctx)

set_option backward.isDefEq.respectTransparency false in
/-- The complete original Beacon tail has one restricted Extract miss and one CTX miss allowance, including every rejected opening. -/
theorem beacon_tail_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (state : NativeState KemSK) :
    ((nativeBeaconTail setup codec publicValue original).run state).IsTotalQueryBound 128 := by
  rw [nativeBeaconTail, PqxdhPhase2DhRootConsumer.tail_root, StateT.run_bind]
  refine isTotalQueryBound_bind (n₂ := 64)
    (beacon_root_uniform setup.hmac publicValue original original.candidate.root_key_input state) ?_
  rintro ⟨_ | root, after⟩
  · trivial
  · simpa only [simulate_native_ctx] using
      ctx_uniform _ 64 (after_root_uniform setup codec original root) after

set_option backward.isDefEq.respectTransparency false in
/-- Server root logging adds no draws beyond the actual restricted Extract query. -/
theorem logged_root_uniform (hmac : HmacSha512) (index : Nat)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32)
    (original : pqxdh.PendingServerRegistration) (state : NativeState KemSK) :
    ((loggedRoot hmac index input original).run state).IsTotalQueryBound 64 := by
  rw [loggedRoot, StateT.run_bind]
  exact isTotalQueryBound_bind (n₂ := 0)
    (root_bytes_uniform hmac (PqxdhServerRelatedRootConsumer.nativeMessage input)
      (absBytes original.root_key_input.bytes) state) (fun _ => by trivial)

set_option backward.isDefEq.respectTransparency false in
/-- Literal core acceptance and consumption preserve all outcomes and need at most one root-table miss. -/
theorem client_uniform (hmac : HmacSha512) (index : Nat) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PqxdhBeaconPhase2Preparation.Word32)
    (state : NativeState KemSK) :
    ((nativeClient hmac index control binding input).run state).IsTotalQueryBound 64 := by
  unfold nativeClient
  split <;> try trivial
  rw [StateT.run_bind]
  exact isTotalQueryBound_bind (n₂ := 0) (logged_root_uniform hmac index input _ state) (fun _ => by trivial)

/-- The actual native Server prefix retains all primitive/base work and costs one scalar plus one arbitrary-key encapsulation allowance. -/
theorem prefix_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (seed : IdentitySeed)
    (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    ((nativePrefix setup codec checks seed raw).run consumed).IsTotalQueryBound (32 + caps.encapsCost) := by
  simpa only [native_prefix, StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using
    server_prefix_uniform setup codec checks caps bounded raw consumed

set_option backward.isDefEq.respectTransparency false in
/-- Every literal accept attempt retains its full rejection/publication path and costs one scalar, one encapsulation and one root-table miss at most. -/
theorem accept_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : KemCaps) (bounded : KemBound setup caps) (seed : IdentitySeed) (scalar : ScalarBytes)
    (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeAccept setup codec checks seed scalar raw).run state).IsTotalQueryBound (96 + caps.encapsCost) := by
  simp only [nativeAccept, StateT.run, nativeGet_bind, nativeCoins_bind, nativeSet_bind]
  refine (isTotalQueryBound_bind (n₂ := 64)
    (prefix_uniform setup codec checks caps bounded seed raw state.2.server.consumed) ?_).mono (by omega)
  rintro ⟨_ | input, consumed⟩ <;> try trivial
  simp only [native_bind_run]
  refine isTotalQueryBound_bind (n₂ := 0) (client_uniform setup.hmac state.2.sessions state.2.server.control _ input _) ?_
  rintro ⟨(reply | _ | _), after⟩ <;> try trivial
  cases reply <;> trivial

set_option backward.isDefEq.respectTransparency false in
/-- One actual optional build has at most one CTX miss; token removal, failed writers, and the complete installed state remain executed. -/
theorem native_build_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeBuild setup codec checks session payload).run state).IsTotalQueryBound 64 := by
  simp only [nativeBuild, StateT.run, nativeGet_bind]
  cases state.2.pending session <;> try trivial
  simp only [nativeCoins_bind, nativeSet_bind]
  exact isTotalQueryBound_bind (n₂ := 0)
    (build_uniform setup codec checks _ _ payload state.2.server ([], state.2.ctx)) (fun _ => by trivial)

/-- The public hash callback uses the original shared CTX cache, with zero draws on hits and at most 64 on misses. -/
theorem hash_uniform (bytes : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeHash bytes).run state).IsTotalQueryBound 64 := by
  simpa only [nativeHash, StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
    CtxComputationalSecurity.ctxRandomOracle_total_query_bound ((), bytes) state.2.ctx

/-- The original public HMAC endpoint pays one possible restricted Extract miss; outside that approved slice it keeps the real deterministic HMAC. -/
theorem hmac_family_uniform (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : HmacBlock) (message : Pqxdh.Bytes) (state : PqxdhJointDhExtractFamily.State) :
    ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar
      (.inr (.publicHmac key message))).run state).IsTotalQueryBound 64 := by
  by_cases inside : key = zeroSalt ∧ message.length = 192
  · rw [PqxdhExtractRomFamily.rom_public_oracle setup.hmac setup.joint setup.dh seed scalar key message inside]
    simpa only [IsTotalQueryBound, isQueryBound_map_iff] using extract_table_uniform message state.cache
  · rw [PqxdhExtractRomFamily.rom_public_real setup.hmac setup.joint setup.dh seed scalar
      (PqxdhJointDhExtractFamily.actualExtract setup.hmac) key message inside,
      PqxdhJointDhExtractFamily.public_evaluation]
    trivial

set_option backward.isDefEq.respectTransparency false in
/-- The native public-HMAC wrapper keeps its original observation and full state while forwarding the same real-or-restricted-table service. -/
theorem hmac_uniform (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : HmacBlock) (message : Pqxdh.Bytes) (state : NativeState KemSK) :
    ((nativeHmac setup seed scalar key message).run state).IsTotalQueryBound 64 := by
  by_cases inside : key = zeroSalt ∧ message.length = 192
  all_goals simp only [nativeHmac, inside, and_self, ite_true, ite_false, StateT.run, native_bind_run,
    nativeTouch, PqxdhServerAuthNative.localState, pure_bind]
  all_goals simp only [PqxdhServerRelatedRootConsumer.familyImpl, IsTotalQueryBound, isQueryBound_map_iff,
    (PqxdhExtractRomFamily.rom_forward setup.hmac setup.joint setup.dh seed scalar).2.2]
  all_goals exact hmac_family_uniform setup seed scalar key message state.1

/-- The original public uniform request is forwarded once, with its full value and both state coordinates. -/
theorem coin_uniform (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed beaconSeed : IdentitySeed) (scalar : ScalarBytes) (coin : Nat) (state : NativeState KemSK) :
    ((nativeHandler setup codec checks seed scalar beaconSeed (.inl coin)).run state).IsTotalQueryBound 1 := by
  change IsTotalQueryBound (spec := unifSpec)
    ((fun reply => (reply, state)) <$> (unifSpec.query coin : ProbComp _)) 1
  simp [IsTotalQueryBound, isQueryBound_map_iff]

end BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts

/-! Checked theorem dependencies. -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.extract_table_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.extract_table_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.root_bytes_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.root_bytes_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.beacon_root_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.beacon_root_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.after_root_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.after_root_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.simulate_native_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.simulate_native_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.ctx_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.ctx_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.beacon_tail_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.beacon_tail_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.logged_root_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.logged_root_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.client_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.client_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.prefix_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.prefix_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.accept_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.accept_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.native_build_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.native_build_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.hash_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.hash_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.hmac_family_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.hmac_family_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.hmac_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.hmac_uniform
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.coin_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNativeUniformCosts.coin_uniform

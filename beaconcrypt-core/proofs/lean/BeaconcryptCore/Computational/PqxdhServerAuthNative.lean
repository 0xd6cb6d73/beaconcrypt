import BeaconcryptCore.Computational.PqxdhServerAuthExperiment

/-! Native source interpretation of the approved R1 Server authentication experiment. The KDF patch is limited to the existing restricted Extract table; the experiment also retains its existing shared CTX/BLAKE2b random oracle. All native preparation, publication, optional replies and complete state are retained. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhServerAuthNative
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf PqxdhJointKdfGame
open PqxdhJointDhExtractRoot
open PqxdhServerRootPreparation PqxdhServerStaticDhSource PqxdhServerRelatedRootInput PqxdhServerClearedRoot
open PqxdhServerRelatedRootConsumer
open PqxdhBeaconPhase2Preparation (Word32)

/-- One native root evaluation reads the approved table at the actual core-built bytes, then computes real Expand and retains both actual family observations. -/
noncomputable def romRootBytes {A : Type} (hmac : HmacSha512)
    (message : PqxdhJointDhExtractFamily.Message) (bytes : Pqxdh.Bytes) :
    StateT (State A) ProbComp RootOutput := fun state =>
  (fun result : HmacBlock × HmacOracle.QueryCache =>
    (expandRoot hmac result.1,
      ((⟨state.1.history ++ [.derive message (some result.1),
          .publicHmac result.1 rootExpandInput (hmac.eval result.1 rootExpandInput)],
        result.2⟩ : PqxdhJointDhExtractFamily.State), state.2))) <$>
    (HmacOracle.randomOracle bytes).run state.1.cache

noncomputable def romRoot {A Reader E : Type} (hmac : HmacSha512)
    (input : Inputs Reader E Word32) (original : pqxdh.PendingServerRegistration) :
    StateT (State A) ProbComp RootOutput :=
  romRootBytes hmac (nativeMessage input) (absBytes original.root_key_input.bytes)

set_option backward.isDefEq.respectTransparency false in
/-- Exact native input equality transports the complete ROM root computation, including its cache and both log entries. -/
theorem root_rom {A Reader E : Type} (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (input : Inputs Reader E PeerEncoding) (original : pqxdh.PendingServerRegistration)
    (address : PqxdhJointDhExtractFamily.input joint dh seed scalar (message input) =
      some (absBytes original.root_key_input.bytes)) :
    familyImpl (A := A) (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)
        (.inr (.derive (message input))) =
      some <$> romRoot hmac (concreteInputs joint seed input) original := by
  funext state
  change (familyImpl (A := A) (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)
    (.inr (.derive (message input)))).run state =
      (some <$> romRoot hmac (concreteInputs joint seed input) original).run state
  rw [StateT.run_map]
  change (fun result => (result.1, (result.2, state.2))) <$>
      ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)
        (.inr (.derive (message input)))).run state.1 =
    (fun result => (some result.1, result.2)) <$>
      (romRoot hmac (concreteInputs joint seed input) original).run state
  rw [PqxdhExtractRomFamily.rom_root, address]
  simp only [romRoot, StateT.run, romRootBytes, Functor.map_map]
  rfl


/-- Literal core acceptance precedes clearing; successful source derivation clears its input before recording consumption and returning the original full token. -/
noncomputable def romSource {A Reader E : Type} (hmac : HmacSha512)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (input : Inputs Reader E Word32) :
    StateT (State A) ProbComp (RustM (Option Returned)) := do
  let accepted := accept control binding input
  let _ ← auxImpl aux .eraseShared
  match accepted with
  | .ok (.Err _) => pure (ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Ok (_, original)) => do
      let root ← romRoot hmac input original
      let _ ← auxImpl aux .eraseInput
      let _ ← auxImpl aux (.consume original.registration_id)
      pure (ok (some ⟨root, cleared original⟩))

set_option backward.isDefEq.respectTransparency false in
/-- Real core acceptance, all rejection paths, clearing and consumption agree with the executable root client, retaining the full cleared token and every primitive state field. -/
theorem client_rom {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes) (aux : QueryImpl AuxSpec (StateT A ProbComp))
    (control : pqxdh.ServerState) (binding : pqxdh.ServerBinding) (input : Inputs Reader E PeerEncoding)
    (references : References domain input) :
    simulateQ (impl ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) aux) (client binding input) =
      romSource hmac aux control binding (concreteInputs joint seed input) := by
  classical
  by_cases valid : localNonzero input
  · obtain ⟨original, accepted, fields, address, rid⟩ := accept_success kdf.crypto joint dh domain secretOfSeed wiring
      seed scalar input references valid control binding
    have token := accepted_cleared binding (concreteInputs joint seed input) control original accepted
    rw [pending_materialized] at token
    have tokenRid : (pending binding input).registration_id = original.registration_id :=
      by simpa only [cleared] using congrArg (fun value : pqxdh.PendingServerRegistration => value.registration_id) token.symm
    have rootEq := root_rom (A := A) hmac joint dh seed scalar input original address
    simp only [client, romSource, accepted, not_true_eq_false, valid, ite_false,
      simulateQ_bind, simulateQ_spec_query, impl, rootEq]
    simp only [bind_map_left, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, impl, ← token, cleared]
    rw [tokenRid]
    rfl
  · have rejected := accept_failure kdf.crypto joint domain secretOfSeed wiring seed input references valid control binding
    simp only [client, romSource, rejected, valid, not_false_eq_true, ite_true, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, impl]
    rfl



noncomputable def romNativeStage {A Reader E : Type} (hmac : HmacSha512)
    (joint : Primitives) (seed : IdentitySeed)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit) (StateT (State A) ProbComp))
    (visit : Word32 → StateT (State A) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (raw : Pqxdh.Bytes) : StateT (State A) ProbComp (RustM (Option Returned)) := do
  let input ← simulateQ (PqxdhServerStaticDhSource.nativeImpl joint seed preImpl visit) (collect raw)
  match input with
  | none => pure (ok none)
  | some input => romSource hmac aux control binding input

set_option backward.isDefEq.respectTransparency false in
/-- The whole original raw prefix derives the references consumed by the root simulation; no arbitrary successful-prefix or input-provenance premise is supplied. -/
theorem server_stage_rom {A Reader E : Type} (kdf : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (joint : Primitives) (dh : DhInterface joint) (domain : PublicDomain joint)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring kdf.crypto joint secretOfSeed)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (preImpl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Unit) (StateT (State A) ProbComp))
    (visit : Word32 → StateT (State A) ProbComp Unit)
    (aux : QueryImpl AuxSpec (StateT A ProbComp)) (control : pqxdh.ServerState)
    (binding : pqxdh.ServerBinding) (raw : Pqxdh.Bytes) :
    stage domain preImpl visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) aux binding raw =
      romNativeStage hmac joint seed preImpl visit aux control binding raw := by
  funext initial
  change (stage domain preImpl visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) aux binding raw).run initial =
    (romNativeStage hmac joint seed preImpl visit aux control binding raw).run initial
  simp only [stage, romNativeStage, collect_realization joint domain seed, StateT.run_bind, bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨input, final⟩ reached
  cases input with
  | none => rfl
  | some input =>
      have references := collect_references domain preImpl visit raw initial final input reached
      exact congrFun (client_rom kdf hmac joint dh domain secretOfSeed wiring seed scalar aux control binding input references) final




/-- The native Beacon callback uses its actual constructed root input and source-only descriptor. The root wrapper is the actual 32-byte native representation. -/
noncomputable def romRootReply {Response A : Type} (hmac : HmacSha512)
    (publicValue : PublicChallenge) (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (input : pqxdh.RootKeyInput) : StateT (State A) ProbComp (Option Word32) :=
  (some ∘ PqxdhRootTableInitialization.rootArray) <$>
    romRootBytes hmac (PqxdhPhase2DhStage.sourceMessage publicValue original) (absBytes input.bytes)

set_option backward.isDefEq.respectTransparency false in
/-- Literal extracted input assembly connects the root-valued family with the native Beacon callback and complete table/history. -/
theorem beacon_root_rom {A : Type} (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type}
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : PqxdhPhase2GapDhSource.References domain pending.collected)
    (converted : PqxdhPhase2GapDhSource.peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    simulateQ (PqxdhPhase2DhRootConsumer.familyImpl (A := A)
      (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction))
      (PqxdhPhase2DhRootConsumer.root (challenge joint dh seed scalar) pending) =
      romRootReply hmac (challenge joint dh seed scalar) original original.candidate.root_key_input := by
  funext state
  change (simulateQ (PqxdhPhase2DhRootConsumer.familyImpl (A := A)
    (PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction))
    (PqxdhPhase2DhRootConsumer.root (challenge joint dh seed scalar) pending)).run state = (romRootReply hmac (challenge joint dh seed scalar) original original.candidate.root_key_input).run state
  rw [PqxdhPhase2DhRootConsumer.family_complete]
  simp only [PqxdhPhase2DhRootConsumer.root, simulateQ_map, simulateQ_spec_query, StateT.run_map]
  rw [PqxdhExtractRomFamily.rom_root,
    beacon_source dh domain seed scalar pending.collected references converted original.candidate.root_key_input related.2.2.2.2]
  unfold romRootReply
  rw [StateT.run_map]
  simp only [StateT.run, romRootBytes, Functor.map_map,
    PqxdhPhase2DhStage.source_message dh scalar _ original pending related]
  rfl



section Beacon
open PqxdhPhase2DhRootConsumer

/-- The literal native tail retains its actual root callback and all post-root effects. -/
noncomputable def romTail {Response A : Type} (hmac : HmacSha512)
    (publicValue : PublicChallenge)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (original : PqxdhBeaconPhase2Preparation.Prepared Response) :=
  simulateQ (withRoot (romRootReply hmac publicValue original) (nativeImpl native))
    (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.tail decode original))

set_option backward.isDefEq.respectTransparency false in
/-- The complete original native tail and its executable related-root client are equal in the same full effect state, before arbitrary continuation. Neither successful opening nor authentication is assumed. -/
theorem beacon_tail_rom {A : Type} (hmac : HmacSha512)
    {joint : Primitives} (dh : DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {Response : Type}
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : PqxdhPhase2GapDhSource.References domain pending.collected)
    (converted : PqxdhPhase2GapDhSource.peer pending.collected.serverConverted = (joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel dh scalar original pending) :
    romTail hmac (challenge joint dh seed scalar) native decode original =
      simulateQ (impl ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native)
        (tail (challenge joint dh seed scalar) decode pending) := by
  have familyEq : impl ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native ∘ₛ rootLift =
      PqxdhPhase2DhRootConsumer.familyImpl (A := A) ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) := by
    funext query
    exact simulateQ_spec_query (impl ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native) _
  have nativeEq : impl ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native ∘ₛ nativeLift =
      nativeImpl native := by
    funext query
    exact simulateQ_spec_query (impl ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native) _
  unfold romTail
  rw [tail_root]
  simp only [tail, simulateQ_bind, ← QueryImpl.simulateQ_compose, familyEq]
  rw [beacon_root_rom hmac dh domain seed scalar original pending references converted related]
  apply bind_congr
  intro value
  cases value with
  | none => simp only [simulateQ_pure]
  | some value =>
      rw [← QueryImpl.simulateQ_compose, nativeEq]
      change simulateQ (nativeImpl native ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter)
        (PqxdhBeaconPhase2Publication.afterRoot decode original value) = _
      rw [QueryImpl.simulateQ_compose, afterRoot_source dh scalar decode original pending related value]


end Beacon


section BeaconStage
open PqxdhPhase2DhStage
/-- The source side retains real selected DH values internally and executes the original preparation before its original native tail. -/
noncomputable def romBeaconStage {joint : Primitives} (dh : DhInterface joint) (scalar : ScalarBytes)
    {I D K X Response A : Type} (hmac : HmacSha512)
    (publicValue : PublicChallenge)
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response)
      (StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp))
    (visit : Word32 → StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp Unit)
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp (Option PqxdhBeaconPhase2Publication.Staged) := do
  let prepared ← simulateQ (PqxdhPhase2GapDhSource.nativeImpl dh scalar aux visit)
    (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)
  match prepared with
  | none => pure none
  | some original => romTail hmac publicValue native decode original

set_option backward.isDefEq.respectTransparency false in
/-- One whole source execution supplies its actual references, native conversion, late raw identity pin, exact 192-byte root input and complete optional record tail. No accepted-target honesty or authentication premise occurs. -/
theorem beacon_stage_rom {joint : Primitives} (dh : DhInterface joint) (domain : PqxdhPhase2GapDhSource.PublicDomain dh)
    (seed : IdentitySeed) (scalar : ScalarBytes) {I D K X Response A : Type}
    (source : FixedHkdfSha512NoSaltSource) (hmac : HmacSha512)
    (secretOfSeed : IdentitySeed → List.Vector UInt8 64) (wiring : SourceWiring source.crypto joint secretOfSeed)
    (aux : QueryImpl (PqxdhBeaconPhase2Preparation.Spec I D K X Response)
      (StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp))
    (conversion : ∀ value initial converted final,
      (some converted, final) ∈ support ((aux (.publicConversion value)).run initial) →
        source.crypto.xpkConv (absBytes value) = some (absBytes converted))
    (visit : Word32 → StateT (PqxdhPhase2DhRootConsumer.State A) ProbComp Unit)
    (erase : ∀ secrets, aux (.eraseShared secrets) = pure ())
    (native : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (StateT A ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (control : pqxdh.BeaconInitSent)
    (pin : absBytes control.expected_server_binding.identity_public_key = (joint.publicKeys seed).ed25519.toList)
    (identity : I) (oneTime : D) (kem : K) (raw : Pqxdh.Bytes) :
    romBeaconStage dh scalar hmac (challenge joint dh seed scalar) aux visit native decode control identity oneTime kem raw =
      simulateQ (impl domain aux visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native)
        (PqxdhPhase2DhStage.stage (challenge joint dh seed scalar) decode control identity oneTime kem raw) := by
  have preEq : impl domain aux visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native ∘ₛ prefixLift =
      PqxdhPhase2GapDhSource.prefixImpl domain aux visit := by
    funext query
    exact simulateQ_spec_query (impl domain aux visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native) _
  have tailEq : impl domain aux visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native ∘ₛ tailLift =
      PqxdhPhase2DhRootConsumer.impl ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native := by
    funext query
    exact simulateQ_spec_query (impl domain aux visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native) _
  funext initial
  change (romBeaconStage dh scalar hmac (challenge joint dh seed scalar) aux visit native decode control identity oneTime kem raw).run initial = _
  simp only [romBeaconStage, PqxdhPhase2DhStage.stage, simulateQ_bind, ← QueryImpl.simulateQ_compose, preEq, StateT.run_bind]
  apply PqxdhPhase2DhMetadata.prepare_converted_continuation dh domain scalar source.crypto aux conversion visit erase
    control identity oneTime kem raw initial
  · intro state
    simp only [simulateQ_pure, StateT.run_pure]
    rfl
  · intro original pending state references converted admitted related
    have actualConversion := PqxdhPhase2DhMetadata.pinned_conversion source.crypto joint secretOfSeed wiring seed
      control pending.collected pending.metadata pin admitted converted
    change (romTail hmac (challenge joint dh seed scalar) native decode original).run state =
      (simulateQ (impl domain aux visit ((PqxdhExtractRomFamily.romImpl hmac joint dh seed scalar ∘ₛ reduction)) native)
        (simulateQ tailLift (PqxdhPhase2DhRootConsumer.tail (challenge joint dh seed scalar) decode pending))).run state
    rw [← QueryImpl.simulateQ_compose, tailEq,
      beacon_tail_rom hmac dh domain seed scalar native decode original pending references actualConversion related]


end BeaconStage


section Experiment
open PqxdhServerAuthExperiment
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

abbrev NativeState (KemSK : Type) := PqxdhJointDhExtractFamily.State × GameState KemSK
abbrev NativeGame (KemSK : Type) := StateT (NativeState KemSK) ProbComp

/-- Evaluate the executable game's family effects while retaining both complete state coordinates. This helper is used only for correspondence statements. -/
noncomputable def evaluate {Result : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : Game KemSK Result) : NativeGame KemSK Result := fun state =>
  (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (work.run state.2)).run state.1

set_option backward.isDefEq.respectTransparency false in
/-- Interpretation retains the entire result-dependent continuation and both full state components. -/
theorem evaluate_bind {Result Next : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : Game KemSK Result)
    (next : Result → Game KemSK Next) :
    evaluate setup seed scalar (work >>= next) =
      (evaluate setup seed scalar work >>= fun value => evaluate setup seed scalar (next value)) := by
  funext state
  let family := PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ family (work.run state.2 >>= fun result => (next result.1).run result.2)).run state.1 =
      (((fun result => (result.1.1, (result.2, result.1.2))) <$>
        (simulateQ family (work.run state.2)).run state.1) >>= fun result =>
          (fun final => (final.1.1, (final.2, final.1.2))) <$>
            (simulateQ family ((next result.1).run result.2.2)).run result.2.1)
  simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]

/-- A native pure result preserves both complete states. -/
theorem evaluate_pure {Result : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (value : Result) :
    evaluate setup seed scalar (pure value) = pure value := by
  funext state
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (pure (value, state.2))).run state.1 = pure (value, state)
  simp only [simulateQ_pure, StateT.run_pure, map_pure]


/-- Ordinary source-local state transitions keep the full family cache/history untouched. -/
def localState {Result : Type} (step : GameState KemSK → Result × GameState KemSK) :
    NativeGame KemSK Result := fun state => pure ((step state.2).1, (state.1, (step state.2).2))

theorem evaluate_local {Result : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (step : GameState KemSK → Result × GameState KemSK) :
    evaluate setup seed scalar (fun state => pure (step state)) = localState step := by
  funext state
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (pure (step state.2))).run state.1 = pure ((step state.2).1, (state.1, (step state.2).2))
  simp only [simulateQ_pure, StateT.run_pure, map_pure]


/-- An ordinary probabilistic source computation retains the complete state. -/
def nativeCoins {Result : Type} (work : ProbComp Result) : NativeGame KemSK Result :=
  fun state => (fun value => (value, state)) <$> work

theorem evaluate_coins {Result : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : ProbComp Result) :
    evaluate setup seed scalar (liftCoins work) = nativeCoins work := by
  funext state
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (familyCoins work >>= fun value => pure (value, state.2))).run state.1 =
      (fun value => (value, state)) <$> work
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [rom_coins]
  simp only [bind_pure_comp, Functor.map_map]


/-- Forwarding preserves the complete unrelated game state beside the family reply and poststate. -/
theorem evaluate_forward (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (query : RootSpec.Domain) :
    evaluate setup seed scalar (forwardFamily query) =
      PqxdhServerRelatedRootConsumer.familyImpl
        (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction) query := by
  funext state
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      ((RootSpec.query query : OracleComp RootSpec _) >>= fun value => pure (value, state.2))).run state.1 =
    (fun result => (result.1, (result.2, state.2))) <$>
      ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction) query).run state.1
  simp only [bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]


/-- The complete adaptive source program is retained under evaluation, not just individual query marginals. -/
theorem evaluate_program {ι' Result : Type} {spec : OracleSpec ι'} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (handler : QueryImpl spec (Game KemSK))
    (work : OracleComp spec Result) :
    evaluate setup seed scalar (simulateQ handler work) =
      simulateQ (fun query => evaluate setup seed scalar (handler query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evaluate_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evaluate_bind, ih]


def nativeTouch (touch : Touch) : NativeGame KemSK Unit :=
  localState fun state => ((), { state with ghost := { state.ghost with touches := state.ghost.touches ++ [touch] } })

/-- The same source ghost append preserves all private state and cache. -/
theorem evaluate_touch (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (touch : Touch) : evaluate setup seed scalar (recordTouch touch) = nativeTouch touch :=
  evaluate_local setup seed scalar _

noncomputable def loggedRoot (hmac : HmacSha512) (index : Nat)
    (input : Inputs Reader ScalarBytes Word32) (original : pqxdh.PendingServerRegistration) :
    NativeGame KemSK RootOutput := do
  let root ← romRoot hmac input original
  nativeTouch (.session index (nativeMessage input) (some root))
  pure root

set_option backward.isDefEq.respectTransparency false in
/-- The concrete session root observer records exactly the same native message and returned root after the actual root callback. -/
theorem session_root_rom (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (index : Nat) (input : Inputs Reader ScalarBytes PeerEncoding) (original : pqxdh.PendingServerRegistration)
    (address : PqxdhJointDhExtractFamily.input setup.joint setup.dh seed scalar (message input) =
      some (absBytes original.root_key_input.bytes)) :
    evaluate setup seed scalar (sessionFamily index (.inr (.derive (message input)))) =
      some <$> loggedRoot setup.hmac index (concreteInputs setup.joint seed input) original := by
  simp only [sessionFamily, evaluate_bind, evaluate_forward, evaluate_touch, evaluate_pure]
  rw [root_rom setup.hmac setup.joint setup.dh seed scalar input original address]
  simp only [loggedRoot, bind_map_left, map_bind, map_pure]
  rfl


def nativeConsume (rid : pqxdh.RegistrationId) : NativeGame KemSK Unit :=
  localState fun state => ((), { state with server :=
    { state.server with consumed := state.server.consumed ++ [absBytes rid.bytes] } })

/-- The actual consumed-ID append changes no other original state or family field. -/
theorem evaluate_consume (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (index : Nat) (rid : pqxdh.RegistrationId) :
    evaluate setup seed scalar (sessionImpl index (.inr (.consume rid))) = nativeConsume rid :=
  evaluate_local setup seed scalar _

/-- Literal native core acceptance and root processing, with only the original ghost annotation added. Logical erase callbacks are the experiment's actual no-ops. -/
noncomputable def nativeClient (hmac : HmacSha512) (index : Nat)
    (control : pqxdh.ServerState) (serverBinding : pqxdh.ServerBinding)
    (input : Inputs Reader ScalarBytes Word32) : NativeGame KemSK (RustM (Option Returned)) := do
  match accept control serverBinding input with
  | .ok (.Err _) => pure (ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Ok (_, original)) => do
      let root ← loggedRoot hmac index input original
      nativeConsume original.registration_id
      pure (ok (some ⟨root, cleared original⟩))

set_option backward.isDefEq.respectTransparency false in
/-- The concrete original client is the literal native core acceptance with the same root/consumption/touch sequence and full state. -/
theorem client_native (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (index : Nat) (control : pqxdh.ServerState) (serverBinding : pqxdh.ServerBinding)
    (input : Inputs Reader ScalarBytes PeerEncoding) (references : References setup.serverDomain input) :
    evaluate setup seed scalar (simulateQ (sessionImpl index) (client serverBinding input)) =
      nativeClient setup.hmac index control serverBinding (concreteInputs setup.joint seed input) := by
  classical
  by_cases valid : localNonzero input
  · obtain ⟨original, accepted, fields, address, rid⟩ := accept_success setup.source.crypto setup.joint setup.dh
      setup.serverDomain setup.secretOfSeed setup.wiring seed scalar input references valid control serverBinding
    have token := accepted_cleared serverBinding (concreteInputs setup.joint seed input) control original accepted
    rw [pending_materialized] at token
    rw [evaluate_program]
    simp only [client, nativeClient, accepted, valid, not_true_eq_false, ite_false,
      simulateQ_bind, simulateQ_spec_query]
    have shared : evaluate setup seed scalar (sessionImpl index (.inr .eraseShared)) = pure () :=
      evaluate_pure setup seed scalar ()
    have erased : evaluate setup seed scalar (sessionImpl index (.inr .eraseInput)) = pure () :=
      evaluate_pure setup seed scalar ()
    have rooted : evaluate setup seed scalar (sessionImpl index (.inl (.inr (.derive (message input))))) =
        some <$> loggedRoot setup.hmac index (concreteInputs setup.joint seed input) original :=
      session_root_rom setup seed scalar index input original address
    simp only [shared, erased, pure_bind, rooted, bind_map_left, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, evaluate_consume, ← token]
    rfl
  · rw [evaluate_program]
    have rejected := accept_failure setup.source.crypto setup.joint setup.serverDomain setup.secretOfSeed setup.wiring
      seed input references valid control serverBinding
    simp only [client, nativeClient, rejected, valid, not_false_eq_true, ite_true,
      simulateQ_bind, simulateQ_spec_query, simulateQ_pure, sessionImpl, evaluate_pure, pure_bind]


def nativeGet : NativeGame KemSK (GameState KemSK) := localState fun state => (state, state)
def nativeSet (value : GameState KemSK) : NativeGame KemSK Unit := localState fun _ => ((), value)
def nativeModify (change : GameState KemSK → GameState KemSK) : NativeGame KemSK Unit :=
  localState fun state => ((), change state)

theorem evaluate_get (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes) :
    evaluate setup seed scalar (get : Game KemSK (GameState KemSK)) = nativeGet :=
  evaluate_local setup seed scalar _

theorem evaluate_set (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (value : GameState KemSK) : evaluate setup seed scalar (set value) = nativeSet value :=
  evaluate_local setup seed scalar _

theorem evaluate_modify (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (change : GameState KemSK → GameState KemSK) :
    evaluate setup seed scalar (modify change) = nativeModify change :=
  evaluate_local setup seed scalar _

/-- The source build calls the original full native builder once for a present token and removes that token on every optional outcome. The original seal log and shared commitment cache are retained. -/
noncomputable def nativeBuild (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) : NativeGame KemSK (Option PqxdhServerRegistrationPublication.Response) := do
  let state ← nativeGet
  match state.pending session with
  | none => pure none
  | some token => do
      let result ← nativeCoins ((simulateQ (tailImpl setup codec checks)
        (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () state.server)).run
          ([], state.ctx))
      let settled := settle state.server result.1
      nativeSet { state with
        pending := Function.update state.pending session none
        server := settled.2
        ctx := result.2.2
        ghost := { state.ghost with seals := state.ghost.seals ++ result.2.1.map (fun context => (session, context)) } }
      pure settled.1

/-- The complete original Server build is the same native source computation, including every failed writer/commit and the entire installed state. -/
theorem build_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (session : Nat) (payload : Option Pqxdh.Bytes) :
    evaluate setup seed scalar (buildOracle setup codec checks session payload) =
      nativeBuild setup codec checks session payload := by
  simp only [buildOracle, nativeBuild, evaluate_bind, evaluate_get]
  apply bind_congr
  intro state
  cases state.pending session with
  | none => exact evaluate_pure setup seed scalar none
  | some token => simp only [evaluate_bind, evaluate_coins, evaluate_set, evaluate_pure]


/-- Native sampling retains the entire mapped reply before the subsequent continuation. -/
theorem nativeCoins_map {Result Next : Type} (f : Result → Next) (work : ProbComp Result) :
    nativeCoins (KemSK := KemSK) (f <$> work) = f <$> nativeCoins work := by
  funext state
  change (fun value => (value, state)) <$> (f <$> work) =
    (f <$> nativeCoins work).run state
  rw [StateT.run_map]
  change (fun value => (value, state)) <$> (f <$> work) =
    (fun result => (f result.1, result.2)) <$> ((fun value => (value, state)) <$> work)
  simp only [Functor.map_map]

noncomputable def nativePrefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    StateT (List Pqxdh.Bytes) ProbComp (Option (Inputs Reader ScalarBytes Word32)) :=
  simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed (serverAux setup codec checks)
    (fun _ => pure ())) (collect raw)

/-- Original native generation, validation and DH order under the full optional result and consumed-state continuation. -/
theorem native_prefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    nativePrefix setup codec checks seed raw =
      Option.map (concreteInputs setup.joint seed) <$> serverPrefix setup codec checks raw :=
  collect_realization setup.joint setup.serverDomain seed (serverAux setup codec checks) (fun _ => pure ()) raw

/-- Native local publication keeps the family state and passes the entire new game state to the continuation. -/
theorem nativeSet_bind {Result : Type} (value : GameState KemSK) (next : Unit → NativeGame KemSK Result)
    (state : NativeState KemSK) :
    (nativeSet value >>= next) state = next () (state.1, value) := rfl

/-- An actual raw Server accept: native source preparation, literal core acceptance, actual-input ROM root, clearing, consumed registration, and one pending-token publication. Every failed attempt still allocates its index. -/
noncomputable def nativeAccept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes) : NativeGame KemSK (Option Nat) := do
  let state ← nativeGet
  let index := state.sessions
  let collected ← nativeCoins ((nativePrefix setup codec checks seed raw).run state.server.consumed)
  nativeSet { state with sessions := index + 1, server := { state.server with consumed := collected.2 } }
  match collected.1 with
  | none => pure none
  | some input => do
      let returned ← nativeClient setup.hmac index state.server.control
        (binding setup (challenge setup.joint setup.dh seed scalar)) input
      match returned with
      | .ok (some token) => do
          nativeModify fun current => { current with pending := Function.update current.pending index (some token) }
          pure (some index)
      | _ => pure none

set_option backward.isDefEq.respectTransparency false in
/-- Whole native raw acceptance equals the executable API, with the exact original session index and complete pending/server/ghost/family state. Prefix provenance is derived from the reached source run. -/
theorem accept_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (raw : Pqxdh.Bytes) :
    evaluate setup seed scalar (acceptOracle setup codec checks (challenge setup.joint setup.dh seed scalar) raw) =
      nativeAccept setup codec checks seed scalar raw := by
  simp only [acceptOracle, nativeAccept, evaluate_bind, evaluate_get]
  apply bind_congr
  intro state
  rw [native_prefix, StateT.run_map, nativeCoins_map]
  simp only [evaluate_coins, evaluate_set, bind_map_left]
  funext primitive
  change (((fun value => (value, primitive)) <$>
    (serverPrefix setup codec checks raw).run state.server.consumed) >>= fun value => _) =
      (((fun value => (value, primitive)) <$>
        (serverPrefix setup codec checks raw).run state.server.consumed) >>= fun value => _)
  simp only [bind_map_left]
  apply OracleComp.bind_congr_of_forall_mem_support
  rintro ⟨input, consumed⟩ reached
  rw [nativeSet_bind, nativeSet_bind]
  cases input with
  | none => simp only [Option.map_none, evaluate_pure]
  | some input =>
      have references := collect_references setup.serverDomain (serverAux setup codec checks)
        (fun _ => pure ()) raw state.server.consumed consumed input reached
      simp only [Option.map_some, evaluate_bind,
        client_native setup seed scalar state.sessions state.server.control _ input references]
      have published (returned : RustM (Option Returned)) :
          evaluate setup seed scalar (match returned with
            | .ok (some token) => do
                modify fun current => { current with pending := Function.update current.pending state.sessions (some token) }
                pure (some state.sessions)
            | _ => pure none) =
          (match returned with
            | .ok (some token) => do
                nativeModify fun current => { current with pending := Function.update current.pending state.sessions (some token) }
                pure (some state.sessions)
            | _ => pure none) := by
        cases returned with
        | fail error => exact evaluate_pure setup seed scalar none
        | div => exact evaluate_pure setup seed scalar none
        | ok result => cases result <;> simp only [evaluate_bind, evaluate_modify, evaluate_pure]
      have same := congrArg (fun next => nativeClient setup.hmac state.sessions state.server.control
        (binding setup (challenge setup.joint setup.dh seed scalar))
        (concreteInputs setup.joint seed input) >>= next) (funext published)
      exact congrFun same _


/-- Pure result projection commutes with whole-state interpretation. -/
theorem evaluate_map {Result Next : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (f : Result → Next) (work : Game KemSK Result) :
    evaluate setup seed scalar (f <$> work) = f <$> evaluate setup seed scalar work := by
  rw [map_eq_bind_pure_comp, evaluate_bind]
  simp only [Function.comp_apply, evaluate_pure, bind_pure_comp]


/-- The actual native callback runs on the shared commitment cache, preserving all family, owner, pending and ghost fields. -/
def nativeCtx {Result : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp Result) :
    NativeGame KemSK Result := fun state =>
  (fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$>
    work.run ((), state.2.ctx)

theorem evaluate_ctx {Result : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp Result) :
    evaluate setup seed scalar (onCtx work) = nativeCtx work := by
  funext state
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (familyCoins (work.run ((), state.2.ctx)) >>= fun result => pure (result.1, { state.2 with ctx := result.2.2 }))).run state.1 =
      (fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$> work.run ((), state.2.ctx)
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [rom_coins]
  simp only [bind_pure_comp, Functor.map_map]


/-- The original Beacon observer precedes the actual root callback; no result or state is exposed by the annotation. -/
noncomputable def nativeBeaconRoot (hmac : HmacSha512) (publicValue : PublicChallenge)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (input : pqxdh.RootKeyInput) :
    NativeGame KemSK (Option Word32) := do
  nativeTouch (.beacon (PqxdhPhase2DhStage.sourceMessage publicValue original))
  romRootReply hmac publicValue original input

set_option backward.isDefEq.respectTransparency false in
/-- The concrete Beacon root logs its actual source descriptor before deriving the same restricted-table value. -/
theorem beacon_root_native (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : PqxdhPhase2GapDhSource.References setup.beaconDomain pending.collected)
    (converted : PqxdhPhase2GapDhSource.peer pending.collected.serverConverted = (setup.joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel setup.dh scalar original pending) :
    evaluate setup seed scalar (simulateQ beaconFamily
      (PqxdhPhase2DhRootConsumer.root (challenge setup.joint setup.dh seed scalar) pending)) =
      nativeBeaconRoot setup.hmac (challenge setup.joint setup.dh seed scalar) original original.candidate.root_key_input := by
  simp only [PqxdhPhase2DhRootConsumer.root, simulateQ_map, simulateQ_spec_query,
    beaconFamily, evaluate_map, evaluate_bind, evaluate_touch, nativeBeaconRoot]
  rw [evaluate_forward, map_bind, PqxdhPhase2DhStage.source_message setup.dh scalar _ original pending related]
  apply bind_congr
  intro _
  funext state
  have same := congrFun (beacon_root_rom (A := GameState KemSK) setup.hmac setup.dh setup.beaconDomain seed scalar
    original pending references converted related) state
  simp only [PqxdhPhase2DhRootConsumer.root, simulateQ_map, simulateQ_spec_query] at same
  exact same

/-- The original executable tail callbacks, retained separately from their native implementation. -/
noncomputable def beaconTailImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhPhase2DhRootConsumer.Spec Response) (Game KemSK)
  | .inl query => beaconFamily query
  | .inr query => onCtx (beaconNative setup codec query)

/-- The literal original tail runs with only its source root callback changed to the restricted Extract table. -/
noncomputable def nativeBeaconTail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (original : PqxdhBeaconPhase2Preparation.Prepared Response) :
    NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged) :=
  simulateQ (PqxdhPhase2DhRootConsumer.withRoot (nativeBeaconRoot setup.hmac publicValue original)
    (fun query => nativeCtx (beaconNative setup codec query)))
    (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.tail codec.frameRead original))

set_option backward.isDefEq.respectTransparency false in
/-- The actual post-root initializer, application getter, raw receive and all publication gates retain their optional replies and complete shared state. -/
theorem beacon_tail_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (scalar : ScalarBytes)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (references : PqxdhPhase2GapDhSource.References setup.beaconDomain pending.collected)
    (converted : PqxdhPhase2GapDhSource.peer pending.collected.serverConverted = (setup.joint.publicKeys seed).convertedX25519)
    (related : PqxdhPhase2DhMetadata.ReadyRel setup.dh scalar original pending) :
    evaluate setup seed scalar (simulateQ (beaconTailImpl setup codec)
      (PqxdhPhase2DhRootConsumer.tail (challenge setup.joint setup.dh seed scalar) codec.frameRead pending)) =
      nativeBeaconTail setup codec (challenge setup.joint setup.dh seed scalar) original := by
  have familyEq : beaconTailImpl setup codec ∘ₛ PqxdhPhase2DhRootConsumer.rootLift = beaconFamily := by
    funext query
    exact simulateQ_spec_query (beaconTailImpl setup codec) _
  have nativeEq : beaconTailImpl setup codec ∘ₛ PqxdhPhase2DhRootConsumer.nativeLift =
      (fun query => onCtx (beaconNative setup codec query)) := by
    funext query
    exact simulateQ_spec_query (beaconTailImpl setup codec) _
  unfold nativeBeaconTail
  rw [PqxdhPhase2DhRootConsumer.tail_root]
  simp only [PqxdhPhase2DhRootConsumer.tail, simulateQ_bind, ← QueryImpl.simulateQ_compose, familyEq,
    evaluate_bind, beacon_root_native setup seed scalar original pending references converted related]
  apply bind_congr
  intro value
  cases value with
  | none => exact evaluate_pure setup seed scalar none
  | some value =>
      rw [← QueryImpl.simulateQ_compose, nativeEq]
      simp only [evaluate_program, evaluate_ctx]
      rw [QueryImpl.simulateQ_compose,
        PqxdhPhase2DhRootConsumer.afterRoot_source setup.dh scalar codec.frameRead original pending related value]

/-- Complete stateless prefix work is evaluated once in source order with its entire native continuation. -/
theorem evaluate_unit {ι' Result : Type} {spec : OracleSpec ι'} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (handler : QueryImpl spec (StateT Unit ProbComp))
    (work : OracleComp spec Result) :
    evaluate setup seed scalar (simulateQ (liftUnit handler) work) =
      nativeCoins ((simulateQ handler work).run' ()) := by
  rw [simulateQ_liftUnit, evaluate_coins]

/-- The actual public conversion callback supplies its literal source conversion, including optional rejection. -/
theorem beacon_conversion (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (server : Word32) (initial after : Unit) (converted : Word32)
    (supported : (some converted, after) ∈ support
      ((beaconAuxUnit setup codec beaconSeed (.publicConversion server)).run initial)) :
    setup.source.crypto.xpkConv (absBytes server) = some (absBytes converted) := by
  simp only [beaconAuxUnit, beaconAux, StateT.run_lift, pure_bind, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at supported
  obtain ⟨found, _⟩ := supported
  cases hconv : setup.source.crypto.xpkConv (absBytes server) with
  | none => simp [hconv] at found
  | some bytes =>
      simp only [hconv, Option.bind_some] at found
      rw [toWord32_some bytes converted found.symm]

/-- Literal original preparation, with the selected scalar used only by the native mathematical source interpreter. -/
noncomputable def nativeBeaconPrefix (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    StateT Unit ProbComp (Option (PqxdhBeaconPhase2Preparation.Prepared Response)) :=
  simulateQ (PqxdhPhase2GapDhSource.nativeImpl setup.dh scalar (beaconAuxUnit setup codec beaconSeed)
    (fun _ => pure ()))
    (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw)

/-- Source prepare then the literal original tail; complete transient source metadata remains private for its existing analysis observer. -/
noncomputable def nativeBeaconStage (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged) := do
  let prepared ← nativeCoins ((nativeBeaconPrefix setup codec scalar beaconSeed control identity oneTime kem raw).run' ())
  match prepared with
  | none => pure none
  | some original => nativeBeaconTail setup codec (challenge setup.joint setup.dh seed scalar) original


/-- The whole native coin computation precedes its complete stateful continuation without changing either state coordinate. -/
theorem nativeCoins_bind {Result Next : Type} (work : ProbComp Result)
    (next : Result → NativeGame KemSK Next) (state : NativeState KemSK) :
    (nativeCoins work >>= next) state = work >>= fun value => next value state := by
  change (((fun value => (value, state)) <$> work) >>= fun result => next result.1 result.2) = _
  rw [bind_map_left]
set_option backward.isDefEq.respectTransparency false in
/-- Full actual Beacon preparation and native record continuation equal the related-DH stage on the same cache and observer state. Source prefix support supplies every reference and input relation. -/
theorem beacon_stage_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent)
    (pin : absBytes control.expected_server_binding.identity_public_key = (setup.joint.publicKeys seed).ed25519.toList)
    (identity : Unit) (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    evaluate setup seed scalar (simulateQ (stageImpl setup codec beaconSeed)
      (PqxdhPhase2DhStage.stage (challenge setup.joint setup.dh seed scalar) codec.frameRead control identity oneTime kem raw)) =
      nativeBeaconStage setup codec seed scalar beaconSeed control identity oneTime kem raw := by
  have preEq : stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.prefixLift =
      liftUnit (KemSK := KemSK) (PqxdhPhase2GapDhSource.prefixImpl setup.beaconDomain
        (beaconAuxUnit setup codec beaconSeed) (fun _ => pure ())) := by
    funext query
    exact simulateQ_spec_query (stageImpl setup codec beaconSeed) _
  have tailEq : stageImpl setup codec beaconSeed ∘ₛ PqxdhPhase2DhStage.tailLift = beaconTailImpl setup codec := by
    funext query
    cases query <;> exact simulateQ_spec_query (stageImpl setup codec beaconSeed) _
  simp only [nativeBeaconStage, PqxdhPhase2DhStage.stage, simulateQ_bind, ← QueryImpl.simulateQ_compose,
    preEq, evaluate_bind, evaluate_unit]
  funext initial
  simp only [nativeCoins_bind, StateT.run'_eq, bind_map_left, nativeBeaconPrefix]
  symm
  apply PqxdhPhase2DhMetadata.prepare_converted_continuation setup.dh setup.beaconDomain scalar setup.source.crypto
    (beaconAuxUnit setup codec beaconSeed) (fun value initial converted final => beacon_conversion setup codec beaconSeed value initial final converted)
    (fun _ => pure ()) (fun _ => rfl) control identity oneTime kem raw ()
  · intro final
    exact congrFun (evaluate_pure setup seed scalar none).symm initial
  · intro original pending final references converted admitted related
    have actualConversion := PqxdhPhase2DhMetadata.pinned_conversion setup.source.crypto setup.joint
      setup.secretOfSeed setup.wiring seed control pending.collected pending.metadata pin admitted converted
    change nativeBeaconTail setup codec (challenge setup.joint setup.dh seed scalar) original initial =
      evaluate setup seed scalar (simulateQ (stageImpl setup codec beaconSeed)
        (simulateQ PqxdhPhase2DhStage.tailLift
          (PqxdhPhase2DhRootConsumer.tail (challenge setup.joint setup.dh seed scalar) codec.frameRead pending))) initial
    rw [← QueryImpl.simulateQ_compose, tailEq,
      beacon_tail_native setup codec seed scalar original pending references actualConversion related]

/-- The local native read returns the complete original game state without changing either coordinate. -/
theorem nativeGet_bind {Result : Type} (next : GameState KemSK → NativeGame KemSK Result)
    (state : NativeState KemSK) : (nativeGet >>= next) state = next state.2 state := rfl

/-- The original active-phase finish runs source preparation, its whole record tail, and literal native final publication or abort. Inactive calls retain both states. -/
noncomputable def nativeFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) :
    NativeGame KemSK (Option Pqxdh.Bytes) := do
  let state ← nativeGet
  match state.beacon.beacon.phase with
  | .initSent control _ oneTime kem => do
      let staged ← nativeBeaconStage setup codec seed scalar beaconSeed control state.beacon.beacon.identity oneTime kem raw
      let current ← nativeGet
      let result := PqxdhBeaconPhase2Publication.finish control current.beacon staged
      nativeSet { current with beacon := result.2, ghost := current.ghost.accept (acceptedOf staged result.1) }
      pure result.1
  | _ => pure none

set_option backward.isDefEq.respectTransparency false in
/-- A reached pinned owner keeps the literal original finish result, full publication state and acceptance-time observer. Pinning is a source-state invariant proved by Phase 1, not a target authentication premise. -/
theorem finish_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : NativeState KemSK)
    (pin : ∀ control prekey oneTime kem, state.2.beacon.beacon.phase = .initSent control prekey oneTime kem →
      control.expected_server_binding = binding setup (challenge setup.joint setup.dh seed scalar)) :
    evaluate setup seed scalar (finishOracle setup codec (challenge setup.joint setup.dh seed scalar) beaconSeed raw) state =
      nativeFinish setup codec seed scalar beaconSeed raw state := by
  simp only [finishOracle, nativeFinish, evaluate_bind, evaluate_get, nativeGet_bind]
  cases phase : state.2.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [evaluate_bind]
      have pinned : absBytes control.expected_server_binding.identity_public_key =
          (setup.joint.publicKeys seed).ed25519.toList := by
        rw [pin control prekey oneTime kem phase]
        exact PqxdhRootTableInitialization.rootArray_bytes _
      rw [beacon_stage_native setup codec seed scalar beaconSeed control pinned]
      simp only [evaluate_get, evaluate_set, evaluate_pure]
  | _ => exact congrFun (evaluate_pure setup seed scalar none) state

/-- The public HMAC service keeps all real outside-domain evaluations and uses the same restricted table on the admitted Extract slice. -/
noncomputable def nativeHmac (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : HmacBlock) (message : Pqxdh.Bytes) : NativeGame KemSK HmacBlock := do
  if key = zeroSalt ∧ message.length = 192 then
    nativeTouch (.adversary message)
  PqxdhServerRelatedRootConsumer.familyImpl
    (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
    (.inr (.publicHmac key message))

/-- Native public HMAC and its original observer retain the whole cache/history and all local state. -/
theorem hmac_native (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (key : HmacBlock) (message : Pqxdh.Bytes) :
    evaluate setup seed scalar (hmacOracle key message) = nativeHmac setup seed scalar key message := by
  by_cases slice : key = zeroSalt ∧ message.length = 192
  · simp only [hmacOracle, nativeHmac, slice, and_self, ite_true, evaluate_bind, evaluate_touch]
    rw [evaluate_forward]
  · simp only [hmacOracle, nativeHmac, slice, ite_false]
    exact evaluate_forward setup seed scalar _

/-- The original shared BLAKE2b cache is evaluated directly; the family and all other fields remain untouched. -/
noncomputable def nativeHash (bytes : Pqxdh.Bytes) : NativeGame KemSK CtxRomAuth.CtxDigest := fun state =>
  (fun result => (result.1, (state.1, { state.2 with ctx := result.2 }))) <$>
    (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2.ctx

/-- The native public hash is the literal original probabilistic cache service. -/
theorem hash_native (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (scalar : ScalarBytes)
    (bytes : Pqxdh.Bytes) : evaluate setup seed scalar (hashOracle bytes) = nativeHash bytes := by
  funext state
  change (fun result => (result.1.1, (result.2, result.1.2))) <$>
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (familyCoins ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2.ctx) >>= fun result =>
        pure (result.1, { state.2 with ctx := result.2 }))).run state.1 = _
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [rom_coins]
  simp only [bind_pure_comp, Functor.map_map, nativeHash]

/-- Independent native API: literal Server/Beacon source operations and the original public primitive/reveal services. No private family descriptor is accepted from the adversary. -/
noncomputable def nativeHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) :
    QueryImpl ServerAuthSpec (NativeGame KemSK)
  | .inl coin => PqxdhServerRelatedRootConsumer.familyImpl
      (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction) (.inl coin)
  | .inr (.accept raw) => nativeAccept setup codec checks seed scalar raw
  | .inr (.build session payload) => nativeBuild setup codec checks session payload
  | .inr (.finish raw) => nativeFinish setup codec seed scalar beaconSeed raw
  | .inr (.hmac key message) => nativeHmac setup seed scalar key message
  | .inr (.hash bytes) => nativeHash bytes
  | .inr (.reveal keyId) => localState fun state => (revealKernel keyId state, state)

/-- Every API query agrees at an original reachable invariant state; no success, target-honesty or cryptographic freshness conclusion is assumed. -/
theorem handler_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed)
    (query : ServerAuthSpec.Domain) (state : NativeState KemSK)
    (invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2) :
    evaluate setup seed scalar (authHandler setup codec checks (challenge setup.joint setup.dh seed scalar) beaconSeed query) state =
      nativeHandler setup codec checks seed scalar beaconSeed query state := by
  rcases query with coin | query
  · exact congrFun (evaluate_forward setup seed scalar _) state
  cases query with
  | accept raw => exact congrFun (accept_native setup codec checks seed scalar raw) state
  | build session payload => exact congrFun (build_native setup codec checks seed scalar session payload) state
  | finish raw => exact finish_native setup codec seed scalar beaconSeed raw state invariant.pinned
  | hmac key message => exact congrFun (hmac_native setup seed scalar key message) state
  | hash bytes => exact congrFun (hash_native setup seed scalar bytes) state
  | reveal keyId => exact congrFun (evaluate_local setup seed scalar _) state

/-- Concrete interpretation only selects source-supported replies; this transports the existing operational invariant through the same whole-state run. -/
theorem evaluate_support {Result : Type} (setup : Setup baseSpec KemSK)
    (seed : IdentitySeed) (scalar : ScalarBytes) (work : Game KemSK Result)
    (state : NativeState KemSK) (result : Result × NativeState KemSK)
    (supported : result ∈ support (evaluate setup seed scalar work state)) :
    (result.1, result.2.2) ∈ support (work.run state.2) := by
  simp only [evaluate, support_map, Set.mem_image] at supported
  obtain ⟨⟨⟨value, after⟩, family⟩, seen, rfl⟩ := supported
  apply OracleComp.support_simulateQ_run'_subset
    (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ seen

/-- Run equation for the complete native bind, retaining both state coordinates before continuation. -/
theorem native_bind_run {Result Next : Type} (first : NativeGame KemSK Result)
    (next : Result → NativeGame KemSK Next) (state : NativeState KemSK) :
    (first >>= next) state = first state >>= fun result => next result.1 result.2 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary adaptive scheduling uses the same native API and full original state. Every reached invariant is derived through the original supported transition, including all rejected and post-acceptance requests. -/
theorem program_native {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed)
    (work : OracleComp ServerAuthSpec Result) (state : NativeState KemSK)
    (invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state.2) :
    evaluate setup seed scalar
      (simulateQ (authHandler setup codec checks (challenge setup.joint setup.dh seed scalar) beaconSeed) work) state =
      (simulateQ (nativeHandler setup codec checks seed scalar beaconSeed) work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => exact congrFun (evaluate_pure setup seed scalar value) state
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evaluate_bind, native_bind_run, StateT.run]
      rw [← handler_native setup codec checks seed scalar beaconSeed query state invariant]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      exact ih result.1 result.2 ((authHandler_step codec checks beaconSeed query state.2
        (result.1, result.2.2) (evaluate_support setup seed scalar _ state result supported)).1 invariant)

/-- Keep both complete final states while discarding only the adversary's unit result, exactly as the original experiment body does. -/
theorem run_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed)
    (work : OracleComp ServerAuthSpec Unit) (state : GameState KemSK) (family : PqxdhJointDhExtractFamily.State)
    (invariant : GameInv Reader Response setup (challenge setup.joint setup.dh seed scalar) state) :
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (Prod.snd <$> (simulateQ (authHandler setup codec checks (challenge setup.joint setup.dh seed scalar) beaconSeed) work).run state)).run family =
      (fun result => (result.2.2, result.2.1)) <$>
        (simulateQ (nativeHandler setup codec checks seed scalar beaconSeed) work).run (family, state) := by
  have same := congrArg (fun result => (fun value => (value.2.2, value.2.1)) <$> result)
    (program_native setup codec checks seed scalar beaconSeed work (family, state) invariant)
  simp only [evaluate, Functor.map_map] at same
  simp only [simulateQ_map, StateT.run_map]
  exact same

/-- Native setup follows the exact chosen experiment order, executes literal Phase 1, then the native adaptive API. All random generation and KEM work remain inside this program. -/
noncomputable def nativeBody (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (adversary : Adversary) (revealed : Option IdentitySeed)
    (family : PqxdhJointDhExtractFamily.State) : ProbComp (GameState KemSK × PqxdhJointDhExtractFamily.State) := do
  let beaconSeed ← sampleSeed
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let publicValue := challenge setup.joint setup.dh seed scalar
  let published ← phase1Run setup codec beaconSeed publicValue oneTime keys.1 keys.2
  let input : AuthInput := ⟨publicValue.identity, setup.serverKeyId, published.1, revealed⟩
  (fun result => (result.2.2, result.2.1)) <$>
    (simulateQ (nativeHandler setup codec checks seed scalar beaconSeed) (adversary input)).run
      (family, initialGameState setup publicValue published.2)

set_option backward.isDefEq.respectTransparency false in
/-- Source setup and Phase 1 supply the operational invariant before the full native adaptive execution. All generator draws and the complete continuation remain in their original experiment order. -/
theorem body_native (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (scalar : ScalarBytes) (adversary : Adversary) (revealed : Option IdentitySeed)
    (family : PqxdhJointDhExtractFamily.State) :
    (simulateQ (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ reduction)
      (body setup codec checks adversary revealed (challenge setup.joint setup.dh seed scalar))).run family =
      nativeBody setup codec checks seed scalar adversary revealed family := by
  simp only [body, nativeBody, simulateQ_bind, StateT.run_bind, rom_coins, bind_map_left]
  apply bind_congr
  intro beaconSeed
  apply bind_congr
  intro oneTime
  apply bind_congr
  intro keys
  apply OracleComp.bind_congr_of_forall_mem_support
  intro published supported
  exact run_native setup codec checks seed scalar beaconSeed _ _ family
    (inv_initial setup codec beaconSeed (challenge setup.joint setup.dh seed scalar) oneTime keys.1 keys.2 published supported)

/-- Independently written native complete experiment; only the approved Extract slice is interpreted by its shared table. -/
noncomputable def actualState (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    ProbComp (IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State) := do
  let seed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let result ← nativeBody setup codec checks seed scalar adversary (if revealSeed then some seed else none)
    PqxdhJointDhExtractFamily.empty
  pure (seed, scalar, result.1, result.2)

/-- The complete joint distribution includes every private/public protocol field, observer entry and shared primitive cache. -/
theorem actual_state (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    actualState setup codec checks revealSeed adversary = gameState setup codec checks revealSeed adversary := by
  simp only [actualState, gameState, body_native]

/-- Native source authentication event under the same exact approved experiment and compromise policy. -/
noncomputable def actual (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp Bool := by
  classical
  exact (fun result => decide (Win setup result.1 result.2.1 result.2.2.1.ghost)) <$>
    actualState setup codec checks revealSeed adversary

/-- The native execution and original executable experiment have the same full event, with no added security premise or reduction loss. -/
theorem actual_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    actual setup codec checks revealSeed adversary = serverAuthGame setup codec checks revealSeed adversary := by
  rw [actual, actual_state]
  rfl

/-- The selected prekey and locally generated one-time scalar occupy distinct actual source fields. This is an operational handle invariant, with no byte inequality premise. -/
def Handles (beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK) : Prop :=
  ∀ control prekey oneTime kem, beacon.beacon.phase = .initSent control prekey oneTime kem →
    prekey = .inl () ∧ ∃ scalar, oneTime = .inr scalar

/-- Literal Phase 1 creates the handle invariant; it is never supplied as an honest-owner assumption. -/
theorem phase1_handles (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (result : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (supported : result ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk)) :
    Handles result.2 := by
  simp only [phase1Run, PqxdhLivePhase1Bundle.bundle, freshBeacon, simulateQ_bind, simulateQ_spec_query,
    phase1Impl, pure_bind] at supported
  intro control prekey other kem phase
  simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_some,
    simulateQ_bind, mem_support_bind_iff] at supported
  obtain ⟨signed, _, supported⟩ := supported
  cases signed with
  | none =>
      simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases phase
  | some bundle =>
      simp only [PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning,
        PqxdhBeaconPhase1Publication.prepare, Option.map_some, simulateQ_bind, simulateQ_spec_query,
        mem_support_bind_iff] at supported
      obtain ⟨written, _, supported⟩ := supported
      cases written with
      | none =>
          simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          cases phase
      | some bytes =>
          simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          simp only [PqxdhBeaconPhase1Publication.publish, RawCtxBeaconLifecycle.Phase.initSent.injEq] at phase
          exact ⟨phase.2.1.symm, oneTime, phase.2.2.1.symm⟩

/-- Every actual API transition preserves the original handle provenance or erases InitSent at its one-shot finish. -/
theorem handler_handles (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (query : ServerAuthSpec.Domain)
    (state : GameState KemSK) (result : ServerAuthSpec.Range query × GameState KemSK)
    (supported : result ∈ support ((authHandler setup codec checks publicValue beaconSeed query).run state))
    (handles : Handles state.beacon) : Handles result.2.beacon := by
  by_cases finished : ∃ raw, query = .inr (.finish raw)
  · obtain ⟨raw, rfl⟩ := finished
    have inactive := (finish_step codec beaconSeed raw state result supported).2.2.2.1
    intro control prekey oneTime kem phase
    exact False.elim (inactive ⟨control, prekey, oneTime, kem, phase⟩)
  · have unchanged := (authHandler_step codec checks beaconSeed query state result supported).2.2.2.2
      (fun raw same => finished ⟨raw, same⟩)
    rw [unchanged]
    exact handles

/-- The source-derived handle invariant is retained through an arbitrary adaptive complete schedule. -/
theorem run_handles {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (work : OracleComp ServerAuthSpec Result)
    (state : GameState KemSK) (result : Result × GameState KemSK)
    (supported : result ∈ support ((simulateQ (authHandler setup codec checks publicValue beaconSeed) work).run state))
    (handles : Handles state.beacon) : Handles result.2.beacon :=
  run_rel (authHandler setup codec checks publicValue beaconSeed)
    (fun before after => Handles before.beacon → Handles after.beacon)
    (fun _ => id) (fun _ _ _ left right => right ∘ left)
    (fun query before after supported => handler_handles setup codec checks publicValue beaconSeed query before after supported)
    work state result supported handles

/-- Native callbacks use the actually stored selected-prekey handle directly; locally owned scalars and every other source callback retain their original implementation. -/
noncomputable def sourceBeaconAux (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response) (StateT Unit ProbComp)
  | .dhPair (.inl ()) point => pure (Option.map PqxdhPhase2GapDhSource.word (setup.dh.dh scalar (PqxdhPhase2GapDhSource.peer point)))
  | query => beaconAuxUnit setup codec beaconSeed query

set_option backward.isDefEq.respectTransparency false in
/-- The internal selected-handle embedding performs exactly the literal source collection with the original prekey and one-time fields, before its complete continuation. -/
theorem collect_handles (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (identity : Unit)
    (oneTime : ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    simulateQ (sourceBeaconAux setup codec scalar beaconSeed)
      (PqxdhBeaconPhase2Preparation.collect identity (.inl ()) (.inr oneTime) kem raw) =
      simulateQ (PqxdhPhase2GapDhSource.nativeImpl setup.dh scalar (beaconAuxUnit setup codec beaconSeed) (fun _ => pure ()))
        (PqxdhBeaconPhase2Preparation.collect identity (.inl ()) (.inr (.inr oneTime)) kem raw) := by
  simp only [PqxdhBeaconPhase2Preparation.collect, OptionT.run_bind, OptionT.run_mk,
    OptionT.run_pure, OptionT.run_monadLift, Option.elimM, simulateQ_bind, simulateQ_spec_query,
    sourceBeaconAux, PqxdhPhase2GapDhSource.nativeImpl]
  repeat' (
    first | rfl | (congr 1; funext reply; cases reply) | (split <;> simp_all only)
    all_goals simp only [Option.elim, simulateQ_bind, simulateQ_spec_query,
      simulateQ_pure, sourceBeaconAux, PqxdhPhase2GapDhSource.nativeImpl, pure_bind])

/-- The native source preparation consumes the actual stored fields, including original rejection and shared-secret erasure, without a new private-key assumption. -/
theorem prepare_handles (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    simulateQ (sourceBeaconAux setup codec scalar beaconSeed)
      (PqxdhBeaconPhase2Preparation.prepare control identity (.inl ()) (.inr oneTime) kem raw) =
      nativeBeaconPrefix setup codec scalar beaconSeed control identity (.inr oneTime) kem raw := by
  simp only [nativeBeaconPrefix, PqxdhBeaconPhase2Preparation.prepare, simulateQ_bind, collect_handles]
  apply bind_congr
  intro collected
  cases collected with
  | none => simp only [simulateQ_pure]
  | some collected =>
      simp only [PqxdhBeaconPhase2Preparation.afterInputs, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, sourceBeaconAux, PqxdhPhase2GapDhSource.nativeImpl]

/-- Erase only the proof's two analysis logs. All original private fields, pending tokens, role states, counters and both actual primitive caches remain. -/
def eraseObservers (state : NativeState KemSK) : NativeState KemSK :=
  (⟨[], state.1.cache⟩, { state.2 with ghost := Ghost.empty })

/-- Uninstrumented actual root callback: read the same table on the supplied native 192-byte input, then perform real Expand. No source descriptor or ephemeral encoding is reconstructed from DH bytes. -/
noncomputable def sourceRoot (hmac : HmacSha512) (input : pqxdh.RootKeyInput) :
    NativeGame KemSK (Option Word32) := fun state =>
  (fun result => (some (PqxdhRootTableInitialization.rootArray (expandRoot hmac result.1)),
    ({ state.1 with cache := result.2 }, state.2))) <$>
    (HmacOracle.randomOracle (absBytes input.bytes)).run state.1.cache

/-- The observer append has no effect on either real cache or any native source field. -/
theorem nativeTouch_bind {Result : Type} (touch : Touch) (next : Unit → NativeGame KemSK Result)
    (state : NativeState KemSK) :
    (nativeTouch touch >>= next) state = next ()
      (state.1, { state.2 with ghost := { state.2.ghost with touches := state.2.ghost.touches ++ [touch] } }) := rfl

/-- Logging the native Beacon root is a pure observation of the exact source callback, including its complete source/cache poststate. -/
theorem root_observation (hmac : HmacSha512) (publicValue : PublicChallenge)
    (original : PqxdhBeaconPhase2Preparation.Prepared Response) (input : pqxdh.RootKeyInput)
    (state : NativeState KemSK) :
    Prod.map id eraseObservers <$> nativeBeaconRoot hmac publicValue original input state =
      sourceRoot hmac input (eraseObservers state) := by
  simp only [nativeBeaconRoot, nativeTouch_bind, romRootReply]
  change Prod.map id eraseObservers <$> (romRootReply hmac publicValue original input).run
    (state.1, { state.2 with ghost := { state.2.ghost with touches := state.2.ghost.touches ++
      [.beacon (PqxdhPhase2DhStage.sourceMessage publicValue original)] } }) = _
  rw [romRootReply, StateT.run_map]
  simp only [romRootBytes, StateT.run, sourceRoot, eraseObservers, Functor.map_map]
  rfl

/-- Shared native tail effects commute with erasing only the analysis observers. -/
theorem ctx_observation {Result : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp Result)
    (state : NativeState KemSK) :
    Prod.map id eraseObservers <$> nativeCtx work state = nativeCtx work (eraseObservers state) := by
  simp only [nativeCtx, eraseObservers, Functor.map_map]
  rfl

/-- Literal native tail callbacks: the supplied input bytes select the root table entry, while every other callback runs its original source implementation. -/
noncomputable def sourceBeaconTail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (NativeGame KemSK) :=
  PqxdhPhase2DhRootConsumer.withRoot (sourceRoot setup.hmac) (fun query => nativeCtx (beaconNative setup codec query))

/-- Every annotated source tail callback erases to its concrete original callback; no transcript-derived context is assumed. -/
theorem tail_callback_observation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) (state : NativeState KemSK) :
    Prod.map id eraseObservers <$>
      (PqxdhPhase2DhRootConsumer.withRoot (nativeBeaconRoot setup.hmac publicValue original)
        (fun query => nativeCtx (beaconNative setup codec query)) query).run state =
      (sourceBeaconTail setup codec query).run (eraseObservers state) := by
  rcases query with query | (input | request | response)
  · exact ctx_observation _ state
  · exact root_observation setup.hmac publicValue original input state
  · exact ctx_observation _ state
  · exact ctx_observation _ state

/-- The entire original native tail, including all optional replies and full caches/private fields, is unchanged by its analysis annotations. -/
theorem tail_observation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (original : PqxdhBeaconPhase2Preparation.Prepared Response)
    (state : NativeState KemSK) :
    Prod.map id eraseObservers <$> nativeBeaconTail setup codec publicValue original state =
      (simulateQ (sourceBeaconTail setup codec)
        (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
          (PqxdhBeaconPhase2Publication.tail codec.frameRead original))).run (eraseObservers state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ eraseObservers
    (tail_callback_observation setup codec publicValue original) _ state

/-- Source stateless callback lifting retains the complete continuation and ambient native state, including every generation or decapsulation coin. -/
theorem native_unit_program {ι' Result : Type} {spec : OracleSpec ι'}
    (handler : QueryImpl spec (StateT Unit ProbComp)) (work : OracleComp spec Result) :
    simulateQ (fun query => nativeCoins (KemSK := KemSK) ((handler query).run' ())) work =
      nativeCoins ((simulateQ handler work).run' ()) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      funext state
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, nativeCoins, map_pure]
      rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, ih]
      funext state
      rw [nativeCoins_bind]
      simp only [StateT.run'_eq, StateT.run_bind, nativeCoins, map_bind, bind_map_left, Functor.map_map]

/-- Complete uninstrumented source stage with the literal stored private handles and original root/tail callbacks. -/
noncomputable def sourceBeaconStage (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (prekey oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) :
    NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged) := do
  let prepared ← nativeCoins ((simulateQ (sourceBeaconAux setup codec scalar beaconSeed)
    (PqxdhBeaconPhase2Preparation.prepare control identity prekey oneTime kem raw)).run' ())
  match prepared with
  | none => pure none
  | some original =>
      simulateQ (sourceBeaconTail setup codec)
        (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
          (PqxdhBeaconPhase2Publication.tail codec.frameRead original))

/-- The complete prepared native stage is an observation of the actual source stage using its literal stored prekey and one-time handles. -/
theorem stage_observation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent)
    (identity : Unit) (oneTime : ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes) (state : NativeState KemSK) :
    Prod.map id eraseObservers <$>
      nativeBeaconStage setup codec seed scalar beaconSeed control identity (.inr oneTime) kem raw state =
      sourceBeaconStage setup codec scalar beaconSeed control identity (.inl ()) (.inr oneTime) kem raw (eraseObservers state) := by
  simp only [nativeBeaconStage, sourceBeaconStage, prepare_handles, nativeCoins_bind, map_bind]
  apply bind_congr
  intro prepared
  cases prepared with
  | none => rfl
  | some original => exact tail_observation setup codec (challenge setup.joint setup.dh seed scalar) original state

/-- The whole original source owner receives direct native preparation and tail callbacks, with the two actual caches shared across every request. -/
noncomputable def sourceBeaconHandler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response) (NativeGame KemSK)
  | .inl query => nativeCoins ((sourceBeaconAux setup codec scalar beaconSeed query).run' ())
  | .inr query => sourceBeaconTail setup codec query

/-- This operation is the literal existing nativeOwner program, including its original private field selection, finish gates, abort and complete publication. -/
noncomputable def sourceFinish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes) :
    NativeGame KemSK (Option Pqxdh.Bytes) := do
  let state ← nativeGet
  let result ← simulateQ (sourceBeaconHandler setup codec scalar beaconSeed)
    (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw state.beacon)
  nativeModify fun current => { current with beacon := result.2 }
  pure result.1

/-- Native primitive callbacks can update the actual caches but cannot publish or alter any protocol field; publication remains in the original owner continuation. -/
theorem source_callback_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Domain)
    (state : NativeState KemSK)
    (result : (PqxdhBeaconPhase2Publication.NativeSpec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response).Range query × NativeState KemSK)
    (supported : result ∈ support ((sourceBeaconHandler setup codec scalar beaconSeed query).run state)) :
    result.2.2 = { state.2 with ctx := result.2.2.ctx } := by
  rcases query with query | query
  · simp only [sourceBeaconHandler, nativeCoins, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    rfl
  · rcases query with query | (input | request | response)
    all_goals simp only [sourceBeaconHandler, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot,
      nativeCtx, sourceRoot, StateT.run, support_map, Set.mem_image] at supported
    all_goals obtain ⟨value, _, rfl⟩ := supported
    all_goals rfl

/-- The complete original native owner executes before any surrounding state installation; every unrelated field survives all codec/crypto failures and callbacks. -/
theorem source_program_fields {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed)
    (work : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec Unit (Unit ⊕ ScalarBytes) KemSK Unit Response) Result)
    (state : NativeState KemSK) (result : Result × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (sourceBeaconHandler setup codec scalar beaconSeed) work).run state)) :
    result.2.2 = { state.2 with ctx := result.2.2.ctx } := by
  apply run_rel (sourceBeaconHandler setup codec scalar beaconSeed)
    (fun before after => after.2 = { before.2 with ctx := after.2.ctx })
    (fun _ => rfl) _ (source_callback_fields setup codec scalar beaconSeed) work state result supported
  intro before middle after left right
  rw [right, left]

set_option backward.isDefEq.respectTransparency false in
/-- The source stage is exactly the existing nativeOwner program before its literal finish projection, on the actual stored private fields. -/
theorem source_owner_stage (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : Unit ⊕ ScalarBytes) (kem : KemSK)
    (phase : beacon.beacon.phase = .initSent control prekey oneTime kem) :
    simulateQ (sourceBeaconHandler setup codec scalar beaconSeed)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw beacon) =
      PqxdhBeaconPhase2Publication.finish control beacon <$>
        sourceBeaconStage setup codec scalar beaconSeed control beacon.beacon.identity prekey oneTime kem raw := by
  have preEq : sourceBeaconHandler setup codec scalar beaconSeed ∘ₛ
      (PqxdhBeaconPhase2Publication.nativeAdapter ∘ₛ PqxdhBeaconPhase2Publication.preLift) =
      (fun query => nativeCoins ((sourceBeaconAux setup codec scalar beaconSeed query).run' ())) := by
    funext query
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.preLift, simulateQ_spec_query,
      PqxdhBeaconPhase2Publication.nativeAdapter, sourceBeaconHandler]
  have tailEq : (sourceBeaconHandler setup codec scalar beaconSeed ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) ∘ₛ
      PqxdhBeaconPhase2Publication.tailLift = sourceBeaconTail setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeTailAdapter := by
    funext query
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.tailLift, simulateQ_spec_query,
      PqxdhBeaconPhase2Publication.nativeAdapter, ← QueryImpl.simulateQ_compose]
    congr 1
    funext nativeQuery
    exact simulateQ_spec_query (sourceBeaconHandler setup codec scalar beaconSeed) _
  simp only [PqxdhBeaconPhase2Publication.nativeOwner, ← QueryImpl.simulateQ_compose,
    PqxdhBeaconPhase2Publication.owner, phase, simulateQ_bind, preEq, native_unit_program,
    sourceBeaconStage, map_bind]
  apply bind_congr
  intro prepared
  cases prepared with
  | none => simp only [simulateQ_pure, map_pure]
  | some original =>
      simp only [bind_pure_comp, simulateQ_map, ← QueryImpl.simulateQ_compose, tailEq]

/-- The literal source stage has no state-installation side effect; every protocol field is retained until the actual owner publishes or aborts. -/
theorem source_stage_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : NativeState KemSK) (control : pqxdh.BeaconInitSent) (prekey oneTime : Unit ⊕ ScalarBytes) (kem : KemSK)
    (phase : state.2.beacon.beacon.phase = .initSent control prekey oneTime kem)
    (result : Option PqxdhBeaconPhase2Publication.Staged × NativeState KemSK)
    (supported : result ∈ support (sourceBeaconStage setup codec scalar beaconSeed control
      state.2.beacon.beacon.identity prekey oneTime kem raw state)) :
    result.2.2 = { state.2 with ctx := result.2.2.ctx } := by
  apply source_program_fields setup codec scalar beaconSeed
    (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw state.2.beacon) state
    (PqxdhBeaconPhase2Publication.finish control state.2.beacon result.1, result.2)
  rw [source_owner_stage setup codec scalar beaconSeed raw state.2.beacon control prekey oneTime kem phase,
    StateT.run_map, support_map]
  exact Set.mem_image_of_mem _ supported

/-- Running a native pure reply preserves both complete state coordinates. -/
theorem native_pure_run {Result : Type} (value : Result) (state : NativeState KemSK) :
    (pure value : NativeGame KemSK Result) state = pure (value, state) := rfl

/-- Native result mapping retains the complete state and evaluated computation. -/
theorem native_map_run {Result Next : Type} (f : Result → Next) (work : NativeGame KemSK Result)
    (state : NativeState KemSK) :
    (f <$> work) state = Prod.map f id <$> work state := by
  exact StateT.run_map f work state

/-- After erasing analysis observers, the actual native finish is the existing nativeOwner operation on exactly its stored source state and both real caches. -/
theorem finish_observation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) (scalar : ScalarBytes) (beaconSeed : IdentitySeed) (raw : Pqxdh.Bytes)
    (state : NativeState KemSK) (handles : Handles state.2.beacon) :
    Prod.map id eraseObservers <$> nativeFinish setup codec seed scalar beaconSeed raw state =
      sourceFinish setup codec scalar beaconSeed raw (eraseObservers state) := by
  simp only [nativeFinish, sourceFinish, nativeGet_bind]
  cases phase : state.2.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
      obtain ⟨rfl, known, rfl⟩ := handles control prekey oneTime kem phase
      have erasedBeacon : (eraseObservers state).2.beacon = state.2.beacon := rfl
      rw [erasedBeacon, source_owner_stage setup codec scalar beaconSeed raw state.2.beacon control (.inl ()) (.inr known) kem phase]
      simp only [native_bind_run, native_map_run, map_bind, bind_map_left]
      rw [← stage_observation setup codec seed scalar beaconSeed control state.2.beacon.beacon.identity known kem raw state,
        bind_map_left]
      apply OracleComp.bind_congr_of_forall_mem_support
      intro result supported
      have sourceSeen : (result.1, eraseObservers result.2) ∈ support
          (sourceBeaconStage setup codec scalar beaconSeed control state.2.beacon.beacon.identity
            (.inl ()) (.inr known) kem raw (eraseObservers state)) := by
        rw [← stage_observation setup codec seed scalar beaconSeed control state.2.beacon.beacon.identity known kem raw state,
          support_map]
        exact Set.mem_image_of_mem _ supported
      have fields := source_stage_fields setup codec scalar beaconSeed raw (eraseObservers state)
        control (.inl ()) (.inr known) kem phase (result.1, eraseObservers result.2) sourceSeen
      have sameBeacon := congrArg GameState.beacon fields
      change result.2.2.beacon = state.2.beacon at sameBeacon
      simp only [nativeGet, nativeSet, nativeModify, localState, pure_bind, native_pure_run, map_pure, Prod.map,
        sameBeacon, eraseObservers]
      rfl
  | _ =>
      simp only [PqxdhBeaconPhase2Publication.nativeOwner, PqxdhBeaconPhase2Publication.owner,
        eraseObservers, phase, simulateQ_pure]
      rfl

/-- Every reachable native prefix obtains the stored-handle premise from the literal Phase-1 execution. The subsequent finish is the original source owner after erasing only analysis observers. -/
theorem reachable_finish_observation {Result : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (seed : IdentitySeed) (scalar oneTime : ScalarBytes)
    (beaconSeed : IdentitySeed) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (published : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (publication : published ∈ support
      (phase1Run setup codec beaconSeed (challenge setup.joint setup.dh seed scalar) oneTime kemPk kemSk))
    (work : OracleComp ServerAuthSpec Result) (family : PqxdhJointDhExtractFamily.State)
    (result : Result × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (nativeHandler setup codec checks seed scalar beaconSeed) work).run
      (family, initialGameState setup (challenge setup.joint setup.dh seed scalar) published.2)))
    (raw : Pqxdh.Bytes) :
    Prod.map id eraseObservers <$> nativeFinish setup codec seed scalar beaconSeed raw result.2 =
      sourceFinish setup codec scalar beaconSeed raw (eraseObservers result.2) := by
  have original := supported
  rw [← program_native setup codec checks seed scalar beaconSeed work _
    (inv_initial setup codec beaconSeed (challenge setup.joint setup.dh seed scalar)
      oneTime kemPk kemSk published publication)] at original
  exact finish_observation setup codec seed scalar beaconSeed raw result.2
    (run_handles setup codec checks (challenge setup.joint setup.dh seed scalar) beaconSeed work _ _
      (evaluate_support setup seed scalar _ _ _ original)
      (phase1_handles setup codec beaconSeed (challenge setup.joint setup.dh seed scalar)
        oneTime kemPk kemSk published publication))

/-- Both constructor-order swaps preserve the evaluated distribution of an arbitrary complete continuation, not merely the marginal key distributions. The KEM program includes its entire actual base interpretation. -/
theorem constructor_order {Result : Type} [MeasurableSpace Result] (setup : Setup baseSpec KemSK)
    (next : IdentitySeed → ScalarBytes → IdentitySeed → ScalarBytes →
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) → ProbComp Result) :
    𝒟[do
      let seed ← sampleSeed
      let scalar ← PqxdhJointGapDh.sampleScalar
      let beaconSeed ← sampleSeed
      let oneTime ← PqxdhJointGapDh.sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      next seed scalar beaconSeed oneTime keys] =
    𝒟[do
      let seed ← sampleSeed
      let beaconSeed ← sampleSeed
      let scalar ← PqxdhJointGapDh.sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      let oneTime ← PqxdhJointGapDh.sampleScalar
      next seed scalar beaconSeed oneTime keys] := by
  apply EvalDistEq.evalDist_eq
  refine EvalDistEq.bind_right _ fun seed => ?_
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun beaconSeed => ?_
  refine EvalDistEq.bind_right _ fun scalar => ?_
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

/-- Native setup in literal source constructor order: Server identity, Beacon identity, Beacon prekey, KEM, then the Phase-1 one-time key. The complete source Phase 1 and native adaptive continuation are unchanged. -/
noncomputable def sourceOrderedState (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    ProbComp (IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State) := do
  let seed ← sampleSeed
  let beaconSeed ← sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  let oneTime ← PqxdhJointGapDh.sampleScalar
  let publicValue := challenge setup.joint setup.dh seed scalar
  let published ← phase1Run setup codec beaconSeed publicValue oneTime keys.1 keys.2
  let input : AuthInput := ⟨publicValue.identity, setup.serverKeyId, published.1, if revealSeed then some seed else none⟩
  let result ← (simulateQ (nativeHandler setup codec checks seed scalar beaconSeed) (adversary input)).run
    (PqxdhJointDhExtractFamily.empty, initialGameState setup publicValue published.2)
  pure (seed, scalar, result.2.2, result.2.1)

/-- Source-order initialization preserves the entire evaluated native experiment, including every private/public field, both caches and all analysis histories. -/
theorem actual_source_order [MeasurableSpace
    (IdentitySeed × ScalarBytes × GameState KemSK × PqxdhJointDhExtractFamily.State)]
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    𝒟[actualState setup codec checks revealSeed adversary] =
      𝒟[sourceOrderedState setup codec checks revealSeed adversary] := by
  simp only [actualState, nativeBody, sourceOrderedState, bind_assoc, bind_map_left]
  exact constructor_order setup _

/-- The original authentication event evaluated after literal source-order setup and the complete native protocol. -/
noncomputable def sourceOrdered (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) : ProbComp Bool := by
  classical
  exact (fun result => decide (Win setup result.1 result.2.1 result.2.2.1.ghost)) <$>
    sourceOrderedState setup codec checks revealSeed adversary

/-- The source-order native authentication experiment has exactly the original event distribution. Both setup swaps are checked against the full continuation, with no additional security premise or loss. -/
theorem source_order_game (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (revealSeed : Bool) (adversary : Adversary) :
    𝒟[sourceOrdered setup codec checks revealSeed adversary] =
      𝒟[serverAuthGame setup codec checks revealSeed adversary] := by
  rw [← actual_game setup codec checks revealSeed adversary]
  simp only [sourceOrdered, actual, sourceOrderedState, actualState, nativeBody,
    map_bind, bind_assoc, bind_map_left, map_pure]
  exact (constructor_order setup _).symm

end Experiment
end BeaconcryptCore.Computational.PqxdhServerAuthNative

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.root_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.root_rom
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.client_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.client_rom
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.server_stage_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.server_stage_rom
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_root_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_root_rom
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_tail_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_tail_rom
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_stage_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_stage_rom
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_local
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_coins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_forward' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_forward
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_touch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_touch
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.session_root_rom' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.session_root_rom
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_consume' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_consume
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.client_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.client_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_get
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_set' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_set
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_modify' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_modify
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.build_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.build_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeCoins_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeCoins_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.native_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.native_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeSet_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeSet_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.accept_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_ctx
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_root_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_root_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_tail_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_tail_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_unit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_unit
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_conversion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_conversion
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeCoins_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeCoins_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_stage_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.beacon_stage_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeGet_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeGet_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.finish_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.finish_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.hmac_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.hmac_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.hash_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.hash_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.handler_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.handler_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.evaluate_support
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.native_bind_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.native_bind_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.program_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.program_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.run_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.run_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.body_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.body_native
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.actual_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.actual_state
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.actual_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.actual_game
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.phase1_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.phase1_handles
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.handler_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.handler_handles
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.run_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.run_handles
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.collect_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.collect_handles
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.prepare_handles' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.prepare_handles
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeTouch_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.nativeTouch_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.root_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.root_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.ctx_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.ctx_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.tail_callback_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.tail_callback_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.tail_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.tail_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.native_unit_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.native_unit_program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.stage_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.stage_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.source_callback_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.source_callback_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.source_program_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.source_program_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.source_owner_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.source_owner_stage
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.source_stage_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.source_stage_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.native_pure_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.native_pure_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.native_map_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.native_map_run
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.finish_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.finish_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.reachable_finish_observation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.reachable_finish_observation
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.constructor_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.constructor_order
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.actual_source_order' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.actual_source_order
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthNative.source_order_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthNative.source_order_game

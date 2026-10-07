-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentReplay
import BeaconcryptCore.Computational.RawCtxReceiveConsumption

/-! Kernel provenance for record replay in the common deployment experiment (CE-6, CE-C3). The record replay invariant needs, for every record kernel, the source receive relation of `RawCtxReceiveConsumption.ConsumedRefines`: the concrete kernel refines an abstract send and receive state over the fixed functional HKDF of the setup's source, its send chain is aligned with its origin, and every consumed receive position is below the receive counter and absent from the skipped-key cache. The source14 schedule creates kernels at two places only. A Server build installs a peer at the key ID of its committed candidate, which the extracted `server_prepare_commit` admits only when that key ID is free, with the candidate's initial kernel advanced by the first registration send, which consumes nothing (`build_live`, `buildOracle_peers`). A Beacon finish establishes its owner with the initial kernel of its root advanced by the source receive that accepted the registration record at sequence one, so exactly the position of sequence one is consumed (`tail_finished`, `finish_owners`). Every other registration command keeps every peer kernel and every established kernel; creation appends a Fresh owner and a bundle never establishes one (`source_step`, `create_owners`, `bundle_owners`). The statements are deterministic support facts about the source programs under the setup's actual primitives; no codec law and no security assumption is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity RawCtxMaterialPositions
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- A ratchet kernel related to the source receive and send states, with nothing consumed yet. -/
def Live (c : Pqxdh.Crypto) (kernel : ConcreteRatchetKernel) : Prop :=
  ∃ sendOrigin receiveOrigin, RawCtxReceiveConsumption.ConsumedRefines c sendOrigin receiveOrigin kernel []

/-- Any consumption invariant of a kernel gives a live kernel. -/
theorem live_of_consumed {c : Pqxdh.Crypto} {sendOrigin receiveOrigin : RatchetChain} {kernel : ConcreteRatchetKernel}
    {spent : List Nat} (consumed : RawCtxReceiveConsumption.ConsumedRefines c sendOrigin receiveOrigin kernel spent) :
    Live c kernel := by
  obtain ⟨send, receive, refines, aligned, _, _⟩ := consumed
  exact ⟨sendOrigin, receiveOrigin, send, receive, refines, aligned, fun _ member => by simp at member, List.nodup_nil⟩

/-- The cache projection of the native state. -/
def cacheOf (state : NativeState KemSK) : RawCtxSharedPrimitive.SharedState Unit := ((), state.2.ctx)

/-- The receive callbacks of a Beacon finish run the source receive primitives on the shared cache. -/
theorem finish_receive (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {Result : Type}
    (work : OracleComp RawCtxWholeOwner.PrimitiveSpec Result) (state : NativeState KemSK) :
    Prod.map id cacheOf <$> (simulateQ (fun query =>
      (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter)
        (.inr (.inl query))) work).run state =
      (simulateQ (RawCtxReceiveConsumption.receiveNative setup.source) work).run (cacheOf state) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ cacheOf (fun query current => ?_) work state
  change Prod.map id cacheOf <$> (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
      (simulateQ PqxdhBeaconPhase2Publication.nativeTailLift
        (simulateQ PqxdhBeaconPhase2Publication.nativeRawLift (RawCtxSourceOpen.nativeAdapter query)))).run current =
    (simulateQ (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source))
      (RawCtxSourceOpen.nativeAdapter query)).run (cacheOf current)
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  refine map_run_simulateQ_eq_of_query_map_eq _ _ cacheOf (fun request inner => ?_) _ current
  simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeRawLift,
    PqxdhBeaconPhase2Publication.nativeTailLift, simulateQ_spec_query]
  change Prod.map id cacheOf <$> nativeCtx (RawCtxSharedPrimitive.nativeImpl setup.source.crypto
    (RawCtxSourceHkdf.kdfImpl setup.source) request) inner = _
  simp only [nativeCtx, Functor.map_map, cacheOf]
  exact id_map _

/-- A kernel related to the source receive and send states that has consumed exactly the receive position of sequence one, the registration record. -/
def Finished (c : Pqxdh.Crypto) (kernel : ConcreteRatchetKernel) : Prop :=
  ∃ sendOrigin receiveOrigin, RawCtxReceiveConsumption.ConsumedRefines c sendOrigin receiveOrigin kernel [0]

/-- The kernel staged by a successful Beacon finish tail is the initial kernel of its root after one source receive that accepted sequence one. -/
theorem tail_finished (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (state final : NativeState KemSK)
    (staged : PqxdhBeaconPhase2Publication.Staged)
    (supported : (some staged, final) ∈ support ((simulateQ (fun query =>
      (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ PqxdhBeaconPhase2Publication.nativeAdapter) (.inr query))
      (PqxdhBeaconPhase2Publication.tail codec.frameRead prepared)).run state)) :
    Finished setup.source.crypto staged.kernel := by
  obtain ⟨root, intermediate, _, after⟩ := PqxdhBeaconPhase2Publication.tail_supported _ codec.frameRead prepared state
    final staged supported
  obtain ⟨initial, initialState, raw, appState, received, initialMember, _, rawMember, _, opening⟩ :=
    PqxdhBeaconPhase2Publication.afterRoot_supported _ codec.frameRead prepared root intermediate final staged after
  obtain ⟨openedReply, sequenceOne, sameKernel, _⟩ :=
    PqxdhBeaconPhase2Publication.afterOpening_success _ _ _ staged opening
  have value : initial = RawCtxSourceHkdf.initialResponse setup.source.crypto
      (PqxdhInitialRatchetComplementarity.beaconPending root).request := by
    simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.nativeAdapter,
      PqxdhBeaconPhase2Publication.nativeTailAdapter, PqxdhBeaconPhase2Publication.nativeTailLift,
      simulateQ_spec_query] at initialMember
    change (initial, initialState) ∈ support (nativeCtx (pure (RawCtxSourceHkdf.initialResponse setup.source.crypto
      (PqxdhInitialRatchetComplementarity.beaconPending root).request)) intermediate) at initialMember
    simp only [nativeCtx, StateT.run_pure, map_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq]
      at initialMember
    exact initialMember.1
  have initialized : BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon root
      (RawCtxSourceHkdf.initialResponse setup.source.crypto) = ok (PqxdhBeaconPhase2Publication.normalInitial
        (PqxdhInitialRatchetComplementarity.beaconPending root) initial) := by
    rw [BeaconcryptCore.Refinement.PqxdhConcreteSession.initializeBeacon_eq, value,
      ← PqxdhBeaconPhase2Publication.normalInitial_exact]
    rfl
  have invariant := RawCtxReceiveConsumption.initialized_spent setup.source.crypto root _ (Or.inl initialized)
  have projected := finish_receive setup codec ((RawCtxWholeOwner.rawReceive codec.frameRead raw).run
    (PqxdhBeaconPhase2Publication.localOwner (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
      (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) initial)))
    appState
  have member : (received.1, cacheOf received.2) ∈ support (RawCtxWholeOwner.rawGame
      (RawCtxReceiveConsumption.receiveNative setup.source) codec.frameRead raw
      (PqxdhBeaconPhase2Publication.localOwner (PqxdhBeaconPhase2Publication.clearedCandidate prepared.candidate)
        (PqxdhBeaconPhase2Publication.normalInitial (PqxdhInitialRatchetComplementarity.beaconPending root) initial))
      (cacheOf appState)) := by
    unfold RawCtxWholeOwner.rawGame
    rw [← projected, support_map]
    exact ⟨received, rawMember, rfl⟩
  have consumed := RawCtxReceiveConsumption.raw_spent setup.source _ _ [] codec.frameRead raw _ invariant
    (cacheOf appState) _ member
  simp only [openedReply, RawCtxReceiveConsumption.recordReply, sequenceOne] at consumed
  rw [sameKernel]
  exact ⟨_, _, consumed⟩

/-- The source primitives of the first registration send are the shared record primitives on the same cache. -/
theorem registration_send {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (work : OracleComp RawCtxSourceSend.PrimitiveSpec Result) :
    simulateQ (PqxdhRegistrationProtocolState.registrationImpl (A := Unit) setup.source codec.frameWrite
        (tailAux codec checks))
      (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (simulateQ PqxdhServerRegistrationPublication.sendLift work)) =
      simulateQ (RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl
        setup.source))
        (simulateQ RawCtxMixedOwner.sendAdapter work) := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  simp only [QueryImpl.apply_compose, PqxdhServerRegistrationPublication.sendLift, RawCtxMixedOwner.sendAdapter,
    simulateQ_spec_query, PqxdhServerRegistrationPublication.nativeAdapter]
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext request
  simp only [QueryImpl.apply_compose, simulateQ_spec_query]
  rfl

/-- The first registration send keeps a live kernel live. -/
theorem send_live (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (kernel : ConcreteRatchetKernel) (context : RawCtxSourceSend.SealContext) (live : Live setup.source.crypto kernel)
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (sent : (ConcreteRatchetKernel × Option RawCtxSourceSend.Encrypted) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : sent ∈ support ((simulateQ (tailImpl setup codec checks)
      (simulateQ PqxdhServerRegistrationPublication.sendLift
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))).run primitive)) :
    Live setup.source.crypto sent.1.1 := by
  obtain ⟨sendOrigin, receiveOrigin, invariant⟩ := live
  have native := tail_native setup codec checks (simulateQ PqxdhServerRegistrationPublication.sendLift
    (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))) primitive
  rw [registration_send] at native
  have member : Prod.map id forgetAux sent ∈ support ((simulateQ (RawCtxMixedShared.sharedImpl setup.source.crypto
      codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source)) (simulateQ RawCtxMixedOwner.sendAdapter
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))).run (forgetAux primitive)) := by
    rw [← native, support_map]
    exact ⟨sent, supported, rfl⟩
  exact live_of_consumed (RawCtxReceiveConsumption.native_send_spent setup.source codec.frameWrite sendOrigin
    receiveOrigin [] kernel context invariant (forgetAux primitive) _ member)

/-- The initial Server kernel of a registration root is live. -/
theorem initial_live (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (root : PqxdhSecretInputKdf.RootOutput) :
    ∃ kernel, PqxdhRootTableInitialization.initialKernelRun source false root = ok kernel ∧ Live source.crypto kernel :=
      by
  obtain ⟨kernel, initialized, _, _, refines⟩ := PqxdhRootTableInitialization.initialize_refines source
    (RawCtxReceiveConsumption.crypto source.crypto) false root
  exact ⟨kernel, initialized, kernel.refined.send_chain, kernel.refined.receive_chain, _, _, refines, rfl,
    fun _ member => by simp at member, List.nodup_nil⟩

/-- A Server registration result that installs nothing, or installs the committed candidate with a live kernel. -/
def LivePublication (c : Pqxdh.Crypto) (candidate : pqxdh.ServerRegistrationCandidate)
    (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))) : Prop :=
  result = ok (none, state) ∨ ∃ kernel bytes, Live c kernel ∧
    result = ok (some ⟨bytes, candidate.key_id⟩, PqxdhServerRegistrationPublication.publish state candidate kernel ())

/-- The first-send tail installs only a live kernel. -/
theorem after_live (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : ConcreteRatchetKernel)
    (live : Live setup.source.crypto kernel)
    (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((simulateQ (tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.afterInitialization candidate authenticated kernel () state)).run primitive))
        :
    LivePublication setup.source.crypto candidate state (ok result.1) := by
  obtain ⟨sent, afterSend, afterErase, sentMember, _, rest⟩ :=
    PqxdhServerRegistrationPublication.afterInitialization_support _ candidate authenticated kernel () state primitive
      result supported
  have advanced := send_live setup codec checks kernel _ live primitive (sent, afterSend) sentMember
  cases hs : sent.2 with
  | none => rw [hs] at rest; rw [rest]; exact Or.inl rfl
  | some encrypted =>
      rw [hs] at rest
      obtain ⟨written, afterWrite, _, same⟩ := rest
      rw [same]
      cases written with
      | none => exact Or.inl rfl
      | some bytes => exact Or.inr ⟨sent.1, bytes, advanced, rfl⟩

/-- Identity, allocation, payload and binding gates keep the live publication boundary. -/
theorem candidate_live (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (candidate : pqxdh.ServerRegistrationCandidate) (root : PqxdhSecretInputKdf.RootOutput) (payload : Option
      Pqxdh.Bytes)
    (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((simulateQ (tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.candidateTail setup.source candidate root payload () state)).run primitive)) :
    LivePublication setup.source.crypto candidate state result.1 := by
  obtain ⟨kernel, hrun, live⟩ := initial_live setup.source root
  have hinit := (PqxdhServerRegistrationPublication.candidate_initialization setup.source candidate root).trans hrun
  obtain ⟨binding, hbinding, _⟩ := PqxdhServerRegistrationPublication.candidate_binding candidate
  simp only [PqxdhServerRegistrationPublication.candidateTail, hinit, hbinding,
    PqxdhServerRegistrationPublication.continueRust, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨valid, afterIdentity⟩, _, supported⟩ := supported
  cases valid
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)
  simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reserved, afterReserve⟩, _, supported⟩ := supported
  cases reserved
  · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at supported
  split_ifs at supported with empty fits
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)
  · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨⟨allocated, afterAllocate⟩, _, supported⟩ := supported
    cases allocated
    · simp only [Bool.not_false, ite_true, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at supported
      exact Or.inl (congrArg Prod.fst supported)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, simulateQ_map, StateT.run_map,
      support_map, Set.mem_image] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact after_live setup codec checks candidate _ kernel live state afterAllocate inner reached
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    exact Or.inl (congrArg Prod.fst supported)

/-- A Server build installs nothing, or installs a live kernel at its candidate's key ID, which was free. -/
theorem build_live (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput) (payload : Option Pqxdh.Bytes)
    (state : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (primitive : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (result : RustM (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) ×
      RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext))
    (supported : result ∈ support ((simulateQ (tailImpl setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () state)).run primitive)) :
    result.1 = ok (none, state) ∨ ∃ candidate kernel bytes, state.server.peers candidate.key_id = none ∧
      Live setup.source.crypto kernel ∧
      result.1 = ok (some ⟨bytes, candidate.key_id⟩, PqxdhServerRegistrationPublication.publish state candidate kernel
        ()) := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [PqxdhServerRegistrationPublication.build, hnext, PqxdhServerRegistrationPublication.continueRust]
    at supported
  cases next with
  | Err error =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      exact Or.inl (congrArg Prod.fst supported)
  | Ok next =>
      obtain ⟨prepared, hprepared⟩ := BeaconcryptCore.PanicFreedom.server_prepare_commit_ok
        state.control pending ⟨state.server.identity, state.identityKeyId⟩
        (if (state.server.peers next).isSome then .Occupied else .Available)
      simp only [hprepared] at supported
      cases prepared with
      | Err error =>
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          exact Or.inl (congrArg Prod.fst supported)
      | Ok candidate =>
          rcases candidate_live setup codec checks candidate root payload state primitive result supported
            with unchanged | ⟨kernel, bytes, live, published⟩
          · exact Or.inl unchanged
          · obtain ⟨available, key⟩ := PqxdhDeploymentCompileRegistration.prepare_key _ _ _ _ candidate hprepared
            rw [hnext] at key
            have sameKey : next = candidate.key_id := by
              cases key
              rfl
            subst sameKey
            have free : state.server.peers candidate.key_id = none := by
              by_contra occupied
              rw [Option.isSome_iff_ne_none.mpr occupied] at available
              simp at available
            exact Or.inr ⟨candidate, kernel, bytes, free, live, published⟩

/-- The established kernel of a Server peer. -/
def peerKernel (server : RawCtxServerRouting.Server Unit Unit) (kid : Std.U64) : Option ConcreteRatchetKernel :=
  (server.peers kid).map (·.kernel)

/-- A Server step keeps every peer kernel, except that a free key ID may receive a live kernel. -/
def PeerStep (c : Pqxdh.Crypto) (before after : RawCtxServerRouting.Server Unit Unit) : Prop :=
  ∀ kid, peerKernel after kid = peerKernel before kid ∨
    (peerKernel before kid = none ∧ ∃ kernel, peerKernel after kid = some kernel ∧ Live c kernel)

/-- The Server build oracle installs only a live kernel, at a free key ID. -/
theorem buildOracle_peers (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (session : Nat) (payload : Option Pqxdh.Bytes) (game : GameState KemSK)
    (result : Option PqxdhServerRegistrationPublication.Response × GameState KemSK)
    (supported : result ∈ support ((buildOracle setup codec checks session payload).run game)) :
    PeerStep setup.source.crypto game.server.server result.2.server.server := by
  simp only [buildOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  cases found : game.pending session with
  | none =>
      simp only [found, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact fun _ => Or.inl rfl
  | some token =>
      simp only [found, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨built, lifted, supported⟩ := supported
      obtain ⟨member, same⟩ := liftCoins_mem _ _ _ lifted
      simp only [same, StateT.run_set, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, rfl, rfl⟩ := supported
      rcases build_live setup codec checks token.pending token.root payload game.server _ built.1 member with
        unchanged | ⟨candidate, kernel, bytes, free, live, published⟩
      · simp only [unchanged, settle]
        exact fun _ => Or.inl rfl
      · intro kid
        simp only [published, settle, PqxdhServerRegistrationPublication.publish, peerKernel]
        by_cases same : kid = candidate.key_id
        · subst same
          right
          refine ⟨by simp only [free, Option.map_none], kernel, by simp, live⟩
        · left
          simp only [Function.update_of_ne same]

/-- The established kernel of an optional owner. -/
def ownerKernel (owner : Option (PqxdhRegistrationSchedule.Owner KemSK)) : Option ConcreteRatchetKernel :=
  match owner with
  | some owner =>
      match owner.beacon.phase with
      | .established _ _ kernel => some kernel
      | _ => none
  | none => none

/-- An owner-registry step that keeps every established kernel. -/
def OwnersSame (before after : List (PqxdhRegistrationSchedule.Owner KemSK)) : Prop :=
  ∀ index : Nat, ownerKernel after[index]? = ownerKernel before[index]?

/-- A Beacon finish keeps every other owner; a rejected finish keeps the addressed owner's established kernel, and a successful finish establishes, for an owner that had none, a kernel that consumed sequence one. -/
theorem finish_owners (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationSchedule.State KemSK) (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State
      KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.finish setup codec index raw).run state)) :
    (∀ other, other ≠ index → result.2.owners[other]? = state.owners[other]?) ∧
      (result.1 = none → ownerKernel result.2.owners[index]? = ownerKernel state.owners[index]?) ∧
      (∀ plaintext, result.1 = some plaintext → ownerKernel state.owners[index]? = none ∧
        ∃ kernel, ownerKernel result.2.owners[index]? = some kernel ∧ Finished setup.source.crypto kernel) := by
  cases found : state.owners[index]? with
  | none =>
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw state found, support_pure,
        Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨fun _ _ => rfl, fun _ => by
        show ownerKernel state.owners[index]? = _
        rw [found], fun _ reply => by cases reply⟩
  | some owner =>
      change result ∈ support (PqxdhRegistrationSchedule.finish setup codec index raw state) at supported
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw state owner found, support_map] at supported
      obtain ⟨reached, member, rfl⟩ := supported
      have bound := (List.getElem?_eq_some_iff.mp found).1
      refine ⟨fun other different => List.getElem?_set_ne (Ne.symm different), ?_, ?_⟩
      · intro rejected
        rw [List.getElem?_set_self bound]
        rcases reached with ⟨⟨reply, next⟩, final⟩
        change reply = none at rejected
        subst rejected
        have shape := PqxdhDeploymentEligibility.finish_failure setup codec raw owner state.shared next final member
        revert shape
        cases phase : owner.beacon.phase with
        | initSent control prekey oneTime kem =>
            intro shape
            subst shape
            simp [ownerKernel, PqxdhBeaconPhase2Preparation.abort, phase]
        | _ =>
            intro shape
            subst shape
            rfl
      · intro plaintext accepted
        rw [List.getElem?_set_self bound]
        rcases reached with ⟨⟨reply, next⟩, final⟩
        change reply = some plaintext at accepted
        subst accepted
        rw [PqxdhBeaconPhase2Publication.nativeOwner, ← QueryImpl.simulateQ_compose] at member
        obtain ⟨control, prekey, oneTime, kem, prepared, intermediate, staged, active, _, tailMember, _, _, _,
          published⟩ := PqxdhBeaconPhase2Publication.owner_success _ codec.frameRead raw plaintext owner next
            state.shared final member
        refine ⟨by simp [ownerKernel, active], staged.kernel, ?_,
          tail_finished setup codec prepared intermediate final staged tailMember⟩
        have equal := congrArg Prod.snd published
        change (PqxdhBeaconPhase2Publication.publish owner staged).2 = next at equal
        rw [← equal]
        simp [ownerKernel, PqxdhBeaconPhase2Publication.publish]

/-- A Phase 1 bundle never establishes an owner and keeps every established kernel. -/
theorem bundle_owners (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (index : Nat)
    (state : PqxdhRegistrationSchedule.State KemSK) (result : Option Pqxdh.Bytes × PqxdhRegistrationSchedule.State
      KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.bundle setup codec index).run state)) :
    OwnersSame state.owners result.2.owners := by
  cases found : state.owners[index]? with
  | none =>
      simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, found,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact fun _ => rfl
  | some owner =>
      change result ∈ support (PqxdhRegistrationSchedule.bundle setup codec index state) at supported
      rw [PqxdhRegistrationSchedule.bundle_source setup codec index state owner found, support_map] at supported
      obtain ⟨reached, member, rfl⟩ := supported
      have bound := (List.getElem?_eq_some_iff.mp found).1
      intro other
      by_cases same : other = index
      · subst same
        rw [List.getElem?_set_self bound, found]
        obtain ⟨rejected, published⟩ := PqxdhDeploymentEligibility.bundle_candidate setup codec other owner reached
          member
        cases reply : reached.1 with
        | none => rw [rejected reply]
        | some bytes =>
            obtain ⟨fresh, prekey, oneTime, kem, _, _, _, phase, next, _⟩ := published bytes reply
            rw [next]
            rcases phase with phase | phase <;> simp [ownerKernel, phase]
      · rw [List.getElem?_set_ne (Ne.symm same)]

/-- Creating an owner appends a Fresh owner and keeps every established kernel. -/
theorem create_owners (setup : Setup baseSpec KemSK) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) (result : Nat × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.create setup pin keyId).run state)) :
    OwnersSame state.owners result.2.owners := by
  obtain ⟨seed, prekey, keys, rfl⟩ := PqxdhDeploymentEligibility.create_support setup pin keyId state result supported
  intro index
  rcases lt_or_ge index state.owners.length with inside | outside
  · simp only [List.getElem?_append_left inside]
  · rw [List.getElem?_append_right outside, List.getElem?_eq_none outside]
    cases index - state.owners.length with
    | zero => rfl
    | succ _ => rfl

/-- Every request of the source14 schedule keeps every Server peer kernel, except that a build may install a live kernel at a free key ID, and every request other than a finish keeps every established kernel. -/
theorem source_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request)
    (state : PqxdhRegistrationSchedule.State KemSK)
    (result : PqxdhRegistrationSchedule.QuerySpec request × PqxdhRegistrationSchedule.State KemSK)
    (supported : result ∈ support ((PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run
      state)) :
    PeerStep setup.source.crypto state.shared.2.server.server result.2.shared.2.server.server ∧
      ((∀ index raw, request ≠ .finish index raw) → OwnersSame state.owners result.2.owners) := by
  have ownerServer : PqxdhRegistrationSchedule.IsOwnerQuery (.inr request) →
      PeerStep setup.source.crypto state.shared.2.server.server result.2.shared.2.server.server := by
    intro isOwner
    rw [PqxdhRegistrationSchedule.owner_fields setup codec checks serverSeed _ isOwner state result supported]
    exact fun _ => Or.inl rfl
  rcases request with ⟨pin, keyId⟩ | index | raw | ⟨session, payload⟩ | ⟨index, raw⟩ | ⟨key, message⟩ | bytes | keyId
  · exact ⟨ownerServer trivial, fun _ => create_owners setup pin keyId state result supported⟩
  · exact ⟨ownerServer trivial, fun _ => bundle_owners setup codec index state result supported⟩
  · simp only [PqxdhRegistrationSchedule.handler,
      ← accept_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar] at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state result supported
    obtain ⟨server, _⟩ := PqxdhDeploymentCompileFootprint.accept_footprint setup codec checks _ raw _ _ reached
    have same : result.2.shared.2.server.server = state.shared.2.server.server := server
    exact ⟨fun _ => Or.inl (by rw [peerKernel, peerKernel, same]), fun _ _ => by rw [owners]⟩
  · simp only [PqxdhRegistrationSchedule.handler,
      ← build_native setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar] at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state result supported
    exact ⟨buildOracle_peers setup codec checks session payload _ _ reached, fun _ _ => by rw [owners]⟩
  · exact ⟨ownerServer trivial, fun notFinish => absurd rfl (notFinish index raw)⟩
  · simp only [PqxdhRegistrationSchedule.handler, ← hmac_native setup serverSeed
      PqxdhRegistrationSchedule.observationScalar]
      at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state result supported
    obtain ⟨server, _⟩ := PqxdhDeploymentCompileFootprint.hmac_fixed key message _ _ reached
    have same : result.2.shared.2.server.server = state.shared.2.server.server := server
    exact ⟨fun _ => Or.inl (by rw [peerKernel, peerKernel, same]), fun _ _ => by rw [owners]⟩
  · simp only [PqxdhRegistrationSchedule.handler, ← hash_native setup serverSeed
      PqxdhRegistrationSchedule.observationScalar]
      at supported
    obtain ⟨owners, reached⟩ :=
      PqxdhDeploymentCompileInvariant.shared_footprint setup serverSeed _ state result supported
    obtain ⟨server, _⟩ := PqxdhDeploymentCompileFootprint.hash_fixed bytes _ _ reached
    have same : result.2.shared.2.server.server = state.shared.2.server.server := server
    exact ⟨fun _ => Or.inl (by rw [peerKernel, peerKernel, same]), fun _ _ => by rw [owners]⟩
  · simp only [PqxdhRegistrationSchedule.handler, PqxdhRegistrationSchedule.onShared_run, localState, support_map,
      support_pure, Set.mem_image, Set.mem_singleton_iff] at supported
    obtain ⟨_, rfl, rfl⟩ := supported
    exact ⟨fun _ => Or.inl rfl, fun _ _ => rfl⟩

end BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.live_of_consumed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.live_of_consumed

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.finish_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.finish_receive

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.tail_finished' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.tail_finished

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.registration_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.registration_send

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.send_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.send_live

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.initial_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.initial_live

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.after_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.after_live

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.candidate_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.candidate_live

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.build_live

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.buildOracle_peers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.buildOracle_peers

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.finish_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.finish_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.bundle_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.bundle_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.create_owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.create_owners

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentRecordKernels.source_step

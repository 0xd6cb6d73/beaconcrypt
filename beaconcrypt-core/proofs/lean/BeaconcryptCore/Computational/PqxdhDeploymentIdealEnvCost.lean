-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRootCostsClient

/-!
# Cost bounds of the ideal environment's commands (CE-11b, unit U3 remainder)

The effect bounds that the frames `PqxdhDeploymentIdealFrame.frame_ideal` and `frame_idealD` need (design-v2 section 6.3, C2a), for every command of the ideal step `PqxdhDeploymentIdealEnv.idealStep` and from every environment state, under `PqxdhServerAuthSourceCosts.KemBound setup caps`:

- Slot reads (`slotLazy_step`, `slotRun_total`): against the allocator in front of the lazy material service a slot read draws nothing at a cached slot, the slot's 44-byte material at a fresh slot with room, and a fresh 108-byte `PqxdhServerAuthKeySchedule.Output` (`output_bound`) when the allocator is full (its no-room branch). The weight `wSlot` charges 1 per coin and 108 per slot read.
- The selected accept (`acceptSelected_bound`): at most `140 + encapsCost` coin effects and nothing else. On a key match it draws the ephemeral (32 coins before encapsulation, `beforeLogged_cost`), nothing after the encapsulation (the challenge ciphertext replaces it, `suffix_cost`) and one slot read for its root (`tailCE_cost`, from the marker tail's single root request); otherwise it is the logged accept (`96 + encapsCost`, `acceptInactive_cost`). This covers the no-room branch at the accept class: 32 + 108 = 140 is within the real accept's `96 + encapsCost` plus the 44 first-touch coins.
- The pool create (`createPoolStep_bound`): within the real create allowance (`64 + keygenCost`; the key generation is drawn only beyond the pool, `createPool_uniform`).
- Owner k's challenge finish (`finishChallenge_bound`): at most `decapsCost + 108` coin effects (one decapsulation in the preparation, `preparation_cost`, and one slot read or one 64-byte Extract value in the grouped request, `groupEnv_bound`), at most one BLAKE2b effect and at most one administrative effect. This covers the no-room branch at the finish class.
- The challenger's draws (`drawParams_uniform`): at most `(count + 1) * keygenCost + encapsCost` coins.
- `idealStep_bound`: every command of the ideal step stays within `PqxdhDeploymentEnvironment.allowanceG (baseAllowance caps) ceFirstTouch` of its class (plan sections 31, 33 and 35, unchanged), with the marked build from `PqxdhDeploymentIdealEnv.idealStep_build_bound` and every other command from `PqxdhDeploymentEnvironment.realStep_bound`.

These are resource bounds in the existing cost model; they add no assumption and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthSourceCosts (KemCaps KemBound serverClass serverUniformCost)
open PqxdhRegistrationJointKemRootCosts (WBound wBound_pure wBound_bind wBound_map wBound_mono wBound_query
  wBound_query_bind wBound_run wBound_simulate wBound_of_total wBound_of_isQueryBoundP isQueryBoundP_of_wBound
  wBound_weight_mono)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealKernel (MatCache SeedCache lazyDummy)
open PqxdhRegistrationJointKemSecondEntry (Alloc slotImpl)
open PqxdhServerAuthNative (NativeState)

variable {KemSK : Type}

/-! ### Slot reads against the allocator in front of the lazy material service -/

section Slots

set_option maxRecDepth 100000 in
/-- One 108-byte key-schedule output draws at most 108 coins. -/
theorem output_bound : ($ᵗ PqxdhServerAuthKeySchedule.Output : ProbComp PqxdhServerAuthKeySchedule.Output).IsTotalQueryBound
    108 := by
  simp only [← PqxdhFullSecretInputKdf.pairSample]
  exact isTotalQueryBound_bind
    (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 76) (fun full =>
      isTotalQueryBound_bind
        (CtxComputationalSecurity.uniformFixedBytes_isTotalQueryBound 32) (fun root =>
          show (pure (full, root) : ProbComp PqxdhServerAuthKeySchedule.Output).IsTotalQueryBound 0 from by trivial))

/-- The weights of a slot client: one per coin and 108 per slot read (the largest draw of a read: a fresh 108-byte value when the allocator is full). -/
def wSlot : SlotSpec.Domain → ℕ
  | .inl _ => 1
  | .inr _ => 108

/-- One read of the lazy material service draws at most 44 coins. -/
theorem lazyDummy_bound (j : PqxdhRecordLiftInterface.Slot 2) (s : MatCache 2 × SeedCache 2) :
    ((lazyDummy j).run s).IsTotalQueryBound 44 := by
  change ((fun m => PqxdhDeploymentHiddenLayout.joinOutput m PqxdhDeploymentHiddenSplit.dummySeed) <$>
    (LazyOracleDiscard.StateLens.fst (MatCache 2) (SeedCache 2)).query
      (spec := PqxdhDeploymentSeedSplit.MaterialSpec 2) j).run s |>.IsTotalQueryBound 44
  rw [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff]
  exact PqxdhDeploymentEnvironment.materialQuery_bound _ j s

set_option maxRecDepth 100000 in
/-- Every step of the allocator in front of the lazy material service draws at most the weight of its request. -/
theorem slotLazy_step (query : SlotSpec.Domain) (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) :
    WBound ((slotImpl lazyDummy query).run state) (fun _ => 1) (wSlot query) := by
  rcases query with coin | point
  · rw [PqxdhRegistrationJointKemSecondEntry.slot_coin]
    exact wBound_map _ ((wBound_query _ _ _).mpr le_rfl)
  · rcases found : state.1.1 point with _ | slot
    · by_cases room : state.1.2 < 2
      · rw [PqxdhRegistrationJointKemSecondEntry.slot_none _ _ _ found room]
        exact wBound_map _ (wBound_mono (wBound_of_total (lazyDummy_bound _ _)) (show 44 ≤ 108 by decide))
      · have full : (slotImpl lazyDummy (.inr point)).run state =
            (fun answer => (answer, state)) <$> ($ᵗ PqxdhServerAuthKeySchedule.Output) := by
          have full : ¬ state.1.2 ≤ 1 := by omega
          simp [slotImpl, found, full]
        rw [full]
        exact wBound_map _ (wBound_of_total output_bound)
    · rw [PqxdhRegistrationJointKemSecondEntry.slot_some _ _ _ _ found]
      exact wBound_map _ (wBound_mono (wBound_of_total (lazyDummy_bound _ _)) (show 44 ≤ 108 by decide))

/-- A weighted bound with weight one on every coin is a total query bound. -/
theorem total_of_wBound {α : Type} {work : ProbComp α} {n : ℕ} (bounded : WBound work (fun _ => 1) n) :
    work.IsTotalQueryBound n :=
  (isQueryBoundP_true_iff work n).mp (isQueryBoundP_of_wBound (fun _ => True) (fun _ _ => le_rfl) bounded)

/-- A slot client within `n` weighted by `wSlot`, run against the allocator in front of the lazy material service, draws at most `n` coins. -/
theorem slotRun_total {α : Type} (work : OracleComp SlotSpec α) (n : ℕ) (bounded : WBound work wSlot n)
    (state : Alloc Coord 2 × (MatCache 2 × SeedCache 2)) :
    ((simulateQ (slotImpl lazyDummy) work).run state).IsTotalQueryBound n :=
  total_of_wBound (wBound_run _ wSlot (fun _ => 1) (fun query state => slotLazy_step query state)
    bounded state)

/-- A lifted probabilistic step is a slot client weighted by its coins. -/
theorem liftS_cost {α : Type} (work : ProbComp α) (n : ℕ) (bounded : work.IsTotalQueryBound n) :
    WBound (PqxdhDeploymentIdealSteps.liftS work) wSlot n :=
  PqxdhRegistrationJointKemRootCosts.wBound_liftComp_inl (fun _ => 1) wSlot (fun _ => rfl) (wBound_of_total bounded)

end Slots

/-! ### The selected accept -/

section Accept
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhServerRootPreparation (Verified Ephemeral)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhJointGapDh (ScalarBytes)

/-- Every native Server callback of the accept prefix draws at most its source class allowance (`serverUniformCost`): 32 for the ephemeral, the encapsulation's cost for an encapsulation, nothing otherwise. -/
theorem prefixNative_step (caps : KemCaps) (bounded : KemBound setup caps) (seed : PqxdhJointIdentity.IdentitySeed)
    (query : (PqxdhServerRootPreparation.Spec Reader ScalarBytes Word32).Domain) (consumed : List Pqxdh.Bytes) :
    WBound ((PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed query).run consumed) (fun _ => 1)
      (serverUniformCost caps (serverClass query)) := by
  apply wBound_of_total
  cases query with
  | staticDh input => trivial
  | decode raw => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.decode raw) consumed
  | identity reader => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.identity reader) consumed
  | identityPoint identity => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.identityPoint identity) consumed
  | pqField reader => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.pqField reader) consumed
  | preField reader => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.preField reader) consumed
  | oneField reader => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.oneField reader) consumed
  | verify identity bytes => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.verify identity bytes) consumed
  | registrationStatus rid => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.registrationStatus rid) consumed
  | reserveRegistration => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded .reserveRegistration consumed
  | parseDh point => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.parseDh point) consumed
  | generate => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded .generate consumed
  | parseKem key => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.parseKem key) consumed
  | encapsulate key => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.encapsulate key) consumed
  | publicConversion identity => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.publicConversion identity) consumed
  | privateConversion => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded .privateConversion consumed
  | ephemeralDh secret point => exact PqxdhRegistrationJointKemRootCosts.serverAux_total setup codec checks caps bounded (.ephemeralDh secret point) consumed

/-- The logged steps before encapsulation draw at most the ephemeral's 32 coins (one generation; no encapsulation). -/
theorem beforeLogged_cost (caps : KemCaps) (verified : Verified Reader) :
    WBound (PqxdhDeploymentLaterServerSource.beforeLogged (E := ScalarBytes) (Shared := Word32) verified)
      (fun query => serverUniformCost caps (serverClass query)) 32 := by
  unfold PqxdhDeploymentLaterServerSource.beforeLogged
  repeat' first
    | trivial
    | (rw [wBound_query_bind]; refine ⟨by simp [serverClass, serverUniformCost], ?_⟩)
    | (fail_if_no_progress simp only [Bool.not_true, Bool.false_eq_true, ite_false])
    | intro answer; cases answer

/-- The candidate-free suffix with the challenge ciphertext draws nothing (`PqxdhRegistrationJointKemRootCosts.after_free`). -/
theorem suffix_cost (caps : KemCaps) (verified : Verified Reader) (ephemeral : Ephemeral ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token) :
    WBound (PqxdhRegistrationJointKemOpaqueSuffix.program (Shared := Word32) verified ephemeral ciphertext token)
      (fun query => serverUniformCost caps (serverClass query)) 0 :=
  wBound_map _ (PqxdhRegistrationJointKemRootCosts.after_free caps verified ephemeral _)

/-- The native root of a known decapsulation result draws at most one 64-byte Extract value. -/
theorem romRoot_uniform (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader)
    (state : NativeState KemSK) :
    ((PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index candidate input).run state).IsTotalQueryBound 64 := by
  simp only [PqxdhRegistrationJointKemOpaqueClient.romRoot, StateT.run_bind, StateT.run_pure]
  apply (isTotalQueryBound_bind (n₁ := 64) (n₂ := 0) ?_ ?_).mono (by omega)
  · exact PqxdhServerAuthNativeUniformCosts.root_bytes_uniform hmac _ _ state
  · intro result
    simp only [PqxdhServerAuthNative.nativeTouch, PqxdhServerAuthNative.localState, StateT.run, pure_bind]
    trivial

/-- Every step of the CE-native marker tail costs at most 108 for a root request (one slot read, or one 64-byte Extract value for a known result) and nothing otherwise. -/
theorem tailCE_step (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain)
    (s : NativeState KemSK × Option (ℕ × Coord)) :
    WBound ((PqxdhDeploymentIdealSteps.tailCE hmac index query).run s) wSlot
      (if PqxdhDeploymentIdealEnvFacts.isRoot query = true then 108 else 0) := by
  rcases query with (input | query) | query
  · simp only [PqxdhDeploymentIdealEnvFacts.isRoot, ite_true]
    change WBound (PqxdhDeploymentIdealSteps.tailCE hmac index (.inl (.inl input)) s) _ _
    unfold PqxdhDeploymentIdealSteps.tailCE
    dsimp only
    split
    · rw [← Nat.add_zero 108]
      exact wBound_bind ((wBound_query _ _ _).mpr le_rfl) fun _ _ => wBound_pure _ _ _
    · exact wBound_map _ (wBound_mono (liftS_cost _ 64 (romRoot_uniform hmac index _ input s.1)) (by omega))
  · simp only [PqxdhDeploymentIdealEnvFacts.isRoot, Bool.false_eq_true, ite_false]
    change WBound ((fun r => (r.1, (r.2, s.2))) <$> PqxdhDeploymentIdealSteps.liftS
      ((PqxdhRegistrationJointKemOpaqueClient.auxiliary KemSK query).run s.1)) _ _
    refine wBound_map _ (liftS_cost _ 0 ?_)
    cases query <;> simp [PqxdhRegistrationJointKemOpaqueClient.auxiliary, PqxdhServerAuthNative.nativeConsume,
      PqxdhServerAuthNative.localState, StateT.run] <;> trivial
  · simp only [PqxdhDeploymentIdealEnvFacts.isRoot, Bool.false_eq_true, ite_false]
    change WBound ((fun r => (r.1, (r.2, s.2))) <$> PqxdhDeploymentIdealSteps.liftS
      ((PqxdhRegistrationJointKemOpaqueTail.mutation query).run s.1)) _ _
    refine wBound_map _ (liftS_cost _ 0 ?_)
    cases query <;> simp [PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeSet,
      PqxdhServerAuthNative.nativeModify, PqxdhServerAuthNative.localState, StateT.run] <;> trivial

/-- The marker tail under the CE-native interpreter costs at most one slot read: at most one root request (`PqxdhDeploymentIdealEnvFacts.tail_root`). -/
theorem tailCE_cost (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (s : NativeState KemSK × Option (ℕ × Coord)) :
    WBound ((simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac index)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)).run s) wSlot 108 := by
  have roots := wBound_of_isQueryBoundP (fun query => PqxdhDeploymentIdealEnvFacts.isRoot query = true) 108
    (PqxdhDeploymentIdealEnvFacts.tail_root serverKeyId publicIdentity state collected)
  exact wBound_run _ _ wSlot (fun query state => tailCE_step hmac index query state) roots s

/-- The native accept tail without input draws nothing: it only advances the session counter. -/
theorem serverTail_none_cost (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : GameState KemSK)
    (consumed : List Pqxdh.Bytes) (s : NativeState KemSK) :
    ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup publicIdentity state (none, consumed)).run
      s).IsTotalQueryBound 0 := by
  simp [PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet, StateT.run]
  trivial

/-- The active selected accept costs at most 140: the ephemeral's 32 coins before encapsulation, nothing after it (the challenge ciphertext replaces the encapsulation), and one slot read for its root. -/
theorem acceptActive_cost (caps : KemCaps) (bounded : KemBound setup caps) (seed : PqxdhJointIdentity.IdentitySeed)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (verified : Verified Reader) (s : NativeState KemSK) :
    WBound ((PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified).run s) wSlot 140 := by
  change WBound (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified s) _ _
  unfold PqxdhDeploymentIdealSteps.acceptActive
  refine wBound_mono (wBound_bind (a := 32) (b := 108) (liftS_cost _ 32 ?_) fun pre _ => ?_) (by omega)
  · exact total_of_wBound (wBound_run _ _ (fun _ => 1)
      (fun query consumed => prefixNative_step setup codec checks caps bounded seed query consumed)
      (beforeLogged_cost caps verified) _)
  · split
    · rw [← Nat.add_zero 108]
      exact wBound_bind (liftS_cost _ 108 ((serverTail_none_cost setup _ _ _ s).mono (Nat.zero_le _)))
        fun _ _ => wBound_pure _ _ _
    · rw [show (108 : ℕ) = 0 + (108 + 0) from rfl]
      refine wBound_bind (liftS_cost _ 0 ?_) fun prepared _ =>
        wBound_bind (tailCE_cost setup.hmac s.2.sessions setup.serverKeyId _ s.2 prepared (s, none))
          fun _ _ => wBound_pure _ _ _
      exact total_of_wBound (wBound_run _ _ (fun _ => 1)
        (fun query consumed => prefixNative_step setup codec checks caps bounded seed query consumed)
        (suffix_cost caps verified _ _ _) _)

/-- The inactive selected accept is the logged accept: at most `96 + encapsCost` coins. -/
theorem acceptInactive_cost (caps : KemCaps) (bounded : KemBound setup caps) (seed : PqxdhJointIdentity.IdentitySeed)
    (raw : Pqxdh.Bytes) (s : NativeState KemSK) :
    WBound ((PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw).run s) wSlot
      (96 + caps.encapsCost) := by
  change WBound (_ <$> PqxdhDeploymentIdealSteps.liftS _) _ _
  refine wBound_map _ (liftS_cost _ _ ?_)
  have accepted := PqxdhRegistrationSchedule.accept_uniform setup codec checks caps bounded seed
    PqxdhRegistrationSchedule.observationScalar raw s
  rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst] at accepted
  simpa only [StateT.run_map, IsTotalQueryBound, isQueryBound_map_iff] using accepted

/-- The selected accept with its encapsulation exposed costs at most `140 + encapsCost`. -/
theorem acceptExposed_cost (caps : KemCaps) (bounded : KemBound setup caps) (seed : PqxdhJointIdentity.IdentitySeed)
    (chosen : PqxdhLiveKemReservation.Pair KemSK) (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes)
    (s : NativeState KemSK) :
    WBound ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw).run s) wSlot
      (140 + caps.encapsCost) := by
  have inactive := wBound_mono (acceptInactive_cost setup codec checks caps bounded seed raw s)
    (show 96 + caps.encapsCost ≤ 140 + caps.encapsCost by omega)
  change WBound (PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw s) _ _
  unfold PqxdhDeploymentIdealSteps.acceptExposed
  cases PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
  | none => exact inactive
  | some verified =>
      dsimp only
      split
      · exact wBound_mono (acceptActive_cost setup codec checks caps bounded seed challenge _ s) (by omega)
      · exact inactive

/-- The selected accept in capability form issues at most `140 + encapsCost` coin effects and nothing else, from every environment state: the ephemeral, and one slot read against the allocator in front of the lazy material service (44 coins at a fresh slot with room, 108 when the allocator is full, none at a cached slot). -/
theorem acceptSelected_bound (caps : KemCaps) (bounded : KemBound setup caps) {count : ℕ}
    (p : PqxdhDeploymentIdealParams.Params KemSK count) (raw : Pqxdh.Bytes)
    (e : PqxdhDeploymentEnvironment.EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk)
    (kind : PqxdhRecordLiftInterface.EffectKind) :
    ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e).IsQueryBoundP
      (fun effect => PqxdhRecordLiftInterface.effectKind effect = kind)
      (if kind = .coin then 140 + caps.encapsCost else 0) := by
  change IsQueryBoundP (PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw e) _ _
  unfold PqxdhDeploymentIdealEnvStep.acceptSelectedEnv
  rw [isQueryBoundP_map_iff]
  apply PqxdhDeploymentEnvironment.coins_bound
  unfold PqxdhDeploymentIdealEnvStep.acceptGame PqxdhDeploymentIdealEnvStep.slotGame
  change ((_ <$> (simulateQ (slotImpl lazyDummy) ((PqxdhDeploymentIdealSteps.acceptExposed setup codec checks
    e.created.seed p.chosen p.challenge raw).run e.native.shared)).run _ : ProbComp _)).IsTotalQueryBound _
  rw [IsTotalQueryBound, isQueryBound_map_iff]
  exact slotRun_total _ _ (acceptExposed_cost setup codec checks caps bounded _ _ _ _ _) _

end Accept

/-! ### The pool create -/

section Create
variable {ι : Type} {baseSpec : OracleSpec ι} (setup : Setup baseSpec KemSK)

/-- The pool create draws at most `64 + keygenCost` coins: the identity and the prekey, and a fresh KEM key pair only beyond the pool. -/
theorem createPool_uniform (caps : KemCaps) (bounded : KemBound setup caps)
    (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    ((PqxdhDeploymentIdealSteps.createPool setup pool pin keyId).run state).IsTotalQueryBound (64 + caps.keygenCost) := by
  simp only [PqxdhDeploymentIdealSteps.createPool, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
    StateT.run_pure, bind_assoc, pure_bind]
  apply (isTotalQueryBound_bind PqxdhJointIdentity.sampleSeed_uniform_bound (n₂ := 32 + caps.keygenCost) ?_).mono
    (by omega)
  intro identity
  apply (isTotalQueryBound_bind PqxdhJointGapDh.sampleScalar_uniform (n₂ := caps.keygenCost) ?_).mono le_rfl
  intro prekey
  apply (isTotalQueryBound_bind (n₁ := caps.keygenCost) (n₂ := 0) ?_ fun _ => ?_).mono (by omega)
  · split
    · exact (show (pure _ : ProbComp _).IsTotalQueryBound 0 from trivial).mono (Nat.zero_le _)
    · exact PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded
  · trivial

/-- The pool create in capability form stays within the real allowance of class 1 at every environment state. -/
theorem createPoolStep_bound (caps : KemCaps) (bounded : KemBound setup caps) {Bk : Type}
    (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (e : PqxdhDeploymentEnvironment.EnvState KemSK Bk) (kind : PqxdhRecordLiftInterface.EffectKind) :
    ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup pool pin keyId).run e).IsQueryBoundP
      (fun effect => PqxdhRecordLiftInterface.effectKind effect = kind)
      (PqxdhDeploymentEnvironment.baseAllowance caps 1 kind) := by
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep
  cases parsed : PqxdhDeploymentInterface.parsePin pin with
  | none => trivial
  | some word =>
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
      apply (isQueryBoundP_bind (PqxdhDeploymentEnvironment.onEnv_bound _ (64 + caps.keygenCost)
        (fun native => createPool_uniform setup caps bounded pool word keyId native) e kind)
        fun _ _ => isQueryBoundP_bind (m := 0) (PqxdhDeploymentEnvironment.issue_admin _
          (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) kind) fun _ _ => isQueryBoundP_pure _ _ _).mono
      cases kind <;> simp [PqxdhDeploymentEnvironment.baseAllowance]

end Create

/-! ### Owner k's challenge finish -/

section Finish
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
open PqxdhRecordLiftInterface (EffectKind effectKind EnvEffects)
open PqxdhRegistrationJointKemRootCosts (wPrep)

/-- Every preparation callback with the challenge handle costs at most its weight: the decapsulation's cost for a decapsulation of any other ciphertext, nothing for the challenge ciphertext or any other callback. -/
theorem preparationCE_step (caps : KemCaps) (bounded : KemBound setup caps)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (query : (PqxdhDeploymentIdealSteps.PreSpecCE KemSK Response).Domain) :
    WBound (PqxdhDeploymentIdealSteps.preparationCE setup codec challenge query) (fun _ => 1) (wPrep caps query) := by
  apply wBound_of_total
  cases query with
  | decapsulate ciphertext keys =>
      simp only [PqxdhDeploymentIdealSteps.preparationCE, wPrep]
      split
      · exact (show (pure _ : ProbComp _).IsTotalQueryBound 0 from trivial).mono (Nat.zero_le _)
      · rw [IsTotalQueryBound, isQueryBound_map_iff]
        exact PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl caps.baseUniform bounded.base _
          caps.decapsUniform caps.decapsBase (bounded.decapsUniform _ _) (bounded.decapsBase _ _)
  | _ => trivial

/-- The addressed owner's preparation with the challenge handle draws at most one decapsulation's coins. -/
theorem preparation_cost (caps : KemCaps) (bounded : KemBound setup caps) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (prekey oneTime : PqxdhJointGapDh.ScalarBytes) (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes) :
    (simulateQ (PqxdhDeploymentIdealSteps.preparationCE setup codec challenge) (PqxdhBeaconPhase2Shared.prepare
      (X := PqxdhJointIdentity.IdentitySeed) (Response := Response) (Shared := PqxdhPhase2DecapsulationRouting.Shared)
      control before.beacon.identity prekey oneTime kem raw)).IsTotalQueryBound caps.decapsCost :=
  total_of_wBound (wBound_simulate _ (wPrep caps) (fun _ => 1) (preparationCE_step setup codec caps bounded challenge)
    (PqxdhRegistrationJointKemRootCosts.prepare_cost caps control _ prekey oneTime kem raw))

/-- The native root of a known decapsulation result draws at most one 64-byte Extract value. -/
theorem markedRoot_uniform (hmac : PqxdhSecretInputKdf.HmacSha512) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) (state : NativeState KemSK) :
    ((PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot hmac candidate secrets).run state).IsTotalQueryBound 64 := by
  unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot
  split
  · exact PqxdhRegistrationSchedule.sourceRoot_uniform hmac _ state
  · trivial

/-- The forwarded Beacon tail after the root issues no coin, at most one BLAKE2b effect (its sequence-one opening) and no administrative effect. -/
theorem knownFwd_bound (pending : PqxdhBeaconPhase2Shared.Prepared Response PqxdhPhase2DecapsulationRouting.Shared)
    (root : PqxdhBeaconPhase2Preparation.Word32) (kind : EffectKind) :
    (simulateQ (PqxdhDeploymentIdealEnvFinish.knownFwd setup codec)
      (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)).IsQueryBoundP
        (fun effect => effectKind effect = kind) (if kind = .hash then 1 else 0) := by
  unfold PqxdhBeaconPhase2Shared.afterRoot
  simp only [simulateQ_bind, simulateQ_spec_query]
  change (pure _ >>= fun response => pure _ >>= fun raw => _ : OracleComp (EnvEffects 2) _).IsQueryBoundP _ _
  simp only [pure_bind]
  split
  · simp only [simulateQ_pure]; trivial
  · simp only [simulateQ_bind, simulateQ_pure]
    rw [← QueryImpl.simulateQ_compose, ← Nat.add_zero (if kind = .hash then 1 else 0)]
    refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_pure _ _ _
    have step : ∀ query, ((PqxdhDeploymentIdealEnvFinish.knownFwd setup codec ∘ₛ
        PqxdhBeaconPhase2Shared.rawLift (Response := Response) (Shared := PqxdhPhase2DecapsulationRouting.Shared))
          query).IsQueryBoundP (fun effect => effectKind effect = kind)
          (if kind = .hash ∧ RawCtxSourceOpen.openingPredicate Sum.isLeft query = true then 1 else 0) := by
      intro query
      rw [QueryImpl.apply_compose]
      simp only [PqxdhBeaconPhase2Shared.rawLift, simulateQ_spec_query]
      exact PqxdhDeploymentEnvironment.primFwd_bound setup.source.crypto setup.source query kind
    by_cases hash : kind = .hash
    · subst hash
      simp only [ite_true, true_and] at step ⊢
      exact RawCtxSourceOpen.simulate_bound _ (fun query => RawCtxSourceOpen.openingPredicate Sum.isLeft query = true) _ _ 1
        (RawCtxSourceOpen.raw_primitive_bounds codec.frameRead _ _).1 step
    · simp only [hash, ite_false, false_and] at step ⊢
      exact RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
        (fun query => by simpa only [ite_false] using step query)

/-- The source commit of a finish issues at most one administrative effect (the owner's abort or known install) and nothing else. -/
theorem commitEnv_bound (e : PqxdhDeploymentEnvironment.EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk)
    (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (shared : NativeState KemSK) (staged : Option PqxdhBeaconPhase2Publication.Staged) (kind : EffectKind) :
    (PqxdhDeploymentIdealEnvFinish.commitEnv e owner control before shared staged).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .administrative then 1 else 0) := by
  unfold PqxdhDeploymentIdealEnvFinish.commitEnv
  rw [← Nat.add_zero (if kind = .administrative then 1 else 0)]
  exact isQueryBoundP_bind (PqxdhDeploymentEnvironment.ownerEffect_bound _ _ _ kind) fun _ _ => isQueryBoundP_pure _ _ _

/-- The grouped finish request of owner k in capability form issues at most 108 coin effects (one slot read, or one 64-byte Extract value for a known result), at most one BLAKE2b effect and at most one administrative effect. -/
theorem groupEnv_bound (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK)
    (e : PqxdhDeploymentEnvironment.EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) (kind : EffectKind) :
    (PqxdhDeploymentIdealEnvFinish.groupEnv setup codec owner control before e pending).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .coin then 108 else 1) := by
  have commit : ∀ shared staged, (PqxdhDeploymentIdealEnvFinish.commitEnv e owner control before shared
      staged).IsQueryBoundP (fun effect => effectKind effect = kind) (if kind = .coin then 0 else 1) := fun shared staged =>
    (commitEnv_bound e owner control before shared staged kind).mono (by cases kind <;> simp)
  unfold PqxdhDeploymentIdealEnvFinish.groupEnv
  split
  · split
    · apply (isQueryBoundP_bind (m := if kind = .coin then 0 else 1) (PqxdhDeploymentEnvironment.coins_bound _ 108
        (total_of_wBound (slotLazy_step _ _)) kind) fun read _ => ?_).mono (by cases kind <;> simp)
      split
      · rw [isQueryBoundP_map_iff]
        exact PqxdhDeploymentEnvironment.finishSplit_env_cost setup codec _ _ owner control before _ kind
      · exact commit _ _
    · exact (commit _ _).mono (by cases kind <;> simp)
  · apply (isQueryBoundP_bind (m := if kind = .coin then 0 else 1) (PqxdhDeploymentEnvironment.coins_bound _ 64
      (markedRoot_uniform _ _ _ _) kind) fun r _ => ?_).mono (by cases kind <;> simp)
    split
    · exact commit _ _
    · apply (isQueryBoundP_bind (knownFwd_bound setup codec _ _ kind) fun staged _ =>
        commitEnv_bound e owner control before _ staged kind).mono
      cases kind <;> simp

/-- Owner k's challenge finish in capability form issues at most `decapsCost + 108` coin effects (its preparation's decapsulation and the grouped request), at most one BLAKE2b effect and at most one administrative effect, from every environment state. -/
theorem finishChallenge_bound (caps : KemCaps) (bounded : KemBound setup caps) {count : ℕ}
    (p : PqxdhDeploymentIdealParams.Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes)
    (e : PqxdhDeploymentEnvironment.EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) (kind : EffectKind) :
    ((PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw).run e).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .coin then caps.decapsCost + 108 else 1) := by
  change IsQueryBoundP (PqxdhDeploymentIdealEnvFinish.finishChallengeEnv setup codec p owner raw e) _ _
  unfold PqxdhDeploymentIdealEnvFinish.finishChallengeEnv
  split
  · split
    · apply (isQueryBoundP_bind (m := if kind = .coin then 108 else 1) (PqxdhDeploymentEnvironment.coins_bound _ _
        (preparation_cost setup codec caps bounded p.challenge _ _ _ _ _ raw) kind) fun prepared _ => ?_).mono
        (by cases kind <;> simp)
      split
      · exact (commitEnv_bound e owner _ _ _ none kind).mono (by cases kind <;> simp)
      · exact groupEnv_bound setup codec owner _ _ e _ kind
    · trivial
  · trivial

end Finish

/-! ### The draw of the challenger's parameters -/

section Draw
variable {ι : Type} {baseSpec : OracleSpec ι} (setup : Setup baseSpec KemSK)

/-- A family of `count` draws of a sampler within `k` coins draws at most `count * k` coins. -/
theorem sampleFamily_uniform (sampler : ProbComp (PqxdhLiveKemReservation.Pair KemSK)) (k : ℕ)
    (bounded : sampler.IsTotalQueryBound k) (count : ℕ) :
    (PqxdhLiveKemSelection.sampleFamily sampler count).IsTotalQueryBound (count * k) := by
  induction count with
  | zero => trivial
  | succ count ih =>
      simp only [PqxdhLiveKemSelection.sampleFamily]
      apply (isTotalQueryBound_bind bounded fun _ => isTotalQueryBound_bind ih fun _ =>
        (show (pure _ : ProbComp _).IsTotalQueryBound 0 from trivial)).mono
      rw [Nat.succ_mul]
      omega

/-- The challenger's draws (the selected key pair, the other `count` key pairs and the challenge encapsulation) draw at most `(count + 1) * keygenCost + encapsCost` coins. -/
theorem drawParams_uniform (caps : KemCaps) (bounded : KemBound setup caps) (count : ℕ) :
    (PqxdhDeploymentIdealParams.drawParams setup count).IsTotalQueryBound
      ((count + 1) * caps.keygenCost + caps.encapsCost) := by
  unfold PqxdhDeploymentIdealParams.drawParams
  have keygen := PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded
  apply (isTotalQueryBound_bind keygen fun chosen => isTotalQueryBound_bind
    (sampleFamily_uniform _ _ keygen count) fun _ => isTotalQueryBound_bind
      (PqxdhServerAuthSourceCosts.ambient_uniform setup.baseImpl caps.baseUniform bounded.base _ caps.encapsUniform
        caps.encapsBase (bounded.encapsUniform _) (bounded.encapsBase _)) fun _ =>
          (show (pure _ : ProbComp _).IsTotalQueryBound 0 from trivial)).mono
  simp only [PqxdhServerAuthSourceCosts.KemCaps.encapsCost, Nat.succ_mul]
  omega

end Draw

/-! ### Every command of the ideal step -/

section Step
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
open PqxdhRecordLiftInterface (EffectKind effectKind)
open PqxdhDeploymentEnvironment (allowanceG baseAllowance ceFirstTouch)

/-- Every command of the ideal step stays within the first-touch allowance of plan sections 31, 33 and 35 (`allowanceG (baseAllowance caps) ceFirstTouch`) at every environment state, for every effect kind: the pool create within the real create allowance, the selected accept within `140 + encapsCost` coins (the real accept's `96 + encapsCost` plus the 44 first-touch coins) including the allocator's no-room branch, the marked build within the build allowance (`PqxdhDeploymentIdealEnv.idealStep_build_bound`), owner k's challenge finish within `decapsCost + 108` coins, one BLAKE2b and one administrative effect, and every other command within its real allowance. -/
theorem idealStep_bound (caps : KemCaps) (bounded : KemBound setup caps) {count : ℕ}
    (t : PqxdhDeploymentIdealParams.Target count) (p : PqxdhDeploymentIdealParams.Params KemSK count)
    (query : PqxdhRecordLiftInterface.EnvQuery)
    (e : PqxdhDeploymentEnvironment.EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) (kind : EffectKind) :
    ((PqxdhDeploymentIdealEnv.idealStep setup codec checks t p query).run e).IsQueryBoundP
      (fun effect => effectKind effect = kind)
      (allowanceG (baseAllowance caps) ceFirstTouch
        (PqxdhDeploymentInterface.queryClass (.inl (.inr query.val))) kind) := by
  have real : ∀ (query : PqxdhRecordLiftInterface.EnvQuery)
      (e : PqxdhDeploymentEnvironment.EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk),
      ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks query).run e).IsQueryBoundP
        (fun effect => effectKind effect = kind)
        (allowanceG (baseAllowance caps) ceFirstTouch (PqxdhDeploymentInterface.queryClass (.inl (.inr query.val))) kind) :=
    fun query e => (PqxdhDeploymentEnvironment.realStep_bound setup codec checks caps bounded query e kind).mono
      (Nat.le_add_right _ _)
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      exact (createPoolStep_bound setup caps bounded (p.pool t) pin keyId e kind).mono (Nat.le_add_right _ _)
  | bundle owner => exact real ⟨.bundle owner, allowed⟩ e
  | accept raw =>
      by_cases selected : e.backend.2.2.accepts = t.accept
      · rw [PqxdhDeploymentIdealEnv.idealStep_selected setup codec checks t p raw allowed e selected]
        refine (acceptSelected_bound setup codec checks caps bounded p raw e kind).mono ?_
        cases kind <;> simp [allowanceG, baseAllowance, ceFirstTouch, PqxdhDeploymentInterface.queryClass]
        omega
      · rw [PqxdhDeploymentIdealEnv.idealStep_accept_other setup codec checks t p raw allowed e selected]
        exact real ⟨.accept raw, allowed⟩ _
  | build session payload =>
      exact PqxdhDeploymentIdealEnv.idealStep_build_bound setup codec checks caps t p session payload allowed e kind
  | finish owner raw =>
      by_cases chosen : e.backend.2.2.active = true ∧ owner = t.kem.val ∧
          PqxdhDeploymentIdealSteps.initSentAt e.native.owners owner = true
      · rw [PqxdhDeploymentIdealEnv.idealStep_challenge setup codec checks t p owner raw allowed e chosen]
        refine (finishChallenge_bound setup codec caps bounded p owner raw e kind).mono ?_
        have wide : caps.decapsCost ≤ max 64 caps.decapsCost := le_max_right _ _
        have floor : 64 ≤ max 64 caps.decapsCost := le_max_left _ _
        cases kind <;> simp [allowanceG, baseAllowance, ceFirstTouch, PqxdhDeploymentInterface.queryClass]
        omega
      · rw [PqxdhDeploymentIdealEnv.idealStep_finish_real setup codec checks t p owner raw allowed e chosen]
        exact real ⟨.finish owner raw, allowed⟩ e
  | hmac key message => exact real ⟨.hmac key message, allowed⟩ e
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

end Step

end BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.output_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.output_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.lazyDummy_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.lazyDummy_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.slotLazy_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.slotLazy_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.total_of_wBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.total_of_wBound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.slotRun_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.slotRun_total

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.liftS_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.liftS_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.prefixNative_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.prefixNative_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.beforeLogged_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.beforeLogged_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.suffix_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.suffix_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.romRoot_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.romRoot_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.tailCE_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.tailCE_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.tailCE_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.tailCE_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.serverTail_none_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.serverTail_none_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptActive_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptActive_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptInactive_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptInactive_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptExposed_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptExposed_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptSelected_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.acceptSelected_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.createPool_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.createPool_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.createPoolStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.createPoolStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.preparationCE_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.preparationCE_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.preparation_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.preparation_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.markedRoot_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.markedRoot_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.knownFwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.knownFwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.commitEnv_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.commitEnv_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.groupEnv_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.groupEnv_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.finishChallenge_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.finishChallenge_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.sampleFamily_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.sampleFamily_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.drawParams_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.drawParams_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.idealStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealEnvCost.idealStep_bound

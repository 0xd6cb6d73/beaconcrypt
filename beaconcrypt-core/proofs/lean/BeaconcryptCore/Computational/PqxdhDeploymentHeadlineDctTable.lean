-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctInvariant
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctHash

/-!
# CE-12 D-ct: the averaged union bound over the R1 table

The hidden key `key32_0` is the key part of slot 0's material in the final split form: a uniform 256-bit value drawn by the lazy slot service at the first touch of slot 0. `KeyHit x`: some value `v` of the R1 table (the Extract family's HMAC cache, `r1`) has `seqKey setup v` (the sequence-one key of the Beacon's open, `PqxdhDeploymentHeadlineDctReceive.seqKey`) equal to `key32_0`. This module bounds its probability on the split game and on the record world with the ideal environment of any target by `r1Cap/2^256` (design section 4.5), for every adaptive adversary that respects its budget, without any independence of `key32_0` from the adversary's view.

- The potential. `tablePotential key b T` is `(|T| + b)/2^256` before the key is drawn and `hits(T, k) + b·mass(k)` after (`hits` counts the table values whose key is `k`, `mass k` is the chance that a uniform value's is); `keyPotential b x` reads it at the split state. `ro_table`: one R1 read of the lazily sampled HMAC oracle with one unit of budget does not raise it in expectation; `material_read`, `slot_read`: the first draw of slot 0's material averages `hits + b·mass` over a uniform key (`hits_draw`, `average_mass`, `material_marginal`) and does not raise it either.
- The charges. `ChargedN` (native programs), `ChargedR`, `ChargedD` (the registration and deployment states), `ChargedG` (slot clients through the allocator in front of the lazy service) and `ChargedX` (the split state) state that a program spends at most `n` units, with the calculi (`pure`, `bind`, `mono`, frames, `chargedN_run` and `chargedG_run` over a query-bounded program by `expected_run_bounded`). Every R1 read is a root derivation (`chargedN_sourceRoot`, `chargedN_romRootBytes`) or a public HMAC (`chargedN_familyHmac`); the native accept, the Beacon finish and the public HMAC cost one unit, every other native command nothing (`chargedD_handler`). The CE-native hidden steps: the Server's marker tail reads the hidden value instead of R1 at the challenge and costs one unit (`chargedG_tailCE`, `chargedG_tail`), as do the selected accept (`chargedG_acceptActive`, `chargedG_acceptExposed`) and owner k's challenge finish (`chargedG_groupCE`, `groupedOwnerCE_bound`, `chargedG_finishChallenge`); the marked build costs nothing (`chargedG_buildHiddenC`).
- The handler. `handler_charged`: every query of the split handler `handlerWith (idealSplit t p created)` costs at most one unit when it is a raw accept, a finish or a public HMAC (`r1Costly`) and nothing otherwise (`chargedX_slotRunX`, `chargedX_onBase`, and `install_le` for the hidden installs, which keep the R1 table and the material). `wrap_r1_bound`: the wrapped adversary makes at most `r1Cap budget` such queries (`PqxdhDeploymentCompileSecrecy.wrap_bound` at the three classes).
- The bound. `split_keyHit`: on the final split game at any target and parameters, `𝒟[KeyHit] ≤ r1Cap/2^256` (`chance_le_expected` with `one_le_keyPotential`, the budgeted supermartingale from `keyPotential_initial`). `world_keyHit`: the same bound for the reassembled final state on the record world with `envGD` (`PqxdhDeploymentIdealEnv.c1_split`, then `split_keyHit` under the draw of the parameters).
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable
open OracleComp.EvalDist (expectedValue)
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhSecretInputKdf (HmacBlock HmacOracle)
open PqxdhDeploymentHeadlineDctTools (size hits mass)
open PqxdhDeploymentHeadlineDctReceive (seqKey)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The table potential and native programs -/

section Native
variable (setup : Setup baseSpec KemSK)

/-- The table potential with budget `b`: before the hidden key is drawn, `(|T| + b)/2^256`; after, the number of table values whose sequence-one key is the hidden key plus `b` times the chance that a fresh value's is. -/
noncomputable def tablePotential (key : Option RawCtxKdfRequestTable.KeyPart) (b : ℕ) (T : HmacOracle.QueryCache) :
    ℝ≥0∞ :=
  match key with
  | none => (size T + b) * (2 ^ 256 : ℝ≥0∞)⁻¹
  | some k => hits (seqKey setup) T k + b * mass (seqKey setup) k

theorem tablePotential_mono (key : Option RawCtxKdfRequestTable.KeyPart) {b c : ℕ} (le : b ≤ c)
    (T : HmacOracle.QueryCache) : tablePotential setup key b T ≤ tablePotential setup key c T := by
  have cast : (b : ℝ≥0∞) ≤ c := by exact_mod_cast le
  cases key with
  | none =>
      simp only [tablePotential]
      gcongr
  | some k =>
      simp only [tablePotential]
      gcongr

/-- One read of the lazily sampled R1 table spends one unit of the budget. -/
theorem ro_table (key : Option RawCtxKdfRequestTable.KeyPart) (b : ℕ) (T : HmacOracle.QueryCache)
    (u : Pqxdh.Bytes) :
    expectedValue ((HmacOracle.randomOracle u).run T) (fun r => tablePotential setup key b r.2) ≤
      tablePotential setup key (b + 1) T := by
  cases key with
  | none =>
      simp only [tablePotential]
      rw [OracleComp.EvalDist.expectedValue_mul_const, OracleComp.EvalDist.expectedValue_add]
      gcongr ?_ * _
      calc _ ≤ (size T + 1) + (b : ℝ≥0∞) := add_le_add (PqxdhDeploymentHeadlineDctTools.ro_size T u)
            (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)
        _ = size T + ((b + 1 : ℕ) : ℝ≥0∞) := by push_cast; ring
  | some k =>
      simp only [tablePotential]
      rw [OracleComp.EvalDist.expectedValue_add]
      calc _ ≤ (hits (seqKey setup) T k + mass (seqKey setup) k) + (b : ℝ≥0∞) * mass (seqKey setup) k :=
            add_le_add (PqxdhDeploymentHeadlineDctTools.ro_hits (seqKey setup) T u k)
              (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)
        _ = _ := by push_cast; ring

/-- A native program charged `n` units of the table budget: whatever the hidden key, the expected table potential after it at budget `b` is at most the potential before it at budget `b + n`. -/
def ChargedN {α : Type} (work : NativeGame KemSK α) (n : ℕ) : Prop :=
  ∀ key b state, expectedValue (work.run state) (fun r => tablePotential setup key b r.2.1.cache) ≤
    tablePotential setup key (b + n) state.1.cache

theorem chargedN_pure {α : Type} (value : α) : ChargedN setup (pure value : NativeGame KemSK α) 0 := by
  intro key b state
  rw [StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
  exact le_rfl

theorem chargedN_bind {α β : Type} {work : NativeGame KemSK α} {next : α → NativeGame KemSK β} {m n : ℕ}
    (first : ChargedN setup work m) (rest : ∀ value, ChargedN setup (next value) n) :
    ChargedN setup (work >>= next) (m + n) := by
  intro key b state
  rw [StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
  calc _ ≤ expectedValue (work.run state) (fun r => tablePotential setup key (b + n) r.2.1.cache) :=
        OracleComp.EvalDist.expectedValue_mono _ fun r => rest r.1 key b r.2
    _ ≤ tablePotential setup key (b + n + m) state.1.cache := first key (b + n) state
    _ = _ := by rw [show b + n + m = b + (m + n) by omega]

theorem chargedN_mono {α : Type} {work : NativeGame KemSK α} {m n : ℕ} (charged : ChargedN setup work m)
    (le : m ≤ n) : ChargedN setup work n := fun key b state =>
  (charged key b state).trans (tablePotential_mono setup key (by omega) _)

/-- A native program that keeps the R1 table costs nothing. -/
theorem chargedN_frame {α : Type} (work : NativeGame KemSK α)
    (kept : ∀ state, ∀ r ∈ support (work.run state), r.2.1.cache = state.1.cache) : ChargedN setup work 0 := by
  intro key b state
  refine le_trans (OracleComp.EvalDist.expectedValue_mono_of_support fun r member => le_of_eq ?_)
    (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)
  rw [kept state r member]
  rfl

theorem chargedN_coins {α : Type} (work : ProbComp α) :
    ChargedN setup (PqxdhServerAuthNative.nativeCoins (KemSK := KemSK) work) 0 :=
  chargedN_frame setup _ fun state r member => by
    change r ∈ support ((fun value => (value, state)) <$> work) at member
    rw [support_map] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl

theorem chargedN_local {α : Type}
    (step : PqxdhServerAuthExperiment.GameState KemSK → α × PqxdhServerAuthExperiment.GameState KemSK) :
    ChargedN setup (PqxdhServerAuthNative.localState step) 0 :=
  chargedN_frame setup _ fun state r member => by
    change r ∈ support (pure ((step state.2).1, (state.1, (step state.2).2)) : ProbComp _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl

theorem chargedN_ctx {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    ChargedN setup (PqxdhServerAuthNative.nativeCtx (KemSK := KemSK) work) 0 :=
  chargedN_frame setup _ fun state r member => by
    rw [PqxdhDeploymentHeadlineDctFinish.nativeCtx_keeps work state r member]

theorem chargedN_sourceRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (input : beaconcrypt_core.pqxdh.RootKeyInput) :
    ChargedN setup (PqxdhServerAuthNative.sourceRoot (KemSK := KemSK) hmac input) 1 := by
  intro key b state
  show expectedValue (PqxdhServerAuthNative.sourceRoot hmac input state) _ ≤ _
  unfold PqxdhServerAuthNative.sourceRoot
  rw [OracleComp.EvalDist.expectedValue_map]
  exact ro_table setup key b state.1.cache _

theorem chargedN_romRootBytes (hmac : PqxdhSecretInputKdf.HmacSha512) (message : PqxdhJointDhExtractFamily.Message)
    (bytes : Pqxdh.Bytes) :
    ChargedN setup (PqxdhServerAuthNative.romRootBytes (A := PqxdhServerAuthExperiment.GameState KemSK) hmac message
      bytes) 1 := by
  intro key b state
  show expectedValue (PqxdhServerAuthNative.romRootBytes hmac message bytes state) _ ≤ _
  unfold PqxdhServerAuthNative.romRootBytes
  rw [OracleComp.EvalDist.expectedValue_map]
  exact ro_table setup key b state.1.cache _

/-- A whole program on native callbacks costs at most its budget of costly requests when each costly request costs one unit and every other request costs nothing. -/
theorem chargedN_run {κ α : Type} {spec : OracleSpec κ} (impl : QueryImpl spec (NativeGame KemSK)) (costly : κ → Prop)
    [DecidablePred costly] (paid : ∀ query, costly query → ChargedN setup (impl query) 1)
    (free : ∀ query, ¬ costly query → ChargedN setup (impl query) 0) (work : OracleComp spec α) (n : ℕ)
    (bounded : work.IsQueryBoundP costly n) : ChargedN setup (simulateQ impl work) n := by
  intro key b state
  have run := PqxdhDeploymentHeadlineDctTools.expected_run_bounded impl costly
    (fun c s => tablePotential setup key (b + c) s.1.cache) (fun c s => tablePotential_mono setup key (by omega) _)
    (fun query s c costlyQuery => by
      have := paid query costlyQuery key (b + c) s
      simpa only [Nat.add_assoc] using this)
    (fun query s c freeQuery => by
      have := free query freeQuery key (b + c) s
      simpa only [Nat.add_zero] using this) work n bounded state
  simpa only [Nat.add_zero] using run

/-- The accept core's root derivation costs one unit. -/
theorem chargedN_client (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes PqxdhBeaconPhase2Preparation.Word32) :
    ChargedN setup (PqxdhServerAuthNative.nativeClient (KemSK := KemSK) hmac index control binding input) 1 := by
  unfold PqxdhServerAuthNative.nativeClient
  split
  · exact chargedN_mono setup (chargedN_pure setup _) (by omega)
  · exact chargedN_mono setup (chargedN_pure setup _) (by omega)
  · exact chargedN_mono setup (chargedN_pure setup _) (by omega)
  · unfold PqxdhServerAuthNative.loggedRoot PqxdhServerAuthNative.romRoot
    refine chargedN_mono setup (chargedN_bind setup (chargedN_bind setup (chargedN_romRootBytes setup _ _ _)
      fun _ => chargedN_bind setup (chargedN_local setup _) fun _ => chargedN_pure setup _)
      fun _ => chargedN_bind setup (chargedN_local setup _) fun _ => chargedN_pure setup _) (by omega)

/-- The native raw accept costs one unit. -/
theorem chargedN_accept (checks : Checks) (codec : Codec Reader Response) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (raw : Pqxdh.Bytes) :
    ChargedN setup (PqxdhServerAuthNative.nativeAccept setup codec checks seed scalar raw) 1 := by
  unfold PqxdhServerAuthNative.nativeAccept
  refine chargedN_mono setup (m := 0 + (0 + (0 + 1))) (chargedN_bind setup (chargedN_local setup _) fun state =>
    chargedN_bind setup (chargedN_coins setup _) fun collected =>
      chargedN_bind setup (chargedN_local setup _) fun _ => ?_) (by omega)
  obtain ⟨_ | input, consumed⟩ := collected
  · exact chargedN_mono setup (chargedN_pure setup _) (by omega)
  · dsimp only
    have client : ChargedN setup (PqxdhServerAuthNative.nativeClient setup.hmac state.sessions state.server.control
        (PqxdhServerAuthExperiment.binding setup (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar)) input) 1 :=
      chargedN_client setup _ _ _ _ _
    refine chargedN_mono setup (m := 1 + 0) (chargedN_bind setup client fun returned => ?_) (by omega)
    split
    · exact chargedN_bind setup (m := 0) (n := 0) (chargedN_local setup _) fun _ => chargedN_pure setup _
    · exact chargedN_pure setup _

/-- The LQ-F logged raw accept costs one unit: its native state is the native accept's. -/
theorem chargedN_acceptLogged (checks : Checks) (codec : Codec Reader Response) (seed : PqxdhJointIdentity.IdentitySeed)
    (raw : Pqxdh.Bytes) : ChargedN setup (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw) 1 := by
  intro key b state
  have same := congrArg (fun m => expectedValue m (fun r : Option ℕ × NativeState KemSK =>
    tablePotential setup key b r.2.1.cache))
    (PqxdhDeploymentLaterServerNative.acceptLogged_fst setup codec checks seed raw state)
  simp only [OracleComp.EvalDist.expectedValue_map] at same
  exact (le_of_eq same).trans (chargedN_accept setup checks codec seed _ raw key b state)

/-- The route-R1 public HMAC request costs one unit. -/
theorem chargedN_familyHmac (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    ChargedN setup (PqxdhServerRelatedRootConsumer.familyImpl (A := PqxdhServerAuthExperiment.GameState KemSK)
      (PqxdhExtractRomFamily.romImpl setup.hmac setup.joint setup.dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction)
      (.inr (.publicHmac key message))) 1 := by
  intro hidden b state
  change expectedValue ((fun r => (r.1, (r.2, state.2))) <$> ((PqxdhExtractRomFamily.romImpl setup.hmac setup.joint
    setup.dh seed scalar ∘ₛ PqxdhJointDhExtractRoot.reduction) (.inr (.publicHmac key message))).run state.1) _ ≤ _
  rw [OracleComp.EvalDist.expectedValue_map]
  simp only [QueryImpl.apply_compose, PqxdhJointDhExtractRoot.reduction, simulateQ_spec_query,
    PqxdhExtractRomFamily.romImpl, StateT.run]
  split_ifs
  · rw [OracleComp.EvalDist.expectedValue_bind]
    simp only [OracleComp.EvalDist.expectedValue_pure]
    exact ro_table setup hidden b state.1.cache message
  · rw [OracleComp.EvalDist.expectedValue_pure]
    exact tablePotential_mono setup hidden (by omega) _

/-- The native public HMAC costs one unit. -/
theorem chargedN_hmac (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    ChargedN setup (PqxdhServerAuthNative.nativeHmac setup seed scalar key message) 1 := by
  unfold PqxdhServerAuthNative.nativeHmac
  split_ifs
  · exact chargedN_bind setup (m := 0) (n := 1) (chargedN_local setup _) fun _ =>
      chargedN_familyHmac setup seed scalar key message
  · exact chargedN_familyHmac setup seed scalar key message

/-- Every native callback of the Beacon finish costs one unit at its root request and nothing otherwise. -/
theorem chargedN_callbacks (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain) :
    ChargedN setup (PqxdhRegistrationSchedule.callbacks setup codec query)
      (if PqxdhRegistrationJointKemRomSplit.rootNative query = true then 1 else 0) := by
  rcases query with query | (query | (input | request | response))
  · exact chargedN_coins setup _
  · exact chargedN_ctx setup _
  · exact chargedN_sourceRoot setup setup.hmac input
  · exact chargedN_ctx setup _
  · exact chargedN_ctx setup _

end Native

/-! ### The registration and deployment states -/

section Lifts
variable (setup : Setup baseSpec KemSK)

/-- A registration program charged `n` units, on the R1 table of its shared native state. -/
def ChargedR {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α) (n : ℕ) : Prop :=
  ∀ key b state, expectedValue (work.run state) (fun r => tablePotential setup key b r.2.shared.1.cache) ≤
    tablePotential setup key (b + n) state.shared.1.cache

/-- A deployment program charged `n` units, on the R1 table of its shared native state. -/
def ChargedD {α : Type} (work : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α) (n : ℕ) : Prop :=
  ∀ key b state, expectedValue (work.run state) (fun r => tablePotential setup key b r.2.native.shared.1.cache) ≤
    tablePotential setup key (b + n) state.native.shared.1.cache

theorem chargedR_onShared {α : Type} {work : NativeGame KemSK α} {n : ℕ} (charged : ChargedN setup work n) :
    ChargedR setup (PqxdhRegistrationSchedule.onShared work) n := by
  intro key b state
  change expectedValue ((fun result => (result.1, { state with shared := result.2 })) <$> work state.shared) _ ≤ _
  rw [OracleComp.EvalDist.expectedValue_map]
  exact charged key b state.shared

theorem chargedD_onNative {α : Type} {work : PqxdhRegistrationSchedule.Game KemSK α} {n : ℕ}
    (charged : ChargedR setup work n) : ChargedD setup (PqxdhDeploymentNative.onNative work) n := by
  intro key b state
  rw [PqxdhDeploymentCompileStep.onNative_run, OracleComp.EvalDist.expectedValue_map]
  exact charged key b state.native

theorem chargedR_mono {α : Type} {work : PqxdhRegistrationSchedule.Game KemSK α} {m n : ℕ}
    (charged : ChargedR setup work m) (le : m ≤ n) : ChargedR setup work n := fun key b state =>
  (charged key b state).trans (tablePotential_mono setup key (by omega) _)

/-- A registration program that keeps the shared native state costs nothing. -/
theorem chargedR_frame {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α)
    (kept : ∀ state, ∀ r ∈ support (work.run state), r.2.shared.1.cache = state.shared.1.cache) :
    ChargedR setup work 0 := by
  intro key b state
  refine le_trans (OracleComp.EvalDist.expectedValue_mono_of_support fun r member => le_of_eq ?_)
    (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)
  rw [kept state r member]
  rfl

/-- A deployment program that keeps the R1 table costs nothing. -/
theorem chargedD_frame {α : Type} (work : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α)
    (kept : ∀ state, ∀ r ∈ support (work.run state), r.2.native.shared.1.cache = state.native.shared.1.cache) :
    ChargedD setup work 0 := by
  intro key b state
  refine le_trans (OracleComp.EvalDist.expectedValue_mono_of_support fun r member => le_of_eq ?_)
    (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)
  rw [kept state r member]
  rfl

/-- The source schedule's Beacon finish costs one unit: the native owner makes at most one root request (`nativeOwner_root`). -/
theorem chargedR_finish (codec : Codec Reader Response) (index : ℕ) (raw : Pqxdh.Bytes) :
    ChargedR setup (PqxdhRegistrationSchedule.finish setup codec index raw) 1 := by
  intro key b state
  cases found : state.owners[index]? with
  | none =>
      rw [PqxdhRegistrationSchedule.finish_missing setup codec index raw state found,
        OracleComp.EvalDist.expectedValue_pure]
      exact tablePotential_mono setup key (by omega) _
  | some owner =>
      change expectedValue (PqxdhRegistrationSchedule.finish setup codec index raw state) _ ≤ _
      rw [PqxdhRegistrationSchedule.finish_source setup codec index raw state owner found,
        OracleComp.EvalDist.expectedValue_map]
      exact chargedN_run setup (PqxdhRegistrationSchedule.callbacks setup codec)
        (fun query => PqxdhRegistrationJointKemRomSplit.rootNative query = true)
        (fun query root => by simpa [root] using chargedN_callbacks setup codec query)
        (fun query root => by simpa [root] using chargedN_callbacks setup codec query) _ 1
        (PqxdhRegistrationJointKemRomSplit.nativeOwner_root codec.frameRead raw owner) key b state.shared

end Lifts

/-! ### Slot clients through the allocator in front of the lazy service -/

section Slots
variable (setup : Setup baseSpec KemSK)

/-- The allocator and the lazy service state. -/
abbrev SlotState := PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhDeploymentIdealSlots.Coord 2 ×
  (PqxdhDeploymentIdealKernel.MatCache 2 × PqxdhDeploymentIdealKernel.SeedCache 2)

/-- The hidden key `key32_0`: the key part of slot 0's material, once drawn. -/
def slotKeyOf (q : SlotState) : Option RawCtxKdfRequestTable.KeyPart := (q.2.1 0).map Prod.fst

/-- A slot client on a state with an R1 table `R`, charged `n` units through the allocator in front of the lazy service. -/
def ChargedG {σ β : Type} (R : σ → HmacOracle.QueryCache)
    (step : StateT σ (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β) (n : ℕ) : Prop :=
  ∀ b s q, expectedValue ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
    (step.run s)).run q) (fun r => tablePotential setup (slotKeyOf r.2) b (R r.1.2)) ≤
      tablePotential setup (slotKeyOf q) (b + n) (R s)

theorem chargedG_pure {σ β : Type} (R : σ → HmacOracle.QueryCache) (value : β) :
    ChargedG setup R (pure value : StateT σ (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β) 0 := by
  intro b s q
  simp only [StateT.run_pure, simulateQ_pure, OracleComp.EvalDist.expectedValue_pure]
  exact le_rfl

theorem chargedG_bind {σ α β : Type} (R : σ → HmacOracle.QueryCache)
    {step : StateT σ (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) α}
    {next : α → StateT σ (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β} {m n : ℕ}
    (first : ChargedG setup R step m) (rest : ∀ value, ChargedG setup R (next value) n) :
    ChargedG setup R (step >>= next) (m + n) := by
  intro b s q
  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
  calc _ ≤ expectedValue ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
        (step.run s)).run q) (fun r => tablePotential setup (slotKeyOf r.2) (b + n) (R r.1.2)) :=
        OracleComp.EvalDist.expectedValue_mono _ fun r => rest r.1.1 b r.1.2 r.2
    _ ≤ tablePotential setup (slotKeyOf q) (b + n + m) (R s) := first (b + n) s q
    _ = _ := by rw [show b + n + m = b + (m + n) by omega]

theorem chargedG_mono {σ β : Type} (R : σ → HmacOracle.QueryCache)
    {step : StateT σ (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) β} {m n : ℕ}
    (charged : ChargedG setup R step m) (le : m ≤ n) : ChargedG setup R step n := fun b s q =>
  (charged b s q).trans (tablePotential_mono setup _ (by omega) _)

/-- A coins-only slot step costs what its program costs on the R1 table. -/
theorem chargedG_lift {σ β : Type} (R : σ → HmacOracle.QueryCache) (work : StateT σ ProbComp β) (n : ℕ)
    (charged : ∀ key b s, expectedValue (work.run s) (fun r => tablePotential setup key b (R r.2)) ≤
      tablePotential setup key (b + n) (R s)) :
    ChargedG setup R (PqxdhDeploymentIdealSteps.onSlots work) n := by
  intro b s q
  change expectedValue ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
    (PqxdhDeploymentIdealSteps.liftS (work.run s))).run q) _ ≤ _
  rw [PqxdhDeploymentIdealErase.slotImpl_coins, OracleComp.EvalDist.expectedValue_map]
  exact charged (slotKeyOf q) b s

/-- A lazy material read does not raise the table potential in expectation: the first draw of slot 0's material averages the hits over a uniform key (`hits_draw`, `average_mass`). -/
theorem material_read (j : PqxdhRecordLiftInterface.Slot 2) (mat : PqxdhDeploymentIdealKernel.MatCache 2) (b : ℕ)
    (T : HmacOracle.QueryCache) :
    expectedValue (((PqxdhDeploymentSeedSplit.MaterialSpec 2).randomOracle j).run mat)
      (fun r => tablePotential setup ((r.2 0).map Prod.fst) b T) ≤
        tablePotential setup ((mat 0).map Prod.fst) b T := by
  cases found : mat j with
  | some m =>
      rw [LazyOracleDiscard.query_of_some found, OracleComp.EvalDist.expectedValue_pure]
  | none =>
      rw [LazyOracleDiscard.query_of_none found, OracleComp.EvalDist.expectedValue_bind]
      simp only [OracleComp.EvalDist.expectedValue_pure]
      by_cases zero : j = 0
      · subst zero
        simp only [QueryCache.cacheQuery_self, Option.map_some, found, Option.map_none]
        change expectedValue ($ᵗ PqxdhDeploymentHiddenLayout.Material : ProbComp _)
          (fun m => tablePotential setup (some m.1) b T) ≤ _
        rw [PqxdhDeploymentHeadlineDctTools.material_marginal (fun k => tablePotential setup (some k) b T)]
        simp only [tablePotential]
        rw [OracleComp.EvalDist.expectedValue_add, PqxdhDeploymentHeadlineDctTools.hits_draw,
          PqxdhDeploymentHeadlineDctTools.keyPart_card]
        have averaged : expectedValue ($ᵗ RawCtxKdfRequestTable.KeyPart : ProbComp RawCtxKdfRequestTable.KeyPart)
            (fun k => (b : ℝ≥0∞) * mass (seqKey setup) k) ≤ (b : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
          simp only [mul_comm (b : ℝ≥0∞)]
          rw [OracleComp.EvalDist.expectedValue_mul_const]
          have bound := PqxdhDeploymentHeadlineDctTools.average_mass (W := RawCtxKdfRequestTable.KeyPart)
            (seqKey setup)
          rw [PqxdhDeploymentHeadlineDctTools.keyPart_card] at bound
          simp only [Nat.cast_pow, Nat.cast_ofNat] at bound
          gcongr
        calc _ ≤ size T * ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹ + (b : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := add_le_add le_rfl averaged
          _ = (size T + b) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
              simp only [Nat.cast_pow, Nat.cast_ofNat]
              ring
      · have other : ∀ m, (mat.cacheQuery j m) 0 = mat 0 := fun m =>
          QueryCache.cacheQuery_of_ne _ _ (Ne.symm zero)
        simp only [other]
        exact OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl

/-- A read through the allocator in front of the lazy service does not raise the table potential in expectation. -/
theorem slot_read (c : PqxdhDeploymentIdealSlots.Coord) (q : SlotState) (b : ℕ) (T : HmacOracle.QueryCache) :
    expectedValue ((PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy (.inr c)).run q)
      (fun r => tablePotential setup (slotKeyOf r.2) b T) ≤ tablePotential setup (slotKeyOf q) b T := by
  rcases found : q.1.1 c with _ | slot
  · by_cases room : q.1.2 < 2
    · rw [PqxdhDeploymentIdealDefer.slotImpl_lazy_new c q found room, OracleComp.EvalDist.expectedValue_map]
      exact material_read setup _ q.2.1 b T
    · simp only [PqxdhRegistrationJointKemSecondEntry.slotImpl, QueryImpl.add_apply_inr, StateT.run_mk, found, room,
        _root_.dite_false, OracleComp.EvalDist.expectedValue_map]
      exact OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl
  · rw [PqxdhDeploymentIdealDefer.slotImpl_lazy_found c q slot found, OracleComp.EvalDist.expectedValue_map]
    exact material_read setup slot q.2.1 b T

/-- A value request at fixed coordinates costs nothing. -/
theorem chargedG_read {σ : Type} (R : σ → HmacOracle.QueryCache) (c : PqxdhDeploymentIdealSlots.Coord) :
    ChargedG setup R (PqxdhDeploymentIdealErase.readAt (σ := σ) c) 0 := by
  intro b s q
  change expectedValue ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
    ((fun v => (v, s)) <$> (PqxdhDeploymentIdealSlots.SlotSpec.query (.inr c) :
      OracleComp PqxdhDeploymentIdealSlots.SlotSpec _))).run q) _ ≤ _
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, OracleComp.EvalDist.expectedValue_map]
  exact slot_read setup c q b (R s)

/-- A whole program on slot callbacks is charged its budget of costly requests when each costly request costs one unit and every other request costs nothing (the nested simulation is flattened, `simulateQ_mapStateTBase_run_eq_map_flattenStateT`). -/
theorem chargedG_run {κ α σ : Type} {spec : OracleSpec κ} (R : σ → HmacOracle.QueryCache)
    (inner : QueryImpl spec (StateT σ (OracleComp PqxdhDeploymentIdealSlots.SlotSpec))) (costly : κ → Prop)
    [DecidablePred costly] (paid : ∀ query, costly query → ChargedG setup R (inner query) 1)
    (free : ∀ query, ¬ costly query → ChargedG setup R (inner query) 0) (work : OracleComp spec α) (n : ℕ)
    (bounded : work.IsQueryBoundP costly n) : ChargedG setup R (simulateQ inner work) n := by
  intro b s q
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, OracleComp.EvalDist.expectedValue_map]
  have flatStep : ∀ (query : κ) (state : σ × SlotState) (c : ℕ),
      expectedValue ((((PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy).mapStateTBase
        inner).flattenStateT query).run state) (fun r => tablePotential setup (slotKeyOf r.2.2) (b + c) (R r.2.1)) =
      expectedValue ((simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
        ((inner query).run state.1)).run state.2)
          (fun r => tablePotential setup (slotKeyOf r.2) (b + c) (R r.1.2)) := by
    intro query state c
    obtain ⟨s', q'⟩ := state
    change expectedValue ((fun z : (spec.Range query × σ) × SlotState => (z.1.1, (z.1.2, z.2))) <$>
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy)
        ((inner query).run s')).run q') _ = _
    rw [OracleComp.EvalDist.expectedValue_map]
  have run := PqxdhDeploymentHeadlineDctTools.expected_run_bounded
    (((PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentIdealKernel.lazyDummy).mapStateTBase
      inner).flattenStateT) costly (fun c state => tablePotential setup (slotKeyOf state.2) (b + c) (R state.1))
    (fun c state => tablePotential_mono setup _ (by omega) _)
    (fun query state c costlyQuery => by
      rw [flatStep]
      simpa only [Nat.add_assoc] using paid query costlyQuery (b + c) state.1 state.2)
    (fun query state c freeQuery => by
      rw [flatStep]
      simpa only [Nat.add_zero] using free query freeQuery (b + c) state.1 state.2) work n bounded (s, q)
  simpa only [Nat.add_zero] using run

end Slots

/-! ### The commands -/

section Commands
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder)

/-- The R1 charge of a command: one unit for a raw accept, a Beacon finish and a public HMAC (each makes at most one R1 read), nothing for every other query. -/
def r1Costly (query : PqxdhDeploymentInterface.Spec.Domain) : Prop :=
  PqxdhDeploymentCompileBudget.commandKind query = 3 ∨ PqxdhDeploymentCompileBudget.commandKind query = 5 ∨
    PqxdhDeploymentCompileBudget.commandKind query = 6

instance (query : PqxdhDeploymentInterface.Spec.Domain) : Decidable (r1Costly query) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The native build keeps the R1 table. -/
theorem chargedN_build (session : ℕ) (payload : Option Pqxdh.Bytes) :
    ChargedN setup (PqxdhServerAuthNative.nativeBuild setup codec checks session payload) 0 := by
  unfold PqxdhServerAuthNative.nativeBuild
  refine chargedN_bind setup (m := 0) (n := 0) (chargedN_local setup _) fun state => ?_
  split
  · exact chargedN_pure setup _
  · exact chargedN_bind setup (m := 0) (n := 0) (chargedN_coins setup _) fun _ =>
      chargedN_bind setup (m := 0) (n := 0) (chargedN_local setup _) fun _ => chargedN_pure setup _

/-- Every query of the native deployment handler is charged at most its R1 charge. -/
theorem chargedD_handler (seed : PqxdhJointIdentity.IdentitySeed) (query : PqxdhDeploymentInterface.Spec.Domain) :
    ChargedD setup (PqxdhDeploymentNative.handler setup codec checks route seed query)
      (if r1Costly query then 1 else 0) := by
  have shared : ∀ {α : Type} (work : PqxdhRegistrationSchedule.Game KemSK α),
      (∀ state, ∀ r ∈ support (work.run state), r.2.shared = state.shared) →
      ChargedD setup (PqxdhDeploymentNative.onNative work) 0 := fun work kept =>
    chargedD_onNative setup (chargedR_frame setup work fun state r member => by rw [kept state r member])
  rcases query with coin | command
  · refine chargedD_frame setup _ fun state r member => ?_
    simp only [PqxdhDeploymentNative.handler, StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · cases command with
    | create pin keyId =>
        refine chargedD_frame setup _ fun state r member => ?_
        change r ∈ support ((match PqxdhDeploymentInterface.parsePin pin with
          | none => pure none
          | some word => some <$> PqxdhDeploymentNative.onNative (PqxdhRegistrationSchedule.handler setup codec checks
              seed (.inr (.create word keyId)))).run state) at member
        split at member
        · rw [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
          subst member
          rfl
        · rw [StateT.run_map, support_map] at member
          obtain ⟨inner, innerMember, rfl⟩ := member
          obtain ⟨created, createdMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ state inner innerMember
          change created ∈ support ((PqxdhRegistrationSchedule.create setup _ keyId).run state.native) at createdMember
          simp only [PqxdhRegistrationSchedule.create, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
            StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
            at createdMember
          obtain ⟨_, _, _, _, _, _, rfl⟩ := createdMember
          rfl
    | bundle index =>
        refine shared _ fun native bundled bundledMember => ?_
        cases found : native.owners[index]? with
        | none =>
            change bundled ∈ support ((PqxdhRegistrationSchedule.bundle setup codec index).run native) at bundledMember
            simp only [PqxdhRegistrationSchedule.bundle, StateT.run_bind, StateT.run_get, pure_bind, found,
              StateT.run_pure, support_pure, Set.mem_singleton_iff] at bundledMember
            rw [bundledMember]
        | some owner =>
            change bundled ∈ support (PqxdhRegistrationSchedule.bundle setup codec index native) at bundledMember
            rw [PqxdhRegistrationSchedule.bundle_source setup codec index native owner found, support_map] at bundledMember
            obtain ⟨_, _, rfl⟩ := bundledMember
            rfl
    | accept raw => exact chargedD_onNative setup (chargedR_onShared setup (chargedN_accept setup checks codec _ _ raw))
    | build session payload =>
        exact chargedD_onNative setup (chargedR_onShared setup (chargedN_build setup codec checks session payload))
    | finish owner raw => exact chargedD_onNative setup (chargedR_finish setup codec owner raw)
    | hmac key message => exact chargedD_onNative setup (chargedR_onShared setup (chargedN_hmac setup _ _ key message))
    | hash bytes =>
        refine chargedD_onNative setup (chargedR_onShared setup (chargedN_frame setup _ fun state r member => ?_))
        change r ∈ support ((fun result => (result.1, (state.1, { state.2 with ctx := result.2 }))) <$>
          (CtxRomAuth.ctxRandomOracle ((), bytes)).run state.2.ctx) at member
        rw [support_map] at member
        obtain ⟨_, _, rfl⟩ := member
        rfl
    | serverSend keyId plaintext =>
        exact chargedD_frame setup _ fun state r member => by
          exact congrArg (fun shared => shared.cache)
            (PqxdhDeploymentNative.serverStep_fields setup codec route (.inl (plaintext, keyId)) state r member).2.2.1
    | serverRaw raw =>
        exact chargedD_frame setup _ fun state r member => by
          exact congrArg (fun shared => shared.cache)
            (PqxdhDeploymentNative.serverStep_fields setup codec route (.inr raw) state r member).2.2.1
    | beaconSend owner plaintext =>
        exact chargedD_frame setup _ fun state r member => by
          exact congrArg (fun shared => shared.cache)
            (PqxdhDeploymentNative.beaconStep_fields setup codec owner (.inl plaintext) state r member).2.1
    | beaconRaw owner raw =>
        exact chargedD_frame setup _ fun state r member => by
          exact congrArg (fun shared => shared.cache)
            (PqxdhDeploymentNative.beaconStep_fields setup codec owner (.inr raw) state r member).2.1

end Commands

/-! ### The registration commands as slot clients -/

section SlotCommands
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (liftS onSlots)

local notation "lazySlots" =>
  PqxdhRegistrationJointKemSecondEntry.slotImpl (PqxdhDeploymentIdealKernel.lazyDummy (n := 2))

/-- An expectation of a function constant on the support is at most that constant. -/
theorem expected_frame {α : Type} (work : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞)
    (constant : ∀ r ∈ support work, f r = c) : expectedValue work f ≤ c :=
  le_trans (OracleComp.EvalDist.expectedValue_mono_of_support fun r member => le_of_eq (constant r member))
    (OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl)

/-- A coins-only native slot step on a native state with a side component costs what its native program costs. -/
theorem chargedG_native {τ α : Type} (work : NativeGame KemSK α) (n : ℕ) (charged : ChargedN setup work n) :
    ChargedG setup (fun z : NativeState KemSK × τ => z.1.1.cache)
      (fun s => (fun r => (r.1, (r.2, s.2))) <$> liftS (work.run s.1)) n := by
  intro b s q
  change expectedValue ((simulateQ lazySlots ((fun r => (r.1, (r.2, s.2))) <$> liftS (work.run s.1))).run q) _ ≤ _
  rw [simulateQ_map, StateT.run_map, PqxdhDeploymentIdealErase.slotImpl_coins, OracleComp.EvalDist.expectedValue_map,
    OracleComp.EvalDist.expectedValue_map]
  exact charged (slotKeyOf q) b s.1

/-- A coins-only native slot step on the native state, with its reply mapped, costs what its native program costs. -/
theorem chargedG_nativeMap {α β : Type} (work : NativeGame KemSK α)
    (g : α × NativeState KemSK → β × NativeState KemSK) (kept : ∀ r, (g r).2 = r.2) (n : ℕ)
    (charged : ChargedN setup work n) :
    ChargedG setup (fun s : NativeState KemSK => s.1.cache) (fun s => g <$> liftS (work.run s)) n := by
  intro b s q
  change expectedValue ((simulateQ lazySlots (g <$> liftS (work.run s))).run q) _ ≤ _
  rw [simulateQ_map, StateT.run_map, PqxdhDeploymentIdealErase.slotImpl_coins, OracleComp.EvalDist.expectedValue_map,
    OracleComp.EvalDist.expectedValue_map]
  simp only [kept]
  exact charged (slotKeyOf q) b s

/-- A coins-only slot step that keeps its state costs nothing. -/
theorem chargedG_coins {σ α : Type} (R : σ → HmacOracle.QueryCache) (work : ProbComp α) :
    ChargedG setup R (fun s => (fun reply => (reply, s)) <$> liftS work) 0 := by
  intro b s q
  change expectedValue ((simulateQ lazySlots ((fun reply => (reply, s)) <$> liftS work)).run q) _ ≤ _
  rw [simulateQ_map, StateT.run_map, PqxdhDeploymentIdealErase.slotImpl_coins, OracleComp.EvalDist.expectedValue_map,
    OracleComp.EvalDist.expectedValue_map]
  exact OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl

/-- The Server's marker-client root request costs one unit. -/
theorem chargedN_romRoot (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) :
    ChargedN setup (PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index candidate input) 1 := by
  unfold PqxdhRegistrationJointKemOpaqueClient.romRoot
  exact chargedN_bind setup (m := 1) (n := 0) (chargedN_romRootBytes setup _ _ _) fun _ =>
    chargedN_bind setup (m := 0) (n := 0) (chargedN_local setup _) fun _ => chargedN_pure setup _

/-- The marker client's auxiliary requests cost nothing. -/
theorem chargedN_auxiliary (query : PqxdhServerRelatedRootConsumer.Auxiliary) :
    ChargedN setup (PqxdhRegistrationJointKemOpaqueClient.auxiliary KemSK query) 0 := by
  refine chargedN_frame setup _ fun state r member => ?_
  cases query <;>
  · change r ∈ support (pure _ : ProbComp _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl

/-- The marker tail's state mutations cost nothing. -/
theorem chargedN_mutation (query : PqxdhRegistrationJointKemOpaqueTail.Mutation KemSK) :
    ChargedN setup (PqxdhRegistrationJointKemOpaqueTail.mutation query) 0 := by
  refine chargedN_frame setup _ fun state r member => ?_
  cases query <;>
  · change r ∈ support (pure _ : ProbComp _) at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl

/-- The native accept tail costs one unit. -/
theorem chargedN_acceptTail (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) × List Pqxdh.Bytes) :
    ChargedN setup (PqxdhRegistrationJointServerAccept.tail setup publicIdentity state collected) 1 := by
  unfold PqxdhRegistrationJointServerAccept.tail
  refine chargedN_bind setup (m := 0) (n := 1) (chargedN_local setup _) fun _ => ?_
  rcases collected with ⟨_ | input, consumed⟩
  · exact chargedN_mono setup (chargedN_pure setup _) (by omega)
  · dsimp only
    refine chargedN_mono setup (m := 1 + 0) (chargedN_bind setup (chargedN_client setup _ _ _ _ _) fun returned => ?_)
      (by omega)
    split
    · exact chargedN_bind setup (m := 0) (n := 0) (chargedN_local setup _) fun _ => chargedN_pure setup _
    · exact chargedN_pure setup _

/-- The marked build keeps the R1 table. -/
theorem chargedN_buildHidden (hidden : PqxdhRegistrationJointKemPostSkeleton.Hidden Response) (session : ℕ)
    (payload : Option Pqxdh.Bytes) :
    ChargedN setup (PqxdhDeploymentIdealSteps.buildHidden (KemSK := KemSK) hidden session payload) 0 := by
  unfold PqxdhDeploymentIdealSteps.buildHidden
  refine chargedN_bind setup (m := 0) (n := 0) (chargedN_local setup _) fun state => ?_
  split
  · exact chargedN_pure setup _
  · exact chargedN_bind setup (m := 0) (n := 0) (chargedN_coins setup _) fun _ =>
      chargedN_bind setup (m := 0) (n := 0) (chargedN_local setup _) fun _ => chargedN_pure setup _

/-- The known-handle grouped finish of the Beacon costs one unit: the private root read, then the continuation on the CTX cache. -/
theorem chargedN_knownGroup (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) :
    ChargedN setup ((do
      let root ← PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac (List.Vector.replicate 32 0)
        pending.root
      match root with
      | none => pure none
      | some root => PqxdhServerAuthNative.nativeCtx (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative
          setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)) :
      NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged))) 1 := by
  refine chargedN_bind setup (m := 1) (n := 0) ?_ fun root => ?_
  · unfold PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot
    split
    · exact chargedN_sourceRoot setup _ _
    · exact chargedN_mono setup (chargedN_pure setup _) (by omega)
  · cases root with
    | none => exact chargedN_pure setup _
    | some root => exact chargedN_ctx setup _

/-- Every request of the Server's marker tail costs one unit at a root request and nothing otherwise. -/
theorem chargedG_tailCE (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (query : (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK).Domain) :
    ChargedG setup (fun z : NativeState KemSK × Option (ℕ × Coord) => z.1.1.cache)
      (PqxdhDeploymentIdealSteps.tailCE hmac index query)
      (if PqxdhDeploymentIdealEnvFacts.isRoot query = true then 1 else 0) := by
  rcases query with (input | query) | query
  · show ChargedG setup _ _ 1
    intro b s q
    change expectedValue ((simulateQ lazySlots (PqxdhDeploymentIdealSteps.tailCE hmac index (.inl (.inl input)) s)).run q)
      _ ≤ _
    cases shared : input.shared with
    | challenge =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, shared]
        rw [simulateQ_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
        simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure, simulateQ_spec_query]
        exact (slot_read setup _ q b s.1.1.cache).trans (tablePotential_mono setup _ (by omega) _)
    | known value =>
        simp only [PqxdhDeploymentIdealSteps.tailCE, shared]
        exact chargedG_native setup _ 1 (chargedN_romRoot setup _ _ _ _) b s q
  · show ChargedG setup _ _ 0
    exact chargedG_native setup _ 0 (chargedN_auxiliary setup query)
  · show ChargedG setup _ _ 0
    exact chargedG_native setup _ 0 (chargedN_mutation setup query)

/-- The Server's marker tail under `tailCE` costs one unit. -/
theorem chargedG_tail (hmac : PqxdhSecretInputKdf.HmacSha512) (serverKeyId : Aeneas.Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    ChargedG setup (fun z : NativeState KemSK × Option (ℕ × Coord) => z.1.1.cache)
      (simulateQ (PqxdhDeploymentIdealSteps.tailCE hmac state.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)) 1 :=
  chargedG_run setup _ _ (fun query => PqxdhDeploymentIdealEnvFacts.isRoot query = true)
    (fun query root => by simpa only [root, ↓reduceIte] using chargedG_tailCE setup hmac state.sessions query)
    (fun query notRoot => by
      simp only [Bool.not_eq_true] at notRoot
      simpa only [notRoot, Bool.false_eq_true, ↓reduceIte] using chargedG_tailCE setup hmac state.sessions query)
    _ 1 (PqxdhDeploymentIdealEnvFacts.tail_root serverKeyId publicIdentity state collected)

/-- The active selected accept costs one unit. -/
theorem chargedG_acceptActive (seed : PqxdhJointIdentity.IdentitySeed)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (verified : PqxdhServerRootPreparation.Verified Reader) :
    ChargedG setup (fun s : NativeState KemSK => s.1.cache)
      (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge verified) 1 := by
  intro b s q
  change expectedValue ((simulateQ lazySlots (PqxdhDeploymentIdealSteps.acceptActive setup codec checks seed challenge
    verified s)).run q) _ ≤ _
  unfold PqxdhDeploymentIdealSteps.acceptActive
  rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealErase.slotImpl_coins, bind_map_left]
  refine OracleComp.EvalDist.expectedValue_bind_le_of_le fun pre => ?_
  split
  · rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealErase.slotImpl_coins, bind_map_left,
      OracleComp.EvalDist.expectedValue_bind]
    simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
    exact chargedN_acceptTail setup _ _ _ (slotKeyOf q) b s
  · rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealErase.slotImpl_coins, bind_map_left]
    refine OracleComp.EvalDist.expectedValue_bind_le_of_le fun prepared => ?_
    rw [simulateQ_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
    simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
    exact chargedG_tail setup setup.hmac _ _ s.2 _ b (s, none) q

/-- The selected raw accept with its encapsulation exposed costs one unit. -/
theorem chargedG_acceptExposed (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) :
    ChargedG setup (fun s : NativeState KemSK => s.1.cache)
      (PqxdhDeploymentIdealSteps.acceptExposed setup codec checks seed chosen challenge raw) 1 := by
  have inactive : ChargedG setup (fun s : NativeState KemSK => s.1.cache)
      (PqxdhDeploymentIdealSteps.acceptInactive setup codec checks seed raw) 1 := by
    unfold PqxdhDeploymentIdealSteps.acceptInactive
    exact chargedG_nativeMap setup (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw)
      (fun r => ((r.1, (false, none)), r.2)) (fun _ => rfl) 1 (chargedN_acceptLogged setup checks codec seed raw)
  unfold PqxdhDeploymentIdealSteps.acceptExposed
  split
  · split
    · exact chargedG_acceptActive setup codec checks seed challenge _
    · exact inactive
  · exact inactive

/-- The grouped finish request of the native owner. -/
def ownerGroupCE : (PqxdhDeploymentIdealSteps.OwnerSpecCE KemSK Response).Domain → Bool
  | .inr _ => true
  | .inl _ => false

/-- The grouped native owner issues at most one grouped finish request. -/
theorem groupedOwnerCE_bound (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.Owner KemSK) :
    (PqxdhDeploymentIdealSteps.groupedOwnerCE (Response := Response) raw state).IsQueryBoundP
      (fun query => ownerGroupCE query = true) 1 := by
  unfold PqxdhDeploymentIdealSteps.groupedOwnerCE
  split
  · refine isQueryBoundP_bind (n := 0) (m := 1) (PqxdhRegistrationJointKemRomSplit.simulate_free _ _
      (fun query => ?_) _) fun prepared _ => ?_
    · exact PqxdhRegistrationJointKemRomSplit.query_free _ _ (by simp [ownerGroupCE])
    cases prepared with
    | none => trivial
    | some prepared =>
        exact isQueryBoundP_bind (n := 1) (m := 0) (PqxdhRegistrationJointKemRomSplit.query_one _ _) fun _ _ => trivial
  · trivial

/-- The CE-native grouped finish costs one unit. -/
theorem chargedG_groupCE (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) :
    ChargedG setup (fun z : NativeState KemSK × Option Coord => z.1.1.cache)
      (PqxdhDeploymentIdealSteps.groupCE setup codec hidden pending) 1 := by
  intro b s q
  change expectedValue ((simulateQ lazySlots (PqxdhDeploymentIdealSteps.groupCE setup codec hidden pending s)).run q)
    _ ≤ _
  unfold PqxdhDeploymentIdealSteps.groupCE
  split
  · split
    · rw [simulateQ_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
      simp only [simulateQ_spec_query]
      refine le_trans (OracleComp.EvalDist.expectedValue_mono _ fun read => ?_) ((slot_read setup _ q b s.1.1.cache).trans
        (tablePotential_mono setup _ (by omega) _))
      rw [simulateQ_bind, StateT.run_bind, PqxdhDeploymentIdealErase.slotImpl_coins, bind_map_left,
        OracleComp.EvalDist.expectedValue_bind]
      simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
      refine expected_frame _ _ _ fun r member => ?_
      rw [PqxdhDeploymentHeadlineDctFinish.nativeCtx_keeps _ s.1 r member]
    · simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
      exact tablePotential_mono setup _ (by omega) _
  · exact chargedG_native setup _ 1 (chargedN_knownGroup setup codec pending) b s q

/-- Owner k's challenge finish costs one unit. -/
theorem chargedG_finishChallenge
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (index : ℕ) (raw : Pqxdh.Bytes) :
    ChargedG setup (fun z : PqxdhRegistrationSchedule.State KemSK × Option Coord => z.1.shared.1.cache)
      (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden challenge index raw) 1 := by
  intro b s q
  change expectedValue ((simulateQ lazySlots (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden challenge
    index raw s)).run q) _ ≤ _
  unfold PqxdhDeploymentIdealSteps.finishChallenge
  split
  · simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
    exact tablePotential_mono setup _ (by omega) _
  · rw [simulateQ_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
    simp only [simulateQ_pure, StateT.run_pure, OracleComp.EvalDist.expectedValue_pure]
    exact chargedG_run setup (fun z : NativeState KemSK × Option Coord => z.1.1.cache)
      (PqxdhDeploymentIdealSteps.ownerImplCE setup codec hidden challenge) (fun query => ownerGroupCE query = true)
      (fun query grouped => by
        rcases query with query | pending
        · simp [ownerGroupCE] at grouped
        · exact chargedG_groupCE setup codec hidden pending)
      (fun query single => by
        rcases query with query | pending
        · exact chargedG_coins setup _ _
        · simp [ownerGroupCE] at single) _ 1 (groupedOwnerCE_bound raw _) b (s.1.shared, s.2) q

end SlotCommands

/-! ### The ideal registration and the split handler -/

section Split
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ}
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (liftS onSlots IdealCore SplitBk)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentHeadlineDctCommit (r1 slotKey)

local notation "lazySlots" =>
  PqxdhRegistrationJointKemSecondEntry.slotImpl (PqxdhDeploymentIdealKernel.lazyDummy (n := 2))

/-- The real registration handler on any backend is charged its command's R1 charge. -/
theorem realRegAt_charged {Bk : Type} {n : ℕ} (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhRecordLiftInterface.EnvQuery) (key : Option RawCtxKdfRequestTable.KeyPart) (b : ℕ)
    (x : XState KemSK Bk n) :
    expectedValue ((PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created query).run x)
      (fun r => tablePotential setup key b r.2.base.native.shared.1.cache) ≤
        tablePotential setup key (b + if r1Costly (.inr query.val) then 1 else 0) x.base.native.shared.1.cache := by
  obtain ⟨command, env⟩ := query
  rcases Classical.em (∃ raw, command = .accept raw) with accept | accept
  · obtain ⟨raw, rfl⟩ := accept
    rw [PqxdhDeploymentIdealEnvReal.realRegAt_accept setup codec checks route created raw x,
      OracleComp.EvalDist.expectedValue_map]
    exact chargedN_acceptLogged setup checks codec created.seed raw key b x.base.native.shared
  · rw [PqxdhDeploymentIdealEnvReal.realRegAt_quiet setup codec checks route created ⟨command, env⟩
      (fun raw same => accept ⟨raw, same⟩) x, OracleComp.EvalDist.expectedValue_map]
    exact chargedD_handler setup codec checks route created.seed (.inr command) key b x.base

/-- The body of a create keeps the shared native state. -/
theorem createReg_shared {Γ : Type} {m : ℕ} (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes)
    (keyId : Aeneas.Std.U64) (y : XState KemSK Γ m) (z : Option ℕ × XState KemSK Γ m)
    (member : z ∈ support ((PqxdhDeploymentIdealSteps.createReg setup pool pin keyId).run y)) :
    z.2.base.native.shared = y.base.native.shared := by
  have based := PqxdhDeploymentIdealCut.onBase_base (match PqxdhDeploymentInterface.parsePin pin with
    | none => pure none
    | some word => some <$> PqxdhDeploymentNative.onNative (PqxdhDeploymentIdealSteps.createPool setup pool word keyId)) y
  have step : (z.1, z.2.base) ∈ support ((match PqxdhDeploymentInterface.parsePin pin with
      | none => pure none
      | some word => some <$> PqxdhDeploymentNative.onNative (PqxdhDeploymentIdealSteps.createPool setup pool word
          keyId) : StateT (PqxdhDeploymentNative.State KemSK) ProbComp (Option ℕ)).run y.base) := by
    rw [← based.1, support_map]
    exact ⟨z, member, rfl⟩
  cases parsed : PqxdhDeploymentInterface.parsePin pin with
  | none =>
      simp only [parsed, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at step
      rw [step.2]
  | some word =>
      simp only [parsed, StateT.run_map] at step
      rw [support_map] at step
      obtain ⟨native, nativeMember, same⟩ := step
      simp only [Prod.mk.injEq] at same
      rw [← same.2]
      obtain ⟨reached, reachedMember, rfl⟩ := PqxdhDeploymentEligibility.onNative_support _ y.base native nativeMember
      exact (PqxdhDeploymentIdealKeymatch.createPool_facts setup pool word keyId y.base.native reached reachedMember).1

/-- The create of the ideal registration keeps the R1 table. -/
theorem chargedG_create (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes)
    (keyId : Aeneas.Std.U64) :
    ChargedG setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache)
      (onSlots (PqxdhDeploymentIdealSteps.createReg setup pool pin keyId)) 0 :=
  chargedG_lift setup _ _ 0 fun key b y => expected_frame _ _ _ fun z member => by
    rw [createReg_shared setup pool pin keyId y z member]
    rfl

/-- The raw accept of the ideal registration costs one unit. -/
theorem chargedG_acceptStep (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (raw : Pqxdh.Bytes) :
    ChargedG setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache)
      (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw) 1 := by
  intro b x q
  change expectedValue ((simulateQ lazySlots (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created
    raw x)).run q) _ ≤ _
  unfold PqxdhDeploymentIdealSteps.acceptStep
  split
  · rw [simulateQ_map, StateT.run_map, OracleComp.EvalDist.expectedValue_map]
    exact chargedG_acceptExposed setup codec checks created.seed p.chosen p.challenge raw b x.base.native.shared q
  · exact chargedG_lift setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache) _ 1
      (fun key b y => realRegAt_charged setup codec checks route created ⟨.accept raw, trivial⟩ key b y) b _ q

/-- The marked build after its hidden read keeps the R1 table. -/
theorem chargedG_buildHiddenC
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : Coord) :
    ChargedG setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache)
      (PqxdhDeploymentIdealKernel.buildHiddenC hidden session payload coords) 0 := by
  unfold PqxdhDeploymentIdealKernel.buildHiddenC
  refine chargedG_bind setup _ (m := 0) (n := 0) (chargedG_read setup _ coords) fun value => ?_
  refine chargedG_lift setup _ _ 0 fun key b y => ?_
  rw [StateT.run_map, OracleComp.EvalDist.expectedValue_map]
  show expectedValue (PqxdhDeploymentIdealErase.buildFocus (hidden value) session payload coords y) _ ≤ _
  unfold PqxdhDeploymentIdealErase.buildFocus
  rw [OracleComp.EvalDist.expectedValue_map]
  exact chargedN_buildHidden setup (hidden value) session payload key b y.base.native.shared

/-- The build of the ideal registration keeps the R1 table. -/
theorem chargedG_buildStepC
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (session : ℕ) (payload : Option Pqxdh.Bytes) :
    ChargedG setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache)
      (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route hidden created session payload) 0 := by
  intro b x q
  change expectedValue ((simulateQ lazySlots (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route hidden
    created session payload x)).run q) _ ≤ _
  unfold PqxdhDeploymentIdealKernel.buildStepC
  split
  · split
    · exact chargedG_buildHiddenC setup hidden session payload _ b x q
    · rw [simulateQ_map, StateT.run_map, OracleComp.EvalDist.expectedValue_map]
      exact chargedG_lift setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache) _ 0
        (fun key b y => realRegAt_charged setup codec checks route created ⟨.build session payload, trivial⟩ key b y)
        b x q
  · rw [simulateQ_map, StateT.run_map, OracleComp.EvalDist.expectedValue_map]
    exact chargedG_lift setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache) _ 0
      (fun key b y => realRegAt_charged setup codec checks route created ⟨.build session payload, trivial⟩ key b y)
      b x q

/-- The finish of the ideal registration costs one unit. -/
theorem chargedG_finishStepC (t : Target count) (p : Params KemSK count)
    (hidden : PqxdhServerAuthKeySchedule.Output → PqxdhRegistrationJointKemPostSkeleton.Hidden Response)
    (created : PqxdhLiveServerConstruction.Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) :
    ChargedG setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache)
      (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p hidden created owner raw) 1 := by
  intro b x q
  change expectedValue ((simulateQ lazySlots (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
    hidden created owner raw x)).run q) _ ≤ _
  unfold PqxdhDeploymentIdealKernel.finishStepC
  split
  · change expectedValue ((simulateQ lazySlots ((fun r => ((r.1, r.2.2), PqxdhDeploymentIdealKernel.assembleF x owner
      r.2)) <$> (PqxdhDeploymentIdealSteps.finishChallenge setup codec hidden p.challenge owner raw).run
        (x.base.native, none))).run q) _ ≤ _
    rw [simulateQ_map, StateT.run_map, OracleComp.EvalDist.expectedValue_map]
    exact chargedG_finishChallenge setup codec hidden p.challenge owner raw b (x.base.native, none) q
  · rw [simulateQ_map, StateT.run_map, OracleComp.EvalDist.expectedValue_map]
    exact chargedG_lift setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache) _ 1
      (fun key b y => realRegAt_charged setup codec checks route created ⟨.finish owner raw, trivial⟩ key b y) b x q

/-- The table potential of the extended state at budget `b`: the R1 table against the key part of slot 0's material, once drawn. -/
noncomputable def keyPotential (b : ℕ) (x : XState KemSK SplitBk 2) : ℝ≥0∞ :=
  tablePotential setup (slotKey x) b (r1 x)

/-- A program on the extended state charged `n` units of the table budget. -/
def ChargedX {β : Type} (work : StateT (XState KemSK SplitBk 2) ProbComp β) (n : ℕ) : Prop :=
  ∀ b x, expectedValue (work.run x) (fun r => keyPotential setup b r.2) ≤ keyPotential setup (b + n) x

/-- A slot program run against the allocator in front of the lazy service is charged what it is charged as a slot client. -/
theorem chargedX_slotRunX {β : Type} (step : StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) β) (n : ℕ)
    (charged : ChargedG setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache) step n) :
    ChargedX setup (PqxdhDeploymentIdealKernel.slotRunX PqxdhDeploymentIdealKernel.lazyDummy step) n := by
  intro b x
  change expectedValue ((fun r => (r.1, PqxdhDeploymentIdealKeys.attachX r.2.1 r.2.2.1 r.2.2.2)) <$>
    (PqxdhDeploymentIdealErase.onPair PqxdhDeploymentIdealKernel.lazyDummy step).run
      (PqxdhDeploymentIdealKeys.detachX x, (x.backend.2.1, (x.backend.1, x.seeds)))) _ ≤ _
  rw [PqxdhDeploymentIdealErase.onPair_run, OracleComp.EvalDist.expectedValue_map, OracleComp.EvalDist.expectedValue_map]
  exact charged b (PqxdhDeploymentIdealKeys.detachX x) (x.backend.2.1, (x.backend.1, x.seeds))

/-- A native deployment step on the base keeps the backend and is charged what it is charged on the base. -/
theorem chargedX_onBase {α : Type} (step : StateT (PqxdhDeploymentNative.State KemSK) ProbComp α) (n : ℕ)
    (charged : ChargedD setup step n) : ChargedX setup (PqxdhDeploymentBackend.onBase step) n := by
  intro b x
  have based := PqxdhDeploymentIdealCut.onBase_base step x
  have bound := charged (slotKey x) b x.base
  rw [← based.1, OracleComp.EvalDist.expectedValue_map] at bound
  refine le_trans (OracleComp.EvalDist.expectedValue_mono_of_support fun r member => le_of_eq ?_) bound
  have key : slotKey r.2 = slotKey x := by
    unfold slotKey
    rw [(based.2 r member).1]
  show tablePotential setup (slotKey r.2) b (r1 r.2) = _
  rw [key]
  rfl

/-- A hidden install after a step does not raise the table potential in expectation: it changes neither the R1 table nor the material cache. -/
theorem install_le {γ : Type} (install : γ × XState KemSK SplitBk 2 → ProbComp (γ × XState KemSK SplitBk 2))
    (kept : ∀ r, ∀ r' ∈ support (install r), r1 r'.2 = r1 r.2 ∧ r'.2.backend.1 = r.2.backend.1) (b : ℕ)
    (r : γ × XState KemSK SplitBk 2) :
    expectedValue (install r) (fun r' => keyPotential setup b r'.2) ≤ keyPotential setup b r.2 :=
  expected_frame _ _ _ fun r' member => by
    unfold keyPotential slotKey
    rw [(kept r r' member).1, (kept r r' member).2]

/-- Every query of the split handler is charged at most its R1 charge. -/
theorem handler_charged (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentInterface.Spec.Domain) :
    ChargedX setup (PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query)
      (if r1Costly query then 1 else 0) := by
  have slot : ∀ (command : PqxdhRecordLiftInterface.EnvQuery) (n : ℕ),
      ChargedG setup (fun y : XState KemSK IdealCore 2 => y.base.native.shared.1.cache)
        (PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p
          (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created command) n →
      ChargedX setup (PqxdhDeploymentIdealKeys.slotCoreX (PqxdhDeploymentIdealSteps.idealProg setup codec route checks t p
        (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks)) PqxdhDeploymentIdealKernel.lazyDummy created
          command) n := fun command n charged => by
    rw [PqxdhDeploymentIdealKernel.slotCoreX_run]
    exact chargedX_slotRunX setup _ n charged
  rcases query with coin | command
  · show ChargedX setup _ 0
    intro b x
    change expectedValue ((StateT.lift (unifSpec.query coin : ProbComp _) :
      StateT (XState KemSK SplitBk 2) ProbComp _).run x) _ ≤ _
    rw [StateT.run_lift, OracleComp.EvalDist.expectedValue_bind]
    simp only [OracleComp.EvalDist.expectedValue_pure]
    exact OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl
  · cases command with
    | create pin keyId =>
        exact slot ⟨.create pin keyId, trivial⟩ 0 (chargedG_create setup _ pin keyId)
    | bundle owner =>
        exact slot ⟨.bundle owner, trivial⟩ 0 (chargedG_lift setup _ _ 0 fun key b y =>
          realRegAt_charged setup codec checks route created ⟨.bundle owner, trivial⟩ key b y)
    | accept raw => exact slot ⟨.accept raw, trivial⟩ 1 (chargedG_acceptStep setup codec checks route t p created raw)
    | hmac key message =>
        exact slot ⟨.hmac key message, trivial⟩ 1 (chargedG_lift setup _ _ 1 fun k b y =>
          realRegAt_charged setup codec checks route created ⟨.hmac key message, trivial⟩ k b y)
    | build session payload =>
        show ChargedX setup _ 0
        intro b x
        change expectedValue ((fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX
          PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.buildStepC setup codec checks route
            (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created session payload)).run x >>=
              PqxdhDeploymentIdealDefer.serverInstall)) _ ≤ _
        rw [OracleComp.EvalDist.expectedValue_map, OracleComp.EvalDist.expectedValue_bind]
        refine le_trans (OracleComp.EvalDist.expectedValue_mono _ fun r => install_le setup _ (fun r r' member =>
          ?_) b r) (chargedX_slotRunX setup _ 0 (chargedG_buildStepC setup codec checks route _ created session payload)
            b x)
        obtain ⟨-, rootKept, -, -, matKept⟩ := PqxdhDeploymentHeadlineDctCommit.serverInstall_keeps r r' member
        exact ⟨congrArg (fun shared => shared.cache) rootKept, matKept⟩
    | finish owner raw =>
        show ChargedX setup _ 1
        intro b x
        change expectedValue ((fun r => (r.1.1, r.2)) <$> ((PqxdhDeploymentIdealKernel.slotRunX
          PqxdhDeploymentIdealKernel.lazyDummy (PqxdhDeploymentIdealKernel.finishStepC setup codec checks route t p
            (PqxdhDeploymentIdealSteps.erasedHidden setup codec checks) created owner raw)).run x >>=
              PqxdhDeploymentIdealDefer.beaconInstall owner)) _ ≤ _
        rw [OracleComp.EvalDist.expectedValue_map, OracleComp.EvalDist.expectedValue_bind]
        refine le_trans (OracleComp.EvalDist.expectedValue_mono _ fun r => install_le setup _ (fun r r' member =>
          ?_) b r) (chargedX_slotRunX setup _ 1 (chargedG_finishStepC setup codec checks route t p _ created owner raw)
            b x)
        obtain ⟨-, sharedKept⟩ := PqxdhDeploymentHeadlineDctCommit.beaconInstall_keeps owner r r' member
        obtain ⟨-, matKept, -⟩ := PqxdhDeploymentIdealDefer.xInstall_support _ _ _ r r' member
        exact ⟨congrArg (fun shared => shared.1.cache) sharedKept, matKept⟩
    | hash bytes =>
        exact chargedX_onBase setup _ _ (chargedD_handler setup codec checks route created.seed (.inr (.hash bytes)))
    | serverSend keyId plaintext =>
        exact chargedX_onBase setup _ _
          (chargedD_handler setup codec checks route created.seed (.inr (.serverSend keyId plaintext)))
    | serverRaw raw =>
        exact chargedX_onBase setup _ _ (chargedD_handler setup codec checks route created.seed (.inr (.serverRaw raw)))
    | beaconSend owner plaintext =>
        exact chargedX_onBase setup _ _
          (chargedD_handler setup codec checks route created.seed (.inr (.beaconSend owner plaintext)))
    | beaconRaw owner raw =>
        exact chargedX_onBase setup _ _
          (chargedD_handler setup codec checks route created.seed (.inr (.beaconRaw owner raw)))

end Split

/-! ### The R1 budget, the hit event and its bound -/

section Bound
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
  (route : RawCtxServerRouting.SenderDecoder) {count : ℕ} {A X : Type}
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)
open PqxdhDeploymentHeadlineDctCommit (r1 slotKey)
open PqxdhDeploymentHeadlineDctEvent (r1Cap)

/-- `wrap_r1_bound`: the wrapped adversary of a budget-respecting adversary makes at most `r1Cap budget` raw accepts, finishes and public HMAC requests (`PqxdhDeploymentCompileSecrecy.wrap_bound` at the three classes, each of whose budget sums is its cap). -/
theorem wrap_r1_bound (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) :
    (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds
      (PqxdhDeploymentInterface.asModeO mode adversary)).IsQueryBoundP r1Costly (r1Cap budget) := by
  have accept := PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode
    adversary budget respects 3
  have finish := PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode
    adversary budget respects 5
  have hmac := PqxdhDeploymentCompileSecrecy.wrap_bound setup.source.crypto codec setup.serverKeyId bounds mode
    adversary budget respects 6
  have acceptSum : ∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds 3 full * budget.cap full = budget.accept := by
    simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost, Budget.cap]
  have finishSum : ∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds 5 full * budget.cap full = budget.finish := by
    simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost, Budget.cap]
  have hmacSum : ∑ full, PqxdhDeploymentCompileSecrecy.wrapCost bounds 6 full * budget.cap full = budget.hmac := by
    simp [Fin.sum_univ_succ, PqxdhDeploymentCompileSecrecy.wrapCost, Budget.cap]
  rw [acceptSum] at accept
  rw [finishSum] at finish
  rw [hmacSum] at hmac
  have joint := PqxdhRegistrationJointKemRomSplit.isQueryBoundP_or _ accept
    (PqxdhRegistrationJointKemRomSplit.isQueryBoundP_or _ finish hmac)
  rw [show budget.accept + (budget.finish + budget.hmac) = r1Cap budget by
    unfold r1Cap
    omega] at joint
  exact joint

/-- The hit event: some value of the R1 table has as sequence-one key the key part of slot 0's material. -/
def KeyHit (x : XState KemSK SplitBk 2) : Prop :=
  ∃ u v k, r1 x u = some v ∧ slotKey x = some k ∧ seqKey setup v = k

/-- On a hit, the table potential at budget zero is at least one. -/
theorem one_le_keyPotential (x : XState KemSK SplitBk 2) (hit : KeyHit setup x) : 1 ≤ keyPotential setup 0 x := by
  obtain ⟨u, v, k, found, keyed, rfl⟩ := hit
  unfold keyPotential tablePotential
  rw [keyed]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  exact PqxdhDeploymentHeadlineDctTools.one_le_hits (seqKey setup) (r1 x) u v found

/-- At the start of the split game the R1 table is empty and slot 0 has no material: the potential is the budget's share. -/
theorem keyPotential_initial (created : PqxdhLiveServerConstruction.Created Unit) (b : ℕ) :
    keyPotential setup b (PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)) =
      (b : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have empty : r1 (PqxdhDeploymentBackend.xinitial (KemSK := KemSK) created
      (PqxdhDeploymentIdealSteps.splitInit created)) = ∅ := rfl
  show (size (r1 (PqxdhDeploymentBackend.xinitial (KemSK := KemSK) created
    (PqxdhDeploymentIdealSteps.splitInit created))) + b) * (2 ^ 256 : ℝ≥0∞)⁻¹ = _
  rw [empty]
  unfold size
  simp

open Classical in
/-- `split_keyHit`: on the final split game at any target and parameters, the hit event has probability at most `r1Cap/2^256` (the potential at the full budget starts at `r1Cap/2^256`, does not increase in expectation, `handler_charged` with `wrap_r1_bound`, and is at least one on a hit at budget zero). -/
theorem split_keyHit (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (runtime : A) :
    𝒟[(fun outcome => outcome.1.any fun value => decide (KeyHit setup value.2.2.2)) <$>
      (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
          adversary).run runtime] {true} ≤ (r1Cap budget : ℝ≥0∞) / 2 ^ 256 := by
  refine (PqxdhDeploymentHeadlineDctTools.chance_le_expected _ _
    (fun outcome => outcome.1.elim 0 fun value => keyPotential setup 0 value.2.2.2) fun outcome _ hit => ?_).trans ?_
  · rcases outcome with ⟨_ | value, after⟩
    · simp at hit
    · simp only [Option.any_some, decide_eq_true_eq] at hit
      exact one_le_keyPotential setup _ hit
  · simp only [PqxdhDeploymentBackend.gameWith, StateT.run]
    rw [OracleComp.EvalDist.expectedValue_bind]
    refine OracleComp.EvalDist.expectedValue_le_of_le _ fun born => ?_
    rcases born with ⟨_ | constructed, after⟩
    · simp
    · dsimp only
      rw [OracleComp.EvalDist.expectedValue_map]
      refine le_trans (PqxdhDeploymentHeadlineDctTools.expected_run_bounded _ r1Costly
        (fun c x => keyPotential setup c x) (fun c x => tablePotential_mono setup _ (by omega) _)
        (fun query x c costly => ?_) (fun query x c free => ?_) _ (r1Cap budget)
        (wrap_r1_bound setup codec bounds mode adversary budget respects) _) (le_of_eq ?_)
      · have charged := handler_charged setup codec checks route t p constructed query c x
        simpa only [costly, ↓reduceIte] using charged
      · have charged := handler_charged setup codec checks route t p constructed query c x
        simpa only [free, ↓reduceIte, Nat.add_zero] using charged
      · rw [keyPotential_initial, div_eq_mul_inv]

open Classical in
/-- `world_keyHit`: on the record world with the ideal environment of any target, the hit event on the reassembled final state without the drawn parameters has probability at most `r1Cap/2^256` (`PqxdhDeploymentIdealEnv.c1_split`, then `split_keyHit` under the draw of the parameters). -/
theorem world_keyHit (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) :
    𝒟[(fun result => (PqxdhDeploymentEnvironmentJoin.joined result).any fun value =>
        decide (KeyHit setup (PqxdhDeploymentEnvironmentDraw.dropX value.2.2.2))) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤ (r1Cap budget : ℝ≥0∞) / 2 ^ 256 := by
  have law := (PqxdhDeploymentIdealEnv.c1_split setup codec route checks t ensureInit identityIndex runtime bounds mode
    adversary).map (fun outcome => outcome.any fun value =>
      decide (KeyHit setup (PqxdhDeploymentEnvironmentDraw.dropX value.2.2.2)))
  have joinedEq : (fun result => (PqxdhDeploymentEnvironmentJoin.joined result).any fun value =>
        decide (KeyHit setup (PqxdhDeploymentEnvironmentDraw.dropX value.2.2.2))) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary =
      (fun outcome => outcome.any fun value =>
        decide (KeyHit setup (PqxdhDeploymentEnvironmentDraw.dropX value.2.2.2))) <$>
        (PqxdhDeploymentEnvironmentJoin.joined <$> PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
            mode adversary) := by
    rw [Functor.map_map]
  rw [joinedEq, ← law.evalDist_eq, map_bind, ← prEvent_eq_evalDist_singleton _ true]
  refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ => ?_
  rw [prEvent_eq_evalDist_singleton]
  have split := split_keyHit setup codec checks route t p ensureInit identityIndex bounds mode adversary budget respects
    runtime
  refine le_of_eq_of_le ?_ split
  rw [Functor.map_map, StateT.run'_eq, Functor.map_map]
  congr 2
  congr 1
  funext outcome
  rcases outcome with ⟨_ | value, after⟩
  · rfl
  · rfl

end Bound

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.tablePotential_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.tablePotential_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.ro_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.ro_table

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_local

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_ctx

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_sourceRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_sourceRoot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_romRootBytes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_romRootBytes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_client

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_acceptLogged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_acceptLogged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_familyHmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_familyHmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_callbacks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_callbacks

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_onShared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_onShared

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedD_onNative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedD_onNative

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedD_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedD_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedR_finish

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_mono

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.material_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.material_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.slot_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.slot_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedD_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedD_handler

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.expected_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.expected_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_nativeMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_nativeMap

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_romRoot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_romRoot

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_auxiliary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_auxiliary

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_mutation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_mutation

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_acceptTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_acceptTail

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_buildHidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_buildHidden

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_knownGroup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedN_knownGroup

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_tailCE' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_tailCE

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_tail

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_acceptActive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_acceptActive

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_acceptExposed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_acceptExposed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.groupedOwnerCE_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.groupedOwnerCE_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_groupCE' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_groupCE

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_finishChallenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_finishChallenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.realRegAt_charged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.realRegAt_charged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.createReg_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.createReg_shared

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_acceptStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_acceptStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_buildHiddenC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_buildHiddenC

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_buildStepC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_buildStepC

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_finishStepC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedG_finishStepC

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedX_slotRunX' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedX_slotRunX

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedX_onBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.chargedX_onBase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.install_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.install_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.handler_charged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.handler_charged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.wrap_r1_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.wrap_r1_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.one_le_keyPotential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.one_le_keyPotential

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.keyPotential_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.keyPotential_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.split_keyHit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.split_keyHit

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.world_keyHit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineDctTable.world_keyHit

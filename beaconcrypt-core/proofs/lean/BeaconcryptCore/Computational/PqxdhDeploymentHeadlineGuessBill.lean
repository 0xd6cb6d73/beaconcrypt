-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineSplitCost
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineAnomaly

/-!
# The phase-1 bill of `β_g`'s predict-then-compare adversary: `guessBill` and `ptc_bills` (CE-12 P2b, design-v2 section 9)

`β_g` (`PqxdhDeploymentHeadlineAnomaly.beta`) is one ML-KEM IND-CCA advantage of `ptc setup.kem (anomalyGuesser … (Target.ofCE budget g) ensureInit 0 runtime bounds mode adversary)`. P1 proved its decapsulation count (`beta_decapsulations`) and that its phase 2 makes no query (`ptc_post`). This module proves the rest of its query bill, the definite form of plan sections 89 and 93 (a): `ptc_bills`, `OneKeyAdversary.MakesAtMostQueries (guessBill caps qInit budget bounds) 0 (budget.finish + 1) 0 0 0`, that is, before the challenge at most `guessBill` uniform queries, no base-oracle query and at most `qFinish + 1` logical decapsulations, and after the challenge no query of any class.

- `guessWeight caps bounds kind` (design-v2's `u kind`): the uniform weight of one complete-interface query of class `kind`, the native commands its secrecy layer issues (`PqxdhDeploymentCompileSecrecy.wrapCost`) each at its split-handler weight (`PqxdhDeploymentHeadlineSplitCost.splitWeight`); `guessWeight_eq` gives the values: the twelve native classes their split weight, `test` 129 (one hidden-bit coin and one send), `fresh` `bounds.max + 128` (one coin per byte and one send).
- `guessBill caps qInit budget bounds := (budget.create + 1) · keygenCost + (qInit + 32) + Σ_kind budget.cap kind · guessWeight caps bounds kind`: the guesser's own key pair and the other `qCreate` pool entries, the Server construction with a generated seed, and the game; `guessBill_eq` is the closed form.
- Steps: `oracleFinish_uniform` (owner k's finish with the decapsulation oracle draws at most `69 · max 64 decapsCost`; its decapsulation is an oracle query, not a coin), `oracleFinish_base`, `guessStep_uniform` (every step of the guesser's handler `guessReg` within `splitWeight`, from `splitStep_uniform` through `ccaCoins_uniform`), `guessStep_base` (no base query, `ccaCoins_excluded`), `flat_uniform` and `flat_base` (one complete-interface query, through `wrap_step` and `FinitePartitionQueryBounds.weighted_bound`), `game_uniform` (the whole game against a budget-respecting adversary, `asModeO_bound` and `weighted_bound`).
- The guesser: `anomalyGuesser_uniform` (at most `(count + 1) · keygenCost + (qInit + 32) + Σ_kind budget.cap kind · guessWeight kind` uniform queries: `keygen_uniform`, `sampleFamily_uniform`, `construct_uniform`, `game_uniform`) and `anomalyGuesser_base` (no base query).
- `ptc_uniform` and `ptc_base` carry the guesser's caps to `ptc`'s phase 1 (the extra decapsulation of the prediction is neither a coin nor a base query); `ptc_bills` collects them with `beta_decapsulations` and `ptc_post`.

Premises: `KemBound setup caps`, the total query bound `qInit` of the runtime initializer and `budget.Respects adversary`, exactly those of `PqxdhDeploymentKemTransfer.kem_transfer_bills`. These are resource bounds in the existing cost model; no assumption is added.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerAuthSourceCosts (KemCaps KemBound)
open PqxdhKemIndCca (MlKem768PublicKey IsMlKemUniformQuery IsMlKemBaseQuery IsMlKemLogicalDecapsulationQuery
  MlKemCCAOracleSpec)
open PqxdhDeploymentBackend (XState handlerWith)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhPrivateKemSource (ccaCoins)
open PqxdhDeploymentCompileBudget (commandKind)
open PqxdhDeploymentCompileSecrecy (wrapCost)
open PqxdhDeploymentHeadlineSplitCost (splitWeight)
open PqxdhDeploymentIdealAnomalyGuesser (guessReg oracleFinish oracleCallbacks prepOracle flat anomalyGuesser)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec queryClass asModeO)

section Steps
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) (caps : KemCaps) {count : ℕ}

/-- Owner k's finish with the decapsulation oracle draws at most `69 · max 64 decapsCost` uniform coins: the native owner program makes at most 69 callbacks (`PqxdhBeaconPhase2Bounds.native_interpreted_bound`), each on the guesser's own coins within `max 64 decapsCost` (`PqxdhRegistrationSchedule.callbacks_uniform`), except the decapsulation, which is one oracle query and no coin. -/
theorem oracleFinish_uniform (bounded : KemBound setup caps) {Bk : Type} {n : ℕ} (index : ℕ) (raw : Pqxdh.Bytes)
    (x : XState KemSK Bk n) :
    ((oracleFinish (baseSpec := baseSpec) setup codec index raw).run x).IsQueryBoundP IsMlKemUniformQuery
      (69 * max 64 caps.decapsCost) := by
  unfold oracleFinish
  dsimp only [StateT.run]
  split
  · exact isQueryBoundP_pure _ _ _
  · rw [isQueryBoundP_map_iff]
    refine PqxdhBeaconPhase2Bounds.native_interpreted_bound _ _ _ (fun query state => ?_) _ _ _ _
    rcases query with query | query
    · cases query
      case decapsulate ciphertext keys =>
        simp only [oracleCallbacks, prepOracle, StateT.run]
        rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro uniform
        exact uniform.elim
      all_goals
        simp only [oracleCallbacks, prepOracle, StateT.run]
        exact PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
          (PqxdhRegistrationSchedule.callbacks_uniform setup codec caps bounded _ state)
    · simp only [oracleCallbacks, StateT.run]
      exact PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
        (PqxdhRegistrationSchedule.callbacks_uniform setup codec caps bounded _ state)

/-- Owner k's finish with the decapsulation oracle makes no base-oracle query. -/
theorem oracleFinish_base {Bk : Type} {n : ℕ} (index : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK Bk n) :
    ((oracleFinish (baseSpec := baseSpec) setup codec index raw).run x).IsQueryBoundP IsMlKemBaseQuery 0 := by
  unfold oracleFinish
  dsimp only [StateT.run]
  split
  · exact isQueryBoundP_pure _ _ _
  · rw [isQueryBoundP_map_iff]
    refine PqxdhDeploymentCompileSecrecy.simulate_zero _ _ (fun query state => ?_) _ _
    rcases query with query | query
    · cases query
      case decapsulate ciphertext keys =>
        simp only [oracleCallbacks, prepOracle, StateT.run]
        rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro base
        exact base.elim
      all_goals
        simp only [oracleCallbacks, prepOracle, StateT.run]
        exact PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ fun _ => id
    · simp only [oracleCallbacks, StateT.run]
      exact PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ fun _ => id

/-- Every step of the guesser's native handler draws at most the split weight of its class: on the guesser's own coins it is the split handler's step (`splitStep_uniform`), and owner k's oracle finish is within the finish weight. Premise: `KemBound setup caps`. -/
theorem guessStep_uniform (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK SplitBk 2) :
    ((guessReg (baseSpec := baseSpec) setup codec route checks t p created query).run x).IsQueryBoundP
      IsMlKemUniformQuery (splitWeight caps (commandKind query)) := by
  by_cases oracle : ∃ raw, query = .inr (.finish t.kem.val raw) ∧ x.backend.2.2.active = false
  · obtain ⟨raw, rfl, inactive⟩ := oracle
    rw [PqxdhDeploymentIdealAnomalyGuesser.guessReg_oracle setup codec route checks t p created raw x inactive]
    exact (oracleFinish_uniform setup codec caps bounded t.kem.val raw x).mono (by simp [splitWeight, commandKind])
  · rw [PqxdhDeploymentIdealAnomalyGuesser.guessReg_lift setup codec route checks t p created query x fun raw same => by
      cases active : x.backend.2.2.active
      · exact absurd ⟨raw, same, active⟩ oracle
      · rfl]
    exact PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _
      (PqxdhDeploymentHeadlineSplitCost.splitStep_uniform setup codec route checks caps bounded t p created query x)

/-- Every step of the guesser's native handler makes no base-oracle query. -/
theorem guessStep_base (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK SplitBk 2) :
    ((guessReg (baseSpec := baseSpec) setup codec route checks t p created query).run x).IsQueryBoundP
      IsMlKemBaseQuery 0 := by
  by_cases oracle : ∃ raw, query = .inr (.finish t.kem.val raw) ∧ x.backend.2.2.active = false
  · obtain ⟨raw, rfl, inactive⟩ := oracle
    rw [PqxdhDeploymentIdealAnomalyGuesser.guessReg_oracle setup codec route checks t p created raw x inactive]
    exact oracleFinish_base setup codec t.kem.val raw x
  · rw [PqxdhDeploymentIdealAnomalyGuesser.guessReg_lift setup codec route checks t p created query x fun raw same => by
      cases active : x.backend.2.2.active
      · exact absurd ⟨raw, same, active⟩ oracle
      · rfl]
    exact PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ fun _ => id

/-- `u kind` (design-v2 section 9): the uniform weight of one complete-interface query of class `kind` in the guesser game, the native commands its secrecy layer issues (`wrapCost`), each at its split weight. -/
def guessWeight (caps : KemCaps) (bounds : FreshBounds) (kind : Fin 14) : ℕ :=
  ∑ core, splitWeight caps core * wrapCost bounds core kind

/-- The values of `guessWeight`: the twelve native classes at their split weight, `test` at `1 + 64 + 64` (the hidden bit and one Server or Beacon send, both send classes charged), `fresh` at `bounds.max + 64 + 64` (one coin per message byte and one send). -/
theorem guessWeight_eq (caps : KemCaps) (bounds : FreshBounds) :
    guessWeight caps bounds = ![1, 64 + caps.keygenCost, 32, 140 + caps.encapsCost, 108 + 64 + 64,
      69 * max 64 caps.decapsCost + 64, 64, 64, 64, 64, 64, 64, 1 + 64 + 64, bounds.max + 64 + 64] := by
  funext kind
  fin_cases kind <;> simp [guessWeight, Fin.sum_univ_succ, splitWeight, wrapCost]

/-- One complete-interface query of the flattened guesser game draws at most `guessWeight` of its class (`wrap_step` and `weighted_bound`). -/
theorem flat_uniform (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count) (bounds : FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) :
    ((flat setup codec bounds (guessReg (baseSpec := baseSpec) setup codec route checks t p created) query).run
      state).IsQueryBoundP IsMlKemUniformQuery (guessWeight caps bounds (queryClass query)) := by
  change ((fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (guessReg setup codec route checks t p created)
    ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run state.1)).run state.2).IsQueryBoundP _ _
  rw [isQueryBoundP_map_iff]
  exact FinitePartitionQueryBounds.weighted_bound commandKind (splitWeight caps)
    (fun core => wrapCost bounds core (queryClass query)) (guessReg setup codec route checks t p created)
    IsMlKemUniformQuery _
    (fun core => PqxdhDeploymentCompileSecrecy.wrap_step setup.source.crypto codec setup.serverKeyId bounds core query
      state.1)
    (fun request inner => guessStep_uniform setup codec route checks caps bounded t p created request inner) state.2

/-- One complete-interface query of the flattened guesser game makes no base-oracle query. -/
theorem flat_base (t : Target count) (p : Params KemSK count) (bounds : FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) :
    ((flat setup codec bounds (guessReg (baseSpec := baseSpec) setup codec route checks t p created) query).run
      state).IsQueryBoundP IsMlKemBaseQuery 0 := by
  change ((fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (guessReg setup codec route checks t p created)
    ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run state.1)).run state.2).IsQueryBoundP _ _
  rw [isQueryBoundP_map_iff]
  exact PqxdhDeploymentCompileSecrecy.simulate_zero _ _
    (fun request inner => guessStep_base setup codec route checks t p created request inner) _ state.2

end Steps

section Guesser
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) (caps : KemCaps) {count : ℕ}

/-- The guesser game against an adversary that respects `budget` draws at most `Σ_kind guessWeight kind · budget.cap kind` uniform coins from every state. -/
theorem game_uniform (bounded : KemBound setup caps) (t : Target count) (p : Params KemSK count) (bounds : FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X)
    (budget : Budget) (respects : budget.Respects adversary) (state : Ledger × XState KemSK SplitBk 2) :
    ((simulateQ (flat setup codec bounds (guessReg (baseSpec := baseSpec) setup codec route checks t p created))
      (asModeO mode adversary)).run state).IsQueryBoundP IsMlKemUniformQuery
        (∑ kind, guessWeight caps bounds kind * budget.cap kind) :=
  FinitePartitionQueryBounds.weighted_bound queryClass (guessWeight caps bounds) budget.cap _ IsMlKemUniformQuery
    (asModeO mode adversary) (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects)
    (fun query inner => flat_uniform setup codec route checks caps bounded t p bounds created query inner) state

/-- `guessBill` (design-v2 section 9, plan section 89): the phase-1 uniform bill of `β_g`'s adversary, `(qCreate + 1) · keygenCost + (qInit + 32) + Σ_kind budget.cap kind · u kind`. -/
def guessBill (caps : KemCaps) (qInit : ℕ) (budget : Budget) (bounds : FreshBounds) : ℕ :=
  (budget.create + 1) * caps.keygenCost + (qInit + 32) + ∑ kind, budget.cap kind * guessWeight caps bounds kind

/-- The closed form of `guessBill`. -/
theorem guessBill_eq (caps : KemCaps) (qInit : ℕ) (budget : Budget) (bounds : FreshBounds) :
    guessBill caps qInit budget bounds = (budget.create + 1) * caps.keygenCost + (qInit + 32) +
      (budget.coin + (64 + caps.keygenCost) * budget.create + 32 * budget.bundle +
        (140 + caps.encapsCost) * budget.accept + 236 * budget.build +
        (69 * max 64 caps.decapsCost + 64) * budget.finish +
        64 * (budget.hmac + budget.hash + budget.serverSend + budget.serverRaw + budget.beaconSend + budget.beaconRaw) +
        129 * budget.test + (bounds.max + 128) * budget.fresh) := by
  simp only [guessBill, guessWeight_eq, Fin.sum_univ_succ, Fin.sum_univ_zero, Budget.cap]
  simp
  ring

/-- The anomaly guesser draws at most `(count + 1) · keygenCost + (qInit + 32) + Σ_kind budget.cap kind · guessWeight kind` uniform coins: its own key pair and the `count` other pool entries (`keygen_uniform`, `sampleFamily_uniform`), the Server construction with a generated seed (`construct_uniform`) and the game (`game_uniform`). Premises: `KemBound setup caps`, `initBound` and `budget.Respects adversary`. -/
theorem anomalyGuesser_uniform (bounded : KemBound setup caps) (t : Target count) (ensureInit : StateT A ProbComp Bool)
    (qInit : ℕ) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (pk : MlKem768PublicKey) :
    (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode adversary pk).IsQueryBoundP
      IsMlKemUniformQuery
        ((count + 1) * caps.keygenCost + (qInit + 32) + ∑ kind, budget.cap kind * guessWeight caps bounds kind) := by
  have keygen := PqxdhServerAuthSourceCosts.keygen_uniform setup caps bounded
  have family := PqxdhDeploymentIdealEnvCost.sampleFamily_uniform _ _ keygen count
  have born := PqxdhLiveServerConstruction.construct_uniform (P := Unit) setup.joint ensureInit qInit initBound identityIndex
    setup.serverKeyId none runtime
  simp only [Option.isNone_none, ite_true] at born
  have reorder : (∑ kind, budget.cap kind * guessWeight caps bounds kind) =
      ∑ kind, guessWeight caps bounds kind * budget.cap kind :=
    Finset.sum_congr rfl fun kind _ => Nat.mul_comm _ _
  rw [reorder, show (count + 1) * caps.keygenCost + (qInit + 32) + ∑ kind, guessWeight caps bounds kind * budget.cap kind
      = caps.keygenCost + (count * caps.keygenCost + ((qInit + 32) +
        ((∑ kind, guessWeight caps bounds kind * budget.cap kind) + 0))) by ring]
  unfold anomalyGuesser
  refine isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _ keygen) fun dummy _ => ?_
  refine isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _ family) fun others _ => ?_
  refine isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_uniform _ _ born) fun born _ => ?_
  rcases born with ⟨_ | created, after⟩
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind (game_uniform setup codec route checks caps bounded t _ bounds created mode adversary
      budget respects _) fun _ _ => isQueryBoundP_pure _ _ _

/-- The anomaly guesser makes no base-oracle query: every draw is on its own coins (`ccaCoins_excluded`). -/
theorem anomalyGuesser_base (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (pk : MlKem768PublicKey) :
    (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode adversary pk).IsQueryBoundP
      IsMlKemBaseQuery 0 := by
  unfold anomalyGuesser
  rw [show (0 : ℕ) = 0 + (0 + (0 + (0 + 0))) by omega]
  refine isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ fun _ => id) fun dummy _ => ?_
  refine isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ fun _ => id) fun others _ => ?_
  refine isQueryBoundP_bind (PqxdhPrivateRootQueryBounds.ccaCoins_excluded _ _ fun _ => id) fun born _ => ?_
  rcases born with ⟨_ | created, after⟩
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_bind (PqxdhDeploymentCompileSecrecy.simulate_zero _ _
      (fun query inner => flat_base setup codec route checks t _ bounds created query inner) _ _)
      fun _ _ => isQueryBoundP_pure _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Phase 1 of `ptc` makes at most the guesser's uniform queries: the decapsulation of the prediction is not a coin. -/
theorem ptc_uniform {SK : Type} (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option PqxdhKemIndCca.MlKem768Ciphertext))
    (count : ℕ) (bound : ∀ pk, (guess pk).IsQueryBoundP IsMlKemUniformQuery count) (pk : MlKem768PublicKey) :
    ((PqxdhDeploymentHeadlineAnomaly.ptc kem guess).preChallenge pk).IsQueryBoundP IsMlKemUniformQuery count := by
  change (guess pk >>= fun predicted => _).IsQueryBoundP IsMlKemUniformQuery count
  rw [← Nat.add_zero count]
  apply isQueryBoundP_bind (bound pk)
  intro predicted _
  cases predicted with
  | none => exact isQueryBoundP_pure _ _ _
  | some c => simp [isQueryBoundP_map_iff, IsMlKemUniformQuery]

set_option backward.isDefEq.respectTransparency false in
/-- Phase 1 of `ptc` makes no base-oracle query when the guesser makes none. -/
theorem ptc_base {SK : Type} (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := SK))
    (guess : MlKem768PublicKey → OracleComp kem.IND_CCA_oracleSpec (Option PqxdhKemIndCca.MlKem768Ciphertext))
    (bound : ∀ pk, (guess pk).IsQueryBoundP IsMlKemBaseQuery 0) (pk : MlKem768PublicKey) :
    ((PqxdhDeploymentHeadlineAnomaly.ptc kem guess).preChallenge pk).IsQueryBoundP IsMlKemBaseQuery 0 := by
  change (guess pk >>= fun predicted => _).IsQueryBoundP IsMlKemBaseQuery 0
  rw [← Nat.add_zero 0]
  apply isQueryBoundP_bind (bound pk)
  intro predicted _
  cases predicted with
  | none => exact isQueryBoundP_pure _ _ _
  | some c => simp [isQueryBoundP_map_iff, IsMlKemBaseQuery]

/-- `ptc_bills` (design-v2 section 9): `β_g`'s predict-then-compare adversary makes, before the challenge, at most `guessBill caps qInit budget bounds` uniform queries, no base-oracle query and at most `budget.finish + 1` logical decapsulation queries, and after the challenge no query of any class. Premises: `KemBound setup caps`, `initBound` and `budget.Respects adversary`, those of `kem_transfer_bills`. -/
theorem ptc_bills (bounded : KemBound setup caps) (ensureInit : StateT A ProbComp Bool) (qInit : ℕ)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (respects : budget.Respects adversary)
    (g : Fin budget.accept × Fin budget.capacity) (runtime : A) :
    (PqxdhDeploymentHeadlineAnomaly.ptc setup.kem (anomalyGuesser setup codec route checks (Target.ofCE budget g)
      ensureInit 0 runtime bounds mode adversary)).MakesAtMostQueries (guessBill caps qInit budget bounds) 0
        (budget.finish + 1) 0 0 0 :=
  ⟨fun pk => ⟨ptc_uniform setup.kem _ _ (fun pk => anomalyGuesser_uniform setup codec route checks caps bounded _ ensureInit
      qInit initBound 0 runtime bounds mode adversary budget respects pk) pk,
    ptc_base setup.kem _ (fun pk => anomalyGuesser_base setup codec route checks _ ensureInit 0 runtime bounds mode
      adversary pk) pk,
    PqxdhDeploymentHeadlineAnomaly.beta_decapsulations setup codec route checks ensureInit bounds mode adversary budget
      respects g runtime pk⟩,
   fun _ _ => ⟨PqxdhDeploymentHeadlineAnomaly.ptc_post _ _ _ _ _,
    PqxdhDeploymentHeadlineAnomaly.ptc_post _ _ _ _ _, PqxdhDeploymentHeadlineAnomaly.ptc_post _ _ _ _ _⟩⟩

end Guesser

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.oracleFinish_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.oracleFinish_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.oracleFinish_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.oracleFinish_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessStep_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessStep_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessStep_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessStep_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessWeight_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessWeight_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.flat_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.flat_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.flat_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.flat_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.game_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.game_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessBill_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.guessBill_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.anomalyGuesser_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.anomalyGuesser_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.anomalyGuesser_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.anomalyGuesser_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.ptc_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.ptc_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.ptc_base' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.ptc_base

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.ptc_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineGuessBill.ptc_bills

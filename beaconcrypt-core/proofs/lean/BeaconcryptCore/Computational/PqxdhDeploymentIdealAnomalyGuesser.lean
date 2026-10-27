-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealKeySwap
import BeaconcryptCore.Computational.PqxdhPrivateKemSource
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactorTools

/-!
# The anomaly guesser with decapsulation access: `anomaly_le_pk` (CE-11b, unit U4)

The public-key-only form of the anomaly bound (plan section 49 Q2 option (b), route of plan section 84): the Beacon-side anomaly `PqxdhDeploymentIdealTrace.Anomaly` on the record world with the ideal environment of a target is bounded by the ciphertext guess of an explicit guesser program that receives the selected public key and a decapsulation oracle for the selected secret key, never the secret key or the challenge. This is the form that CE-12a's predict-then-compare IND-CCA reduction consumes; the guesser's interface is the KEM's IND-CCA oracle interface (`MlKemCCAOracleSpec`, the phase-1 interface of `PqxdhKemIndCca.OneKeyAdversary`).

- `ctGuessByCca setup guess`: the probability that `guess`, run on the public key of a fresh key pair with the pre-challenge decapsulation oracle of its secret key (`KEMScheme.IND_CCA_preChallengeImpl`) and before the encapsulation, outputs the encapsulation's ciphertext; `ctGuessByCca_le_pk` (at most `ctGuessPk`), `ctGuessByCca_ambient` (for oracle-free guessers it is `PqxdhDeploymentIdealAnomaly.ctGuessBy`).
- The oracle finish (`prepOracle`, `oracleCallbacks`, `oracleFinish`): owner `k`'s registration finish with its decapsulation answered by the oracle; interpreted by the pre-challenge oracle of the selected secret key (`interp`), at the state with owner `k`'s secret key replaced, it is the real finish (`oracleCallbacks_interp`, `oracleFinish_interp`, through `PqxdhPhase2KemHandles.native_owner_run`).
- The guesser's native handler (`guessReg`): the final split game's step on the guesser's own coins, except owner `k`'s finish while the selected accept is not active, which is the oracle finish (`guessReg_lift`, `guessReg_oracle`, `guessReg_interp`).
- The coupling: on the flattened games (`flat`, `splitHandler_flat`, `mapRun_flat`, `flat_transcript`, `flat_keeps`, `flat_selected`, `coinSend_swaps`, `simulate_swaps`, `flat_step`), the final split game at the selected key pair and the guesser game interpreted by the selected secret key's oracle are identical until the selected raw accept up to the replacement of owner `k`'s secret key, so the transcript guess has the same law (`guess_lawEq`, with `PqxdhDeploymentIdealGuess.lawEq_until_stop`).
- `anomalyGuesser`: draws a key pair of its own (whose secret half stands in for the selected one), the other pool entries and the Server construction, runs the guesser game at the selected public key and outputs the transcript guess. `guesser_eval`, `pair_lawEq`, `split_guess_cca` (the split-side guess probability equals `ctGuessByCca` of the guesser), `guess_le_cca` (the transcript guess event on the record world, through `PqxdhDeploymentIdealEnv.c1_split`), `anomaly_le_pk` and `anomaly_prefix_le_pk` (the anomaly, and the anomaly on a prefix, under `Phase1ReadBack` and `Phase2ReadBack`).
- Query bound: `anomalyGuesser_decapsulations`: against an adversary respecting a budget, the guesser makes at most `budget.finish` decapsulation queries (one per oracle finish at most, `oracleFinish_decapsulate`); every other query is one of its own coins.

These are equalities in law, bounds and query counts; no assumption is added and no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement
open OracleComp.ProgramLogic.Relational

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext MlKemSharedSecret MlKemCCAOracleSpec)
open PqxdhRegistrationSchedule (Owner)
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentIdealKeySwap

/-! ### Owner k's finish with the decapsulation oracle -/

section Oracle
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
open PqxdhPrivateKemSource (ccaCoins evalKem)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)

/-- The interpretation of the decapsulation-oracle interface by the KEM's pre-challenge oracle for the secret key `secret` (`PqxdhKemIndCca.OneKeyAdversary`'s phase-1 oracle), followed by the setup's fixed ambient interpreter: `evalKem` query by query. -/
noncomputable def interp (secret : KemSK) : QueryImpl (MlKemCCAOracleSpec baseSpec) ProbComp :=
  PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl ∘ₛ
    PqxdhStatefulPhase1EufCma.localKemPreChallengeImpl setup.kem secret

/-- Interpreting a program by `interp` is `PqxdhPrivateKemSource.evalKem`. -/
theorem simulateQ_interp {α : Type} (secret : KemSK) (work : OracleComp (MlKemCCAOracleSpec baseSpec) α) :
    simulateQ (interp setup secret) work = evalKem setup.baseImpl setup.kem secret work := by
  rw [interp, QueryImpl.simulateQ_compose]
  rfl

/-- The guesser's own coins are interpreted as themselves (`PqxdhPrivateKemSource.evalKem_coins`). -/
theorem interp_coins {α : Type} (secret : KemSK) (work : ProbComp α) :
    simulateQ (interp setup secret) (ccaCoins work) = work := by
  rw [simulateQ_interp, PqxdhPrivateKemSource.evalKem_coins]

/-- The preparation callbacks of owner k's finish with the decapsulation oracle: a decapsulation queries the oracle at the ciphertext's bytes and never reads a secret key; every other callback is the native one on its own coins. -/
noncomputable def prepOracle :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec IdentitySeed ScalarBytes (MlKem768PublicKey × KemSK) IdentitySeed Response)
      (StateT (PqxdhServerAuthNative.NativeState KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))
  | .decapsulate ciphertext _ => fun s =>
      (fun reply => (Option.map PqxdhRootTableInitialization.rootArray reply, s)) <$>
        ((MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext ciphertext)) :
          OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret))
  | query => fun s => ccaCoins ((PqxdhRegistrationSchedule.callbacks setup codec (.inl query)).run s)

/-- The native finish callbacks with the decapsulation answered by the oracle (`prepOracle`); the tail callbacks are the native ones on their own coins. -/
noncomputable def oracleCallbacks :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes (MlKem768PublicKey × KemSK) IdentitySeed
      Response) (StateT (PqxdhServerAuthNative.NativeState KemSK) (OracleComp (MlKemCCAOracleSpec baseSpec)))
  | .inl query => prepOracle setup codec query
  | .inr query => fun s => ccaCoins ((PqxdhRegistrationSchedule.callbacks setup codec (.inr query)).run s)

/-- Interpreted by the pre-challenge oracle of the secret key `secret`, the oracle callbacks with any key-pair relabelling are the native callbacks with every key pair's secret half replaced by `secret`. -/
theorem oracleCallbacks_interp (secret : KemSK) (relabel : MlKem768PublicKey × KemSK → MlKem768PublicKey × KemSK) :
    PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup secret) (oracleCallbacks setup codec) ∘ₛ
        PqxdhPhase2KemHandles.native relabel =
      PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ PqxdhPhase2KemHandles.native (withSecret secret) := by
  funext query
  refine StateT.ext fun s => ?_
  rcases query with query | query
  · cases query
    case decapsulate ciphertext keys =>
      simp only [QueryImpl.apply_compose, PqxdhPhase2KemHandles.native, PqxdhPhase2KemHandles.preparation,
        simulateQ_spec_query, PqxdhRegistrationJointKemEntryFactor.mapRun_run, oracleCallbacks, prepOracle]
      change simulateQ (interp setup secret) ((fun reply => (Option.map PqxdhRootTableInitialization.rootArray reply, s)) <$>
        ((MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext ciphertext)) :
          OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKemSharedSecret))) =
        (fun value => (value, s)) <$> simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
          (Option.map PqxdhRootTableInitialization.rootArray <$>
            setup.kem.decaps secret (PqxdhPhase2InputBytes.ciphertext ciphertext))
      simp only [simulateQ_map, simulateQ_spec_query, interp, QueryImpl.apply_compose, Functor.map_map]
      rfl
    all_goals simp only [QueryImpl.apply_compose, PqxdhPhase2KemHandles.native, PqxdhPhase2KemHandles.preparation,
        simulateQ_spec_query, PqxdhRegistrationJointKemEntryFactor.mapRun_run, oracleCallbacks, prepOracle]
    all_goals exact interp_coins setup secret _
  · simp only [QueryImpl.apply_compose, PqxdhPhase2KemHandles.native, simulateQ_spec_query,
      PqxdhRegistrationJointKemEntryFactor.mapRun_run, oracleCallbacks]
    exact interp_coins setup secret _

/-- Owner `index`'s registration finish with the decapsulation oracle: the real finish (the LQ snapshot of the addressed owner, then `PqxdhRegistrationSchedule.finish`, which runs the native owner program on its callbacks and reinstalls the returned owner) with the native callbacks replaced by `oracleCallbacks`. It never reads a KEM secret key: the owner's own key pair is only passed to the decapsulation request, which the oracle answers from the ciphertext alone. -/
noncomputable def oracleFinish {Bk : Type} {n : ℕ} (index : ℕ) (raw : Pqxdh.Bytes) :
    StateT (XState KemSK Bk n) (OracleComp (MlKemCCAOracleSpec baseSpec)) (Option Pqxdh.Bytes) := fun x =>
  match x.base.native.owners[index]? with
  | none => pure (none, { x with snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some index) })
  | some owner => (fun result => (result.1.1, { x with
      base := { x.base with native := { shared := result.2, owners := x.base.native.owners.set index result.1.2 } },
      snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some index) })) <$>
    (simulateQ (oracleCallbacks setup codec) (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run
      x.base.native.shared

/-- Interpreted by the pre-challenge oracle of owner `index`'s secret key `old`, the oracle finish at the state with that key replaced by `new` is the real finish at the original state, with the key replaced in its final state; the real finish keeps owner `index`'s key. -/
theorem oracleFinish_interp {Bk : Type} {n : ℕ} (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (created : PqxdhLiveServerConstruction.Created Unit) (index : ℕ) (old new : KemSK) (raw : Pqxdh.Bytes)
    (x : XState KemSK Bk n) (held : HoldsX index old x) :
    simulateQ (interp setup old) ((oracleFinish setup codec index raw).run (swapX index new x)) =
      Prod.map id (swapX index new) <$>
        (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.finish index raw, trivial⟩).run x ∧
    ∀ r ∈ support ((PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created
        ⟨.finish index raw, trivial⟩).run x), HoldsX index old r.2 := by
  have real : (PqxdhDeploymentIdealSteps.realRegAt setup codec route checks created ⟨.finish index raw, trivial⟩).run x =
      (fun r => (r.1, { x with
          base := { x.base with native := r.2 }
          snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some index) })) <$>
        (PqxdhRegistrationSchedule.finish setup codec index raw).run x.base.native := by
    rw [PqxdhDeploymentIdealEnvReal.realRegAt_quiet setup codec checks route created _ (fun _ same => by cases same)]
    change _ <$> ((fun result => (result.1, { x.base with native := result.2 })) <$>
      (PqxdhRegistrationSchedule.finish setup codec index raw).run x.base.native) = _
    rw [Functor.map_map]
    rfl
  rcases found : x.base.native.owners[index]? with _ | o
  · have found' : (swapX index new x).base.native.owners[index]? = none := by
      simp [swapX, swapNative, swapSched, found]
    rw [real, PqxdhRegistrationSchedule.finish_missing setup codec index raw _ found]
    refine ⟨?_, ?_⟩
    · change simulateQ (interp setup old) (match (swapX index new x).base.native.owners[index]? with
        | none => _ | some owner => _) = _
      have owners : (swapX (Bk := Bk) (n := n) index new x).base.native.owners =
          x.base.native.owners.modify index (swapOwner new) := rfl
      rw [found', simulateQ_pure, map_pure, map_pure]
      simp only [owners, snapshotAt_swap]
      rfl
    · intro r member
      simp only [map_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact held
  · have found' : (swapX index new x).base.native.owners[index]? = some (swapOwner new o) := by
      simp [swapX, swapNative, swapSched, found]
    have bound : index < x.base.native.owners.length := (List.getElem?_eq_some_iff.mp found).1
    have realRun : (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw o)).run x.base.native.shared =
        (fun result => ((result.1.1, swapOwner old result.1.2), result.2)) <$>
          (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec ∘ₛ PqxdhPhase2KemHandles.native (withSecret old))
            (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw o)).run x.base.native.shared := by
      conv_lhs => rw [← held o found]
      exact (PqxdhPhase2KemHandles.native_owner_run (withSecret old) _ codec.frameRead raw o _).symm
    have source : (PqxdhRegistrationSchedule.finish setup codec index raw).run x.base.native =
        (fun result => (result.1.1, ({ shared := result.2, owners := x.base.native.owners.set index result.1.2 } :
          PqxdhRegistrationSchedule.State KemSK))) <$>
          (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
            (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw o)).run x.base.native.shared :=
      PqxdhRegistrationSchedule.finish_source setup codec index raw _ _ found
    rw [real, source]
    refine ⟨?_, ?_⟩
    · change simulateQ (interp setup old) (match (swapX index new x).base.native.owners[index]? with
        | none => _ | some owner => _) = _
      rw [found', simulateQ_map, PqxdhRegistrationJointKemEntryFactor.simulateQ_mapRun,
        show swapOwner new o = PqxdhBeaconPhase1Publication.mapState id (withSecret new) o from rfl]
      rw [← PqxdhPhase2KemHandles.native_owner_run (withSecret new) _ codec.frameRead raw o _,
        oracleCallbacks_interp]
      change _ = Prod.map id (swapX index new) <$> (_ <$> (_ <$> (simulateQ (PqxdhRegistrationSchedule.callbacks setup
        codec) (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw o)).run x.base.native.shared))
      rw [realRun]
      simp only [Functor.map_map]
      refine congrArg (fun f => f <$> _) (funext fun r => ?_)
      have owners : (swapX (Bk := Bk) (n := n) index new x).base.native.owners =
          x.base.native.owners.modify index (swapOwner new) := rfl
      simp only [Prod.map, id_eq, owners, snapshotAt_swap]
      rw [show PqxdhBeaconPhase1Publication.mapState id (withSecret new) r.1.2 = swapOwner new (swapOwner old r.1.2) from
        (swapOwner_swapOwner new old r.1.2).symm, modify_set_same]
      rfl
    · intro r member
      rw [support_map] at member
      obtain ⟨r', member', rfl⟩ := member
      change r' ∈ support ((fun result => _) <$> (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw o)).run x.base.native.shared) at member'
      rw [realRun, Functor.map_map, support_map] at member'
      obtain ⟨r'', -, rfl⟩ := member'
      intro o' found''
      change (x.base.native.owners.set index (swapOwner old r''.1.2))[index]? = some o' at found''
      rw [List.getElem?_set_self bound, Option.some.injEq] at found''
      subst found''
      exact swapOwner_swapOwner _ _ _

end Oracle

/-! ### The guesser's native handler -/

section Guesser
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentBackend (handlerWith)
open PqxdhPrivateKemSource (ccaCoins)

/-- The guesser's native handler over the decapsulation-oracle interface: the native handler of the final split game at the parameters `p`, on its own coins, except that a finish of owner `k` while the selected accept is not active is the oracle finish, which answers its decapsulation by the oracle. -/
noncomputable def guessReg (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit) :
    QueryImpl PqxdhDeploymentInterface.Spec
      (StateT (XState KemSK SplitBk 2) (OracleComp (MlKemCCAOracleSpec baseSpec)))
  | .inr (.finish owner raw) => fun x =>
      if owner = t.kem.val ∧ x.backend.2.2.active = false then (oracleFinish setup codec owner raw).run x
      else ccaCoins ((handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p
        created) (.inr (.finish owner raw))).run x)
  | query => fun x => ccaCoins ((handlerWith setup codec route
      (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query).run x)

/-- Away from owner `k`'s finishes while the selected accept is not active, the guesser's handler is the split game's step on its own coins. -/
theorem guessReg_lift (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentInterface.Spec.Domain) (x : XState KemSK SplitBk 2)
    (notOracle : ∀ raw, query = .inr (.finish t.kem.val raw) → x.backend.2.2.active = true) :
    (guessReg setup codec route checks t p created query).run x =
      ccaCoins ((handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)
        query).run x) := by
  rcases query with coin | command
  · rfl
  · cases command with
    | finish owner raw =>
        change (if owner = t.kem.val ∧ x.backend.2.2.active = false then _ else _) = _
        split_ifs with oracle
        · obtain ⟨rfl, inactive⟩ := oracle
          rw [notOracle raw rfl] at inactive
          cases inactive
        · rfl
    | _ => rfl

/-- Owner `k`'s finish while the selected accept is not active is the oracle finish. -/
theorem guessReg_oracle (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (raw : Pqxdh.Bytes) (x : XState KemSK SplitBk 2) (inactive : x.backend.2.2.active = false) :
    (guessReg setup codec route checks t p created (.inr (.finish t.kem.val raw))).run x =
      (oracleFinish setup codec t.kem.val raw).run x := by
  change (if t.kem.val = t.kem.val ∧ x.backend.2.2.active = false then _ else _) = _
  split_ifs with oracle
  · rfl
  · exact absurd ⟨rfl, inactive⟩ oracle

/-- Before the selected raw accept, the guesser's handler at the parameters with the selected secret key replaced, interpreted by the pre-challenge oracle of the selected secret key, at the state with owner `k`'s secret key replaced, is the final split game's step with the replacement applied to its final state; the split game's step keeps owner `k`'s secret key. -/
theorem guessReg_interp (t : Target count) (p : Params KemSK count) (new : KemSK)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK SplitBk 2) (inactive : x.backend.2.2.active = false) (unmarked : x.backend.2.2.marks = none)
    (other : ¬ PqxdhDeploymentIdealAnomalyBound.SelectedAt t x query) (held : HoldsX t.kem.val p.chosen.2 x) :
    (PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup p.chosen.2)
        (guessReg setup codec route checks t (withChosen p new) created) query).run (swapX t.kem.val new x) =
      Prod.map id (swapX t.kem.val new) <$> (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query).run x ∧
    ∀ r ∈ support ((handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p
        created) query).run x), HoldsX t.kem.val p.chosen.2 r.2 := by
  rw [PqxdhRegistrationJointKemEntryFactor.mapRun_run]
  by_cases owner : ∃ raw, query = .inr (.finish t.kem.val raw)
  · obtain ⟨raw, rfl⟩ := owner
    have real : ¬ (x.backend.2.2.active = true ∧ t.kem.val = t.kem.val ∧
        PqxdhDeploymentIdealSteps.initSentAt x.base.native.owners t.kem.val = true) := fun chosen => by
      rw [inactive] at chosen; cases chosen.1
    rw [guessReg_oracle setup codec route checks t (withChosen p new) created raw (swapX t.kem.val new x) inactive]
    change _ = _ <$> (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
      ⟨.finish t.kem.val raw, trivial⟩).run x ∧
      ∀ r ∈ support ((PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created
        ⟨.finish t.kem.val raw, trivial⟩).run x), _
    rw [PqxdhDeploymentIdealEnvStep.idealSplit_finish_real setup codec route checks t p created _ raw x real]
    exact oracleFinish_interp setup codec checks route created t.kem.val p.chosen.2 new raw x held
  · rw [guessReg_lift setup codec route checks t (withChosen p new) created query (swapX t.kem.val new x)
      (fun raw same => absurd ⟨raw, same⟩ owner), interp_coins]
    exact split_swaps setup codec checks route t p new created query x inactive unmarked other
      (fun raw same => owner ⟨raw, same⟩) held

end Guesser

/-! ### Simulations under the replacement -/

section Simulate

/-- Two simulations of a program whose queries avoid a set: when every allowed query's steps are related by the replacement, so are the whole simulations. -/
theorem simulate_swaps {ι' σ α : Type} {spec : OracleSpec ι'} (impl₁ impl₂ : QueryImpl spec (StateT σ ProbComp))
    (swap : σ → σ) (inv : σ → Prop) (bad : spec.Domain → Prop) [DecidablePred bad]
    (step : ∀ query, ¬ bad query → Swaps swap inv (impl₁ query) (impl₂ query))
    (work : OracleComp spec α) (bounded : work.IsQueryBoundP bad 0) :
    Swaps swap inv (simulateQ impl₁ work) (simulateQ impl₂ work) := by
  induction work using OracleComp.inductionOn with
  | pure value =>
      intro s held
      refine ⟨by simp, ?_⟩
      intro r member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact held
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      obtain ⟨allowed, rest⟩ := bounded
      have good : ¬ bad query := by
        rcases allowed with free | impossible
        · exact free
        · omega
      have restBound : ∀ reply, (next reply).IsQueryBoundP bad 0 := fun reply => by
        have bound := rest reply
        simp only [good, ↓reduceIte] at bound
        exact bound
      intro s held
      obtain ⟨same, keeps⟩ := step query good s held
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind]
      refine ⟨?_, ?_⟩
      · rw [same, bind_map_left, map_bind]
        exact bind_congr_of_forall_mem_support _ fun r member => (ih r.1 (restBound r.1) r.2 (keeps r member)).1
      · intro r member
        rw [mem_support_bind_iff] at member
        obtain ⟨r', member', member⟩ := member
        exact (ih r'.1 (restBound r'.1) r'.2 (keeps r' member')).2 r member

end Simulate

/-! ### The flattened games -/

section Flat
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentBackend (handlerWith)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhDeploymentInterface (Entry)
open PqxdhDeploymentTranscript (acceptCount)
open PqxdhDeploymentIdealGuess (guessCt UntilStop)
open PqxdhDeploymentIdealAnomalyBound (Early SelectedQ stopGuess)

/-- A native handler composed with the secrecy layer, flattened onto the product of the ledger and the handler's state (as `PqxdhDeploymentIdealAnomalyBound.splitHandler`). -/
noncomputable def flat {σ : Type} {m : Type → Type} [Monad m] (bounds : PqxdhDeploymentInterface.FreshBounds)
    (handler : QueryImpl PqxdhDeploymentInterface.Spec (StateT σ m)) :
    QueryImpl PqxdhDeploymentInterface.FullSpec (StateT (Ledger × σ) m) := fun query state =>
  (fun r => (r.1.1, (r.1.2, r.2))) <$>
    (simulateQ handler ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds query).run state.1)).run state.2

/-- The flattened final split game is `flat` of the split game's native handler. -/
theorem splitHandler_flat (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    PqxdhDeploymentIdealAnomalyBound.splitHandler setup codec route checks t p bounds created =
      flat setup codec bounds (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)) := rfl

/-- Interpreting each step of a flattened handler is flattening the interpreted handler. -/
theorem mapRun_flat {σ : Type} {ιA : Type} {A : OracleSpec ιA} (bounds : PqxdhDeploymentInterface.FreshBounds)
    (interpret : QueryImpl A ProbComp) (handler : QueryImpl PqxdhDeploymentInterface.Spec (StateT σ (OracleComp A))) :
    PqxdhRegistrationJointKemEntryFactor.mapRun interpret (flat setup codec bounds handler) =
      flat setup codec bounds (PqxdhRegistrationJointKemEntryFactor.mapRun interpret handler) := by
  funext query
  refine StateT.ext fun state => ?_
  rw [PqxdhRegistrationJointKemEntryFactor.mapRun_run]
  change simulateQ interpret (_ <$> _) = _ <$> _
  rw [simulateQ_map, PqxdhRegistrationJointKemEntryFactor.simulateQ_mapRun]

/-- Every step of a flattened handler appends exactly one entry, the query with its reply, to the transcript (`PqxdhDeploymentIdealAnomalyBound.splitHandler_transcript` for any native handler). -/
theorem flat_transcript {σ : Type} (bounds : PqxdhDeploymentInterface.FreshBounds)
    (handler : QueryImpl PqxdhDeploymentInterface.Spec (StateT σ ProbComp)) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × σ) :
    ∀ result ∈ support ((flat setup codec bounds handler query).run state),
      result.2.1.transcript = state.1.transcript ++ [⟨query, result.1⟩] := by
  intro result member
  change result ∈ support (_ <$> _) at member
  rw [support_map] at member
  obtain ⟨reached, reachedMember, rfl⟩ := member
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at reachedMember
    obtain ⟨answer, _, rfl⟩ := reachedMember
    rfl
  · have value : reached.1 ∈ support ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds
        (.inr secrecy)).run state.1) := by
      apply OracleComp.support_simulateQ_run'_subset handler _ state.2
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, reachedMember, rfl⟩
    exact PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto codec setup.serverKeyId bounds secrecy
      state.1 reached.1 value

/-- Every step of a flattened handler keeps a stopped state's guess. -/
theorem flat_keeps (t : Target count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (handler : QueryImpl PqxdhDeploymentInterface.Spec (StateT (XState KemSK SplitBk 2) ProbComp))
    (query : PqxdhDeploymentInterface.Query) (state : Ledger × XState KemSK SplitBk 2) (value : Option MlKem768Ciphertext) (stopped : stopGuess codec t state = some value) :
    ∀ result ∈ support ((flat setup codec bounds handler query).run state), stopGuess codec t result.2 = some value := by
  intro result member
  have transcriptEq := flat_transcript setup codec bounds handler query state result member
  unfold stopGuess at stopped ⊢
  split at stopped
  · rename_i later
    have later' : t.accept < acceptCount result.2.1.transcript := by
      rw [transcriptEq]
      exact lt_of_lt_of_le later (PqxdhDeploymentIdealBeacon.acceptCount_prefix _ _)
    simp only [later', ↓reduceIte, Option.some.injEq]
    rw [transcriptEq, PqxdhDeploymentIdealGuess.guessCt_append codec t _ _ later]
    exact Option.some.inj stopped
  · cases stopped

/-- A raw accept made when the transcript has exactly the selected ordinal of raw accept attempts stops every flattened handler with the guess of the transcript before it. -/
theorem flat_selected (t : Target count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (handler : QueryImpl PqxdhDeploymentInterface.Spec (StateT (XState KemSK SplitBk 2) ProbComp)) (raw : Pqxdh.Bytes)
    (state : Ledger × XState KemSK SplitBk 2)
    (count : acceptCount state.1.transcript = t.accept) :
    ∀ result ∈ support ((flat setup codec bounds handler (.inl (.inr (.accept raw)))).run state),
      stopGuess codec t result.2 = some (guessCt codec t state.1.transcript) := by
  intro result member
  have transcriptEq := flat_transcript setup codec bounds handler _ state result member
  unfold stopGuess
  rw [transcriptEq, PqxdhDeploymentIdealTrace.acceptCount_accept, count]
  simp only [Nat.lt_succ_self, ↓reduceIte, Option.some.injEq]
  unfold guessCt PqxdhDeploymentIdealGuess.earlyFinish
  rw [PqxdhDeploymentIdealAnomalyBound.cutAt_selected t.accept _ count raw]

/-- Coins and sends of the guesser's handler, interpreted by the pre-challenge oracle of the selected secret key, are the split game's coins and sends under the replacement: they are the native steps on their own coins, which read no KEM secret key. -/
theorem coinSend_swaps (t : Target count) (p : Params KemSK count) (new : KemSK)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (coinSend : PqxdhDeploymentSecrecy.coinOrSend query = true) :
    Swaps (swapX t.kem.val new) (HoldsX t.kem.val p.chosen.2)
      (handlerWith setup codec route (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created) query)
      (PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup p.chosen.2)
        (guessReg setup codec route checks t (withChosen p new) created) query) := by
  intro x held
  rw [PqxdhRegistrationJointKemEntryFactor.mapRun_run, guessReg_lift setup codec route checks t (withChosen p new) created
    query (swapX t.kem.val new x) (fun raw same => by subst same; cases coinSend), interp_coins]
  rcases query with coin | command
  · refine ⟨?_, ?_⟩
    · simp only [handlerWith, StateT.run_lift, map_bind, map_pure]
      rfl
    · intro r member
      simp only [handlerWith, StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨_, _, rfl⟩ := member
      exact held
  · cases command with
    | serverSend keyId plaintext =>
        exact onBase_swaps t.kem.val p.chosen.2 new _ _
          (serverStep_swaps setup codec route t.kem.val p.chosen.2 new (.inl (plaintext, keyId))) x held
    | beaconSend owner plaintext =>
        exact onBase_swaps t.kem.val p.chosen.2 new _ _
          (beaconStep_swaps setup codec t.kem.val p.chosen.2 new owner (.inl plaintext)) x held
    | _ => cases coinSend

/-- Before the selected raw accept, every step of the flattened guesser game, interpreted by the pre-challenge oracle of the selected secret key, at the state with owner `k`'s secret key replaced, is the flattened split game's step with the replacement applied to its final state; the split game's step keeps owner `k`'s secret key. -/
theorem flat_step (t : Target count) (p : Params KemSK count) (new : KemSK)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (created : PqxdhLiveServerConstruction.Created Unit)
    (query : PqxdhDeploymentInterface.Query) (state : Ledger × XState KemSK SplitBk 2) (early : Early t state)
    (other : ¬ SelectedQ t state query) (held : HoldsX t.kem.val p.chosen.2 state.2) :
    (flat setup codec bounds (PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup p.chosen.2)
        (guessReg setup codec route checks t (withChosen p new) created)) query).run
        (state.1, swapX t.kem.val new state.2) =
      Prod.map id (Prod.map id (swapX t.kem.val new)) <$> (flat setup codec bounds (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)) query).run state ∧
    ∀ r ∈ support ((flat setup codec bounds (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)) query).run state),
      HoldsX t.kem.val p.chosen.2 r.2.2 := by
  rcases query with request | secrecy
  · obtain ⟨same, keeps⟩ := guessReg_interp setup codec route checks t p new created request state.2 early.inactive
      early.unmarked other held
    have shape : ∀ {σ : Type} (handler : QueryImpl PqxdhDeploymentInterface.Spec (StateT σ ProbComp)) (x : σ),
        (flat setup codec bounds handler (.inl request)).run (state.1, x) =
          (fun r => (r.1, (state.1.record (.inl request) r.1, r.2))) <$> (handler request).run x := by
      intro σ handler x
      change (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ handler ((ledgerImpl setup.source.crypto codec
        setup.serverKeyId bounds (.inl request)).run state.1)).run x = _
      rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
        Functor.map_map]
      rfl
    refine ⟨?_, ?_⟩
    · rw [shape, shape, same, Functor.map_map, Functor.map_map]
      rfl
    · intro r member
      rw [shape, support_map] at member
      obtain ⟨r', member', rfl⟩ := member
      exact keeps r' member'
  · have shape : ∀ {σ : Type} (handler : QueryImpl PqxdhDeploymentInterface.Spec (StateT σ ProbComp)) (x : σ),
        (flat setup codec bounds handler (.inr secrecy)).run (state.1, x) =
          (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ handler ((ledgerImpl setup.source.crypto codec
            setup.serverKeyId bounds (.inr secrecy)).run state.1)).run x := fun _ _ => rfl
    obtain ⟨same, keeps⟩ := simulate_swaps _ _ (swapX t.kem.val new) (HoldsX t.kem.val p.chosen.2)
      (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false)
      (fun query allowed => coinSend_swaps setup codec route checks t p new created query
        (by simpa using allowed)) _
      (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy state.1)
      state.2 held
    refine ⟨?_, ?_⟩
    · rw [shape, shape, same, Functor.map_map, Functor.map_map]
      rfl
    · intro r member
      rw [shape, support_map] at member
      obtain ⟨r', member', rfl⟩ := member
      exact keeps r' member'

/-- The transcript guess has the same law on the flattened final split game at the selected key pair and on the flattened guesser game at the selected public key with another secret key, interpreted by the pre-challenge oracle of the selected secret key: the two runs are identical until the selected raw accept up to the replacement of owner `k`'s secret key (`flat_step`), which stops both with the guess of the same transcript (`PqxdhDeploymentIdealAnomalyBound.selected_stop`, `flat_selected`), and the guess does not change afterwards (`PqxdhDeploymentIdealGuess.lawEq_until_stop`). -/
theorem guess_lawEq {X : Type} (t : Target count) (p : Params KemSK count) (new : KemSK)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (created : PqxdhLiveServerConstruction.Created Unit)
    (adversary : OracleComp PqxdhDeploymentInterface.FullSpec X) :
    LazyOracleDiscard.LawEq ((fun result => guessCt codec t result.2.1.transcript) <$>
        (simulateQ (PqxdhDeploymentIdealAnomalyBound.splitHandler setup codec route checks t p bounds created)
          adversary).run (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)))
      ((fun result => guessCt codec t result.2.1.transcript) <$>
        (simulateQ (flat setup codec bounds (PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup p.chosen.2)
          (guessReg setup codec route checks t (withChosen p new) created))) adversary).run
            (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))) := by
  rw [splitHandler_flat]
  have law := PqxdhDeploymentIdealGuess.lawEq_until_stop (flat setup codec bounds (handlerWith setup codec route
    (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)))
    (flat setup codec bounds (PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup p.chosen.2)
      (guessReg setup codec route checks t (withChosen p new) created)))
    (fun first second => second = (first.1, swapX t.kem.val new first.2) ∧ Early t first ∧
      HoldsX t.kem.val p.chosen.2 first.2)
    (stopGuess codec t) (stopGuess codec t)
    (fun query state value stopped => flat_keeps setup codec t bounds _ query state value stopped)
    (fun query state value stopped => flat_keeps setup codec t bounds _ query state value stopped)
    ?_ adversary (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))
    (Ledger.empty, swapX t.kem.val new (PqxdhDeploymentBackend.xinitial created
      (PqxdhDeploymentIdealSteps.splitInit created)))
    ⟨rfl, PqxdhDeploymentIdealAnomalyBound.early_initial t created, fun _ found => by cases found⟩
    (fun result => guessCt codec t result.2.1.transcript) (fun result => guessCt codec t result.2.1.transcript) ?_
  · rwa [swapX_initial] at law
  · rintro query first second ⟨rfl, early, held⟩
    by_cases selected : SelectedQ t first query
    · rcases query with (coin | command) | secrecy
      · exact absurd selected id
      · cases command with
        | accept raw =>
            have count : acceptCount first.1.transcript = t.accept := early.count.trans selected
            exact relTriple_post_mono (PqxdhServerAuthEntryFactor.relTriple_support _ _ _ _
              (PqxdhDeploymentIdealAnomalyBound.selected_stop setup codec route checks t p bounds created _ first early
                selected)
              (flat_selected setup codec t bounds _ raw (first.1, swapX t.kem.val new first.2) count))
              fun _ _ both => Or.inr ⟨_, both⟩
        | _ => exact absurd selected id
      · exact absurd selected id
    · obtain ⟨same, keeps⟩ := flat_step setup codec route checks t p new bounds created query first early selected held
      rw [same, ← id_map ((flat setup codec bounds (handlerWith setup codec route
        (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p created)) query).run first)]
      rw [Functor.map_map]
      refine relTriple_map (relTriple_refl_of_mem_support _ fun result member => Or.inl ⟨rfl, rfl,
        PqxdhDeploymentIdealAnomalyBound.early_step setup codec route checks t p bounds created query first early selected
          result member, keeps result member⟩)
  · intro left right post
    rcases post with ⟨_, eq, _⟩ | ⟨value, leftStop, rightStop⟩
    · rw [eq]
    · unfold stopGuess at leftStop rightStop
      split at leftStop
      · split at rightStop
        · exact (Option.some.inj leftStop).trans (Option.some.inj rightStop).symm
        · cases rightStop
      · cases leftStop

end Flat

/-! ### The ciphertext guess with a decapsulation oracle and the anomaly guesser -/

section Bound
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentBackend (handlerWith)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentIdealGuess (guessCt)
open PqxdhPrivateKemSource (ccaCoins evalKem)
open PqxdhInitializerSecrecy (kemAmbientImpl)

/-- The ciphertext guess of a guesser with decapsulation access (plan section 84): the probability that `guess`, run on the public key of a fresh key pair with the pre-challenge decapsulation oracle of its secret key (the phase-1 oracle of `PqxdhKemIndCca.OneKeyAdversary`, `KEMScheme.IND_CCA_preChallengeImpl`) and before the encapsulation to that key, outputs the encapsulation's ciphertext. The guesser's interface is the KEM's IND-CCA oracle interface `MlKemCCAOracleSpec`; its ambient queries are interpreted by the setup's fixed ambient interpreter, like key generation and encapsulation. A definition, not an assumption. -/
noncomputable def ctGuessByCca
    (guess : MlKem768PublicKey → OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKem768Ciphertext)) : ENNReal :=
  𝒟[simulateQ (kemAmbientImpl setup.baseImpl) (do
      let pair ← setup.kem.keygen
      let guessed ← simulateQ (setup.kem.IND_CCA_preChallengeImpl pair.2) (guess pair.1)
      let encapsulated ← setup.kem.encaps pair.1
      pure (decide (guessed = some encapsulated.1)))] {true}

/-- `ctGuessByCca` with the ambient interpretation pushed inside: the key pair, the guesser evaluated with the decapsulation oracle of the selected secret key (`PqxdhPrivateKemSource.evalKem`), then the encapsulation. -/
theorem ctGuessByCca_evalKem
    (guess : MlKem768PublicKey → OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKem768Ciphertext)) :
    ctGuessByCca setup guess =
      𝒟[simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        evalKem setup.baseImpl setup.kem pair.2 (guess pair.1) >>= fun guessed =>
          simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
            pure (decide (guessed = some encapsulated.1))] {true} := by
  unfold ctGuessByCca
  simp only [simulateQ_bind, simulateQ_pure]
  rfl

/-- A guesser with decapsulation access still hits the encapsulation with probability at most `ctGuessPk`: its guess is a random variable of the key pair made before the encapsulation (`PqxdhDeploymentIdealAnomalyBound.pairGuess_le`). -/
theorem ctGuessByCca_le_pk
    (guess : MlKem768PublicKey → OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKem768Ciphertext)) :
    ctGuessByCca setup guess ≤ PqxdhDeploymentIdealTrace.ctGuessPk setup := by
  rw [ctGuessByCca_evalKem]
  refine le_of_eq_of_le ?_ (PqxdhDeploymentIdealAnomalyBound.pairGuess_le setup
    (fun pair => some <$> evalKem setup.baseImpl setup.kem pair.2 (guess pair.1)))
  congr 2
  refine bind_congr fun pair => ?_
  rw [bind_map_left]
  refine bind_congr fun guessed => bind_congr fun encapsulated => ?_
  simp only [Option.some.injEq]

/-- A guesser without decapsulation queries, lifted into the IND-CCA interface (`PqxdhDeploymentIdealAnomaly.ambientLift`), has the ciphertext guess `PqxdhDeploymentIdealAnomaly.ctGuessBy`: `ctGuessByCca` extends it. -/
theorem ctGuessByCca_ambient (guess : MlKem768PublicKey → OracleComp (unifSpec + baseSpec) MlKem768Ciphertext) :
    ctGuessByCca setup (fun pk => some <$> simulateQ (PqxdhDeploymentIdealAnomaly.ambientLift setup) (guess pk)) =
      PqxdhDeploymentIdealAnomaly.ctGuessBy setup guess := by
  unfold ctGuessByCca PqxdhDeploymentIdealAnomaly.ctGuessBy
  congr 3
  refine bind_congr fun pair => ?_
  erw [simulateQ_map, PqxdhDeploymentIdealAnomaly.guess_preChallenge]
  rw [bind_map_left]
  refine bind_congr fun guessed => bind_congr fun encapsulated => ?_
  simp only [Option.some.injEq, eq_comm]

/-- The anomaly guesser (plan section 84): a program over the KEM's IND-CCA oracle interface that receives the selected public key `pk` and never a secret key or the challenge. It draws a key pair of its own (whose secret half `dummy.2` stands in for the selected secret key in the state), the other pool entries and the Server construction on its own coins, runs the final split game of the target at the parameters `(pk, dummy.2)`, `others` and the all-zero challenge with owner `k`'s finishes while the selected accept is not active answered through the decapsulation oracle (`guessReg`), and outputs the transcript guess (`PqxdhDeploymentIdealGuess.guessCt`), which the selected raw accept freezes. -/
noncomputable def anomalyGuesser (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (pk : MlKem768PublicKey) :
    OracleComp (MlKemCCAOracleSpec baseSpec) (Option MlKem768Ciphertext) := do
  let dummy ← ccaCoins (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let others ← ccaCoins (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen)
    count)
  let born ← ccaCoins ((PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId
    none).run runtime)
  match born.1 with
  | none => pure none
  | some created => do
      let result ← (simulateQ (flat setup codec bounds (guessReg setup codec route checks t
        ⟨(pk, dummy.2), others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ created))
        (PqxdhDeploymentInterface.asModeO mode adversary)).run
          (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))
      pure (guessCt codec t result.2.1.transcript)

/-- The anomaly guesser evaluated with the decapsulation oracle of a secret key: its own draws, then the flattened guesser game with each step interpreted by that oracle (`guessReg_interp`'s left-hand side), at the parameters of the selected key pair with the secret key replaced by the guesser's own (`withChosen`). -/
theorem guesser_eval (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (pair : PqxdhLiveKemReservation.Pair KemSK) :
    evalKem setup.baseImpl setup.kem pair.2
        (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode adversary pair.1) =
      simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun dummy =>
        PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>=
          fun others => (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId
            none).run runtime >>= fun born => match born.1 with
          | none => pure none
          | some created => (fun result => guessCt codec t result.2.1.transcript) <$>
              (simulateQ (flat setup codec bounds (PqxdhRegistrationJointKemEntryFactor.mapRun (interp setup pair.2)
                (guessReg setup codec route checks t (withChosen ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩
                  dummy.2) created))) (PqxdhDeploymentInterface.asModeO mode adversary)).run
                (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created)) := by
  simp only [anomalyGuesser, PqxdhPrivateKemSource.evalKem_bind, PqxdhPrivateKemSource.evalKem_coins]
  refine bind_congr fun dummy => bind_congr fun others => bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · rfl
  · simp only [PqxdhPrivateKemSource.evalKem_bind, ← simulateQ_interp]
    rw [PqxdhRegistrationJointKemEntryFactor.simulateQ_mapRun, mapRun_flat]
    simp only [simulateQ_pure, bind_pure_comp]
    rfl

/-- For every key pair, the transcript guess of the final split game at that key pair (after the other entries' draw) has the law of the anomaly guesser at its public key, evaluated with the decapsulation oracle of its secret key (`guess_lawEq`, the guesser's own key pair dropped by `LazyOracleDiscard.lawEq_drop`). -/
theorem pair_lawEq (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (pair : PqxdhLiveKemReservation.Pair KemSK) :
    LazyOracleDiscard.LawEq (Option.join <$> (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl
        setup.baseImpl) setup.kem.keygen) count >>= fun others =>
          PqxdhDeploymentIdealAnomalyBound.guessView codec t <$> (PqxdhDeploymentBackend.gameWith setup codec route
            PqxdhDeploymentIdealSteps.splitInit (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t
              ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩) ensureInit identityIndex bounds mode
                adversary).run' runtime))
      (evalKem setup.baseImpl setup.kem pair.2
        (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode adversary pair.1)) := by
  rw [guesser_eval]
  refine (LazyOracleDiscard.lawEq_drop (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) _).symm.trans
    (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun dummy => ?_)
  rw [map_bind]
  refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun others => ?_
  rw [PqxdhDeploymentIdealAnomalyBound.game_guess, map_bind]
  refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · exact LazyOracleDiscard.LawEq.of_eq (by simp)
  · have law := (guess_lawEq setup codec route checks t ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩
      dummy.2 bounds created (PqxdhDeploymentInterface.asModeO mode adversary))
    simp only [Functor.map_map, Option.join_some]
    exact law

open Classical in
/-- On the challenger's draws followed by the final split game, the transcript guess is the challenge ciphertext with probability exactly the ciphertext guess of the anomaly guesser with decapsulation access: the guess has the same law at every challenge (`PqxdhDeploymentIdealAnomalyBound.game_guess_law`), so the encapsulation is drawn after it (`LazyOracleDiscard.lawEq_swap`), and for every key pair the guess is the guesser's output (`pair_lawEq`). -/
theorem split_guess_cca (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
        (fun outcome => decide (PqxdhDeploymentIdealAnomalyBound.guessView codec t outcome = some (some p.challenge))) <$>
          (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
            (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
              adversary).run' runtime] {true} =
      ctGuessByCca setup (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode
        adversary) := by
  let guessOf : Params KemSK count → ProbComp (Option (Option MlKem768Ciphertext)) := fun p =>
    PqxdhDeploymentIdealAnomalyBound.guessView codec t <$> (PqxdhDeploymentBackend.gameWith setup codec route
      PqxdhDeploymentIdealSteps.splitInit (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit
        identityIndex bounds mode adversary).run' runtime
  have law : LazyOracleDiscard.LawEq
      (PqxdhDeploymentIdealParams.drawParams setup count >>= fun p =>
        (fun outcome => decide (PqxdhDeploymentIdealAnomalyBound.guessView codec t outcome = some (some p.challenge))) <$>
          (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
            (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t p) ensureInit identityIndex bounds mode
              adversary).run' runtime)
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>=
          fun others => guessOf ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩) >>= fun guessed =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          pure (decide (guessed = some (some encapsulated.1)))) := by
    unfold PqxdhDeploymentIdealParams.drawParams
    simp only [bind_assoc, pure_bind]
    refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun pair => ?_
    refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun others => ?_
    have pointwise : ∀ encapsulated : MlKem768Ciphertext × MlKemSharedSecret,
        LazyOracleDiscard.LawEq
          ((fun outcome => decide (PqxdhDeploymentIdealAnomalyBound.guessView codec t outcome =
              some (some encapsulated.1))) <$>
            (PqxdhDeploymentBackend.gameWith setup codec route PqxdhDeploymentIdealSteps.splitInit
              (PqxdhDeploymentIdealDefer.idealSplit setup codec route checks t ⟨pair, others, encapsulated.1⟩) ensureInit
                identityIndex bounds mode adversary).run' runtime)
          (guessOf ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ >>= fun guessed =>
            pure (decide (guessed = some (some encapsulated.1)))) := by
      intro encapsulated
      have same := (PqxdhDeploymentIdealAnomalyBound.game_guess_law setup codec route checks t
        ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ encapsulated.1 ensureInit identityIndex bounds mode
          adversary runtime).symm.map (fun guessed => decide (guessed = some (some encapsulated.1)))
      simp only [Functor.map_map] at same
      refine same.trans (LazyOracleDiscard.LawEq.of_eq ?_)
      simp only [guessOf, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
    refine (LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) pointwise).trans ?_
    exact LazyOracleDiscard.lawEq_swap _ _ _
  have cca : LazyOracleDiscard.LawEq
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        (PqxdhLiveKemSelection.sampleFamily (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen) count >>=
          fun others => guessOf ⟨pair, others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩) >>= fun guessed =>
        simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          pure (decide (guessed = some (some encapsulated.1))))
      (simulateQ (kemAmbientImpl setup.baseImpl) setup.kem.keygen >>= fun pair =>
        evalKem setup.baseImpl setup.kem pair.2 (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime
          bounds mode adversary pair.1) >>= fun guessed =>
          simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
            pure (decide (guessed = some encapsulated.1))) := by
    refine LazyOracleDiscard.LawEq.bind (LazyOracleDiscard.LawEq.refl _) fun pair => ?_
    have joined : ∀ guessed : Option (Option MlKem768Ciphertext),
        (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          (pure (decide (guessed = some (some encapsulated.1))) : ProbComp Bool)) =
        (simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
          pure (decide (guessed.join = some encapsulated.1))) := by
      intro guessed
      refine bind_congr fun encapsulated => ?_
      rcases guessed with _ | _ | value <;> simp
    simp only [joined]
    refine (LazyOracleDiscard.LawEq.of_eq (bind_map_left Option.join _ (fun guessed =>
      simulateQ (kemAmbientImpl setup.baseImpl) (setup.kem.encaps pair.1) >>= fun encapsulated =>
        (pure (decide (guessed = some encapsulated.1)) : ProbComp Bool))).symm).trans ?_
    exact LazyOracleDiscard.LawEq.bind (pair_lawEq setup codec route checks t ensureInit identityIndex runtime bounds mode
      adversary pair) fun _ => LazyOracleDiscard.LawEq.refl _
  rw [(law.trans cca).evalDist_eq, ctGuessByCca_evalKem]

open Classical in
/-- The transcript guess event on the record world with the ideal environment of a target has probability at most the ciphertext guess of the anomaly guesser with decapsulation access: the event has the same probability on the challenger's draws followed by the final split game (`PqxdhDeploymentIdealEnv.c1_split`, as in `PqxdhDeploymentIdealAnomalyBound.guess_le_pk_sup`), where it is exactly `ctGuessByCca` of the guesser (`split_guess_cca`). No read-back premise. -/
theorem guess_le_cca (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧
        guessCt codec t value.2.1.2.transcript = some value.2.2.backend.1.challenge)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤
      ctGuessByCca setup (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode
        adversary) := by
  let hit : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × Ledger ×
      XState KemSK (Params KemSK count × SplitBk) 2) → Prop :=
    fun outcome => ∃ value, outcome = some value ∧
      guessCt codec t value.2.2.1.transcript = some value.2.2.2.backend.1.challenge
  refine (PqxdhDeploymentIdealAnomalyBound.evalDist_decide_mono _ _
    (fun result => hit (PqxdhDeploymentEnvironmentJoin.joined result))
    fun result _ ⟨value, found, guessed⟩ => ⟨(value.1, value.2.1.1, value.2.1.2,
      PqxdhDeploymentEnvironmentJoin.merge value.2.2 result.2), by
        simp only [PqxdhDeploymentEnvironmentJoin.joined, found, Option.map_some], guessed⟩).trans ?_
  have law := (PqxdhDeploymentIdealEnv.c1_split setup codec route checks t ensureInit identityIndex runtime bounds mode
    adversary).map (fun outcome => decide (hit outcome))
  have joinedEq : (fun result => decide (hit (PqxdhDeploymentEnvironmentJoin.joined result))) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary =
      (fun outcome => decide (hit outcome)) <$> (PqxdhDeploymentEnvironmentJoin.joined <$>
        PqxdhRecordLiftWorld.run setup codec route
          (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
            mode adversary) := by
    rw [Functor.map_map]
  rw [joinedEq, ← law.evalDist_eq, map_bind]
  refine le_of_eq ((Eq.trans ?_ (split_guess_cca setup codec route checks t ensureInit identityIndex runtime bounds mode
    adversary)))
  congr 2
  refine bind_congr fun p => ?_
  rw [Functor.map_map]
  congr 1
  funext outcome
  rcases outcome with _ | value
  · simp [hit, PqxdhDeploymentIdealAnomalyBound.guessView]
  · simp [hit, PqxdhDeploymentIdealAnomalyBound.guessView, PqxdhDeploymentEnvironmentDraw.withX]

open Classical in
/-- `anomaly_le_pk` (plan sections 49 Q2 option (b) and 84): under `Phase1ReadBack` and `Phase2ReadBack`, the record world with the ideal environment of a target has the Beacon-side anomaly with probability at most the ciphertext guess of the explicit anomaly guesser (`anomalyGuesser`), a program over the KEM's IND-CCA oracle interface that receives only the selected public key and answers owner `k`'s decapsulations through the decapsulation oracle: the anomaly implies the transcript guess event (`PqxdhDeploymentIdealGuess.anomaly_guess`), bounded by `guess_le_cca`. This is the form that CE-12a's predict-then-compare IND-CCA reduction consumes. -/
theorem anomaly_le_pk (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧
        PqxdhDeploymentIdealTrace.Anomaly setup.source.crypto codec serverKid t value.2.1.2.transcript)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤
      ctGuessByCca setup (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode
        adversary) :=
  (PqxdhDeploymentIdealAnomalyBound.evalDist_decide_mono _ _ (fun result => ∃ value, result.1 = some value ∧
      guessCt codec t value.2.1.2.transcript = some value.2.2.backend.1.challenge)
    fun result member ⟨value, found, anomaly⟩ => ⟨value, found,
      PqxdhDeploymentIdealGuess.anomaly_guess setup codec route checks phase1 phase2 t ensureInit identityIndex runtime
        serverKid bounds mode adversary result member value found anomaly⟩).trans
    (guess_le_cca setup codec route checks t ensureInit identityIndex runtime bounds mode adversary)

open Classical in
/-- `anomaly_le_pk` for the anomaly on a prefix (the exceptional alternative of `PqxdhDeploymentIdealBeacon.ideal_slots_prefix`): under `Phase1ReadBack` and `Phase2ReadBack`, the event that owner `k` designates the target on some prefix of the final transcript through a finish made before the selected raw accept has probability at most the ciphertext guess of `anomalyGuesser`, through `PqxdhDeploymentIdealGuess.anomaly_prefix_guess` and `guess_le_cca`. -/
theorem anomaly_prefix_le_pk (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    𝒟[(fun result => decide (∃ value, result.1 = some value ∧ ∃ pre rest, value.2.1.2.transcript = pre ++ rest ∧
        PqxdhDeploymentIdealTrace.Anomaly setup.source.crypto codec serverKid t pre)) <$>
      PqxdhRecordLiftWorld.run setup codec route
        (PqxdhDeploymentIdealEnv.envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds
          mode adversary] {true} ≤
      ctGuessByCca setup (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode
        adversary) :=
  (PqxdhDeploymentIdealAnomalyBound.evalDist_decide_mono _ _ (fun result => ∃ value, result.1 = some value ∧
      guessCt codec t value.2.1.2.transcript = some value.2.2.backend.1.challenge)
    fun result member ⟨value, found, pre, rest, split, anomaly⟩ => ⟨value, found,
      PqxdhDeploymentIdealGuess.anomaly_prefix_guess setup codec route checks phase1 phase2 t ensureInit identityIndex
        runtime serverKid bounds mode adversary result member value found pre rest split anomaly⟩).trans
    (guess_le_cca setup codec route checks t ensureInit identityIndex runtime bounds mode adversary)

end Bound

/-! ### Query bounds of the anomaly guesser -/

section Queries
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentBackend (handlerWith)
open PqxdhDeploymentSecrecy (Ledger ledgerImpl)
open PqxdhPrivateKemSource (ccaCoins)
open PqxdhKemIndCca (IsMlKemLogicalDecapsulationQuery)

/-- A probabilistic computation run on the guesser's own coins makes no decapsulation query. -/
theorem ccaCoins_decapsulate {α : Type} (work : ProbComp α) :
    (ccaCoins (baseSpec := baseSpec) work).IsQueryBoundP IsMlKemLogicalDecapsulationQuery 0 :=
  (OracleComp.isQueryBoundP_false work 0).simulateQ_of_step (fun _ impossible => impossible.elim)
    fun query _ => by
      rw [isQueryBoundP_query_iff]
      intro decap
      exact decap.elim

/-- The oracle finish makes at most one decapsulation query: the native owner program decapsulates at most once (`nativeOwner_decapsulate`), each decapsulation is one oracle query, and every other callback runs on the guesser's own coins. -/
theorem oracleFinish_decapsulate {Bk : Type} {n : ℕ} (index : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK Bk n) :
    ((oracleFinish (baseSpec := baseSpec) setup codec index raw).run x).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery 1 := by
  unfold oracleFinish
  dsimp only [StateT.run]
  split
  · exact isQueryBoundP_pure _ _ _
  · rw [isQueryBoundP_map_iff]
    refine (nativeOwner_decapsulate _ raw _).simulateQ_run_of_step (fun query decap state => ?_)
      (fun query other state => ?_) _
    · rcases query with query | query
      · cases query <;> try cases decap
        simp only [oracleCallbacks, prepOracle, StateT.run]
        rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro _
        exact Nat.one_pos
      · cases decap
    · rcases query with query | query
      · cases query
        case decapsulate ciphertext keys => exact absurd rfl other
        all_goals exact ccaCoins_decapsulate _
      · exact ccaCoins_decapsulate _

/-- Every step of the guesser's native handler makes at most one decapsulation query. -/
theorem guessReg_decapsulate (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (x : XState KemSK SplitBk 2) :
    ((guessReg (baseSpec := baseSpec) setup codec route checks t p created query).run x).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery 1 := by
  by_cases oracle : ∃ raw, query = .inr (.finish t.kem.val raw) ∧ x.backend.2.2.active = false
  · obtain ⟨raw, rfl, inactive⟩ := oracle
    rw [guessReg_oracle setup codec route checks t p created raw x inactive]
    exact oracleFinish_decapsulate setup codec t.kem.val raw x
  · rw [guessReg_lift setup codec route checks t p created query x fun raw same => by
      cases active : x.backend.2.2.active
      · exact absurd ⟨raw, same, active⟩ oracle
      · rfl]
    exact (ccaCoins_decapsulate _).mono (Nat.zero_le 1)

/-- Every step of the guesser's native handler other than a finish makes no decapsulation query. -/
theorem guessReg_decapsulate_other (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Spec.Domain)
    (other : ∀ owner raw, query ≠ .inr (.finish owner raw)) (x : XState KemSK SplitBk 2) :
    ((guessReg (baseSpec := baseSpec) setup codec route checks t p created query).run x).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery 0 := by
  rw [guessReg_lift setup codec route checks t p created query x fun raw same => absurd same (other _ raw)]
  exact ccaCoins_decapsulate _

/-- Every step of the flattened guesser game makes at most one decapsulation query, and none unless it is a finish. -/
theorem flat_decapsulate (t : Target count) (p : Params KemSK count) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (created : PqxdhLiveServerConstruction.Created Unit) (query : PqxdhDeploymentInterface.Query)
    (state : Ledger × XState KemSK SplitBk 2) :
    ((flat setup codec bounds (guessReg (baseSpec := baseSpec) setup codec route checks t p created) query).run
      state).IsQueryBoundP IsMlKemLogicalDecapsulationQuery
        (if PqxdhDeploymentInterface.queryClass query = 5 then 1 else 0) := by
  rcases query with request | secrecy
  · change ((fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (guessReg setup codec route checks t p created)
      ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds (.inl request)).run state.1)).run state.2).IsQueryBoundP
        _ _
    rw [isQueryBoundP_map_iff, PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, isQueryBoundP_map_iff]
    split
    · exact guessReg_decapsulate setup codec route checks t p created request state.2
    · rename_i notFinish
      refine guessReg_decapsulate_other setup codec route checks t p created request (fun owner raw same => ?_) state.2
      subst same
      exact notFinish rfl
  · change ((fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ (guessReg setup codec route checks t p created)
      ((ledgerImpl setup.source.crypto codec setup.serverKeyId bounds (.inr secrecy)).run state.1)).run state.2).IsQueryBoundP
        _ _
    have notFinish : PqxdhDeploymentInterface.queryClass (.inr secrecy) ≠ 5 := by
      rcases secrecy <;> simp [PqxdhDeploymentInterface.queryClass]
    simp only [notFinish, ↓reduceIte]
    rw [isQueryBoundP_map_iff]
    refine (PqxdhDeploymentSecrecy.secrecy_frame setup.source.crypto codec setup.serverKeyId bounds secrecy
      state.1).simulateQ_run_of_step (fun query _ inner => guessReg_decapsulate setup codec route checks t p created
        query inner) (fun query coinSend inner => guessReg_decapsulate_other setup codec route checks t p created query
          (fun owner raw same => by subst same; exact coinSend rfl) inner) _

/-- The query bound of the anomaly guesser (plan section 84): against an adversary that respects a budget, the guesser makes at most `budget.finish` decapsulation queries on every execution path, one for each of owner `k`'s finishes made while the selected accept is not active (the oracle finish decapsulates at most once, `oracleFinish_decapsulate`), every other query being one of its own coins. -/
theorem anomalyGuesser_decapsulations (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ)
    (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (budget : PqxdhDeploymentInterface.Budget)
    (respects : budget.Respects adversary) (pk : MlKem768PublicKey) :
    (anomalyGuesser setup codec route checks t ensureInit identityIndex runtime bounds mode adversary pk).IsQueryBoundP
      IsMlKemLogicalDecapsulationQuery budget.finish := by
  unfold anomalyGuesser
  rw [show budget.finish = 0 + (0 + (0 + (budget.finish + 0))) by omega]
  refine isQueryBoundP_bind (ccaCoins_decapsulate _) fun dummy _ => ?_
  refine isQueryBoundP_bind (ccaCoins_decapsulate _) fun others _ => ?_
  refine isQueryBoundP_bind (ccaCoins_decapsulate _) fun born _ => ?_
  rcases born with ⟨_ | created, after⟩
  · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind ?_ fun _ _ => isQueryBoundP_pure _ _ _
    have total := FinitePartitionQueryBounds.weighted_bound PqxdhDeploymentInterface.queryClass
      (fun kind => if kind = 5 then 1 else 0) budget.cap
      (flat setup codec bounds (guessReg setup codec route checks t
        ⟨(pk, dummy.2), others, PqxdhDeploymentIdealAnomalyBound.zeroCt⟩ created))
      IsMlKemLogicalDecapsulationQuery (PqxdhDeploymentInterface.asModeO mode adversary)
      (PqxdhDeploymentCompileSecrecy.asModeO_bound mode adversary budget respects)
      (fun query state => flat_decapsulate setup codec route checks t _ bounds created query state)
      (Ledger.empty, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.splitInit created))
    have sum : (∑ kind : Fin 14, (if kind = 5 then 1 else 0) * budget.cap kind) = budget.finish := by
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rfl
    rw [sum] at total
    exact total

end Queries

end BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.simulateQ_interp' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.simulateQ_interp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.interp_coins' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.interp_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.oracleCallbacks_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.oracleCallbacks_interp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.oracleFinish_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.oracleFinish_interp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_oracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_oracle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_interp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_interp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.simulate_swaps' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.simulate_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.splitHandler_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.splitHandler_flat

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.mapRun_flat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.mapRun_flat

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_transcript' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_transcript

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.coinSend_swaps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.coinSend_swaps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guess_lawEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guess_lawEq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca_evalKem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca_evalKem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca_le_pk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca_le_pk

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca_ambient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca_ambient

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guesser_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guesser_eval

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.pair_lawEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.pair_lawEq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.split_guess_cca' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.split_guess_cca

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guess_le_cca' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guess_le_cca

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.anomaly_prefix_le_pk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.anomaly_prefix_le_pk

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ccaCoins_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.ccaCoins_decapsulate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.oracleFinish_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.oracleFinish_decapsulate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_decapsulate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_decapsulate_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.guessReg_decapsulate_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_decapsulate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.flat_decapsulate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser_decapsulations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser_decapsulations

-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLater
import BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff

/-! LQ-F upstream, unit C2: CE-11b's split chain and C6 for the later ideal game (unit 11b-L of the CE plan, LQ-F upstream design-v2 section 4.2). The later ideal game `PqxdhDeploymentIdealLaterGame.idealLaterGame` (`IL_g`) runs the LQ-F later game `PqxdhDeploymentFinishErasure.laterWith` with CE-11b's ideal registration and the fixed real post phase `realPost` (LQ-F design-v2 D5). This module replays CE-11b's chain from the ideal registration to the final split form (`PqxdhDeploymentIdealDefer.ideal_to_split`) for the later game, with the generic tools of `PqxdhDeploymentIdealLater`, and composes it with C6 for the ideal environment of a target (`PqxdhDeploymentIdealEnv.envGD`).

- The split chain for the later game, pointwise in the target and the challenger's draws, every step with the real post phase: C7 (`erase_ideal_later`, `PqxdhDeploymentFinishErasure.erase_later_ctx` at the ideal pair, the real post phase commuting with CTX completions by `realPost_commutes`), the represent step (`represent_ideal_later`), seed relocation (`seed_move_later`), their composition (`ideal_to_splitX_later`), the kernel identities (`ideal_to_splitEager_later`, `PqxdhDeploymentIdealKernel.split_kernel`), the seed deferral (`split_later`, `PqxdhDeploymentIdealLater.defer_seeds_later` at CE-11b's pair `splitSeeds`, the real post phase commuting with seed completions by `realPost_commutes_seed`) and the whole chain (`ideal_to_split_later`): the later game with the ideal registration and the later game with the final split form have the same law up to the split view (`PqxdhDeploymentIdealKeys.splitView`: the deployment state with the CTX cache emptied, the allocator and the ideal backend, the LQ-F snapshot and the log).
- The post phase of the final split form is the real post phase (`idealSplit_hmac`, `postNative_split`): its HMAC command is the logged real HMAC `realRegAt`, which is the native HMAC on the deployment state with the rest of the extended state kept (`PqxdhDeploymentIdealLaterGame.realRegAt_hmac`), so `PqxdhDeploymentIdealLaterGame.postNative_real` applies.
- C6 for the ideal environment of a target: at the full reassembled state for the final split form (`c6_split`, `PqxdhDeploymentIdealLater.join_later_param` with `PqxdhDeploymentIdealEnv.ideal_splits`), and for the later ideal game itself at the observed projection (`c6_ideal`: the post-run output, the run-phase ledger and the produced frames), at the public projection (`c6_ideal_public`: also the Server's public data, the record view and the Beacon-side reveal with the Server ephemeral log) and for `IL_g` (`c6_idealGame`); the decision of the later second compile lemma (`PqxdhDeploymentIdealLaterGame.ceDecideL`) is the hand-off decision `PqxdhDeploymentIdealHandoff.decisionOn` on the observed projection (`ceDecideL_observed`), so `IL_g` and the later record world with `envGD` give it the same probability (`c6_idealGame_decide`).
- U-L3's reveal constraint (`envReveal_blind`): the environment's reveal reads the environment's owners, snapshot, Server seed and log, and neither the backend (the hidden-slot material) nor the shared native state (the HMAC cache, hence the R1 slice of item 2).

These are equalities of programs and in law; they charge nothing, add no assumption or contract, and make no security claim. LQ-F claims confidentiality only. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec Handle)
open PqxdhDeploymentBackend (XState)
open PqxdhDeploymentFinishErasure (outcomeMap laterWith realPost fullX)
open PqxdhDeploymentSeedSplit (mapBackend joinTable seedFree)
open PqxdhDeploymentIdealSlots (Coord)
open PqxdhDeploymentIdealSteps (IdealCore IdealBk TableState SplitBk idealInit splitInit idealReg idealProg
  idealCoreErased erasedHidden realRegAt)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentIdealKeys (idealSplitX splitView moveSeeds)
open PqxdhDeploymentIdealKernel (idealSplitEager)
open PqxdhDeploymentIdealDefer (idealSplit)
open PqxdhDeploymentIdealEnv (envGD idealStep IdealInv)
open PqxdhDeploymentEnvironmentJoin (joined postNative envReveal)
open PqxdhDeploymentEnvironmentDraw (withX)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentLater (PostSpec)
open PqxdhRegistrationJointKemSecondEntry (Alloc emptyAlloc)
open LazyOracleDiscard (LawEq)

variable {KemSK : Type}

/-! ### The split chain for the later game -/

section Chain
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- C7 for the later game with the ideal registration and the real post phase (the later form of `PqxdhDeploymentIdealErase.erase_ideal`): the later games with the ideal registration and with its C7-erased core have the same law of the Server's public data, the second adversary's output, the run-phase ledger and the final state with the CTX cache emptied. -/
theorem erase_ideal_later (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap fullX <$> (laterWith setup codec route idealInit (idealReg setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime)
      (outcomeMap fullX <$> (laterWith setup codec route idealInit
        (idealCoreErased setup codec route checks t p PqxdhDeploymentSeedSplit.tableService)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime) := by
  have erased := PqxdhDeploymentFinishErasure.erase_later_ctx setup codec route
    (fun created => PqxdhDeploymentIdealErase.idealPair setup codec route checks t p PqxdhDeploymentSeedSplit.tableService
      created) (realPost setup codec checks) (fun created query =>
        PqxdhDeploymentFinishErasure.realPost_commutes setup codec checks created query)
    idealInit ensureInit identityIndex bounds mode first second runtime
  simp only [PqxdhDeploymentIdealErase.idealPair_erased] at erased
  exact erased

/-- The represent step for the C7-erased ideal registration in the later game (the later form of `PqxdhDeploymentIdealKeys.represent_ideal`): the later game with item 2's persistent lazy table, read through the table's cache, and the later game with the split service, read through the joined table, have the same law. -/
theorem represent_ideal_later (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap (mapBackend Prod.fst) <$> (laterWith setup codec route idealInit
        (fun created => idealCoreErased setup codec route checks t p PqxdhDeploymentSeedSplit.tableService created)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime)
      (outcomeMap (mapBackend joinTable) <$> (laterWith setup codec route
        (fun _ => ((∅, ∅), (emptyAlloc, IdealCore.initial)))
        (fun created => idealCoreErased setup codec route checks t p PqxdhDeploymentSeedSplit.splitService created)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime) :=
  PqxdhDeploymentIdealLater.represent_split_later setup codec route checks
    (fun {S} svc created => idealCoreErased setup codec route checks t p (S := S) svc created)
    (PqxdhDeploymentIdealSteps.idealCoreErased_natural setup codec route checks t p)
    (fun _ => (emptyAlloc, IdealCore.initial)) ensureInit identityIndex bounds mode first second runtime

/-- Seed relocation for the C7-erased ideal registration in the later game (the later form of `PqxdhDeploymentIdealKeys.seed_move`): the later game with the split service, with the seeds moved from the service state into the extended state's seed table, is exactly the later game with `idealSplitX`. -/
theorem seed_move_later (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    outcomeMap moveSeeds <$> (laterWith setup codec route (fun _ => ((∅, ∅), (emptyAlloc, IdealCore.initial)))
        (fun created => idealCoreErased setup codec route checks t p PqxdhDeploymentSeedSplit.splitService created)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime =
      (laterWith setup codec route splitInit (idealSplitX setup codec route checks t p) (realPost setup codec checks)
        ensureInit identityIndex bounds mode first second).run runtime :=
  PqxdhDeploymentIdealLater.game_moveSeeds_later setup codec route checks
    (idealProg setup codec route checks t p (erasedHidden setup codec checks))
    (fun created query => PqxdhDeploymentIdealKeys.idealProg_seedFrame setup codec route checks t p _ created query)
    PqxdhDeploymentSeedSplit.splitService splitInit ensureInit identityIndex bounds mode first second runtime

/-- From the later game with the ideal registration to the first-touch split form (the later form of `PqxdhDeploymentIdealKeys.ideal_to_splitX`): C7, the represent step and the seed relocation, read through `splitView`. -/
theorem ideal_to_splitX_later (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap splitView <$> (laterWith setup codec route idealInit (idealReg setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime)
      (outcomeMap splitView <$> (laterWith setup codec route splitInit (idealSplitX setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime) := by
  have erased := (erase_ideal_later setup codec route checks t p ensureInit identityIndex bounds mode first second
    runtime).map (outcomeMap (X := Out) (A := A) (fun x : XState KemSK (IdealBk TableState) 2 =>
      ((x.base, x.backend.2, x.snap, x.log) :
        PqxdhDeploymentNative.State KemSK × (Alloc Coord 2 × IdealCore) × PqxdhDeploymentLater.Snap ×
          PqxdhDeploymentLaterServerSource.Log)))
  have represented := (represent_ideal_later setup codec route checks t p ensureInit identityIndex bounds mode first
    second runtime).map (outcomeMap (X := Out) (A := A)
      (fun x : XState KemSK ((PqxdhDeploymentSeedSplit.OutputSpec 2).QueryCache × (Alloc Coord 2 × IdealCore)) 2 =>
        splitView x))
  have moved := congrArg (fun work => outcomeMap (X := Out) (A := A)
    (fun x : XState KemSK SplitBk 2 => splitView x) <$> work)
    (seed_move_later setup codec route checks t p ensureInit identityIndex bounds mode first second runtime)
  simp only [Functor.map_map, PqxdhDeploymentIdealKeys.outcomeMap_comp] at erased represented moved
  refine (LawEq.of_eq ?_).trans (erased.trans ((LawEq.of_eq ?_).trans (represented.trans (LawEq.of_eq ?_))))
  · rfl
  · rfl
  · rw [← moved]
    congr 1

/-- From the later game with the ideal registration to the eager split form (the later form of `PqxdhDeploymentIdealKernel.ideal_to_splitEager`): `ideal_to_splitX_later` with the kernel identities `PqxdhDeploymentIdealKernel.split_kernel`, read through `splitView`. -/
theorem ideal_to_splitEager_later (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap splitView <$> (laterWith setup codec route idealInit (idealReg setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime)
      (outcomeMap splitView <$> (laterWith setup codec route splitInit (idealSplitEager setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime) := by
  have kernel : idealSplitX setup codec route checks t p = idealSplitEager setup codec route checks t p := by
    funext created query
    exact PqxdhDeploymentIdealKernel.split_kernel setup codec route checks t p created query
  rw [← kernel]
  exact ideal_to_splitX_later setup codec route checks t p ensureInit identityIndex bounds mode first second runtime

/-- The seed deferral of the ideal registration in the later game with the real post phase (the later form of `PqxdhDeploymentIdealDefer.split_game`): the eager split form and the final split form, whose seeds are drawn at the hidden installs only, have the same law once the seed table is emptied. `PqxdhDeploymentIdealLater.defer_seeds_later` at CE-11b's pair `splitSeeds`; the real post phase commutes with seed completions (`realPost_commutes_seed`). -/
theorem split_later (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap seedFree <$> (laterWith setup codec route splitInit (idealSplitEager setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime)
      (outcomeMap seedFree <$> (laterWith setup codec route splitInit (idealSplit setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime) := by
  have erased : (fun created => (PqxdhDeploymentIdealDefer.splitSeeds setup codec route checks t p created).erased) =
      idealSplit setup codec route checks t p :=
    funext fun created => PqxdhDeploymentIdealDefer.splitSeeds_erased setup codec route checks t p created
  rw [← erased]
  exact PqxdhDeploymentIdealLater.defer_seeds_later setup codec route PqxdhDeploymentIdealDefer.InvX
    (fun created => PqxdhDeploymentIdealDefer.splitSeeds setup codec route checks t p created) splitInit
    PqxdhDeploymentIdealDefer.initial_invX
    (fun created query notEnv x holds => PqxdhDeploymentIdealDefer.fixed_invX setup codec route _ query notEnv x holds)
    (realPost setup codec checks) (fun created query => PqxdhDeploymentSeedSplit.realPost_commutes_seed setup codec
      checks created query) ensureInit identityIndex bounds mode first second runtime

/-- The later game with the ideal registration and the later game with its final split form (the later form of `PqxdhDeploymentIdealDefer.ideal_to_split`), both with the real post phase, have the same law up to the split view (the deployment state with the CTX cache emptied, the allocator and the ideal backend, the LQ-F snapshot and the log). -/
theorem ideal_to_split_later (t : Target count) (p : Params KemSK count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    LawEq (outcomeMap splitView <$> (laterWith setup codec route idealInit (idealReg setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime)
      (outcomeMap splitView <$> (laterWith setup codec route splitInit (idealSplit setup codec route checks t p)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime) := by
  have view : (outcomeMap (X := Out) (A := A) splitView :
      _ → Option (_ × Out × _ × _) × A) = outcomeMap splitView ∘ outcomeMap (X := Out) (A := A)
        (seedFree (KemSK := KemSK) (Bk := SplitBk) (n := 2)) := by
    funext outcome
    rw [Function.comp_apply, PqxdhDeploymentIdealKeys.outcomeMap_comp]
    rfl
  refine (ideal_to_splitEager_later setup codec route checks t p ensureInit identityIndex bounds mode first second
    runtime).trans ?_
  rw [view, comp_map, comp_map]
  exact (split_later setup codec route checks t p ensureInit identityIndex bounds mode first second runtime).map _

end Chain

/-! ### The post phase of the final split form -/

section Post
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- The HMAC command of the final split form is the native HMAC on the deployment state with the rest of the extended state kept: it is the logged real HMAC `realRegAt` in front of the lazy material service, which it does not touch (`PqxdhDeploymentIdealLaterGame.realRegAt_hmac`). -/
theorem idealSplit_hmac (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (x : XState KemSK SplitBk 2) :
    (idealSplit setup codec route checks t p created ⟨.hmac key message, trivial⟩).run x =
      (fun r => (r.1, { x with base := r.2 })) <$>
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.hmac key message))).run x.base := by
  change (fun r => (r.1.1, PqxdhDeploymentIdealKeys.attachX r.1.2 r.2.1 r.2.2)) <$>
    (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (PqxdhDeploymentIdealKernel.lazyDummy (n := 2)))
      (PqxdhDeploymentIdealSteps.liftS ((realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩).run
        (PqxdhDeploymentIdealKeys.detachX x)))).run (x.backend.2.1, (x.backend.1, x.seeds)) = _
  rw [PqxdhDeploymentIdealCut.slotImpl_lift, Functor.map_map, PqxdhDeploymentIdealLaterGame.realRegAt_hmac,
    Functor.map_map]
  rfl

/-- The post phase of the native game with the final split form is the real post phase. -/
theorem postNative_split (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    postNative setup codec route (idealSplit setup codec route checks t p created) =
      realPost setup codec checks created :=
  PqxdhDeploymentIdealLaterGame.postNative_real setup codec route checks created _ fun key message x =>
    idealSplit_hmac setup codec route checks t p created key message x

end Post

/-! ### C6 for the ideal environment of a target -/

section Environments
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- C6 for the ideal environment at the full reassembled state (the later form of `PqxdhDeploymentIdealEnv.c1_split`; `PqxdhDeploymentIdealLater.join_later_param` with `PqxdhDeploymentIdealEnv.ideal_splits`): the draw of the challenger's parameters followed by the later game with the final split form at them and the real post phase (the parameters added to the final backend) and the later record world with `envGD` and the environment's reveal have the same law of the Server's public data, the second adversary's output, the run-phase ledger and the full reassembled final state. The real post phase is the post phase of the native game with the final split form (`postNative_split`). -/
theorem c6_split (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    LawEq (drawParams setup count >>= fun p => (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        withX p value.2.2.2)) <$>
        (laterWith setup codec route splitInit (idealSplit setup codec route checks t p) (realPost setup codec checks)
          ensureInit identityIndex bounds mode first second).run' runtime)
      (joined <$> PqxdhRecordLiftLater.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
        setup.serverKeyId bounds mode envReveal first second) := by
  have joinedLater := PqxdhDeploymentIdealLater.join_later_param setup codec route (drawParams setup count) splitInit
    (fun p => idealSplit setup codec route checks t p) (idealStep setup codec checks t) ensureInit identityIndex runtime
    (fun _ => IdealInv t) (fun _ => PqxdhDeploymentIdealEnv.idealInv_stable t)
    (fun _ created => PqxdhDeploymentIdealEnv.idealInv_start t created)
    (fun p created => PqxdhDeploymentIdealEnv.ideal_splits setup codec route checks t p created) bounds mode first second
  refine (LawEq.of_eq ?_).trans joinedLater
  refine bind_congr fun p => ?_
  rw [PqxdhDeploymentIdealLaterGame.laterWith_postNative setup codec route splitInit _ (realPost setup codec checks)
    (fun created => postNative setup codec route (idealSplit setup codec route checks t p created))
    (fun created query x => by rw [postNative_split setup codec route checks t p created])]

/-- C6 for the later ideal game (the later form of `PqxdhDeploymentIdealEnv.c1_ideal`): the draw of the challenger's parameters followed by the later game with the ideal registration at them and the real post phase, and the later record world with `envGD` and the environment's reveal, have the same law of the second adversary's output, the run-phase ledger and the produced frames (the observed projection), through `ideal_to_split_later` pointwise under the draw and `c6_split`. -/
theorem c6_ideal (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    LawEq (drawParams setup count >>= fun p => (fun outcome => outcome.map fun value =>
        (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (laterWith setup codec route idealInit (idealReg setup codec route checks t p) (realPost setup codec checks)
          ensureInit identityIndex bounds mode first second).run' runtime)
      ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (joined <$> PqxdhRecordLiftLater.run setup codec route
          (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode envReveal first
            second)) := by
  have pointwise : ∀ p : Params KemSK count,
      LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
          (laterWith setup codec route idealInit (idealReg setup codec route checks t p) (realPost setup codec checks)
            ensureInit identityIndex bounds mode first second).run' runtime)
        ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
          (laterWith setup codec route splitInit (idealSplit setup codec route checks t p) (realPost setup codec checks)
            ensureInit identityIndex bounds mode first second).run' runtime) := by
    intro p
    have viewed := (ideal_to_split_later setup codec route checks t p ensureInit identityIndex bounds mode first second
      runtime).map (fun outcome => outcome.1.map fun value => (value.2.1, value.2.2.1, value.2.2.2.1.produced))
    simp only [Functor.map_map, StateT.run'_eq] at viewed ⊢
    refine (LawEq.of_eq ?_).trans (viewed.trans (LawEq.of_eq ?_))
    · congr 1
      funext a
      rcases a with ⟨_ | v, after⟩ <;> rfl
    · congr 1
      funext a
      rcases a with ⟨_ | v, after⟩ <;> rfl
  have joinedLaw := (c6_split setup codec route checks t ensureInit identityIndex runtime bounds mode first second).map
    (fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced))
  rw [map_bind] at joinedLaw
  simp only [Functor.map_map] at joinedLaw
  refine (LawEq.bind (LawEq.refl _) pointwise).trans ?_
  simp only [Functor.map_map]
  refine (LawEq.of_eq ?_).trans joinedLaw
  refine bind_congr fun p => ?_
  congr 1
  funext outcome
  rcases outcome with _ | value <;> rfl

/-- C6 for the later ideal game at the public projection (the later ideal form of `PqxdhDeploymentEnvironmentJoin.join_later_public`): the draw of the challenger's parameters followed by the later game with the ideal registration at them and the real post phase, and the later record world with `envGD` and the environment's reveal, have the same law of the Server's public data, the second adversary's output, the run-phase ledger, the record view (produced frames and raw-attempt counters) and the Beacon-side reveal with the Server ephemeral log of the final state. -/
theorem c6_ideal_public (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    LawEq (drawParams setup count >>= fun p => (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
        (value.2.2.2.base.produced,
          (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
        (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log))) <$>
        (laterWith setup codec route idealInit (idealReg setup codec route checks t p) (realPost setup codec checks)
          ensureInit identityIndex bounds mode first second).run' runtime)
      ((fun result => result.1.map fun value => (value.1, value.2.1.1, value.2.1.2,
          PqxdhRecordLiftLater.recordView result.2,
          (PqxdhDeploymentLater.revealOf value.2.2.native.owners value.2.2.snap, value.2.2.log))) <$>
        PqxdhRecordLiftLater.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode envReveal first second) := by
  have pointwise : ∀ p : Params KemSK count,
      LawEq ((fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
          (value.2.2.2.base.produced,
            (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
          (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log))) <$>
          (laterWith setup codec route idealInit (idealReg setup codec route checks t p) (realPost setup codec checks)
            ensureInit identityIndex bounds mode first second).run' runtime)
        ((fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
          (value.2.2.2.base.produced,
            (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
          (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log))) <$>
          (laterWith setup codec route splitInit (idealSplit setup codec route checks t p) (realPost setup codec checks)
            ensureInit identityIndex bounds mode first second).run' runtime) := by
    intro p
    have viewed := (ideal_to_split_later setup codec route checks t p ensureInit identityIndex bounds mode first second
      runtime).map (fun outcome => outcome.1.map fun value => (value.1, value.2.1, value.2.2.1,
        (value.2.2.2.1.produced,
          (⟨value.2.2.2.1.serverRaw, value.2.2.2.1.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
        (PqxdhDeploymentLater.revealOf value.2.2.2.1.native.owners value.2.2.2.2.2.1, value.2.2.2.2.2.2)))
    simp only [Functor.map_map, StateT.run'_eq] at viewed ⊢
    refine (LawEq.of_eq ?_).trans (viewed.trans (LawEq.of_eq ?_))
    · congr 1
      funext a
      rcases a with ⟨_ | v, after⟩ <;> rfl
    · congr 1
      funext a
      rcases a with ⟨_ | v, after⟩ <;> rfl
  have joinedLaw := (c6_split setup codec route checks t ensureInit identityIndex runtime bounds mode first second).map
    (fun outcome => outcome.map fun value => (value.1, value.2.1, value.2.2.1,
      (value.2.2.2.base.produced,
        (⟨value.2.2.2.base.serverRaw, value.2.2.2.base.ownerRaw⟩ : PqxdhRecordLiftWorld.RawCounters)),
      (PqxdhDeploymentLater.revealOf value.2.2.2.base.native.owners value.2.2.2.snap, value.2.2.2.log)))
  rw [map_bind, Functor.map_map] at joinedLaw
  simp only [Functor.map_map] at joinedLaw
  refine (LawEq.bind (LawEq.refl _) pointwise).trans ?_
  refine (LawEq.of_eq ?_).trans (joinedLaw.trans (LawEq.of_eq ?_))
  · refine bind_congr fun p => ?_
    congr 1
    funext outcome
    rcases outcome with _ | value <;> rfl
  · congr 1
    funext result
    rcases result with ⟨_ | value, w⟩
    · rfl
    · simp only [joined, Option.map_some, Option.some.injEq]
      rw [show (PqxdhDeploymentEnvironmentJoin.merge value.2.2 w).base.native.owners =
        (PqxdhDeploymentEnvironmentJoin.fill w value.2.2.native).owners from rfl,
        PqxdhDeploymentEnvironmentJoin.revealOf_fill]
      rfl

/-- C6 for the later ideal game `IL_g` itself (`PqxdhDeploymentIdealLaterGame.idealLaterGame`, its draw included; the later form of `PqxdhDeploymentIdealEnv.c1_idealGame`) at the observed projection: it has the law of the later record world with `envGD` at the target of `g` and the environment's reveal. -/
theorem c6_idealGame (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    LawEq ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run' runtime)
      ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (joined <$> PqxdhRecordLiftLater.run setup codec route
          (envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId bounds mode envReveal
            first second)) := by
  refine (LawEq.of_eq ?_).trans (c6_ideal setup codec route checks (Target.ofCE budget g) ensureInit 0 runtime bounds
    mode first second)
  simp only [PqxdhDeploymentIdealLaterGame.idealLaterGame, StateT.run'_eq, StateT.run, map_bind, Functor.map_map]

/-- The decision of the later second compile lemma on an outcome of the later game (`PqxdhDeploymentIdealLaterGame.ceDecideL`: the LQ-F event happens and the claim designates `g`, on the LQ-F outcome `laterOf`) is the hand-off decision `PqxdhDeploymentIdealHandoff.decisionOn` on the outcome's observed projection (the post-run output, the run-phase ledger and the produced frames), false when no Server was constructed (the later form of `PqxdhDeploymentIdealHandoff.ceDecide_observed`). -/
theorem ceDecideL_observed {Bk : Type} {n : ℕ} (budget : Budget) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK Bk n) × A) :
    PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim g outcome =
      (outcome.1.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)).any
        (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget event claim g) := by
  rcases outcome with ⟨_ | value, after⟩
  · simp [PqxdhDeploymentIdealLaterGame.ceDecideL, PqxdhDeploymentLaterServerTransfer.happens,
      PqxdhDeploymentIdealLaterGame.laterOf, PqxdhDeploymentLaterServerTransfer.observeGame]
  · simp only [PqxdhDeploymentIdealLaterGame.ceDecideL, PqxdhDeploymentLaterServerTransfer.happens,
      PqxdhDeploymentLaterServerTransfer.designated, PqxdhDeploymentIdealLaterGame.laterOf,
      PqxdhDeploymentLaterServerTransfer.observeGame, Option.map_some, Option.any_some, Option.bind_some,
      PqxdhDeploymentIdealHandoff.decisionOn]
    cases happened : event (value.2.1, value.2.2.1, value.2.2.2.base.produced) <;>
      simp [happened, PqxdhDeploymentBackend.laterView]

/-- The later ideal game `IL_g` and the later record world with `envGD` at the target of `g` and the environment's reveal give the decision of the later second compile lemma the same probability (`c6_idealGame`, `ceDecideL_observed`): the right-hand side of `PqxdhDeploymentIdealLaterGame.IdealCompileServerTarget` is the probability of the hand-off decision on the later record world's observation. -/
theorem c6_idealGame_decide (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) :
    𝒟[PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim g <$>
        (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
          second).run runtime] {true} =
      𝒟[(fun result => (PqxdhRecordLiftWorld.observed result).any
          (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftLater.run setup codec route
          (envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId bounds mode envReveal
            first second] {true} := by
  have left : PqxdhDeploymentIdealLaterGame.ceDecideL setup codec budget event claim g <$>
      (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
        second).run runtime =
      (fun observed => observed.any (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget event claim g)) <$>
        ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
          (PqxdhDeploymentIdealLaterGame.idealLaterGame setup codec route checks budget g ensureInit bounds mode first
            second).run' runtime) := by
    rw [StateT.run'_eq, Functor.map_map, Functor.map_map]
    congr 1
    funext outcome
    exact ceDecideL_observed setup codec budget event claim g outcome
  have right : (fun observed => observed.any (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget event claim g)) <$>
      ((fun outcome => outcome.map fun value => (value.2.1, value.2.2.1, value.2.2.2.base.produced)) <$>
        (joined <$> PqxdhRecordLiftLater.run setup codec route
          (envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId bounds mode envReveal
            first second)) =
      (fun result => (PqxdhRecordLiftWorld.observed result).any
          (PqxdhDeploymentIdealHandoff.decisionOn setup codec budget event claim g)) <$>
        PqxdhRecordLiftLater.run setup codec route
          (envGD setup codec checks (Target.ofCE budget g) ensureInit 0 runtime) setup.serverKeyId bounds mode envReveal
            first second := by
    simp only [Functor.map_map]
    congr 1
    funext result
    rcases result with ⟨_ | value, state⟩ <;> rfl
  rw [left, ← right]
  exact congrArg (fun measure => measure {true})
    ((c6_idealGame setup codec route checks budget g ensureInit runtime bounds mode first second).map _).evalDist_eq

end Environments

/-! ### The reveal constraint of U-L3 -/

/-- U-L3's reveal constraint (LQ-F design-v2 F16): the environment's reveal does not read the backend (the hidden-slot material) or the shared native state (the HMAC cache, hence the R1 slice of item 2). -/
theorem envReveal_blind {Bk : Type} (e : PqxdhDeploymentEnvironment.EnvState KemSK Bk) (b : Bk)
    (shared : PqxdhServerAuthNative.NativeState KemSK) :
    envReveal { e with backend := b, native := { e.native with shared := shared } } = envReveal e := rfl

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.erase_ideal_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.erase_ideal_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.represent_ideal_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.represent_ideal_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.seed_move_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.seed_move_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ideal_to_splitX_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ideal_to_splitX_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ideal_to_splitEager_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ideal_to_splitEager_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.split_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.split_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ideal_to_split_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ideal_to_split_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.idealSplit_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.idealSplit_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.postNative_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.postNative_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_ideal_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_ideal_public

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_idealGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_idealGame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ceDecideL_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.ceDecideL_observed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_idealGame_decide' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.c6_idealGame_decide

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.envReveal_blind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterEnv.envReveal_blind

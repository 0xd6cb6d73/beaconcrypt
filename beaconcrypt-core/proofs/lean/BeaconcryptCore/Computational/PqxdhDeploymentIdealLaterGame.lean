-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemTargets
import BeaconcryptCore.Computational.PqxdhDeploymentIdealCut
import BeaconcryptCore.Computational.PqxdhDeploymentEnvironmentJoin

/-! LQ-F upstream, unit D2: the later ideal game `IL_g` and the frozen target of the later second compile lemma (U-L2). CE-11b's ideal game `PqxdhDeploymentIdealSteps.idealGame` runs the common deployment experiment with the ideal registration at the target of `g`; its later counterpart runs the LQ-F later game with a pluggable registration and post phase (`PqxdhDeploymentFinishErasure.laterWith`) with the same ideal registration, the same drawn parameters and the real post phase (`idealLaterGame`, LQ-F upstream design-v2 D5; not CE-11b's design-v2). This module fixes the game, the projection to the LQ-F outcome and the decision, and states the target `IdealCompileServerTarget` for the later units to prove; it also gives the bridges that unit C needs to compose the later game with the record lift.

- `idealLaterGame`: the challenger's draws for the budget's KEM creations, then `laterWith` with the initial ideal backend, the ideal registration at `Target.ofCE budget g`, the real post phase `realPost` (fresh coins, the native HMAC and BLAKE2b on the final deployment state), identity index 0. `laterOf` is the projection of a later-game outcome to an outcome of the LQ-F game (the projection of `laterWith_real`: the snapshot, the deployment state and the log), and `laterOf_real` restates `laterWith_real` with it. `ceDecideL` is the decision of the later second compile lemma: the LQ-F event happens and the claim designates `g`, on `laterOf`.
- `laterWith_split`: per constructed Server, the later game is the run of `gameWith`'s handler followed by the post phase `laterTail` with the identity projection; the form in which the run-phase arguments of CE-11b apply to the later game.
- The post phase of the ideal registration is the real post phase. `realRegAt_hmac`: the HMAC step of the logged real handler `realRegAt` is the native HMAC on the deployment state with the snapshot and the log unchanged (`PqxdhDeploymentLaterServerGame.handler_quiet`; a non-finish command leaves the snapshot alone). `postNative_real`: for every registration handler that answers HMAC in that way, the post phase of the native game with that handler (`PqxdhDeploymentEnvironmentJoin.postNative`, the run-phase handler on the post commands) is `realPost`; coins and BLAKE2b are the fixed steps of the handler, which agree with `realPost` by definition. It is the generic form of `PqxdhDeploymentEnvironmentReal.postNative_real`, the case of the real registration `realReg`; a consumer that opens both namespaces names them qualified. `idealReg_hmac` and `postNative_ideal`: the ideal registration answers HMAC as `realRegAt` (`PqxdhDeploymentIdealSteps.idealProg_real`, `PqxdhDeploymentIdealCut.slotCore_lift`), so its `postNative` is `realPost`. `laterWith_postNative` is the congruence of the later game in the post handler, and `idealLater_postNative` writes `idealLaterGame` in the `postNative` form that `PqxdhDeploymentEnvironmentJoin.join_later` takes.
- The target `IdealCompileServerTarget` (LQ-F design-v2 unit B2, `PqxdhDeploymentIdealLaterCompile.ideal_compile_server`): under the codec contracts `Phase1ReadBack` and `Phase2ReadBack` and for a run-phase adversary within its budget and every post-run adversary, the logged two-slot world of the compiled LQ-F program at the per-target decision accepts with the probability that the later ideal game ends with the event and the designation `g`. It is the later form of `PqxdhDeploymentIdealCompile.ideal_compile`. It takes no post budget (LQ-F design-v2 section 4.7): the post part forwards only coin, HMAC and BLAKE2b commands (`PqxdhDeploymentLaterCompile.postCore`), which read no field (their field costs `PqxdhDeploymentCompileBudget.cost (.inr _) (postCore _)` are zero, the fact behind `PqxdhDeploymentLaterCompile.compile_later_reads` and, for the KEM field, the proof of `PqxdhDeploymentLaterServerCompileBudget.compile_server_no_kem`), and the compiled program makes no KEM read (`compile_server_no_kem`). Without a post budget the logged scan, which contains the whole post part when the selected accept is never reached, has no finite coin, HMAC or BLAKE2b cap, and at LQ-F the identity-read cap is `qCreate`, not 0. The proof therefore cannot reuse the classical cut lemmas that take a `certified` bound in all fourteen source kinds together with `unreadIdentity` (`PqxdhDeploymentIdealBranch.slotGameAt_cut`, `PqxdhDeploymentIdealCut.item2_prefix`, `PqxdhDeploymentIdealPoolSource.kemCommands_stopped`); it uses per-kind step bounds, as the LQ-F chain does (`PqxdhDeploymentLaterServerReserve.creations`, `PqxdhDeploymentLaterServerCompileBudget.compile_server_creates`, `compile_server_no_kem`).

These are definitions, a target statement and program equalities; no assumption, contract or premise is added. LQ-F claims confidentiality only. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentBackend (XState RegImpl handlerWith xinitial)
open PqxdhDeploymentFinishErasure (laterWith laterTail realPost)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec Handle asModeO)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentKemTransfer (Observed selectedKem)
open PqxdhDeploymentLater (PostSpec)
open PqxdhDeploymentIdealSteps (IdealBk TableState idealReg idealInit realRegAt idealProg)
open PqxdhDeploymentEnvironmentJoin (postNative)
open PqxdhDeploymentLaterServerItemTargets (laterSlotGame)

/-! ### The later game, per constructed Server -/

section Split
variable {KemSK Bk : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The later game per constructed Server: the run of `gameWith`'s handler from the initial extended state, followed by the post phase `laterTail` with the identity projection. -/
theorem laterWith_split (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n)
    (postWith : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    (laterWith setup codec route init reg postWith ensureInit identityIndex bounds mode first second).run runtime =
      (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime >>=
        fun born => match born.1 with
        | none => pure (none, born.2)
        | some created =>
          (simulateQ (handlerWith setup codec route (reg created))
              (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode first))).run
              (xinitial created (init created)) >>=
            laterTail postWith created second id born.2 := by
  simp only [laterWith, StateT.run]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · rfl
  · simp only [map_bind, map_pure]
    rfl

/-- The later game is unchanged when its post handler is replaced by one with the same steps. -/
theorem laterWith_postNative (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (reg : PqxdhLiveServerConstruction.Created Unit → RegImpl KemSK Bk n)
    (postWith postWith' : PqxdhLiveServerConstruction.Created Unit →
      QueryImpl PostSpec (StateT (XState KemSK Bk n) ProbComp))
    (same : ∀ created query x, (postWith created query).run x = (postWith' created query).run x)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    laterWith setup codec route init reg postWith ensureInit identityIndex bounds mode first second =
      laterWith setup codec route init reg postWith' ensureInit identityIndex bounds mode first second := by
  have handlers : postWith = postWith' :=
    funext fun created => funext fun query => StateT.ext fun x => same created query x
  rw [handlers]

end Split

/-! ### The post phase of the ideal registration -/

section Post
variable {KemSK : Type} {n : ℕ}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The HMAC step of `realRegAt` is the native HMAC on the deployment state with the snapshot and the log unchanged (`handler_quiet` for the log; a non-finish command leaves the snapshot alone). -/
theorem realRegAt_hmac {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (x : XState KemSK Bk n) :
    (realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩).run x =
      (fun r => (r.1, { x with base := r.2 })) <$>
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.hmac key message))).run x.base := by
  change (fun result => (result.1, { x with base := result.2.1, log := result.2.2, snap := x.snap })) <$>
      (PqxdhDeploymentLaterServerGame.handler setup codec checks route created.seed (.inr (.hmac key message))).run
        (x.base, x.log) = _
  rw [PqxdhDeploymentLaterServerGame.handler_quiet setup codec checks route created.seed _ (fun _ same => by cases same),
    Functor.map_map]

/-- The post phase of the native game with a registration handler that answers HMAC as the native HMAC on the deployment state, with the rest of the extended state kept, is the real post phase: coins and BLAKE2b are fixed steps of the handler and agree with `realPost` by definition. This is the generic form of `PqxdhDeploymentEnvironmentReal.postNative_real` (the real registration `realReg`), which has the same short name. -/
theorem postNative_real {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (reg : RegImpl KemSK Bk n)
    (hmac : ∀ key message (x : XState KemSK Bk n), (reg ⟨.hmac key message, trivial⟩).run x =
      (fun r => (r.1, { x with base := r.2 })) <$>
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.hmac key message))).run x.base) :
    postNative setup codec route reg = realPost setup codec checks created := by
  funext query
  apply StateT.ext
  intro x
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [postNative, QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    rfl
  · simp only [postNative, QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    exact hmac key message x
  · simp only [postNative, QueryImpl.apply_compose, PqxdhDeploymentLater.postEmbed, simulateQ_spec_query]
    rfl

variable {count : ℕ}

/-- The ideal registration answers HMAC as `realRegAt`, hence as the native HMAC on the deployment state with the rest of the extended state kept (`idealProg_real`, `slotCore_lift`, `realRegAt_hmac`). -/
theorem idealReg_hmac (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (x : XState KemSK (IdealBk TableState) 2) :
    (idealReg setup codec route checks t p created ⟨.hmac key message, trivial⟩).run x =
      (fun r => (r.1, { x with base := r.2 })) <$>
        (PqxdhDeploymentNative.handler setup codec checks route created.seed (.inr (.hmac key message))).run x.base := by
  have run := PqxdhDeploymentIdealCut.slotCore_lift (idealProg setup codec route checks t p
    (PqxdhRegistrationJointKemEntryFactor.factoredHidden setup codec checks)) PqxdhDeploymentSeedSplit.tableService
    created ⟨.hmac key message, trivial⟩ x
    ((realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩).run
      (PqxdhDeploymentIdealSlots.detach x)) rfl
  change (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created _).run x = _ at run
  change (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created _).run x = _
  rw [run, realRegAt_hmac, Functor.map_map]
  rfl

/-- The post phase of the native game with the ideal registration is the real post phase. -/
theorem postNative_ideal (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) :
    postNative setup codec route (idealReg setup codec route checks t p created) =
      realPost setup codec checks created :=
  postNative_real setup codec route checks created _ fun key message x =>
    idealReg_hmac setup codec route checks t p created key message x

end Post

/-! ### The later ideal game, the projection and the decision -/

section Game
variable {KemSK : Type}
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X Out : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- `IL_g`: the challenger's draws for the budget's KEM creations, then the LQ-F later game with the ideal registration at the target of `g`, from the initial ideal backend, with identity index 0 and the real post phase. -/
noncomputable def idealLaterGame (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk TableState) 2)) :=
  fun runtime => do
    let p ← drawParams setup budget.create
    (laterWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p)
      (realPost setup codec checks) ensureInit 0 bounds mode first second).run runtime

/-- `IL_g` in the `postNative` form that `PqxdhDeploymentEnvironmentJoin.join_later` takes: the post phase of the native game with the ideal registration. -/
theorem idealLater_postNative (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) :
    idealLaterGame setup codec route checks budget g ensureInit bounds mode first second =
      (fun runtime => drawParams setup budget.create >>= fun p =>
        (laterWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p)
          (fun created => postNative setup codec route (idealReg setup codec route checks (Target.ofCE budget g) p
            created)) ensureInit 0 bounds mode first second).run runtime) := by
  funext runtime
  refine bind_congr fun p => ?_
  rw [laterWith_postNative setup codec route idealInit _ (realPost setup codec checks)
    (fun created => postNative setup codec route (idealReg setup codec route checks (Target.ofCE budget g) p created))
    (fun created query x => by rw [postNative_ideal setup codec route checks (Target.ofCE budget g) p created])]

/-- The LQ-F outcome of a later-game outcome: the Server's public data, the post-run output, and the ledger with the LQ-F view of the final state (snapshot, deployment state, log); the projection of `PqxdhDeploymentFinishErasure.laterWith_real`. -/
def laterOf {Bk : Type} {n : ℕ} (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
    PqxdhDeploymentSecrecy.Ledger × XState KemSK Bk n) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out ×
      PqxdhDeploymentLaterServerGame.LaterState KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1, (result.2.2.1, PqxdhDeploymentBackend.laterView result.2.2.2)),
    outcome.2)

/-- `laterWith_real` through `laterOf`: the later game with the real registration and the real post phase, projected, is the LQ-F game. -/
theorem laterOf_real (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (bounds : FreshBounds) (mode : Mode)
    (first : OracleComp (ModeSpec mode) X)
    (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (runtime : A) :
    laterOf <$> (laterWith setup codec route (fun _ => ()) (PqxdhDeploymentBackend.realReg setup codec route checks)
        (realPost setup codec checks) ensureInit identityIndex bounds mode first second).run runtime =
      (PqxdhDeploymentLaterServerGame.game setup codec checks route ensureInit identityIndex bounds mode first
        second).run runtime :=
  PqxdhDeploymentFinishErasure.laterWith_real setup codec route checks ensureInit identityIndex bounds mode first second
    runtime

/-- The decision of the later second compile lemma on a later-game outcome: the LQ-F event happens and the claim designates `g`, on the LQ-F outcome. -/
noncomputable def ceDecideL {Bk : Type} {n : ℕ} (budget : Budget) (event : Observed Out → Bool)
    (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
    (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × Out × PqxdhDeploymentSecrecy.Ledger ×
      XState KemSK Bk n) × A) : Bool :=
  decide (PqxdhDeploymentLaterServerTransfer.happens event (laterOf outcome) = true ∧
    PqxdhDeploymentLaterServerTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
      (laterOf outcome) = some g)

end Game

/-! ### The target of U-L2 -/

/-- Target of U-L2 (LQ-F design-v2 unit B2, `PqxdhDeploymentIdealLaterCompile.ideal_compile_server`), the later form of `PqxdhDeploymentIdealCompile.ideal_compile`: under `Phase1ReadBack` and `Phase2ReadBack`, for a run-phase adversary within its budget and every post-run adversary, the logged two-slot world of the compiled LQ-F program at the per-target decision accepts with the same probability as the later ideal game ends with the LQ-F event and the designation `g`. No post budget is taken (LQ-F design-v2 section 4.7): the post part forwards only coin, HMAC and BLAKE2b commands, which read no field, and the compiled program makes no KEM read (`PqxdhDeploymentLaterServerCompileBudget.compile_server_no_kem`). Unit B therefore proves it with per-kind step bounds, not with the classical cut lemmas' `certified` bound in all fourteen source kinds and `unreadIdentity` (module docstring). LQ-F claims confidentiality only. -/
def IdealCompileServerTarget : Prop :=
  ∀ {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (checks : Checks),
    PqxdhServerAuthNegativeControl.Phase1ReadBack codec → PqxdhServerAuthNegativeControl.Phase2ReadBack codec →
    ∀ (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode) (first : OracleComp (ModeSpec mode) X)
      (second : X → PqxdhDeploymentLaterServerGame.Reveal → OracleComp PostSpec Out) (budget : Budget),
    budget.Respects first →
    ∀ (event : Observed Out → Bool) (claim : Observed Out → Option Handle) (g : Fin budget.accept × Fin budget.capacity)
      (runtime : A),
    𝒟[laterSlotGame (Reader := Reader) setup codec checks ensureInit none
        (PqxdhDeploymentLaterServerTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentLaterServerCompile.compileServer setup codec route bounds mode first second) runtime
        budget.create (selectedKem budget g) g.1.val 2] {true} =
      𝒟[ceDecideL setup codec budget event claim g <$>
        (idealLaterGame setup codec route checks budget g ensureInit bounds mode first second).run runtime] {true}

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.laterWith_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.laterWith_split

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.laterWith_postNative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.laterWith_postNative

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.realRegAt_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.realRegAt_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.postNative_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.postNative_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.idealReg_hmac' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.idealReg_hmac

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.postNative_ideal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.postNative_ideal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.idealLater_postNative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.idealLater_postNative

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.laterOf_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterGame.laterOf_real

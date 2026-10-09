-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealBranch

/-!
# The selected accept at the cut (CE-11b, unit U6)

`PqxdhDeploymentIdealBranch` reduces the second compile lemma of CE-11b to its selected-key branch (`SelectedBranch`): an outcome of the common prefix whose CE cut is pending at raw bytes that verify to the selected PQ key. This module splits that branch at the selected accept's encapsulation. On both sides the native steps before encapsulation of the Server's seed come first; a rejection there accepts nothing on either side; and an ephemeral leads to the active branch (`ActiveBranch`), from which the selected-key branch, and with it the second compile lemma, follow (`selected_of_active`, `ideal_compile_of_active`).

- Item 2's side. The steps before encapsulation of item 2's stopped source (the source-suffix handler at the Server's identity slot, the actual encapsulator and the stopped selected-first router) issue no static DH request (`beforeLogged_plain`), so they run as coins through the router with its state kept (`stopped_coins`, `stopped_plain`, `stopped_program`) and are the native steps before encapsulation of any seed with the logged ephemeral scalar forgotten (`stopped_before`, from `PqxdhDeploymentLaterServerSource.beforeLogged_fst`). Hence the rest of item 2's opaque scan at such a cut is the native steps followed by a completed run or the active cut (`opaqueRest_selected`, with the compiled continuation `compiledNext`), and item 2's side is in law the native steps followed by nothing accepted or item 2's post-challenge phase on the active cut (`itemRest_selected`).
- The CE side. At the canonical state at the cut the selected raw accept is the selected step of the ideal registration (`selectedStep`) on `PqxdhDeploymentIdealSteps.acceptActive`, whose native steps before encapsulation pass through the first-touch allocator as coins (`acceptStep_selected`). On a rejection before encapsulation the accept is inactive and leaves no mark, and no later step changes the mark (`PqxdhDeploymentIdealKeymatch.run_settled`), so the decision together with the mark is false; on an ephemeral the CE side is `activeCE`, the selected accept from the steps after encapsulation (`acceptAfter`: item 2's candidate-free suffix with the challenge ciphertext and marker, then item 2's marker tail under `tailCE`) followed by the continuation of the deployment program (`resumeMarked_selected`).
- `ActiveBranch` is the remaining obligation of unit U6: for every outcome of the common prefix with the strengthened relation at the cut whose cut is pending at raw bytes that verify to the selected PQ key, and every outcome of the native steps before encapsulation that reaches the encapsulation, item 2's post-challenge phase on the active cut and `activeCE` have the same law. This module does not prove it.

Premises: the approved codec contracts `Phase1ReadBack` and `Phase2ReadBack` and the CE budget (through `PqxdhDeploymentIdealBranch`). These are program equalities and equalities in law. They charge nothing and make no security claim; `ideal_compile_of_active` is a reduction, not the second compile lemma.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealActive
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompile (Local merge compileImpl)
open PqxdhDeploymentIdealCut (CutCE scanCE finishCE cutState unghost commonPrefix)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X : Type}

/-! ### The steps before encapsulation under the stopped router -/

section Before
open PqxdhServerRootPreparation (Verified)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Whether a native preparation request is other than the static DH. -/
def plain : (PqxdhServerRootPreparation.Spec Reader PqxdhJointGapDh.ScalarBytes
    PqxdhBeaconPhase2Preparation.Word32).Domain → Bool
  | .staticDh _ => false
  | _ => true

/-- The stopped router passes coins through. -/
theorem stopped_coins (selected : ℕ) (pairs : List (PqxdhLiveKemReservation.Pair KemSK)) {α : Type} (work : ProbComp α)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (PqxdhLiveKemBirth.coins work)).run).run state = (fun reply => (some reply, state)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [PqxdhLiveKemBirth.coins, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, map_bind] at ih ⊢
      simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, StateT.run,
        bind_map_left]
      exact bind_congr fun reply => ih reply

/-- Every preparation request other than the static DH, compiled by item 2's source-suffix handler at any identity slot, interpreted by the actual encapsulator and run by the stopped router, is the native Server callback of any seed, and keeps the router state. -/
theorem stopped_plain (identityIndex : ℕ) (raw : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (selected : ℕ) (pairs : List (PqxdhLiveKemReservation.Pair KemSK))
    (query : (PqxdhServerRootPreparation.Spec Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32).Domain) (isPlain : plain query = true) (consumed : List Pqxdh.Bytes)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          ((PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw query).run
            consumed))).run).run state =
      (fun reply => (some reply, state)) <$>
        (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed query).run consumed := by
  have plainRun : ∀ (aux : (PqxdhRegistrationJointServerPrefix.AuxSpec Reader).Domain),
      (∀ key, aux ≠ .encapsulate key) →
      ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
          (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
            ((PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw (.inr aux)).run
              consumed))).run).run state =
        (fun reply => (some reply, state)) <$> (PqxdhServerAuthExperiment.serverAux setup codec checks aux).run consumed := by
    intro aux notEncapsulate
    have shape : (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw (.inr aux)).run consumed =
        simulateQ PqxdhRegistrationJointKemEncapsulation.forward
          (PqxdhLiveKemBirth.coins ((PqxdhServerAuthExperiment.serverAux setup codec checks aux).run consumed)) := by
      cases aux <;> first | rfl | exact absurd rfl (notEncapsulate _)
    rw [shape, PqxdhRegistrationJointKemEncapsulation.forward_actual, stopped_coins]
    rfl
  rcases query with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | key | _ | _ | _ | point
  case staticDh => cases isPlain
  case encapsulate =>
    simp only [PqxdhRegistrationJointKemSourceSuffix.handler, QueryImpl.apply_compose,
      PqxdhRegistrationJointServerPrefix.compiler, simulateQ_spec_query,
      PqxdhRegistrationJointKemEncapsulation.prefixImpl, StateT.run, simulateQ_map,
      PqxdhRegistrationJointKemEncapsulation.actual, PqxdhDeploymentIdealSteps.prefixNative,
      PqxdhServerStaticDhSource.nativeImpl, PqxdhServerAuthExperiment.serverAux, StateT.lift]
    rw [OptionT.run_map]
    change StateT.run (Option.map (fun answer => (answer, consumed)) <$>
      (simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (PqxdhLiveKemBirth.coins (PqxdhServerAuthExperiment.encapsulate setup key))).run) state = _
    rw [StateT.run_map, stopped_coins, Functor.map_map, bind_pure_comp, Functor.map_map]
    rfl
  all_goals simp only [PqxdhRegistrationJointKemSourceSuffix.handler, QueryImpl.apply_compose,
    PqxdhRegistrationJointServerPrefix.compiler, simulateQ_spec_query]
  all_goals exact plainRun _ (fun _ same => by cases same)

/-- A native preparation program without static DH requests, compiled by item 2's source-suffix handler at any identity slot, interpreted by the actual encapsulator and run by the stopped router, is the program under the native Server callbacks of any seed, and keeps the router state. -/
theorem stopped_program (identityIndex : ℕ) (raw : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (selected : ℕ) (pairs : List (PqxdhLiveKemReservation.Pair KemSK)) {α : Type}
    (work : OracleComp (PqxdhServerRootPreparation.Spec Reader PqxdhJointGapDh.ScalarBytes
      PqxdhBeaconPhase2Preparation.Word32) α)
    (plainOnly : work.IsQueryBoundP (fun query => plain query = false) 0) (consumed : List Pqxdh.Bytes)
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw) work).run
            consumed))).run).run state =
      (fun reply => (some reply, state)) <$>
        (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed) work).run consumed := by
  induction work using OracleComp.inductionOn generalizing consumed with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at plainOnly
      obtain ⟨allowed, rest⟩ := plainOnly
      have isPlain : plain query = true := by
        rcases allowed with free | impossible
        · simpa using free
        · omega
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, OptionT.run_bind, Option.elimM]
      rw [stopped_plain setup codec checks identityIndex raw seed selected pairs query isPlain consumed state,
        bind_map_left, map_bind]
      refine bind_congr fun reply => ?_
      have restBound := rest reply.1
      simp only [isPlain, Bool.true_eq_false, ite_false] at restBound
      exact ih reply.1 restBound reply.2

/-- The steps before encapsulation issue no static DH request. -/
theorem beforeLogged_plain (verified : Verified Reader) :
    (PqxdhDeploymentLaterServerSource.beforeLogged (E := PqxdhJointGapDh.ScalarBytes)
      (Shared := PqxdhBeaconPhase2Preparation.Word32) verified).IsQueryBoundP (fun query => plain query = false) 0 := by
  unfold PqxdhDeploymentLaterServerSource.beforeLogged
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp [plain]), fun status => ?_⟩
  cases status
  · rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (by simp [plain]), fun reserved => ?_⟩
    cases reserved
    · exact trivial
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (by simp [plain]), fun validPrekey => ?_⟩
      cases validPrekey
      · exact trivial
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [isQueryBoundP_query_bind_iff]
        refine ⟨Or.inl (by simp [plain]), fun validOneTime => ?_⟩
        cases validOneTime
        · exact trivial
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [isQueryBoundP_query_bind_iff]
          refine ⟨Or.inl (by simp [plain]), fun generated => ?_⟩
          cases generated
          · exact trivial
          · rw [isQueryBoundP_query_bind_iff]
            refine ⟨Or.inl (by simp [plain]), fun validKem => ?_⟩
            cases validKem
            · exact trivial
            · exact trivial
  · exact trivial

/-- The steps before encapsulation of the selected accept in item 2's stopped source: compiled by the source-suffix handler at any identity slot, interpreted by the actual encapsulator and run by the stopped router, they are the native steps before encapsulation of any seed with the logged ephemeral scalar forgotten, and keep the router state. -/
theorem stopped_before (identityIndex : ℕ) (raw : Pqxdh.Bytes) (seed : PqxdhJointIdentity.IdentitySeed)
    (selected : ℕ) (pairs : List (PqxdhLiveKemReservation.Pair KemSK)) (verified : Verified Reader)
    (consumed : List Pqxdh.Bytes) (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          ((simulateQ (PqxdhRegistrationJointKemSourceSuffix.handler setup codec checks identityIndex raw)
            (PqxdhRegistrationJointKemCollected.beforeEncapsulation verified)).run consumed))).run).run state =
      (fun pre => (some (pre.1.1, pre.2), state)) <$>
        (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) verified)).run
          consumed := by
  rw [← PqxdhDeploymentLaterServerSource.beforeLogged_fst, simulateQ_map, StateT.run_map, simulateQ_map, simulateQ_map,
    OptionT.run_map]
  rw [StateT.run_map, stopped_program setup codec checks identityIndex raw seed selected pairs _
    (beforeLogged_plain verified) consumed state, Functor.map_map]
  rfl

end Before

/-! ### Both sides at a selected-key cut -/

section Selected
open PqxdhServerRootPreparation (Verified)
open PqxdhDeploymentIdealParams (Target Params)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- The compiled continuation of a pending CE cut (`PqxdhDeploymentIdealCut.compileCut`). -/
noncomputable def compiledNext {Y : Type} (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec Y) (copies : Local) :
    Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (Y × Local) := fun answer =>
  (simulateQ (compileImpl setup codec route) (next answer)).run
    { copies with log := PqxdhDeploymentCompile.logReply copies.log (.accept raw) answer }

/-- The rest of item 2's opaque scan at a pending CE cut whose raw bytes verify, under the stopped router: the native steps before encapsulation of the Server's seed (any seed) with the logged scalar forgotten, then a rejection before encapsulation completes the run, and an ephemeral saves the active cut, with the router state kept. -/
theorem opaqueRest_selected {Y R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : (Y × Local) × PqxdhRegistrationJointAcceptCutTag.Tag → R) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp Spec Y) (copies : Local)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (shared : PqxdhServerAuthNative.NativeState KemSK)
    (value : Verified Reader) (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (seed : PqxdhJointIdentity.IdentitySeed) (selected : ℕ) (pairs : List (PqxdhLiveKemReservation.Pair KemSK))
    (state : PqxdhDynamicKemJointSource.State KemSK) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (PqxdhDeploymentIdealCut.opaqueRest setup codec checks identityIndex publicIdentity observe
          ((PqxdhDeploymentIdealCut.compileCut setup codec route (.pending raw next, copies), owners), shared))).run).run
        state =
      (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
            (PqxdhRegistrationJointKemRawOpaque.rejectRun setup codec checks identityIndex publicIdentity observe raw
              (compiledNext setup codec route raw next copies) owners shared (none, pre.2))).run).run state
        | some ephemeral => pure (some (.pending raw value ephemeral pre.2 shared owners
            (compiledNext setup codec route raw next copies)), state) := by
  simp only [PqxdhDeploymentIdealCut.opaqueRest, PqxdhDeploymentIdealCut.compileCut, verified]
  rw [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, stopped_before setup codec checks identityIndex
    raw seed selected pairs value shared.2.server.consumed state, bind_map_left]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · rfl
  · simp only [Option.elim, simulateQ_pure, OptionT.run_pure, StateT.run_pure]
    rfl

/-- Item 2's side at a pending CE cut whose raw bytes verify (in law): the native steps before encapsulation of any seed, then on a rejection before encapsulation nothing is accepted, and on an ephemeral item 2's post-challenge phase runs on the active cut with the router state of the cut. -/
theorem itemRest_selected {A Y : Type} (t : Target count) (p : Params KemSK count) (decision : Y × Local → Bool)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (after : A)
    (reached : (CutCE Y × Local) × PqxdhRegistrationJointSchedule.State KemSK) (raw : Pqxdh.Bytes)
    (next : Option ℕ → OracleComp Spec Y) (pending : reached.1.1 = .pending raw next) (value : Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (seed : PqxdhJointIdentity.IdentitySeed) :
    LazyOracleDiscard.LawEq
      (PqxdhDeploymentIdealBranch.itemRest (Reader := Reader) setup codec route checks t p decision created after reached)
      ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          reached.2.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => pure false
        | some ephemeral => PqxdhDeploymentIdealBranch.itemPost setup codec checks t p decision
            (.ready created p.others (some (.pending raw value ephemeral pre.2 reached.2.shared
              (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners
              (compiledNext setup codec route raw next reached.1.2)))
              (reached.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.pool.2) after)) := by
  rcases reached with ⟨⟨cut, copies⟩, source⟩
  simp only at pending
  subst pending
  unfold PqxdhDeploymentIdealBranch.itemRest
  rw [opaqueRest_selected setup codec route checks _ _ _ raw next copies _ _ value verified seed, bind_assoc]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre _ => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · refine (PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun result member => LazyOracleDiscard.LawEq.of_eq
      (PqxdhDeploymentIdealBranch.itemPost_dead setup codec checks t p decision created result.1 result.2 after ?_)).trans
      (LazyOracleDiscard.lawEq_drop _ _)
    intro raw' value' ephemeral' consumed' native' owners' next' found
    have produced := PqxdhDeploymentIdealBranch.optionRun_support _ _ _ result member _ found
    obtain ⟨outcome, impossible⟩ := PqxdhDeploymentIdealBranch.rejectRun_complete setup codec checks _ _ _ _ _ _ _ _ _
      produced
    cases impossible
  · simp only [pure_bind]
    exact LazyOracleDiscard.LawEq.refl _

/-- The selected accept's steps from the reached encapsulation, given the ephemeral, the consumed set and the logged scalar of the steps before it (the second branch of `PqxdhDeploymentIdealSteps.acceptActive`): item 2's candidate-free suffix with the challenge ciphertext and marker under the native callbacks, then item 2's marker tail under `tailCE`; the accept is active. -/
noncomputable def acceptAfter (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (value : Verified Reader) (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (logged : Option PqxdhJointGapDh.ScalarBytes) :
    StateT (PqxdhServerAuthNative.NativeState KemSK) (OracleComp PqxdhDeploymentIdealSlots.SlotSpec)
      PqxdhDeploymentIdealSteps.AcceptOut := fun s => do
  let prepared ← PqxdhDeploymentIdealSteps.liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
    (PqxdhRegistrationJointKemOpaqueSuffix.program (Shared := PqxdhBeaconPhase2Preparation.Word32) value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge)).run consumed)
  let answer ← (simulateQ (PqxdhDeploymentIdealSteps.tailCE setup.hmac s.2.sessions)
    (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared)).run
      (s, none)
  pure (((answer.1, logged), (true, answer.2.2)), answer.2.1)

/-- The selected raw accept of the ideal registration with a given native step for the accept (the first branch of `PqxdhDeploymentIdealSteps.acceptStep`): the accept counter advances, the session, the logged scalar, the activity flag and the mark are recorded. -/
noncomputable def selectedStep (step : StateT (PqxdhServerAuthNative.NativeState KemSK)
    (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) PqxdhDeploymentIdealSteps.AcceptOut) :
    StateT (PqxdhDeploymentBackend.XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2)
      (OracleComp PqxdhDeploymentIdealSlots.SlotSpec) (Option ℕ) := fun x =>
  let counted : PqxdhDeploymentBackend.XState KemSK PqxdhDeploymentIdealSteps.IdealCore 2 :=
    { x with backend := { x.backend with accepts := x.backend.accepts + 1 } }
  (fun r => (r.1.1.1, { counted with
      base := { counted.base with native := { counted.base.native with shared := r.2 } }
      log := counted.log ++ [r.1.1.2]
      backend := { counted.backend with active := r.1.2.1, marks := r.1.2.2 } })) <$> step.run x.base.native.shared

/-- The CE side of an active selected accept at the cut, from the steps after encapsulation: the selected accept with `acceptAfter` through the first-touch allocator of the canonical state at the cut, then the continuation of the deployment program with the ideal registration, read by a decision of the result, the deployment state and the mark. -/
noncomputable def activeCE {Y : Type} (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (decision : Y × PqxdhDeploymentNative.State KemSK × Bool → Bool) (base : PqxdhDeploymentNative.State KemSK)
    (next : Option ℕ → OracleComp Spec Y) (value : Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) : ProbComp Bool :=
  (fun outcome => decision (outcome.1, outcome.2.base, PqxdhDeploymentIdealBranch.marked outcome.2)) <$>
    ((fun r => (r.1.1, PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2)) <$>
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((selectedStep (acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed logged)).run
          (PqxdhDeploymentIdealSlots.detach (cutState t created base)))).run
        ((cutState t created base).backend.2.1, (cutState t created base).backend.1) >>= fun r =>
      (simulateQ (PqxdhDeploymentBackend.handlerWith setup codec route
        (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p created)) (next r.1)).run r.2)

/-- The selected accept at the canonical state at the cut, on raw bytes that verify to the selected PQ key: the native steps before encapsulation, then either the inactive accept tail or the steps after encapsulation (`acceptAfter`). -/
theorem acceptStep_selected (t : Target count) (p : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)
    (base : PqxdhDeploymentNative.State KemSK) (raw : Pqxdh.Bytes) (value : Verified Reader)
    (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (matched : value.keys.pqKey = p.chosen.1) :
    (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
        (PqxdhDeploymentIdealSlots.detach (cutState t created base)) =
      PqxdhDeploymentIdealSteps.liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          base.native.shared.2.server.consumed) >>= fun pre =>
        match pre.1.1 with
        | none => (selectedStep (fun s => do
            let r ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
              (setup.joint.publicKeys created.seed) s.2 (none, pre.2)).run s)
            pure (((r.1, pre.1.2), (false, none)), r.2))).run (PqxdhDeploymentIdealSlots.detach (cutState t created base))
        | some ephemeral => (selectedStep (acceptAfter setup codec checks created.seed p.challenge value ephemeral pre.2
            pre.1.2)).run (PqxdhDeploymentIdealSlots.detach (cutState t created base)) := by
  have selected : (PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
      (PqxdhDeploymentIdealSlots.detach (cutState t created base)) =
      (selectedStep (PqxdhDeploymentIdealSteps.acceptExposed setup codec checks created.seed p.chosen p.challenge raw)).run
        (PqxdhDeploymentIdealSlots.detach (cutState t created base)) := by
    have counter : (PqxdhDeploymentIdealSlots.detach (cutState t created base)).backend.accepts = t.accept := by
      simp [PqxdhDeploymentIdealSlots.detach, cutState, PqxdhDeploymentIdealCut.withAccepts]
    change (if (PqxdhDeploymentIdealSlots.detach (cutState t created base)).backend.accepts = t.accept then _ else _) = _
    simp only [counter, ↓reduceIte]
    rfl
  rw [selected]
  simp only [PqxdhDeploymentIdealSteps.acceptExposed, verified, matched, ↓reduceIte]
  change _ <$> (PqxdhDeploymentIdealSteps.liftS _ >>= _) = _
  rw [map_bind]
  refine bind_congr fun pre => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · rfl
  · rfl

/-- The CE side at a pending cut whose raw bytes verify to the selected PQ key (in law): the native steps before encapsulation of the Server's seed, then on a rejection before encapsulation nothing is accepted (the selected accept is inactive and leaves no mark, which no later step changes), and on an ephemeral the active form `activeCE`. -/
theorem resumeMarked_selected {Y : Type} (t : Target count) (p : Params KemSK count)
    (created : PqxdhLiveServerConstruction.Created Unit) (decision : Y × PqxdhDeploymentNative.State KemSK → Bool)
    (base : PqxdhDeploymentNative.State KemSK) (raw : Pqxdh.Bytes) (next : Option ℕ → OracleComp Spec Y)
    (value : Verified Reader) (verified : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value)
    (matched : value.keys.pqKey = p.chosen.1) :
    LazyOracleDiscard.LawEq
      (PqxdhDeploymentIdealBranch.resumeMarked setup codec route checks t p created
        (fun outcome => decision (outcome.1, outcome.2.1) && outcome.2.2) (.pending raw next) base)
      ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          base.native.shared.2.server.consumed >>= fun pre =>
        match pre.1.1 with
        | none => pure false
        | some ephemeral => activeCE setup codec route checks t p created
            (fun outcome => decision (outcome.1, outcome.2.1) && outcome.2.2) base next value ephemeral pre.2 pre.1.2) := by
  have accept : (PqxdhDeploymentBackend.handlerWith setup codec route
      (PqxdhDeploymentIdealSteps.idealReg setup codec route checks t p created) (.inr (.accept raw))).run
        (cutState t created base) =
      (simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
          (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
          base.native.shared.2.server.consumed >>= fun pre =>
        (fun r => (r.1.1, PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2)) <$>
          (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
            (match pre.1.1 with
            | none => (selectedStep (fun s => do
                let r ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
                  (setup.joint.publicKeys created.seed) s.2 (none, pre.2)).run s)
                pure (((r.1, pre.1.2), (false, none)), r.2))).run
                  (PqxdhDeploymentIdealSlots.detach (cutState t created base))
            | some ephemeral => (selectedStep (acceptAfter setup codec checks created.seed p.challenge value ephemeral
                pre.2 pre.1.2)).run (PqxdhDeploymentIdealSlots.detach (cutState t created base)))).run
            ((cutState t created base).backend.2.1, (cutState t created base).backend.1) := by
    change (PqxdhDeploymentIdealSlots.slotCore _ PqxdhDeploymentSeedSplit.tableService created
      ⟨.accept raw, trivial⟩).run (cutState t created base) = _
    rw [PqxdhDeploymentIdealSlots.slotCore_run]
    change (fun r => (r.1.1, PqxdhDeploymentIdealSlots.attach r.1.2 r.2.1 r.2.2)) <$>
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
        ((PqxdhDeploymentIdealSteps.acceptStep setup codec route checks t p created raw).run
          (PqxdhDeploymentIdealSlots.detach (cutState t created base)))).run
        ((cutState t created base).backend.2.1, (cutState t created base).backend.1) = _
    rw [acceptStep_selected setup codec route checks t p created base raw value verified matched, simulateQ_bind,
      StateT.run_bind, PqxdhDeploymentIdealCut.slotImpl_lift, bind_map_left, map_bind]
  unfold PqxdhDeploymentIdealBranch.resumeMarked
  simp only [finishCE, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [accept, bind_assoc, map_bind]
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre _ => ?_
  rcases pre with ⟨⟨_ | ephemeral, logged⟩, consumed⟩
  · change LazyOracleDiscard.LawEq _ (pure false)
    apply PqxdhDeploymentIdealBranch.map_const_lawEq
    intro outcome member
    rw [mem_support_bind_iff] at member
    obtain ⟨reached, reachedMember, member⟩ := member
    rw [support_map] at reachedMember
    obtain ⟨inner, innerMember, rfl⟩ := reachedMember
    have produced : inner.1 ∈ support ((selectedStep (fun s => do
        let r ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
          (setup.joint.publicKeys created.seed) s.2 (none, consumed)).run s)
        pure (((r.1, logged), (false, none)), r.2))).run
          (PqxdhDeploymentIdealSlots.detach (cutState t created base))) := by
      apply OracleComp.support_simulateQ_run'_subset
        (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
        ((cutState t created base).backend.2.1, (cutState t created base).backend.1)
      rw [StateT.run'_eq, support_map]
      exact ⟨inner, innerMember, rfl⟩
    unfold selectedStep at produced
    rw [StateT.run, support_map] at produced
    obtain ⟨result, resultMember, same⟩ := produced
    dsimp only [StateT.run] at resultMember
    rw [mem_support_bind_iff] at resultMember
    obtain ⟨_, _, resultMember⟩ := resultMember
    rw [support_pure, Set.mem_singleton_iff] at resultMember
    subst resultMember
    have marks : inner.1.2.backend.marks = none := by rw [← same]
    have accepts : inner.1.2.backend.accepts = t.accept + 1 := by
      rw [← same]
      simp [PqxdhDeploymentIdealSlots.detach, cutState, PqxdhDeploymentIdealCut.withAccepts]
    have settled := PqxdhDeploymentIdealKeymatch.run_settled setup codec route checks t p created (next inner.1.1)
      (PqxdhDeploymentIdealSlots.attach inner.1.2 inner.2.1 inner.2.2)
      (by change t.accept < inner.1.2.backend.accepts; rw [accepts]; exact Nat.lt_succ_self _) outcome member
    simp only [PqxdhDeploymentIdealBranch.marked, settled]
    change (decision _ && (inner.1.2.backend.marks).isSome) = false
    rw [marks]
    exact Bool.and_false _
  · simp only [bind_map_left]
    exact LazyOracleDiscard.LawEq.of_eq (by simp only [activeCE, bind_map_left])

end Selected

/-! ### The reduction of the selected-key branch to the active branch -/

section Reduction
open PqxdhServerRootPreparation (Verified)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentKemTransfer (Observed)
open PqxdhDeploymentCompileCaps (transported)
open LazyOracleDiscard (LawEq)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The active branch of the second compile lemma at the challenger's draws `p` (the obligation that the post-challenge simulation of unit U6 is to discharge, in `PqxdhDeploymentIdealPost`): for every constructed Server, every outcome of the common prefix with the strengthened relation at the cut whose CE cut is pending at raw bytes that verify to the selected PQ key, and every outcome of the native steps before encapsulation that reaches the encapsulation with an ephemeral, item 2's post-challenge phase on the active cut and the CE side from the steps after encapsulation (`activeCE`, with the decision together with the mark) have the same law. -/
def ActiveBranch {A : Type} (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (p : Params KemSK budget.create) : Prop :=
  ∀ (born : Option (PqxdhLiveServerConstruction.Created Unit) × PqxdhRegistrationJointServerPrefix.State KemSK A),
    born ∈ support ((PqxdhRegistrationJointServerBirth.source setup.joint ensureInit setup.serverKeyId none).run
      ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime)) →
    ∀ created, born.1 = some created →
    ∀ reached, reached ∈ support (commonPrefix setup codec route checks (Target.ofCE budget g) p created born.2.1
      (PqxdhDeploymentSecrecy.wrap setup.source.crypto codec setup.serverKeyId bounds (asModeO mode adversary))) →
    PqxdhDeploymentIdealBranch.CutRelIndexed setup codec route (Target.ofCE budget g) p created
      (transported bounds budget) reached →
    ∀ raw next, reached.1.1 = .pending raw next →
    ∀ value, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some value →
    value.keys.pqKey = p.chosen.1 →
    ∀ pre, pre ∈ support ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks created.seed)
      (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) value)).run
        reached.2.shared.2.server.consumed) →
    ∀ ephemeral, pre.1.1 = some ephemeral →
    LawEq (PqxdhDeploymentIdealBranch.itemPost setup codec checks (Target.ofCE budget g) p
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (.ready (PqxdhRegistrationJointServerBirth.encode created) p.others
          (some (.pending raw value ephemeral pre.2 reached.2.shared
            (PqxdhRegistrationJointGeneratedFinish.encodeState setup reached.2).owners
            (compiledNext setup codec route raw next reached.1.2)))
          (reached.2.pool.1, PqxdhDeploymentIdealPoolSource.routerOf reached.2.pool.2) born.2.2))
      (activeCE setup codec route checks (Target.ofCE budget g) p created
        (fun outcome => PqxdhDeploymentIdealBranch.markedDecision setup codec budget event claim g
          (some (PqxdhRegistrationJointServerBirth.encode created, outcome.1, outcome.2.1, outcome.2.2)))
        (merge reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)) next value ephemeral pre.2 pre.1.2)

/-- The selected-key branch (`PqxdhDeploymentIdealBranch.SelectedBranch`) from the active branch: on both sides the native steps before encapsulation of the Server's seed come first (`itemRest_selected`, from `stopped_before`; `resumeMarked_selected`), a rejection before encapsulation accepts nothing on both sides, and an ephemeral leads to the active branch. -/
theorem selected_of_active {A : Type} (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (budget : Budget) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A) (p : Params KemSK budget.create)
    (active : ActiveBranch (Reader := Reader) setup codec route checks ensureInit bounds mode adversary budget event claim
      g runtime p) :
    PqxdhDeploymentIdealBranch.SelectedBranch (Reader := Reader) setup codec route checks ensureInit bounds mode adversary
      budget event claim g runtime p := by
  intro born bornMember created constructed reached reachedMember related raw next pending value verified matched
  rw [pending]
  refine (itemRest_selected setup codec route checks (Target.ofCE budget g) p _ _ born.2.2 reached raw next pending value
    verified created.seed).trans (LawEq.trans ?_ (resumeMarked_selected setup codec route checks (Target.ofCE budget g) p
      created (fun outcome : (X × PqxdhDeploymentSecrecy.Ledger) × PqxdhDeploymentNative.State KemSK =>
        decide (event (outcome.1.1, outcome.1.2, outcome.2.produced) = true ∧
          PqxdhDeploymentKemTransfer.target setup.source.crypto codec setup.serverKeyId budget claim
            (outcome.1.1, outcome.1.2, outcome.2.produced) = some g))
      (merge reached.1.2 (PqxdhRegistrationJointSchedule.source reached.2)) raw next value verified matched).symm)
  refine PqxdhDeploymentSeedSplit.LawEq.bind_support _ fun pre preMember => ?_
  rcases found : pre.1.1 with _ | ephemeral
  · exact LawEq.refl _
  · exact active born bornMember created constructed reached reachedMember related raw next pending value verified matched
      pre preMember ephemeral found

/-- The second compile lemma (design-v2 section 8.1) from its active branch: `PqxdhDeploymentIdealBranch.ideal_compile_of_selected` with `selected_of_active`. Premises: the approved codec contracts, the budget and the active branch at every draw of the challenger. -/
theorem ideal_compile_of_active {A : Type} (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (ensureInit : StateT A ProbComp Bool)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (budget : Budget)
    (respects : budget.Respects adversary) (event : Observed X → Bool)
    (claim : Observed X → Option PqxdhDeploymentInterface.Handle) (g : Fin budget.accept × Fin budget.capacity)
    (runtime : A)
    (active : ∀ p ∈ support (drawParams setup budget.create),
      ActiveBranch (Reader := Reader) setup codec route checks ensureInit bounds mode adversary budget event claim g
        runtime p) :
    𝒟[PqxdhRegistrationJointKemSecondEntry.slotGame setup codec checks ensureInit none
        (PqxdhDeploymentKemTransfer.decision setup.source.crypto codec setup.serverKeyId budget event claim g)
        (PqxdhDeploymentCompileSecrecy.compileFull setup codec route bounds mode adversary) runtime budget.create
        (PqxdhDeploymentKemTransfer.selectedKem budget g) g.1.val 2] {true} =
      𝒟[(fun outcome => decide (PqxdhDeploymentKemTransfer.happens event
          (PqxdhDeploymentIdealBranch.classicalOf outcome) = true ∧
          PqxdhDeploymentKemTransfer.designated setup.source.crypto codec setup.serverKeyId budget claim
            (PqxdhDeploymentIdealBranch.classicalOf outcome) = some g)) <$>
        (PqxdhDeploymentIdealSteps.idealGame setup codec route checks budget g ensureInit bounds mode adversary).run
          runtime] {true} :=
  PqxdhDeploymentIdealBranch.ideal_compile_of_selected setup codec route checks phase1 phase2 ensureInit bounds mode
    adversary budget respects event claim g runtime fun p drawn =>
      selected_of_active setup codec route checks ensureInit bounds mode adversary budget event claim g runtime p
        (active p drawn)

end Reduction

end BeaconcryptCore.Computational.PqxdhDeploymentIdealActive

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_program

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.beforeLogged_plain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.beforeLogged_plain

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.stopped_before

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.opaqueRest_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.opaqueRest_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.itemRest_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.itemRest_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.acceptStep_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.acceptStep_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.resumeMarked_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.resumeMarked_selected

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.selected_of_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.selected_of_active

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.ideal_compile_of_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealActive.ideal_compile_of_active

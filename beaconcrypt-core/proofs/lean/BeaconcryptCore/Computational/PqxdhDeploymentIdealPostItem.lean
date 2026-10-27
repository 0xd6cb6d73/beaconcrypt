-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSource

/-!
# Item 2's side of the post-challenge simulation: the service layers and the erasures (CE-11b, unit U6, second part)

`PqxdhDeploymentIdealPostSim` writes item 2's post-challenge phase on an active cut as the skeleton's resumed client run through two layers: the upper layers (the grouped client and the skeleton's native layer) and the service layers (the actual encapsulator, the post-challenge router, the challenger's CCA evaluation and the table layers), with the router transcripts erased. This module prepares that form for the per-request simulation against the middle execution of `PqxdhDeploymentIdealPostSource`.

- The service layers on native skeleton steps: a coin of the skeleton's exposed encapsulation interface passes through every KEM layer (`service_coin`, through item 2's `post_coins`), and a table request passes through to the table layers (`service_table`); hence every native step of the skeleton (a client of coins and of the table oracles whose coins go to the coin channel, as `PqxdhRegistrationJointKemPostSkeleton.liftT` sends them) runs through the service layers as through the table layers alone, without stopping and with the router state kept (`service_native`). Helpers: `fwd_liftComp` (forwarding the table oracles through a stateless layer acts on a lifted program as the layer) and `tableLayer_lift` (the table layers pass lifted coins through).
- The skeleton never reads the analysis observers of its game state (`GhostFree`, with `cleanSkel`): the skeleton's primitives (`ghostFree_gameStep`, `ghostFree_setGame`, `ghostFree_modifyGame`, `ghostFree_tableRead`, `ghostFree_valueRead`, `ghostFree_mark`), its native steps (`ghostFree_tailStep`, `ghostFree_clientStep`, `ghostFree_acceptTail`, `ghostFree_acceptStep`, `ghostFree_buildStep`, `ghostFree_hmacStep`, `ghostFree_groupStep`) and so its whole native layer (`skelImpl_ghostFree`) and the upper layers (`upperLayer_neverRead`, with `cleanUpper`, through item 2's `run_erase`).
- `itemPost_clean`: item 2's post-challenge phase on a pending prechallenge context whose verified PQ key is the selected one is the Server's private resumption followed by the tagged client through the upper layers that erase the skeleton's game observers (from the resumption's skeleton state with those observers erased), all through the service layers that erase the router transcripts, followed by the skeleton's decision.

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec SkelState fwd fwdOption coinLift)
open PqxdhRegistrationJointKemEntryFactor (Output)
open PqxdhDeploymentIdealPostSim (SlotState ServiceState tableLayer serviceLayer)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### The service layers on native skeleton steps -/

section Lift
variable {ιA ιB ιT : Type} {A : OracleSpec ιA} {B : OracleSpec ιB} {T : OracleSpec ιT}

/-- Forwarding the table oracles through a stateless layer acts on a lifted program as the layer. -/
theorem fwd_liftComp (layer : QueryImpl A (OracleComp B)) {α : Type} (work : OracleComp A α) :
    simulateQ (fwd (T := T) layer) (OracleComp.liftComp work (A + T)) = OracleComp.liftComp (simulateQ layer work) (B + T) := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (fwd (T := T) layer)
    (fun query => OracleComp.liftComp (layer query) (B + T)) (fun _ => rfl)]
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map, ih,
        OracleComp.liftComp_bind]

end Lift

/-- The table layers pass a lifted probabilistic computation through, keeping their state. -/
theorem tableLayer_lift {α : Type} (work : ProbComp α) (state : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    (simulateQ tableLayer (OracleComp.liftComp work (SkelSpec Output))).run state = (fun a => (a, state)) <$> work := by
  have nested := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
      (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
    (PqxdhRegistrationJointKemEntryFactor.publicLocalV Output) (OracleComp.liftComp work (SkelSpec Output)) state.1 state.2
  have back := congrArg (fun run => (fun z : (α × PqxdhSecretInputKdf.HmacOracle.QueryCache) × SlotState =>
    (z.1.1, (z.1.2, z.2))) <$> run) nested
  simp only [Functor.map_map] at back
  have flat : (simulateQ tableLayer (OracleComp.liftComp work (SkelSpec Output))).run state =
      (fun z : (α × PqxdhSecretInputKdf.HmacOracle.QueryCache) × SlotState => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
          (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
          ((simulateQ (PqxdhRegistrationJointKemEntryFactor.publicLocalV Output)
            (OracleComp.liftComp work (SkelSpec Output))).run state.1)).run state.2 := by
    rw [back]
    exact (id_map _).symm
  rw [flat, PqxdhDeploymentIdealSteps.publicLocal_coins, simulateQ_map, StateT.run_map,
    PqxdhDeploymentIdealCut.slotImpl_lift]
  simp only [Functor.map_map]

section Native
variable (setup : Setup baseSpec KemSK) {count : ℕ} (selected : Fin (count + 1))
  (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK)
  (challenge : MlKem768Ciphertext)

/-- A coin of the skeleton's exposed encapsulation interface passes through the service layers, which keep their router state and their table state. -/
theorem service_coin (coin : unifSpec.Domain) (state : ServiceState KemSK) :
    ((serviceLayer setup selected chosen others challenge (.inl (.inl (.inr (.inl coin))))).run).run state =
      (fun reply => (some reply, state)) <$> (unifSpec.query coin : ProbComp _) := by
  simp only [serviceLayer, PqxdhDeploymentIdealPostSim.optionLower, OptionT.run_mk, StateT.run_mk,
    QueryImpl.apply_compose, PqxdhRegistrationJointKemPostSkeleton.fwd_inl]
  have actual : PqxdhRegistrationJointKemEncapsulation.actual setup (.inl (.inr (.inl coin))) =
      ((PqxdhLiveKemBirth.Spec KemSK).query (.inr (.inl coin)) : OracleComp (PqxdhLiveKemBirth.Spec KemSK) _) := rfl
  rw [actual]
  unfold PqxdhRegistrationJointKemPostSkeleton.fwdOption
  rw [QueryImpl.simulateQ_add_liftComp_left, simulateQ_spec_query]
  simp only [OptionT.run_mk, StateT.run_mk]
  have routed : ((PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
      (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge
        PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder (.inr (.inl coin))).run).run state.1 =
      (fun reply => (some reply, state.1)) <$> PqxdhPrivateKemSource.ccaCoins (baseSpec := baseSpec)
        (unifSpec.query coin : ProbComp _) := rfl
  rw [routed, OracleComp.liftComp_map, simulateQ_map, QueryImpl.simulateQ_compose, fwd_liftComp,
    ← PqxdhRegistrationJointKemPostSkeleton.evaluate_layer, PqxdhDynamicKemJointRouter.post_coins, StateT.run_map,
    tableLayer_lift]
  simp only [Functor.map_map]

/-- A table request of the skeleton passes through the KEM layers of the service layers to the table layers, which answer it; the router state is kept. -/
theorem service_table (point : (TSpec Output).Domain) (state : ServiceState KemSK) :
    ((serviceLayer setup selected chosen others challenge (.inr point)).run).run state =
      (fun result => (some result.1, (state.1, result.2))) <$> (tableLayer (.inr point)).run state.2 := by
  simp only [serviceLayer, PqxdhDeploymentIdealPostSim.optionLower, OptionT.run_mk, StateT.run_mk,
    QueryImpl.apply_compose, PqxdhRegistrationJointKemPostSkeleton.fwd_inr, simulateQ_spec_query,
    PqxdhRegistrationJointKemPostSkeleton.fwdOption_inr, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- A native step of the skeleton (a client of coins and of the table oracles, its coins sent to the exposed encapsulation interface's coin channel) runs through the service layers as through the table layers alone, without stopping and with the router state kept. -/
theorem service_native {α : Type} (work : OracleComp (SkelSpec Output) α) (state : ServiceState KemSK) :
    ((simulateQ (serviceLayer setup selected chosen others challenge)
        (simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) work)).run).run state =
      (fun result => (some result.1, (state.1, result.2))) <$> (simulateQ tableLayer work).run state.2 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      have first : ∀ (head : OracleComp (Enc KemSK + TSpec Output) ((SkelSpec Output).Range query))
          (step : ((simulateQ (serviceLayer setup selected chosen others challenge) head).run).run state =
            (fun result => (some result.1, (state.1, result.2))) <$> (tableLayer query).run state.2),
          ((simulateQ (serviceLayer setup selected chosen others challenge)
            (head >>= fun reply => simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) (next reply))).run).run
              state =
            (fun result => (some result.1, (state.1, result.2))) <$> (simulateQ tableLayer
              ((SkelSpec Output).query query >>= next)).run state.2 := by
        intro head step
        rw [simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, step, bind_map_left,
          simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
        refine bind_congr fun result => ?_
        exact ih result.1 (state.1, result.2)
      rw [simulateQ_bind, simulateQ_spec_query]
      refine first _ ?_
      rcases query with coin | point
      · rw [PqxdhRegistrationJointKemPostSkeleton.fwd_inl, QueryImpl.simulateQ_liftComp_left_eq_of_apply
          (spec₁' := Enc KemSK) (spec₂' := TSpec Output) (serviceLayer setup selected chosen others challenge)
          (fun query => serviceLayer setup selected chosen others challenge (.inl query)) (fun _ => rfl)]
        change ((simulateQ (fun query => serviceLayer setup selected chosen others challenge (.inl query) :
          QueryImpl (Enc KemSK) (OptionT (StateT (ServiceState KemSK) ProbComp)))
            ((Enc KemSK).query (.inl (.inr (.inl coin))) : OracleComp (Enc KemSK) _)).run).run state = _
        rw [simulateQ_spec_query, service_coin]
        rfl
      · rw [PqxdhRegistrationJointKemPostSkeleton.fwd_inr, simulateQ_spec_query, service_table]

end Native

/-! ### The skeleton never reads the analysis observers of its game state -/

section Ghost
open PqxdhRegistrationJointKemPostSkeleton (NGame SClient clean gameStep setGame modifyGame tableRead valueRead)

/-- The skeleton state with the analysis observers of its game state erased. -/
def cleanSkel {V : Type} (state : SkelState KemSK V) : SkelState KemSK V := (clean state.1, state.2)

/-- Erasing the observers twice is erasing them once. -/
theorem cleanSkel_idem {V : Type} (state : SkelState KemSK V) : cleanSkel (cleanSkel state) = cleanSkel state := rfl

/-- A computation on the skeleton state never reads the analysis observers of the game state. -/
def GhostFree {V α : Type} {M : Type → Type} [Monad M] (work : StateT (SkelState KemSK V) M α) : Prop :=
  ∀ state, Prod.map id cleanSkel <$> work.run state = Prod.map id cleanSkel <$> work.run (cleanSkel state)

variable {V : Type} {M : Type → Type} [Monad M] [LawfulMonad M]

/-- A pure computation is `GhostFree`. -/
theorem ghostFree_pure {α : Type} (value : α) : GhostFree (KemSK := KemSK) (V := V) (M := M) (pure value) := by
  intro state
  simp only [StateT.run_pure, map_pure]
  rfl

/-- `GhostFree` computations are closed under bind. -/
theorem ghostFree_bind {α β : Type} (work : StateT (SkelState KemSK V) M α) (next : α → StateT (SkelState KemSK V) M β)
    (first : GhostFree work) (rest : ∀ value, GhostFree (next value)) : GhostFree (work >>= next) := by
  intro state
  have later : ∀ result : α × SkelState KemSK V, Prod.map id cleanSkel <$> (next result.1).run result.2 =
      Prod.map id cleanSkel <$> (next (Prod.map id cleanSkel result).1).run (Prod.map id cleanSkel result).2 :=
    fun result => rest result.1 result.2
  let after : α × SkelState KemSK V → M (β × SkelState KemSK V) := fun result =>
    Prod.map id cleanSkel <$> (next result.1).run result.2
  calc Prod.map id cleanSkel <$> (work >>= next).run state
      = work.run state >>= fun result => after (Prod.map id cleanSkel result) := by
        simp only [StateT.run_bind, map_bind]
        exact bind_congr later
    _ = (Prod.map id cleanSkel <$> work.run state) >>= after := (bind_map_left _ _ _).symm
    _ = (Prod.map id cleanSkel <$> work.run (cleanSkel state)) >>= after := by rw [first state]
    _ = work.run (cleanSkel state) >>= fun result => after (Prod.map id cleanSkel result) := bind_map_left _ _ _
    _ = Prod.map id cleanSkel <$> (work >>= next).run (cleanSkel state) := by
        simp only [StateT.run_bind, map_bind]
        exact (bind_congr later).symm

/-- A game-state computation of the source (`gameStep`, which runs on the game state without observers) is `GhostFree`. -/
theorem ghostFree_gameStep {α : Type} (work : StateT (PqxdhServerAuthExperiment.GameState KemSK) ProbComp α) :
    GhostFree (KemSK := KemSK) (V := V) (gameStep work) := by
  intro state
  rfl

/-- Replacing the game state is `GhostFree`. -/
theorem ghostFree_setGame (game : PqxdhServerAuthExperiment.GameState KemSK) :
    GhostFree (KemSK := KemSK) (V := V) (setGame game) := by
  intro state
  rfl

/-- A change of the game state is `GhostFree` when its result without observers does not depend on the observers of its input. -/
theorem ghostFree_modifyGame (change : PqxdhServerAuthExperiment.GameState KemSK → PqxdhServerAuthExperiment.GameState KemSK)
    (same : ∀ game, clean (change game) = clean (change (clean game))) :
    GhostFree (KemSK := KemSK) (V := V) (modifyGame change) := by
  intro state
  simp only [modifyGame, StateT.run, map_pure, Prod.map, id_eq, cleanSkel]
  rw [same state.1]

/-- A direct table read is `GhostFree`. -/
theorem ghostFree_tableRead (point : Pqxdh.Bytes) : GhostFree (KemSK := KemSK) (V := V) (tableRead point) := by
  intro state
  simp only [tableRead, StateT.run, Functor.map_map]
  rfl

/-- A hidden read is `GhostFree`. -/
theorem ghostFree_valueRead (point : PqxdhCorrelatedExtractFamily.Message) :
    GhostFree (KemSK := KemSK) (V := V) (valueRead point) := by
  intro state
  simp only [valueRead, StateT.run, Functor.map_map]
  rfl

/-- `GhostFree` is closed under mapping the result. -/
theorem ghostFree_map {α β : Type} (f : α → β) (work : StateT (SkelState KemSK V) M α) (free : GhostFree work) :
    GhostFree (f <$> work) := by
  intro state
  have mapped := congrArg (fun run => Prod.map f id <$> run) (free state)
  simp only [Functor.map_map] at mapped
  simp only [StateT.run_map, Functor.map_map]
  exact mapped

/-- A `GhostFree` native-layer program stays `GhostFree` on the exposed encapsulation interface (`liftT`). -/
theorem ghostFree_liftT {α : Type} (work : NGame KemSK V α) (free : GhostFree work) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.liftT (KemSK := KemSK) work) := by
  intro state
  simp only [PqxdhRegistrationJointKemPostSkeleton.liftT, StateT.run, ← simulateQ_map]
  have mapped := free state
  simp only [StateT.run] at mapped
  rw [mapped]

/-- Recording the hidden Server session and its value (`mark`) is `GhostFree`. -/
theorem ghostFree_mark (index : ℕ) (value : V) :
    GhostFree (KemSK := KemSK) (PqxdhRegistrationJointKemPostSkeleton.mark index value) := by
  intro state
  rfl

section Steps
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The Beacon tail callbacks of the skeleton (`tailStep`) are `GhostFree`. -/
theorem ghostFree_tailStep (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.tailStep (V := V) setup codec query) := by
  rcases query with query | query
  · exact ghostFree_gameStep _
  · cases query with
    | root input => exact ghostFree_bind _ _ (ghostFree_tableRead _) fun _ => ghostFree_pure _
    | initial request => exact ghostFree_gameStep _
    | application response => exact ghostFree_gameStep _

/-- The Server's core acceptance and root of a raw accept in the skeleton (`clientStep`) are `GhostFree`. -/
theorem ghostFree_clientStep (hmac : PqxdhSecretInputKdf.HmacSha512) (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.clientStep (KemSK := KemSK) (V := V) hmac control binding input) := by
  unfold PqxdhRegistrationJointKemPostSkeleton.clientStep
  split
  · exact ghostFree_pure _
  · exact ghostFree_pure _
  · exact ghostFree_pure _
  · refine ghostFree_bind _ _ ?_ fun _ => ghostFree_bind _ _ (ghostFree_modifyGame _ fun _ => rfl) fun _ =>
      ghostFree_pure _
    exact ghostFree_map _ _ (ghostFree_tableRead _)

/-- The Server's accept tail in the skeleton (`acceptTail`) is `GhostFree`. -/
theorem ghostFree_acceptTail (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (game : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) ×
      List Pqxdh.Bytes) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.acceptTail (V := V) setup publicIdentity game collected) := by
  unfold PqxdhRegistrationJointKemPostSkeleton.acceptTail
  refine ghostFree_bind _ _ (ghostFree_setGame _) fun _ => ?_
  rcases collected with ⟨_ | input, consumed⟩
  · exact ghostFree_pure _
  · refine ghostFree_bind _ _ (ghostFree_clientStep _ _ _ _) fun returned => ?_
    rcases returned with (_ | token) | _ | _
    · exact ghostFree_pure _
    · exact ghostFree_bind _ _ (ghostFree_modifyGame _ fun _ => rfl) fun _ => ghostFree_pure _
    · exact ghostFree_pure _
    · exact ghostFree_pure _

/-- The Server's raw accept in the skeleton (`acceptStep`) is `GhostFree`. -/
theorem ghostFree_acceptStep (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (raw : Pqxdh.Bytes) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.acceptStep (V := V) setup codec checks identityIndex
      publicIdentity raw) := by
  unfold PqxdhRegistrationJointKemPostSkeleton.acceptStep
  refine ghostFree_bind _ _ (fun state => rfl) fun before => ghostFree_bind _ _ (fun state => ?_) fun collected =>
    ghostFree_liftT _ (ghostFree_acceptTail setup _ _ _)
  simp only [StateT.run, Functor.map_map]
  rfl

/-- The Server build in the skeleton (`buildStep`) is `GhostFree`. -/
theorem ghostFree_buildStep (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) (session : ℕ)
    (payload : Option Pqxdh.Bytes) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.buildStep setup codec checks services session payload) := by
  intro state
  simp only [PqxdhRegistrationJointKemPostSkeleton.buildStep, StateT.run]
  change Prod.map id cleanSkel <$> (match state.1.pending session with
    | none => _
    | some token => _) = Prod.map id cleanSkel <$> (match state.1.pending session with
    | none => _
    | some token => _)
  rcases state.1.pending session with _ | token
  · simp only [map_pure]
    rfl
  · simp only [map_bind, map_pure]
    rfl

/-- The adversary's public HMAC in the skeleton (`hmacStep`) is `GhostFree`. -/
theorem ghostFree_hmacStep (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.hmacStep (KemSK := KemSK) (V := V) setup key message) := by
  unfold PqxdhRegistrationJointKemPostSkeleton.hmacStep
  split
  · exact ghostFree_tableRead _
  · exact ghostFree_pure _

/-- The grouped Beacon finish in the skeleton (`groupStep`) is `GhostFree`. -/
theorem ghostFree_groupStep (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (pending : PqxdhRegistrationJointKemPostSkeleton.Pending Response) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.groupStep (KemSK := KemSK) setup codec services pending) := by
  unfold PqxdhRegistrationJointKemPostSkeleton.groupStep
  split
  · split
    · exact ghostFree_bind _ _ (ghostFree_valueRead _) fun _ => ghostFree_gameStep _
    · exact ghostFree_bind _ _ (ghostFree_tableRead _) fun _ => ghostFree_gameStep _
  · exact ghostFree_pure _

/-- The skeleton's native layer never reads the analysis observers of its game state. -/
theorem skelImpl_ghostFree (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (query : (PqxdhRegistrationJointKemPostSkeleton.GSpec KemSK Response).Domain) :
    GhostFree (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services
      query) := by
  rcases query with ((query | query) | command) | pending
  · intro state
    simp only [PqxdhRegistrationJointKemPostSkeleton.skelImpl, StateT.run, Functor.map_map]
    rfl
  · exact ghostFree_liftT _ (ghostFree_tailStep setup codec query)
  · cases command with
    | accept raw => exact ghostFree_acceptStep setup codec checks identityIndex publicIdentity raw
    | build session payload => exact ghostFree_liftT _ (ghostFree_buildStep setup codec checks services session payload)
    | hmac key message => exact ghostFree_liftT _ (ghostFree_hmacStep setup key message)
    | hash bytes => exact ghostFree_liftT _ (ghostFree_gameStep _)
    | reveal keyId => exact ghostFree_liftT _ (ghostFree_gameStep _)
  · exact ghostFree_liftT _ (ghostFree_groupStep setup codec services pending)

/-- The upper layers' state with the analysis observers of the skeleton's game state erased. -/
def cleanUpper (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK V) :
    List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK V :=
  (state.1, cleanSkel state.2)

/-- The upper layers never read the analysis observers of the skeleton's game state. -/
theorem upperLayer_neverRead (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (selected : ℕ)
    (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) :
    PqxdhRegistrationJointKemObserverFree.NeverRead cleanUpper
      (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks identityIndex publicIdentity selected challenge
        services) := by
  intro query state
  have erased : ∀ sk : SkelState KemSK V, Prod.map id cleanSkel <$>
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services)
        ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge query).run state.1)).run sk =
      (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanSkel
        (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services))
        ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge query).run state.1)).run
        (cleanSkel sk) := fun sk =>
    PqxdhRegistrationJointKemObserverFree.run_erase cleanSkel cleanSkel_idem _
      (fun query state => skelImpl_ghostFree setup codec checks identityIndex publicIdentity services query state) _ sk
  have left := erased state.2
  have right := erased (cleanSkel state.2)
  rw [cleanSkel_idem] at right
  change Prod.map id cleanUpper <$> ((fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services)
        ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge query).run state.1)).run
        state.2) =
    Prod.map id cleanUpper <$> ((fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services)
        ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge query).run state.1)).run
        (cleanSkel state.2))
  have mapped : ∀ sk : SkelState KemSK V, Prod.map id cleanUpper <$> ((fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services)
        ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge query).run state.1)).run sk) =
      (fun r => (r.1.1, (r.1.2, r.2))) <$> (Prod.map id cleanSkel <$>
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services)
        ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge query).run state.1)).run sk) := by
    intro sk
    simp only [Functor.map_map]
    rfl
  rw [mapped, mapped, left, right]

end Steps

end Ghost

/-! ### Item 2's post-challenge phase with both erasures -/

section Clean
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhRegistrationJointKemEntryFactor (factoredServices)
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}

/-- Item 2's post-challenge phase on a pending prechallenge context whose verified PQ key is the selected one: the Server's private resumption, then the tagged client through the upper layers that erase the analysis observers of the skeleton's game state, from the skeleton state of the resumption with those observers erased, all through the service layers that erase the router transcripts, followed by the skeleton's decision. -/
theorem itemPost_clean {A Y : Type} {count : ℕ} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (t : Target count) (p : Params KemSK count)
    (decision : Y × PqxdhDeploymentCompile.Local → Bool) (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit)
    (others : Fin count → MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (next : Option ℕ → OracleComp (PqxdhRegistrationJointKemCommands.SourceSpec KemSK) (Y × PqxdhDeploymentCompile.Local))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    PqxdhDeploymentIdealBranch.itemPost setup codec checks t p decision
        (.ready created others (some (.pending raw value ephemeral consumed native owners next)) state after) =
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$>
        ((simulateQ (PqxdhRegistrationJointKemObserverFree.eraseOptionImpl PqxdhDeploymentIdealPostSim.eraseService
          (serviceLayer setup t.kem p.chosen others p.challenge))
          ((simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac native.2.sessions
              (factoredServices setup codec checks))
            (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks created.server.server.metadata.identityIndex
              created.publicIdentity raw value ephemeral (PqxdhAcceptedRegistration.ciphertextArray p.challenge)
              .challenge native.2 consumed)).run (native.2, none) >>= fun answer =>
            (fun result => ((result.1, result.2.1), result.2.2)) <$>
              (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpper
                (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
                  created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks)))
                (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw
                  next answer.1)).run (owners, cleanSkel answer.2))).run).run
          (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
            (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  rw [PqxdhDeploymentIdealPostSim.itemPost_erased setup codec checks t p decision created others raw value matched
    ephemeral consumed native owners next state after, PqxdhDeploymentIdealPostSim.skelResume_upper]
  have inner : ∀ answer : Option ℕ × SkelState KemSK Output,
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpper
          (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks)))
          (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw
            next answer.1)).run (owners, cleanSkel answer.2) =
      (fun result : (Bool × List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) × SkelState KemSK Output =>
          (result.1, cleanSkel result.2)) <$>
        ((fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
            created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks))
            (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw
              next answer.1)).run (owners, answer.2)) := by
    intro answer
    have erased := PqxdhRegistrationJointKemObserverFree.run_erase cleanUpper (fun _ => rfl)
      (PqxdhDeploymentIdealPostSim.upperLayer setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks))
      (upperLayer_neverRead setup codec checks _ _ _ _ _)
      (PqxdhRegistrationJointAcceptKemCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
        answer.1) (owners, answer.2)
    change _ = _ <$> (_ <$> _)
    rw [show (owners, cleanSkel answer.2) = cleanUpper (owners, answer.2) from rfl, ← erased]
    simp only [Functor.map_map]
    rfl
  simp only [inner, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
  refine bind_congr fun reached => ?_
  rcases reached with ⟨_ | answer, after⟩
  · rfl
  · simp only [Option.elim, simulateQ_map, OptionT.run_map, StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> _) (funext fun reached => ?_)
    rcases reached with ⟨_ | result, after⟩ <;> rfl

end Clean

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.fwd_liftComp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.fwd_liftComp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.tableLayer_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.tableLayer_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.service_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.service_coin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.service_table' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.service_table

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.service_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.service_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.cleanSkel_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.cleanSkel_idem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_pure

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_gameStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_gameStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_setGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_setGame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_modifyGame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_modifyGame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_tableRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_tableRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_valueRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_valueRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_map

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_liftT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_liftT

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_mark' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_mark

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_tailStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_tailStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_clientStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_clientStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_acceptTail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_acceptTail

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_acceptStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_acceptStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_buildStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_buildStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_hmacStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_hmacStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_groupStep' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.ghostFree_groupStep

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.skelImpl_ghostFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.skelImpl_ghostFree

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.upperLayer_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.upperLayer_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.itemPost_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem.itemPost_clean

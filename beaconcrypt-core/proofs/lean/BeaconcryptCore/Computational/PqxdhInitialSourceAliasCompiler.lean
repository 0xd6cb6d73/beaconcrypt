import BeaconcryptCore.Computational.PqxdhInitialSourceExperiment
import BeaconcryptCore.Computational.PqxdhInitialCurrentBeacon
import BeaconcryptCore.Computational.PqxdhInitialObserverCallbackBudgets

/-!
The source alias client retains the original selective table, cursor, chronological log, private state and source result. Its only separate state is the root-family cache, owned by the response-only initializer interpreter. Ordinary callbacks remain their complete original probabilistic computations. The client first obtains the shared initial64 response and then runs the complete original source sequence.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialBeaconAmbient
variable {ι M P I D K X Response A N Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev LocalState (A N : Type) := RawCtxSelectiveFamilyLog.LoggedState A × N
abbrev External := PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared
abbrev Plain (A N : Type) := StateT (RawCtxSharedPrimitive.SharedState A × N) ProbComp
abbrev SourceSpec := PqxdhInitialNativeLog.Spec extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared S B

def attach (state : LocalState A N) (cache : RootOracle.QueryCache) : PqxdhInitialNativeLog.State A N RootOracle.QueryCache :=
  (state.1, (state.2, cache))

def restore (result : (Result × LocalState A N) × RootOracle.QueryCache) :=
  (result.1.1, attach result.1.2 result.2)

def plainExternal (external : QueryImpl (External (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)) (Plain A N)) :
    QueryImpl (External (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)) (Ambient A N RootOracle.QueryCache) :=
  fun query state cache => (fun result => (result, cache)) <$> (external query).run state

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (stage : Nat)
  (external : QueryImpl (External (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)) (Plain A N))

noncomputable def externalCoins (query : (External (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)).Domain)
    (state : LocalState A N) : OracleComp PqxdhInitialLabelCompiler.Spec
      ((External (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response)).Range query × LocalState A N) :=
  PqxdhInitialLabelCompiler.coins ((fun result => (result.1, (((result.2.1, state.1.1.2), state.1.2), result.2.2))) <$>
    (external query).run (state.1.1.1, state.2))

noncomputable def compiler : QueryImpl
    (SourceSpec (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B))
    (StateT (LocalState A N) (OracleComp PqxdhInitialLabelCompiler.Spec))
  | .inl query => fun state => PqxdhInitialLabelCompiler.coins ((fun result => (result.1, (result.2, state.2))) <$>
      (RawCtxSelectiveFamilyLog.handler source writer stage query).run state.1)
  | .inr (.inr (.inr (.inl secrets))) => fun state => do
      let response ← PqxdhInitialLabelCompiler.Spec.query (.inr (PqxdhInitialRootLabelBridge.request source secrets))
      pure (some (PqxdhInitialRootAudit.kernel (List.Vector.replicate 32 0, response)).refined, state)
  | .inr (.inl query) => externalCoins external (.inl query)
  | .inr (.inr (.inl reply)) => externalCoins external (.inr (.inl reply))
  | .inr (.inr (.inr (.inr query))) => externalCoins external (.inr (.inr (.inr query)))

variable (selected : Message) (previousRoot : RootOutput) (response : PqxdhInitialRootLabelService.Response)
local notation "labelled" => PqxdhInitialRootLabelService.labelledFull source (QueryImpl.ofLift unifSpec ProbComp) selected response
local notation "native" => PqxdhInitialNativeLog.handler source writer stage
  (PqxdhInitialOriginFinishPath.withInitial source selected previousRoot response (plainExternal external))

/-- One response-only source callback preserves its full reply and every original interpreter field after reattaching the root cache. -/
theorem step (query : (SourceSpec (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)).Domain)
    (state : LocalState A N) (cache : RootOracle.QueryCache) :
    restore <$> (simulateQ labelled ((compiler source writer stage external query).run state)).run cache =
      (native query).run (attach state cache) := by
  cases query with
  | inl query =>
    rw [PqxdhInitialNativeLog.live_handler]
    simp only [compiler, StateT.run, PqxdhInitialCurrentBeacon.coins_labelled, Functor.map_map]
    rfl
  | inr query =>
    rw [PqxdhInitialNativeLog.external_handler]
    rcases query with query | (reply | (secrets | query))
    · simp only [compiler, externalCoins, PqxdhInitialOriginFinishPath.withInitial, plainExternal,
        StateT.run, Functor.map_map]
      rw [PqxdhInitialCurrentBeacon.coins_labelled]
      simp only [Functor.map_map]
      rfl
    · simp only [compiler, externalCoins, PqxdhInitialOriginFinishPath.withInitial, plainExternal,
        StateT.run, Functor.map_map]
      rw [PqxdhInitialCurrentBeacon.coins_labelled]
      simp only [Functor.map_map]
      rfl
    · have erased := PqxdhInitialNativeInitializer.initial_erase source selected previousRoot response secrets
        (state.1.1.1, state.2) cache
      simp only [compiler, StateT.run, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
        PqxdhInitialRootLabelService.labelledFull, QueryImpl.add_apply_inr]
      have mapped := congrArg (fun work => (fun result => (result.1.1, (((result.1.2.1, state.1.1.2), state.1.2), (result.1.2.2, result.2)))) <$> work) erased
      change restore <$> ((fun a => (some (PqxdhInitialRootAudit.kernel (List.Vector.replicate 32 0, a)).refined, state)) <$>
        PqxdhInitialRootLabelService.labelled source selected response (PqxdhInitialRootLabelBridge.request source secrets)).run cache = _
      rw [StateT.run_map]
      change _ = (fun result => (result.1.1, (((result.1.2.1, state.1.1.2), state.1.2), (result.1.2.2, result.2)))) <$>
        ((Prod.snd <$> PqxdhInitialNativeInitializer.initial source selected previousRoot response secrets).run
          (state.1.1.1, state.2)).run cache
      rw [StateT.run_map, StateT.run_map]
      simpa only [Functor.map_map, restore, attach, StateT.run, Prod.eta] using mapped.symm
    · simp only [compiler, externalCoins, PqxdhInitialOriginFinishPath.withInitial, plainExternal,
        StateT.run, Functor.map_map]
      rw [PqxdhInitialCurrentBeacon.coins_labelled]
      simp only [Functor.map_map]
      rfl

/-- The full adaptive original client has the identical complete source result and state after restoring the separately interpreted root cache. -/
theorem program (client : OracleComp
    (SourceSpec (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)) Result)
    (state : LocalState A N) (cache : RootOracle.QueryCache) :
    restore <$> (simulateQ labelled ((simulateQ (compiler source writer stage external) client).run state)).run cache =
      (simulateQ native client).run (attach state cache) := by
  induction client using OracleComp.inductionOn generalizing state cache with
  | pure value => rfl
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← step source writer stage external selected previousRoot response query state cache]
    simp only [bind_map_left]
    apply bind_congr
    intro result
    exact ih result.1.1 result.1.2 result.2

/-- Every compiled source callback makes at most one private initializer request, including rejected and repeated attempts; all original coins belong to the other query class. -/
theorem step_initial (query : (SourceSpec (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)).Domain)
    (state : LocalState A N) :
    ((compiler source writer stage external query).run state).IsQueryBoundP PqxdhInitialObserverCallbackBudgets.IsService 1 := by
  cases query with
  | inl query => exact (PqxdhInitialObserverCallbackBudgets.coins_service _).mono (Nat.zero_le 1)
  | inr query =>
    rcases query with query | (reply | (secrets | query))
    · exact (PqxdhInitialObserverCallbackBudgets.coins_service _).mono (Nat.zero_le 1)
    · exact (PqxdhInitialObserverCallbackBudgets.coins_service _).mono (Nat.zero_le 1)
    · simp [compiler, StateT.run, PqxdhInitialObserverCallbackBudgets.IsService]
    · exact (PqxdhInitialObserverCallbackBudgets.coins_service _).mono (Nat.zero_le 1)

/-- The complete adaptive source client retains its original total callback allowance as a conservative initializer-attempt allowance. -/
theorem program_initial (client : OracleComp
    (SourceSpec (extra := extra) (I := I) (D := D) (K := K) (X := X) (Response := Response) (S := S) (B := B)) Result)
    (budget : Nat) (bounded : client.IsTotalQueryBound budget) (state : LocalState A N) :
    ((simulateQ (compiler source writer stage external) client).run state).IsQueryBoundP
      PqxdhInitialObserverCallbackBudgets.IsService budget := by
  induction client using OracleComp.inductionOn generalizing budget state with
  | pure value => trivial
  | query_bind query next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    have bound := isQueryBoundP_bind (step_initial source writer stage external query state)
      (fun result _ => ih result.1 (budget - 1) (bounded.2 result.1) result.2)
    exact bound.mono (by omega)

section SourceClient
variable (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (owner : RawCtxProtocolReveals.Owner S B) (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N)
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

noncomputable def initialState (response : PqxdhInitialRootLabelService.Response) : LocalState A N :=
  (((shared, ((fun _ => none), ⟨PqxdhInitialSourceExperiment.root source zeroRoot response owner, 0⟩)), []), privateState)

noncomputable def client : OracleComp PqxdhInitialLabelCompiler.Spec
    ((Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × LocalState A N) := do
  let response ← PqxdhInitialLabelCompiler.Spec.query (.inr (.family selected))
  (simulateQ (compiler source writer stage external)
    (PqxdhInitialNativeCarried.original source (PqxdhInitialSelectedOrigin.mark source selected) sender route decode
      (PqxdhInitialSourceExperiment.execution response index metadata ready post before))).run
    (initialState source owner shared privateState response)

/-- The alias client obtains the shared initializer response once, then exactly runs the complete original source experiment with its whole final state. -/
theorem client_source (cache : RootOracle.QueryCache) :
    restore <$> (simulateQ labelled
      (client source writer stage external selected sender route decode index metadata ready post before owner shared privateState)).run cache =
      PqxdhInitialSourceExperiment.run source writer selected zeroRoot response (plainExternal external)
        sender route decode index metadata ready post before owner shared privateState cache stage := by
  unfold client
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
    PqxdhInitialRootLabelService.labelledFull, QueryImpl.add_apply_inr]
  rw [PqxdhInitialRootLabelService.selected_reply]
  simp only [pure_bind]
  exact program source writer stage external selected zeroRoot response _
    (initialState source owner shared privateState response) cache

/-- The response-only source client counts its initial shared response plus every possible initializer callback in the original builder and bounded adaptive suffix. -/
theorem client_initial (qPost : Nat) (bounded : ∀ reply, (post reply).IsTotalQueryBound qPost) :
    (client source writer stage external selected sender route decode index metadata ready post before owner shared privateState).IsQueryBoundP
      PqxdhInitialObserverCallbackBudgets.IsService (1 + (7 + qPost * 67)) := by
  unfold client
  apply isQueryBoundP_bind
    (show OracleComp.IsQueryBoundP (PqxdhInitialLabelCompiler.Spec.query (.inr (.family selected)) : OracleComp PqxdhInitialLabelCompiler.Spec _) PqxdhInitialObserverCallbackBudgets.IsService 1 by
      simp [PqxdhInitialObserverCallbackBudgets.IsService])
  intro response _
  apply program_initial
  exact PqxdhInitialOriginPost.sequence_total source _ _ _ sender route decode index metadata ready post qPost bounded _

noncomputable def observation (response : PqxdhInitialRootLabelService.Response) (number : Std.U64)
    (ancestors disclosed : List RatchetChain)
    (result : ((Bool × PqxdhInitialOriginPostPath.Snapshot M P I D K S B) × LocalState A N) × RootOracle.QueryCache) : Bool :=
  PqxdhInitialPublishedEvent.sourceDecision source (PqxdhInitialSourceExperiment.root source zeroRoot response owner)
    owner number ancestors disclosed (restore result)

/-- The labelled alias client preserves the exact original publication and complete source-lineage freshness observation for any selected record, stage and initializer response. -/
theorem observed_source (cache : RootOracle.QueryCache) (number : Std.U64) (ancestors disclosed : List RatchetChain) :
    observation source owner response number ancestors disclosed <$>
      (simulateQ labelled (client source writer stage external selected sender route decode index metadata ready post before owner shared privateState)).run cache =
      PqxdhInitialSourceExperiment.game source writer selected zeroRoot response (plainExternal external)
        sender route decode index metadata ready post before owner number ancestors disclosed shared privateState cache stage := by
  rw [PqxdhInitialSourceExperiment.game, ← client_source source writer stage external selected response
    sender route decode index metadata ready post before owner shared privateState cache]
  simp only [Functor.map_map]
  rfl

end SourceClient
end BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.step

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.program

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.step_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.step_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.program_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.program_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.client_source

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.client_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.client_initial

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.observed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceAliasCompiler.observed_source

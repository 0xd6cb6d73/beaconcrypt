-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv
import BeaconcryptCore.Computational.PqxdhRecordLiftOrigins

/-!
# The provenance-annotated record world with the ledger (CE-11b, unit U4)

Generic tools for invariants of the provenance-annotated record world (`PqxdhRecordLiftOrigins.handler`) with the CE ledger, for every environment (design-v2 section 7.2, items 1 and 4):

- The annotated joint step `aWorldStep` (`aWorldStep_run`, `aWorldStep_erase`, `aWorldStep_reg`, `aWorldStep_fixed`) and the ledger layer over it (`ledgerStep`); `run_keeps_origins` (`ledger_keeps` and `run_keeps_origins` of design-v2 in one statement): every outcome of the CE ledger over the open program, interpreted by the environment and the annotated World from an admissible joint state, keeps `Good`, a stable admissibility predicate and a relation `R` between the transcript, the environment state, the World and the annotation, when every registration command keeps `R`; `world_keeps_origins` for the whole annotated record world `annotatedRun` (which erases to `PqxdhRecordLiftWorld.run`, `annotatedRun_erase`).
- The annotation invariant `AnnInv` of the World and its annotation: every hidden origin is at a handle the World holds (`Present`), every used marker has an origin (`Covered`), every origin's marker is used (`PqxdhRecordLiftOrigins.Marked`). Every World effect keeps it, and an effect that is not a hidden install keeps the annotation (`aEffects_keeps`, through `installServer_annInv` and `installBeacon_annInv`); it reads the World only through its fixed view (`annInv_view`). For environment programs: `aRun_rel` (the annotation changes only through allowed hidden installs), `aRun_free` (no hidden install: the annotation is kept) and `aRun_owner` (hidden installs only Beacon installs at one owner: only that owner's origin changes).

These are support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (EnvEffects WorldSpec Environment EnvQuery effectLift)
open PqxdhRecordLiftOrigins (Origins annotate)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentEnvironmentJoin (Good Stable Splits fixedView worldStep)
open PqxdhDeploymentInterface (Entry)

variable {n : ℕ} {KemSK : Type}

/-! ### Annotating requests -/

section Annotate

/-- The World requests that may change the provenance annotation: the Server and Beacon installs and the owner append. -/
def isAnnot : (WorldSpec n).Domain → Bool
  | .inr (.inl (.inr (.installServer _ _ _))) => true
  | .inr (.inl (.inr (.installBeacon _ _ _))) => true
  | .inr (.inl (.inr (.appendOwner _ _ _))) => true
  | _ => false

/-- Every other request keeps the annotation. -/
theorem annotate_other (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query) (o : Origins n)
    (other : isAnnot query = false) : annotate query reply o = o := by
  rcases query with created | ((coin | capability) | record)
  · rfl
  · rfl
  · cases capability <;> first | rfl | simp [isAnnot] at other
  · rfl

variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A request that is not an install or an append is the World's request with the annotation kept. -/
theorem handler_other (query : (WorldSpec n).Domain) (state : PqxdhRecordLiftOrigins.State n)
    (other : isAnnot query = false) :
    (PqxdhRecordLiftOrigins.handler setup codec route query).run state =
      (fun result => (result.1, (result.2, state.2))) <$>
        (PqxdhRecordLiftWorld.handler setup codec route query).run state.1 := by
  have kept : ∀ reply, annotate query reply state.2 = state.2 := fun reply => annotate_other query reply state.2 other
  simp only [PqxdhRecordLiftOrigins.handler, StateT.run, kept, bind_pure_comp]

/-- A World program without an install or an append keeps the annotation: its annotated run is its World run with the annotation unchanged. -/
theorem free_run {α : Type} (work : OracleComp (WorldSpec n) α)
    (free : work.IsQueryBoundP (fun query => isAnnot query = true) 0) (w : PqxdhRecordLiftWorld.State n)
    (o : Origins n) :
    (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route) work).run (w, o) =
      (fun result => (result.1, (result.2, o))) <$>
        (simulateQ (PqxdhRecordLiftWorld.handler setup codec route) work).run w := by
  induction work using OracleComp.inductionOn generalizing w with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      have other : isAnnot query = false := by
        rcases free.1 with notAnnot | impossible
        · simpa using notAnnot
        · exact absurd impossible (Nat.lt_irrefl 0)
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      rw [handler_other setup codec route query (w, o) other, bind_map_left]
      refine bind_congr fun result => ?_
      have rest := free.2 result.1
      simp only [other, Bool.false_eq_true, ite_false] at rest
      exact ih result.1 rest result.2

end Annotate

/-! ### The annotated joint step -/

section Joint
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response E : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- The World's effects with the provenance annotation (`PqxdhRecordLiftOrigins.handler` on environment effects). -/
noncomputable def aEffects : QueryImpl (EnvEffects n) (StateT (PqxdhRecordLiftOrigins.State n) ProbComp) :=
  fun query => PqxdhRecordLiftOrigins.handler setup codec route (.inr (.inl query))

/-- The annotated handler on lifted environment effects is `aEffects`. -/
theorem aEffects_compose :
    (PqxdhRecordLiftOrigins.handler setup codec route (n := n)) ∘ₛ effectLift = aEffects setup codec route := by
  funext query
  simp only [QueryImpl.apply_compose, effectLift, simulateQ_spec_query]
  rfl

/-- Erasing the annotation of an environment program's annotated run gives its World run. -/
theorem aEffects_erase {α : Type} (work : OracleComp (EnvEffects n) α) (state : PqxdhRecordLiftOrigins.State n) :
    Prod.map id Prod.fst <$> (simulateQ (aEffects setup codec route) work).run state =
      (simulateQ PqxdhRecordLiftWorld.effects work).run state.1 :=
  map_run_simulateQ_eq_of_query_map_eq _ _ _
    (fun query current => PqxdhRecordLiftOrigins.handler_erase setup codec route (.inr (.inl query)) current) work state

/-- The record world's interpretation of the open program on the joint state (environment state, World state, provenance annotation): `PqxdhDeploymentEnvironmentJoin.worldStep` with the annotated handler. -/
noncomputable def aWorldStep (env : Environment n E) :
    QueryImpl PqxdhDeploymentInterface.Spec (StateT (E × PqxdhRecordLiftOrigins.State n) ProbComp) :=
  ((PqxdhRecordLiftOrigins.handler setup codec route).mapStateTBase (PqxdhRecordLiftInterface.native env)).flattenStateT

/-- One annotated joint step is one native dispatch step interpreted by the annotated World. -/
theorem aWorldStep_run (env : Environment n E) (query : PqxdhDeploymentInterface.Spec.Domain) (e : E)
    (state : PqxdhRecordLiftOrigins.State n) :
    (aWorldStep setup codec route env query).run (e, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
          ((PqxdhRecordLiftInterface.native env query).run e)).run state := rfl

/-- Erasing the annotation of an annotated joint step gives the joint step. -/
theorem aWorldStep_erase {Bk : Type} (env : Environment n (EnvState KemSK Bk))
    (query : PqxdhDeploymentInterface.Spec.Domain) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n)
    (o : Origins n) :
    (fun result => (result.1, (result.2.1, result.2.2.1))) <$> (aWorldStep setup codec route env query).run (e, (w, o)) =
      (worldStep setup codec route env query).run (e, w) := by
  rw [aWorldStep_run, PqxdhDeploymentEnvironmentJoin.worldStep_run, Functor.map_map,
    ← PqxdhRecordLiftOrigins.schedule_erase setup codec route _ (w, o), Functor.map_map]
  rfl

/-- A registration command of the open program is the environment step interpreted by the annotated World. -/
theorem aWorldStep_reg (env : Environment n E) (query : EnvQuery) (e : E) (state : PqxdhRecordLiftOrigins.State n) :
    (aWorldStep setup codec route env (.inr query.val)).run (e, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (aEffects setup codec route) ((env.step query).run e)).run state := by
  rw [aWorldStep_run]
  rcases query with ⟨command, allowed⟩
  cases command
  all_goals first
    | exact absurd allowed id
    | (simp only [PqxdhRecordLiftInterface.native, PqxdhRecordLiftInterface.environmentStep, StateT.run]
       rw [← QueryImpl.simulateQ_compose, aEffects_compose]
       rfl)

/-- A query of the open program that is not a registration command of the environment. -/
def IsFixed : PqxdhDeploymentInterface.Spec.Domain → Prop
  | .inl _ => True
  | .inr (.hash _) => True
  | .inr (.serverSend _ _) => True
  | .inr (.serverRaw _) => True
  | .inr (.beaconSend _ _) => True
  | .inr (.beaconRaw _ _) => True
  | _ => False

/-- A lifted World program without an install or an append issues none on the environment's state either. -/
theorem lift_free {α : Type} (work : OracleComp (WorldSpec n) α)
    (free : work.IsQueryBoundP (fun request => isAnnot request = true) 0) (e : E) :
    ((StateT.lift work : StateT E (OracleComp (WorldSpec n)) α).run e).IsQueryBoundP
      (fun request => isAnnot request = true) 0 := by
  rw [StateT.run_lift]
  exact isQueryBoundP_bind (m := 0) free fun _ _ => isQueryBoundP_pure _ _ _

/-- One World request that is not an install or an append. -/
theorem query_free (request : (WorldSpec n).Domain) (other : isAnnot request = false) :
    (liftM ((WorldSpec n).query request) : OracleComp (WorldSpec n) _).IsQueryBoundP
      (fun request => isAnnot request = true) 0 :=
  (isQueryBoundP_query_iff _ _ _).mpr fun annotating => by simp [other] at annotating

/-- A query that is not a registration command keeps the annotation: the annotated joint step is the joint step with the annotation unchanged. -/
theorem aWorldStep_fixed {Bk : Type} (env : Environment n (EnvState KemSK Bk))
    (query : PqxdhDeploymentInterface.Spec.Domain) (fixed : IsFixed query) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (o : Origins n) :
    (aWorldStep setup codec route env query).run (e, (w, o)) =
      (fun result => (result.1, (result.2.1, (result.2.2, o)))) <$> (worldStep setup codec route env query).run (e, w) := by
  have free : ((PqxdhRecordLiftInterface.native env query).run e).IsQueryBoundP (fun request => isAnnot request = true)
      0 := by
    rcases query with coin | command
    · exact lift_free _ (query_free _ rfl) e
    · cases command <;> simp only [IsFixed] at fixed
      all_goals exact lift_free _ (query_free _ rfl) e
  rw [aWorldStep_run, PqxdhDeploymentEnvironmentJoin.worldStep_run, free_run setup codec route _ free, Functor.map_map,
    Functor.map_map]

end Joint

/-! ### Keeping an invariant on the annotated record world with the ledger -/

section Keeps
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response Bk : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- Every annotated joint step from an admissible joint state (`Good` and the stable predicate `inv`) is admissible: its annotation erases to a joint step (`PqxdhDeploymentEnvironmentJoin.worldStep_keeps`). -/
theorem aWorldStep_good (env : Environment n (EnvState KemSK Bk))
    (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv) (query : PqxdhDeploymentInterface.Spec.Domain) (e : EnvState KemSK Bk)
    (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (good : Good created e w) (holds : inv e w) :
    ∀ result ∈ support ((aWorldStep setup codec route env query).run (e, (w, o))),
      Good created result.2.1 result.2.2.1 ∧ inv result.2.1 result.2.2.1 := by
  intro result member
  have erased : (result.1, (result.2.1, result.2.2.1)) ∈ support ((worldStep setup codec route env query).run (e, w)) := by
    rw [← aWorldStep_erase, support_map]
    exact ⟨result, member, rfl⟩
  exact PqxdhDeploymentEnvironmentJoin.worldStep_keeps setup codec route env reg created inv stable splits query e w good
    holds _ erased

/-- A query that is not a registration command keeps the environment state and the World's fixed view. -/
theorem worldStep_fixedView (env : Environment n (EnvState KemSK Bk)) (query : PqxdhDeploymentInterface.Spec.Domain)
    (fixed : IsFixed query) (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) :
    ∀ result ∈ support ((worldStep setup codec route env query).run (e, w)),
      result.2.1 = e ∧ fixedView result.2.2 = fixedView w := by
  intro result member
  rcases query with coin | command
  · rw [PqxdhDeploymentEnvironmentJoin.worldStep_coin, support_map] at member
    obtain ⟨inner, innerMember, rfl⟩ := member
    exact ⟨rfl, PqxdhDeploymentEnvironmentJoin.effects_view (.inl coin) (Or.inl ⟨coin, rfl⟩) w inner innerMember⟩
  · cases command <;> simp only [IsFixed] at fixed
    case hash bytes =>
      rw [PqxdhDeploymentEnvironmentJoin.worldStep_hash, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact ⟨rfl, PqxdhDeploymentEnvironmentJoin.effects_view (.inr (.hash bytes)) (Or.inr ⟨bytes, rfl⟩) w inner
        innerMember⟩
    case serverSend keyId plaintext =>
      rw [PqxdhDeploymentEnvironmentJoin.worldStep_serverSend, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact ⟨rfl, PqxdhDeploymentEnvironmentJoin.serverStep_view setup codec route _ w inner innerMember⟩
    case serverRaw raw =>
      rw [PqxdhDeploymentEnvironmentJoin.worldStep_serverRaw, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact ⟨rfl, PqxdhDeploymentEnvironmentJoin.serverStep_view setup codec route _ w inner innerMember⟩
    case beaconSend owner plaintext =>
      rw [PqxdhDeploymentEnvironmentJoin.worldStep_beaconSend, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact ⟨rfl, PqxdhDeploymentEnvironmentJoin.beaconStep_view setup codec owner _ w inner innerMember⟩
    case beaconRaw owner raw =>
      rw [PqxdhDeploymentEnvironmentJoin.worldStep_beaconRaw, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact ⟨rfl, PqxdhDeploymentEnvironmentJoin.beaconStep_view setup codec owner _ w inner innerMember⟩

/-- The CE handler's ledger layer over the annotated joint step: one flattened stateful handler on the ledger, the environment state, the World state and the provenance annotation. -/
noncomputable def ledgerStep (env : Environment n (EnvState KemSK Bk)) (crypto : Pqxdh.Crypto) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) :
    QueryImpl PqxdhDeploymentInterface.FullSpec
      (StateT (PqxdhDeploymentSecrecy.Ledger × (EnvState KemSK Bk × PqxdhRecordLiftOrigins.State n)) ProbComp) :=
  ((aWorldStep setup codec route env).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds)).flattenStateT

/-- One step of `ledgerStep`. -/
theorem ledgerStep_run (env : Environment n (EnvState KemSK Bk)) (crypto : Pqxdh.Crypto) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (ledger : PqxdhDeploymentSecrecy.Ledger) (state : EnvState KemSK Bk × PqxdhRecordLiftOrigins.State n) :
    (ledgerStep setup codec route env crypto serverKid bounds query).run (ledger, state) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (aWorldStep setup codec route env)
          ((PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds query).run ledger)).run state := rfl

/-- A transcript entry that is not a registration command of the environment. -/
def QuietEntry (entry : Entry) : Prop :=
  ∀ (query : EnvQuery) (reply : PqxdhRecordLiftInterface.EnvSpec.Range query), entry ≠ ⟨.inl (.inr query.val), reply⟩

/-- A query that sends or draws a coin is not a registration command. -/
theorem coinOrSend_fixed (query : PqxdhDeploymentInterface.Spec.Domain)
    (sent : PqxdhDeploymentSecrecy.coinOrSend query = true) : IsFixed query := by
  rcases query with coin | command
  · trivial
  · cases command <;> simp_all [PqxdhDeploymentSecrecy.coinOrSend, IsFixed]

/-- A program of coins and sends (the secrecy commands' programs) interpreted by the annotated joint step from an admissible joint state keeps the environment state and the annotation, keeps the World's fixed view, stays admissible and returns an outcome of the program. -/
theorem fixed_run (env : Environment n (EnvState KemSK Bk))
    (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv) {α : Type} (work : OracleComp PqxdhDeploymentInterface.Spec α)
    (onlyFixed : work.IsQueryBoundP (fun query => PqxdhDeploymentSecrecy.coinOrSend query = false) 0)
    (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (good : Good created e w)
    (holds : inv e w) :
    ∀ result ∈ support ((simulateQ (aWorldStep setup codec route env) work).run (e, (w, o))),
      result.2.1 = e ∧ result.2.2.2 = o ∧ fixedView result.2.2.1 = fixedView w ∧
        Good created e result.2.2.1 ∧ inv e result.2.2.1 ∧ result.1 ∈ support work := by
  induction work using OracleComp.inductionOn generalizing w with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨rfl, rfl, rfl, good, holds, by simp⟩
  | query_bind query next ih =>
      intro result member
      rw [isQueryBoundP_query_bind_iff] at onlyFixed
      have sent : PqxdhDeploymentSecrecy.coinOrSend query = true := by
        rcases onlyFixed.1 with notFixed | impossible
        · simpa using notFixed
        · exact absurd impossible (Nat.lt_irrefl 0)
      have fixed := coinOrSend_fixed query sent
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, rest⟩ := member
      have admitted := aWorldStep_good setup codec route env reg created inv stable splits query e w o good holds step
        stepMember
      rw [aWorldStep_fixed setup codec route env query fixed e w o, support_map] at stepMember
      obtain ⟨plain, plainMember, rfl⟩ := stepMember
      obtain ⟨same, view⟩ := worldStep_fixedView setup codec route env query fixed e w plain plainMember
      dsimp only at admitted rest
      rw [same] at admitted rest
      have nextFixed := onlyFixed.2 plain.1
      simp only [sent, Bool.true_eq_false, ite_false] at nextFixed
      obtain ⟨sameE, sameO, nextView, nextGood, nextHolds, nextMember⟩ :=
        ih plain.1 nextFixed plain.2.2 admitted.1 admitted.2 result rest
      exact ⟨sameE, sameO, nextView.trans view, nextGood, nextHolds,
        (mem_support_bind_iff _ _ _).mpr ⟨plain.1, mem_support_query query plain.1, nextMember⟩⟩

/-- One step of the ledger layer over the annotated joint step keeps `Good`, the stable predicate `inv` and a relation `R` between the transcript, the environment state, the World state and the provenance annotation, when `R` reads the World only through its fixed view, survives appending an entry that is not a registration command, and is kept by every registration command of the environment interpreted by the annotated World effects (with its entry appended). -/
theorem ledgerStep_keeps (env : Environment n (EnvState KemSK Bk))
    (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv)
    (R : List Entry → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Origins n → Prop)
    (rView : ∀ transcript e w w' o, fixedView w' = fixedView w → R transcript e w o → R transcript e w' o)
    (rQuiet : ∀ transcript e w o (entry : Entry), QuietEntry entry → R transcript e w o → R (transcript ++ [entry]) e w o)
    (rStep : ∀ (query : EnvQuery) transcript e w o, Good created e w → inv e w → R transcript e w o →
      ∀ result ∈ support ((simulateQ (aEffects setup codec route) ((env.step query).run e)).run (w, o)),
        R (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2)
    (crypto : Pqxdh.Crypto) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (state : PqxdhDeploymentSecrecy.Ledger × (EnvState KemSK Bk × PqxdhRecordLiftOrigins.State n))
    (holds : Good created state.2.1 state.2.2.1 ∧ inv state.2.1 state.2.2.1 ∧
      R state.1.transcript state.2.1 state.2.2.1 state.2.2.2) :
    ∀ result ∈ support ((ledgerStep setup codec route env crypto serverKid bounds query).run state),
      Good created result.2.2.1 result.2.2.2.1 ∧ inv result.2.2.1 result.2.2.2.1 ∧
        R result.2.1.transcript result.2.2.1 result.2.2.2.1 result.2.2.2.2 := by
  rcases state with ⟨ledger, e, w, o⟩
  obtain ⟨good, invHolds, rHolds⟩ := holds
  intro result member
  rw [ledgerStep_run, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at innerMember
    obtain ⟨answer, answerMember, rfl⟩ := innerMember
    have admitted := aWorldStep_good setup codec route env reg created inv stable splits request e w o good invHolds
      answer answerMember
    have fixedCase : IsFixed request → R (ledger.record (.inl request) answer.1).transcript answer.2.1 answer.2.2.1
        answer.2.2.2 := by
      intro fixed
      rw [aWorldStep_fixed setup codec route env request fixed e w o, support_map] at answerMember
      obtain ⟨plain, plainMember, rfl⟩ := answerMember
      obtain ⟨same, view⟩ := worldStep_fixedView setup codec route env request fixed e w plain plainMember
      dsimp only
      rw [same]
      refine rQuiet _ _ _ _ _ (fun command reply equal => ?_) (rView _ _ _ _ _ view rHolds)
      have queries := congrArg Entry.query equal
      simp only [Sum.inl.injEq] at queries
      subst queries
      rcases command with ⟨command, allowed⟩
      cases command <;> first | exact absurd allowed id | exact fixed
    have commandCase : ∀ command : EnvQuery, request = .inr command.val →
        R (ledger.record (.inl request) answer.1).transcript answer.2.1 answer.2.2.1 answer.2.2.2 := by
      intro command same
      subst same
      rw [aWorldStep_reg setup codec route env command e (w, o), support_map] at answerMember
      obtain ⟨stepped, steppedMember, rfl⟩ := answerMember
      exact rStep command ledger.transcript e w o good invHolds rHolds stepped steppedMember
    refine ⟨admitted.1, admitted.2, ?_⟩
    rcases request with coin | command
    · exact fixedCase trivial
    · cases command with
      | create pin keyId => exact commandCase ⟨.create pin keyId, trivial⟩ rfl
      | bundle owner => exact commandCase ⟨.bundle owner, trivial⟩ rfl
      | accept raw => exact commandCase ⟨.accept raw, trivial⟩ rfl
      | build session payload => exact commandCase ⟨.build session payload, trivial⟩ rfl
      | finish owner raw => exact commandCase ⟨.finish owner raw, trivial⟩ rfl
      | hmac key message => exact commandCase ⟨.hmac key message, trivial⟩ rfl
      | hash _ => exact fixedCase trivial
      | serverSend _ _ => exact fixedCase trivial
      | serverRaw _ => exact fixedCase trivial
      | beaconSend _ _ => exact fixedCase trivial
      | beaconRaw _ _ => exact fixedCase trivial
  · obtain ⟨same, sameO, view, nextGood, nextHolds, produced⟩ := fixed_run setup codec route env reg created inv stable
      splits _ (PqxdhDeploymentSecrecy.secrecy_frame crypto codec serverKid bounds secrecy ledger) e w o good invHolds
      inner innerMember
    refine ⟨by rw [same]; exact nextGood, by rw [same]; exact nextHolds, ?_⟩
    dsimp only
    rw [PqxdhDeploymentEligibility.ledger_secrecy crypto codec serverKid bounds secrecy ledger inner.1 produced, same,
      sameO]
    refine rQuiet _ _ _ _ _ (fun command reply equal => ?_) (rView _ _ _ _ _ view rHolds)
    have queries := congrArg Entry.query equal
    simp at queries

/-- `run_keeps_origins` (design-v2 section 7.2, items 1 and 4, `ledger_keeps` and `run_keeps_origins` in one statement): every outcome of the CE ledger over the open program, interpreted by the environment and the provenance-annotated World from an admissible joint state, is admissible and satisfies `R` for its final transcript, environment state, World state and annotation, under the obligations of `ledgerStep_keeps`. -/
theorem run_keeps_origins {X : Type} (env : Environment n (EnvState KemSK Bk))
    (reg : PqxdhDeploymentBackend.RegImpl KemSK Bk n) (created : PqxdhLiveServerConstruction.Created Unit)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : Splits created reg env.step inv)
    (R : List Entry → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Origins n → Prop)
    (rView : ∀ transcript e w w' o, fixedView w' = fixedView w → R transcript e w o → R transcript e w' o)
    (rQuiet : ∀ transcript e w o (entry : Entry), QuietEntry entry → R transcript e w o → R (transcript ++ [entry]) e w o)
    (rStep : ∀ (query : EnvQuery) transcript e w o, Good created e w → inv e w → R transcript e w o →
      ∀ result ∈ support ((simulateQ (aEffects setup codec route) ((env.step query).run e)).run (w, o)),
        R (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2)
    (crypto : Pqxdh.Crypto) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (adversary : OracleComp PqxdhDeploymentInterface.FullSpec X) (ledger : PqxdhDeploymentSecrecy.Ledger)
    (e : EnvState KemSK Bk) (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (good : Good created e w)
    (holds : inv e w) (rHolds : R ledger.transcript e w o) :
    ∀ result ∈ support ((simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
        ((simulateQ (PqxdhRecordLiftInterface.native env)
          ((simulateQ (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds) adversary).run ledger)).run
            e)).run (w, o)),
      Good created result.1.2 result.2.1 ∧ inv result.1.2 result.2.1 ∧
        R result.1.1.2.transcript result.1.2 result.2.1 result.2.2 := by
  intro result member
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at member
  obtain ⟨flat, flatMember, rfl⟩ := member
  change flat ∈ support ((simulateQ (aWorldStep setup codec route env)
    ((simulateQ (PqxdhDeploymentSecrecy.ledgerImpl crypto codec serverKid bounds) adversary).run ledger)).run
      (e, (w, o))) at flatMember
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, support_map] at flatMember
  obtain ⟨inner, innerMember, rfl⟩ := flatMember
  exact PqxdhDeploymentEnvironmentJoin.keeps_simulateQ (ledgerStep setup codec route env crypto serverKid bounds)
    (fun state => Good created state.2.1 state.2.2.1 ∧ inv state.2.1 state.2.2.1 ∧
      R state.1.transcript state.2.1 state.2.2.1 state.2.2.2)
    (fun query state both => ledgerStep_keeps setup codec route env reg created inv stable splits R rView rQuiet rStep
      crypto serverKid bounds query state both)
    adversary (ledger, (e, (w, o))) ⟨good, holds, rHolds⟩ inner innerMember

/-- The provenance-annotated record world: the frozen open program interpreted by `PqxdhRecordLiftOrigins.handler` from the initial World and the empty annotation (design-v2 section 7.2, item 5). Erasing the annotation gives `PqxdhRecordLiftWorld.run` (`annotatedRun_erase`). -/
noncomputable def annotatedRun {E X : Type} (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :=
  (simulateQ (PqxdhRecordLiftOrigins.handler setup codec route)
    (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary)).run
      PqxdhRecordLiftOrigins.initial

/-- Erasing the annotation of the provenance-annotated record world gives the record world. -/
theorem annotatedRun_erase {E X : Type} (env : Environment n E) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    Prod.map id Prod.fst <$> annotatedRun setup codec route env serverKid bounds mode adversary =
      PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary :=
  PqxdhRecordLiftOrigins.schedule_erase setup codec route _ PqxdhRecordLiftOrigins.initial

/-- Every outcome of the provenance-annotated record world with an environment whose every startup outcome is a constructed Server with an initial environment state at which the stable predicate `inv` and the relation `R` hold with the initialized fresh World, the empty transcript and the empty annotation, and whose step splits every constructed Server's registration handler relative to `inv` and keeps `R` as in `ledgerStep_keeps`: the final environment state and World are admissible and satisfy `R` with the final transcript and annotation. -/
theorem world_keeps_origins {X : Type} (env : Environment n (EnvState KemSK Bk))
    (reg : PqxdhLiveServerConstruction.Created Unit → PqxdhDeploymentBackend.RegImpl KemSK Bk n)
    (inv : EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Prop) (stable : Stable inv)
    (splits : ∀ created, Splits created (reg created) env.step inv)
    (R : List Entry → EnvState KemSK Bk → PqxdhRecordLiftWorld.State n → Origins n → Prop)
    (rView : ∀ transcript e w w' o, fixedView w' = fixedView w → R transcript e w o → R transcript e w' o)
    (rQuiet : ∀ transcript e w o (entry : Entry), QuietEntry entry → R transcript e w o → R (transcript ++ [entry]) e w o)
    (rStep : ∀ created (query : EnvQuery) transcript e w o, Good created e w → inv e w → R transcript e w o →
      ∀ result ∈ support ((simulateQ (aEffects setup codec route) ((env.step query).run e)).run (w, o)),
        R (transcript ++ [⟨.inl (.inr query.val), result.1.1⟩]) result.1.2 result.2.1 result.2.2)
    (born : ∀ created start, some (created, start) ∈ support env.start →
      ∃ backend, start = PqxdhDeploymentEnvironment.envInitial created backend ∧
        inv start (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := n))) ∧
        R [] start (PqxdhDeploymentEnvironmentJoin.initialized created (PqxdhRecordLiftWorld.initial (n := n)))
          PqxdhRecordLiftOrigins.empty)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    ∀ result ∈ support (annotatedRun setup codec route env serverKid bounds mode adversary),
      ∀ value, result.1 = some value → ∃ created, Good created value.2.2 result.2.1 ∧
        inv value.2.2 result.2.1 ∧ R value.2.1.2.transcript value.2.2 result.2.1 result.2.2 := by
  intro result member value found
  unfold annotatedRun at member
  rw [PqxdhDeploymentEnvironmentDraw.program_rest, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
  obtain ⟨step, stepMember, rest⟩ := member
  have coinsFree : (simulateQ PqxdhRecordLiftInterface.coinLift env.start).IsQueryBoundP
      (fun request => isAnnot request = true) 0 :=
    RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
      (fun coin => by
        simp only [ite_false]
        exact query_free (n := n) (.inr (.inl (.inl coin))) rfl)
  have init : (PqxdhRecordLiftOrigins.initial : PqxdhRecordLiftOrigins.State n) =
      (PqxdhRecordLiftWorld.initial, PqxdhRecordLiftOrigins.empty) := rfl
  rw [init, free_run setup codec route _ coinsFree, support_map] at stepMember
  obtain ⟨plain, plainMember, rfl⟩ := stepMember
  have counted := PqxdhDeploymentEnvironmentJoin.coins_world setup codec route env.start
    (PqxdhRecordLiftWorld.initial (n := n))
  have inMapped : Prod.map id PqxdhDeploymentEnvironmentJoin.uncount plain ∈ support (Prod.map id
      PqxdhDeploymentEnvironmentJoin.uncount <$> (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        (simulateQ PqxdhRecordLiftInterface.coinLift env.start)).run (PqxdhRecordLiftWorld.initial (n := n))) := by
    rw [support_map]
    exact ⟨plain, plainMember, rfl⟩
  rw [counted, support_map] at inMapped
  obtain ⟨startValue, startMember, same⟩ := inMapped
  have started : plain.1 ∈ support env.start := by
    have first := congrArg Prod.fst same
    simp only [Prod.map_fst, id_eq] at first
    rw [← first]
    exact startMember
  have fresh : PqxdhDeploymentEnvironmentJoin.uncount plain.2 =
      PqxdhDeploymentEnvironmentJoin.uncount (PqxdhRecordLiftWorld.initial (n := n)) := by
    have second := congrArg Prod.snd same
    simp only [Prod.map_snd] at second
    exact second.symm
  rcases plain with ⟨_ | ⟨created, start⟩, w⟩
  · simp only [PqxdhDeploymentEnvironmentDraw.worldRest, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at rest
    subst rest
    cases found
  · obtain ⟨backend, rfl, holds, rHolds⟩ := born created _ started
    have vacant : w.server = none := congrArg PqxdhRecordLiftWorld.State.server fresh
    have initRun : (PqxdhRecordLiftOrigins.handler setup codec route (.inl created)).run (w, PqxdhRecordLiftOrigins.empty) =
        pure ((), (PqxdhDeploymentEnvironmentJoin.initialized created w, PqxdhRecordLiftOrigins.empty)) := by
      rw [handler_other setup codec route _ _ rfl]
      change (fun result => (result.1, (result.2, PqxdhRecordLiftOrigins.empty))) <$>
        PqxdhRecordLiftWorld.initializeServer created w = _
      simp only [PqxdhRecordLiftWorld.initializeServer, vacant]
      rfl
    dsimp only [PqxdhDeploymentEnvironmentDraw.worldRest] at rest
    rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, initRun, pure_bind, simulateQ_bind, StateT.run_bind,
      mem_support_bind_iff] at rest
    obtain ⟨middle, middleMember, final⟩ := rest
    rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at final
    subst final
    simp only [Option.some.injEq] at found
    subst found
    have view := PqxdhDeploymentEnvironmentJoin.initialized_view created w fresh
    exact ⟨created, run_keeps_origins setup codec route env (reg created) created inv stable (splits created) R rView
      rQuiet (rStep created) setup.source.crypto serverKid bounds _ PqxdhDeploymentSecrecy.Ledger.empty _ _ _
      (PqxdhDeploymentEnvironmentJoin.good_initial created backend w fresh) (stable _ _ _ view holds)
      (rView _ _ _ _ _ view rHolds) middle middleMember⟩

end Keeps

/-! ### The annotation invariant of the World -/

section Invariant
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- A hidden install request, at any number of slots. -/
def hiddenEffect : (EnvEffects n).Domain → Bool
  | .inr (.installServer _ _ (.hidden _)) => true
  | .inr (.installBeacon _ _ (.hidden _)) => true
  | _ => false

/-- Every hidden origin is at a handle the World holds: a Server peer present at its key ID, an established owner. -/
def Present (w : PqxdhRecordLiftWorld.State n) (o : Origins n) : Prop :=
  (∀ keyId slot, o.peers keyId = some slot →
    ∃ server, w.server = some server ∧ (server.records.server.peers keyId).isSome = true) ∧
  (∀ owner slot, o.owners owner = some slot → ∃ shell kernel, w.owners[owner]? = some (.established shell kernel))

/-- Every used slot role has a hidden origin. -/
def Covered (w : PqxdhRecordLiftWorld.State n) (o : Origins n) : Prop :=
  (∀ slot, w.used slot .server = true → ∃ keyId, o.peers keyId = some slot) ∧
  (∀ slot, w.used slot .beacon = true → ∃ owner, o.owners owner = some slot)

/-- The annotation invariant: the hidden origins are at present handles (`Present`), every used marker has an origin (`Covered`), and every origin's marker is used (`PqxdhRecordLiftOrigins.Marked`). -/
structure AnnInv (w : PqxdhRecordLiftWorld.State n) (o : Origins n) : Prop where
  present : Present w o
  covered : Covered w o
  marked : PqxdhRecordLiftOrigins.Marked (w, o)

/-- The annotation invariant holds for the initial World and the empty annotation. -/
theorem annInv_initial : AnnInv (PqxdhRecordLiftWorld.initial (n := n)) PqxdhRecordLiftOrigins.empty := by
  refine ⟨⟨fun _ _ found => ?_, fun _ _ found => ?_⟩, ⟨fun _ found => ?_, fun _ found => ?_⟩,
    ⟨fun _ _ found => ?_, fun _ _ found => ?_⟩⟩ <;>
    simp [PqxdhRecordLiftOrigins.empty, PqxdhRecordLiftWorld.initial] at found

/-- One annotated World effect: the World's effect, then the annotation of its reply. -/
theorem aEffects_run (query : (EnvEffects n).Domain) (state : PqxdhRecordLiftOrigins.State n) :
    (aEffects setup codec route query).run state =
      (fun result => (result.1, (result.2, annotate (.inr (.inl query)) result.1 state.2))) <$>
        (PqxdhRecordLiftWorld.effects query).run state.1 := by
  simp only [aEffects, PqxdhRecordLiftOrigins.handler, PqxdhRecordLiftWorld.handler, StateT.run, bind_pure_comp]
  rfl

/-- A World step that keeps the Server, the owners and the used markers keeps the annotation invariant. -/
theorem annInv_same (w w' : PqxdhRecordLiftWorld.State n) (o : Origins n) (server : w'.server = w.server)
    (owners : w'.owners = w.owners) (used : w'.used = w.used) (holds : AnnInv w o) : AnnInv w' o := by
  obtain ⟨⟨peers, owned⟩, ⟨coveredServer, coveredBeacon⟩, ⟨markedServer, markedBeacon⟩⟩ := holds
  refine ⟨⟨fun keyId slot found => ?_, fun owner slot found => ?_⟩, ⟨fun slot u => ?_, fun slot u => ?_⟩,
    ⟨fun keyId slot found => ?_, fun owner slot found => ?_⟩⟩
  · rw [server]; exact peers keyId slot found
  · rw [owners]; exact owned owner slot found
  · rw [used] at u; exact coveredServer slot u
  · rw [used] at u; exact coveredBeacon slot u
  · change w'.used slot .server = true; rw [used]; exact markedServer keyId slot found
  · change w'.used slot .beacon = true; rw [used]; exact markedBeacon owner slot found

/-- The annotation invariant reads the World only through its fixed view. -/
theorem annInv_view (w w' : PqxdhRecordLiftWorld.State n) (o : Origins n) (view : fixedView w' = fixedView w)
    (holds : AnnInv w o) : AnnInv w' o := by
  have used : w'.used = w.used := congrArg Prod.fst view
  have servers := congrArg (fun v => v.2.2.1) view
  have owners := congrArg (fun v => v.2.2.2) view
  dsimp only [fixedView] at servers owners
  obtain ⟨⟨peers, owned⟩, ⟨coveredServer, coveredBeacon⟩, ⟨markedServer, markedBeacon⟩⟩ := holds
  refine ⟨⟨fun keyId slot found => ?_, fun owner slot found => ?_⟩, ⟨fun slot u => ?_, fun slot u => ?_⟩,
    ⟨fun keyId slot found => ?_, fun owner slot found => ?_⟩⟩
  · obtain ⟨server, present, isSome⟩ := peers keyId slot found
    rw [present] at servers
    rcases present' : w'.server with _ | server'
    · rw [present'] at servers; cases servers
    · rw [present'] at servers
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at servers
      have atKey := congrFun servers.2.2 keyId
      refine ⟨server', rfl, ?_⟩
      rcases hpeer : server'.records.server.peers keyId with _ | peer
      · rw [hpeer] at atKey
        rcases hold : server.records.server.peers keyId with _ | peer
        · rw [hold] at isSome; cases isSome
        · rw [hold] at atKey; cases atKey
      · rfl
  · obtain ⟨shell, kernel, phase⟩ := owned owner slot found
    have atOwner := congrArg (fun list => list[owner]?) owners
    simp only [List.getElem?_map, phase, Option.map_some] at atOwner
    rcases hphase : w'.owners[owner]? with _ | phase'
    · rw [hphase] at atOwner; cases atOwner
    · rw [hphase, Option.map_some, Option.some.injEq] at atOwner
      cases phase' with
      | inactive tag => simp [PqxdhDeploymentEnvironmentJoin.stripPhase] at atOwner
      | established shell' kernel' => exact ⟨shell', kernel', rfl⟩
  · rw [used] at u; exact coveredServer slot u
  · rw [used] at u; exact coveredBeacon slot u
  · change w'.used slot .server = true; rw [used]; exact markedServer keyId slot found
  · change w'.used slot .beacon = true; rw [used]; exact markedBeacon owner slot found

open PqxdhRecordLiftInterface (KernelRef BeaconShell Role) in
/-- Setting one marker: the marker of a slot and role after `PqxdhRecordLiftWorld.markUsed` at a hidden slot. -/
theorem update_used (used : PqxdhRecordLiftInterface.Slot n → Role → Bool) (j slot : PqxdhRecordLiftInterface.Slot n)
    (role role' : Role) :
    Function.update used j (Function.update (used j) role true) slot role' = true ↔
      (slot = j ∧ role' = role) ∨ used slot role' = true := by
  by_cases same : slot = j
  · subst same
    by_cases sameRole : role' = role
    · subst sameRole; simp
    · simp [sameRole]
  · simp [same]

open PqxdhRecordLiftInterface (KernelRef BeaconShell) in
/-- A Server install keeps the annotation invariant with its reply annotated, and a known install keeps the annotation. -/
theorem installServer_annInv (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (holds : AnnInv w o) :
    ∀ result ∈ support ((PqxdhRecordLiftWorld.installServer keyId identity ref).run w),
      AnnInv result.2 (annotate (.inr (.inl (.inr (.installServer keyId identity ref)))) result.1 o) ∧
        ((∀ slot, ref ≠ .hidden slot) →
          annotate (.inr (.inl (.inr (.installServer keyId identity ref)))) result.1 o = o) := by
  intro result member
  by_cases admitted : PqxdhRecordLiftWorld.ServerVacant w keyId ∧ PqxdhRecordLiftWorld.Unused w .server ref
  · obtain ⟨⟨server, found, vacant⟩, unused⟩ := admitted
    have empty : o.peers keyId = none := by
      rcases hpeer : o.peers keyId with _ | slot
      · rfl
      · obtain ⟨server', found', isSome⟩ := holds.present.1 keyId slot hpeer
        rw [found] at found'
        cases found'
        rw [vacant] at isSome
        cases isSome
    simp only [PqxdhRecordLiftWorld.installServer, StateT.run, found, ite_eq_left (And.intro vacant unused),
      bind_pure_comp, support_map] at member
    obtain ⟨resolved, resolvedMember, rfl⟩ := member
    obtain ⟨⟨peers, owned⟩, ⟨coveredServer, coveredBeacon⟩, ⟨markedServer, markedBeacon⟩⟩ := holds
    cases ref with
    | known kernel =>
        simp only [PqxdhRecordLiftWorld.resolve] at resolvedMember
        subst resolvedMember
        have same : annotate (.inr (.inl (.inr (.installServer keyId identity (.known kernel))))) true o = o := by
          simp only [annotate, ite_true, PqxdhRecordLiftOrigins.origin]
          rw [← empty, Function.update_eq_self]
        refine ⟨?_, fun _ => same⟩
        rw [same]
        refine ⟨⟨fun kid slot hpeer => ?_, fun owner slot hown => owned owner slot hown⟩,
          ⟨coveredServer, coveredBeacon⟩, ⟨markedServer, markedBeacon⟩⟩
        refine ⟨_, rfl, ?_⟩
        by_cases at_ : kid = keyId
        · subst at_; simp
        · obtain ⟨server', found', isSome⟩ := peers kid slot hpeer
          rw [found] at found'
          cases found'
          simpa [Function.update_of_ne at_] using isSome
    | hidden j =>
        obtain ⟨_, _, _, _, usedEq, serverEq, ownersEq, _⟩ :=
          PqxdhRecordLiftWorld.resolve_hidden_facts .server j w resolved resolvedMember
        refine ⟨?_, fun never => absurd rfl (never j)⟩
        simp only [annotate, ite_true, PqxdhRecordLiftOrigins.origin]
        refine ⟨⟨fun kid slot hpeer => ?_, fun owner slot hown => ?_⟩, ⟨fun slot u => ?_, fun slot u => ?_⟩,
          ⟨fun kid slot hpeer => ?_, fun owner slot hown => ?_⟩⟩
        · refine ⟨_, rfl, ?_⟩
          by_cases at_ : kid = keyId
          · subst at_; simp
          · simp only [Function.update_of_ne at_] at hpeer
            obtain ⟨server', found', isSome⟩ := peers kid slot hpeer
            rw [found] at found'
            cases found'
            simpa [Function.update_of_ne at_] using isSome
        · obtain ⟨shell, kernel, phase⟩ := owned owner slot hown
          exact ⟨shell, kernel, by simp only [PqxdhRecordLiftWorld.markUsed]; rw [ownersEq]; exact phase⟩
        · simp only [PqxdhRecordLiftWorld.markUsed, usedEq] at u
          rcases (update_used w.used j slot .server .server).mp u with ⟨rfl, -⟩ | old
          · exact ⟨keyId, by simp⟩
          · obtain ⟨kid, hpeer⟩ := coveredServer slot old
            have ne : kid ≠ keyId := fun same => by rw [same, empty] at hpeer; cases hpeer
            exact ⟨kid, by simpa [Function.update_of_ne ne] using hpeer⟩
        · simp only [PqxdhRecordLiftWorld.markUsed, usedEq] at u
          rcases (update_used w.used j slot .server .beacon).mp u with ⟨-, wrong⟩ | old
          · cases wrong
          · exact coveredBeacon slot old
        · change (PqxdhRecordLiftWorld.markUsed resolved.2 .server (.hidden j)).used slot .server = true
          simp only [PqxdhRecordLiftWorld.markUsed, usedEq]
          by_cases at_ : kid = keyId
          · subst at_
            simp only [Function.update_self, Option.some.injEq] at hpeer
            exact (update_used w.used j slot .server .server).mpr (Or.inl ⟨hpeer.symm, rfl⟩)
          · simp only [Function.update_of_ne at_] at hpeer
            exact (update_used w.used j slot .server .server).mpr (Or.inr (markedServer kid slot hpeer))
        · change (PqxdhRecordLiftWorld.markUsed resolved.2 .server (.hidden j)).used slot .beacon = true
          simp only [PqxdhRecordLiftWorld.markUsed, usedEq]
          exact (update_used w.used j slot .server .beacon).mpr (Or.inr (markedBeacon owner slot hown))
  · rw [PqxdhRecordLiftWorld.installServer_refused keyId identity ref w admitted, support_pure,
      Set.mem_singleton_iff] at member
    subst member
    have same : annotate (.inr (.inl (.inr (.installServer keyId identity ref)))) false o = o := by
      simp [annotate]
    exact ⟨by rw [same]; exact holds, fun _ => same⟩

open PqxdhRecordLiftInterface (KernelRef BeaconShell) in
/-- A Beacon install keeps the annotation invariant with its reply annotated, and a known install keeps the annotation. -/
theorem installBeacon_annInv (owner : ℕ) (shell : BeaconShell) (ref : KernelRef n)
    (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (holds : AnnInv w o) :
    ∀ result ∈ support ((PqxdhRecordLiftWorld.installBeacon owner shell ref).run w),
      AnnInv result.2 (annotate (.inr (.inl (.inr (.installBeacon owner shell ref)))) result.1 o) ∧
        ((∀ slot, ref ≠ .hidden slot) →
          annotate (.inr (.inl (.inr (.installBeacon owner shell ref)))) result.1 o = o) := by
  intro result member
  by_cases admitted : PqxdhRecordLiftWorld.BeaconReady w owner ∧ PqxdhRecordLiftWorld.Unused w .beacon ref
  · obtain ⟨ready, unused⟩ := admitted
    have empty : o.owners owner = none := by
      rcases hown : o.owners owner with _ | slot
      · rfl
      · obtain ⟨_, _, phase⟩ := holds.present.2 owner slot hown
        rw [PqxdhRecordLiftWorld.BeaconReady] at ready
        rw [ready] at phase
        cases phase
    have inside : owner < w.owners.length := by
      rw [PqxdhRecordLiftWorld.BeaconReady] at ready
      exact (List.getElem?_eq_some_iff.mp ready).1
    simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run, ite_eq_left (And.intro ready unused),
      bind_pure_comp, support_map] at member
    obtain ⟨resolved, resolvedMember, rfl⟩ := member
    obtain ⟨⟨peers, owned⟩, ⟨coveredServer, coveredBeacon⟩, ⟨markedServer, markedBeacon⟩⟩ := holds
    cases ref with
    | known kernel =>
        simp only [PqxdhRecordLiftWorld.resolve] at resolvedMember
        subst resolvedMember
        have same : annotate (.inr (.inl (.inr (.installBeacon owner shell (.known kernel))))) true o = o := by
          simp only [annotate, ite_true, PqxdhRecordLiftOrigins.origin]
          rw [← empty, Function.update_eq_self]
        refine ⟨?_, fun _ => same⟩
        rw [same]
        refine ⟨⟨fun kid slot hpeer => peers kid slot hpeer, fun x slot hown => ?_⟩,
          ⟨coveredServer, coveredBeacon⟩, ⟨markedServer, markedBeacon⟩⟩
        have ne : x ≠ owner := fun same => by rw [same, empty] at hown; cases hown
        obtain ⟨shell', kernel', phase⟩ := owned x slot hown
        exact ⟨shell', kernel', by simpa [List.getElem?_set_ne (Ne.symm ne)] using phase⟩
    | hidden j =>
        obtain ⟨_, _, _, _, usedEq, serverEq, ownersEq, _⟩ :=
          PqxdhRecordLiftWorld.resolve_hidden_facts .beacon j w resolved resolvedMember
        refine ⟨?_, fun never => absurd rfl (never j)⟩
        simp only [annotate, ite_true, PqxdhRecordLiftOrigins.origin]
        refine ⟨⟨fun kid slot hpeer => ?_, fun x slot hown => ?_⟩, ⟨fun slot u => ?_, fun slot u => ?_⟩,
          ⟨fun kid slot hpeer => ?_, fun x slot hown => ?_⟩⟩
        · obtain ⟨server, found, isSome⟩ := peers kid slot hpeer
          exact ⟨server, by simp only [PqxdhRecordLiftWorld.markUsed]; rw [serverEq]; exact found, isSome⟩
        · by_cases at_ : x = owner
          · subst at_
            exact ⟨shell, resolved.1, by simp [List.getElem?_set_self inside]⟩
          · simp only [Function.update_of_ne at_] at hown
            obtain ⟨shell', kernel', phase⟩ := owned x slot hown
            exact ⟨shell', kernel', by simpa [List.getElem?_set_ne (Ne.symm at_)] using phase⟩
        · simp only [PqxdhRecordLiftWorld.markUsed, usedEq] at u
          rcases (update_used w.used j slot .beacon .server).mp u with ⟨-, wrong⟩ | old
          · cases wrong
          · exact coveredServer slot old
        · simp only [PqxdhRecordLiftWorld.markUsed, usedEq] at u
          rcases (update_used w.used j slot .beacon .beacon).mp u with ⟨rfl, -⟩ | old
          · exact ⟨owner, by simp⟩
          · obtain ⟨x, hown⟩ := coveredBeacon slot old
            have ne : x ≠ owner := fun same => by rw [same, empty] at hown; cases hown
            exact ⟨x, by simpa [Function.update_of_ne ne] using hown⟩
        · change (PqxdhRecordLiftWorld.markUsed resolved.2 .beacon (.hidden j)).used slot .server = true
          simp only [PqxdhRecordLiftWorld.markUsed, usedEq]
          exact (update_used w.used j slot .beacon .server).mpr (Or.inr (markedServer kid slot hpeer))
        · change (PqxdhRecordLiftWorld.markUsed resolved.2 .beacon (.hidden j)).used slot .beacon = true
          simp only [PqxdhRecordLiftWorld.markUsed, usedEq]
          by_cases at_ : x = owner
          · subst at_
            simp only [Function.update_self, Option.some.injEq] at hown
            exact (update_used w.used j slot .beacon .beacon).mpr (Or.inl ⟨hown.symm, rfl⟩)
          · simp only [Function.update_of_ne at_] at hown
            exact (update_used w.used j slot .beacon .beacon).mpr (Or.inr (markedBeacon x slot hown))
  · rw [PqxdhRecordLiftWorld.installBeacon_refused owner shell ref w admitted, support_pure,
      Set.mem_singleton_iff] at member
    subst member
    have same : annotate (.inr (.inl (.inr (.installBeacon owner shell ref)))) false o = o := by
      simp [annotate]
    exact ⟨by rw [same]; exact holds, fun _ => same⟩

/-- Every annotated World effect keeps the annotation invariant, and an effect that is not a hidden install keeps the annotation. -/
theorem aEffects_keeps (query : (EnvEffects n).Domain) (w : PqxdhRecordLiftWorld.State n) (o : Origins n)
    (holds : AnnInv w o) :
    ∀ result ∈ support ((aEffects setup codec route query).run (w, o)),
      AnnInv result.2.1 result.2.2 ∧ (hiddenEffect query = false → result.2.2 = o) := by
  intro result member
  rw [aEffects_run, support_map] at member
  obtain ⟨inner, innerMember, rfl⟩ := member
  dsimp only
  rcases query with coin | capability
  · exact ⟨annInv_view w inner.2 o
      (PqxdhDeploymentEnvironmentJoin.effects_view (.inl coin) (Or.inl ⟨coin, rfl⟩) w inner innerMember) holds,
      fun _ => rfl⟩
  · have charged := annInv_same w (PqxdhRecordLiftWorld.chargeEffect (.inr capability) w) o rfl rfl rfl holds
    change inner ∈ support ((PqxdhRecordLiftWorld.capability capability).run
      (PqxdhRecordLiftWorld.chargeEffect (.inr capability) w)) at innerMember
    cases capability with
    | peerPresent keyId =>
        simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        exact ⟨charged, fun _ => rfl⟩
    | ownerPresent owner =>
        simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        exact ⟨charged, fun _ => rfl⟩
    | appendOwner sender identity phase =>
        simp only [PqxdhRecordLiftWorld.capability, StateT.run, support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        have vacant : o.owners w.owners.length = none := by
          rcases hown : o.owners w.owners.length with _ | slot
          · rfl
          · obtain ⟨_, _, found⟩ := holds.present.2 _ slot hown
            simp at found
        have same : annotate (.inr (.inl (.inr (.appendOwner sender identity phase)))) w.owners.length o = o := by
          simp only [annotate]
          rw [← vacant, Function.update_eq_self]
        refine ⟨?_, fun _ => same⟩
        dsimp only
        change AnnInv _ (annotate (.inr (.inl (.inr (.appendOwner sender identity phase)))) w.owners.length o)
        rw [same]
        obtain ⟨⟨peers, owned⟩, covered, marked⟩ := holds
        refine ⟨⟨peers, fun owner slot hown => ?_⟩, covered, marked⟩
        obtain ⟨shell, kernel, found⟩ := owned owner slot hown
        have inside : owner < w.owners.length := (List.getElem?_eq_some_iff.mp found).1
        exact ⟨shell, kernel, by
          change (w.owners ++ [PqxdhRecordLiftBeacon.Phase.inactive phase])[owner]? = _
          rw [List.getElem?_append_left inside]
          exact found⟩
    | advanceOwner owner phase =>
        simp only [PqxdhRecordLiftWorld.capability, StateT.run] at innerMember
        have kept : annotate (.inr (.inl (.inr (.advanceOwner owner phase)))) inner.1 o = o := rfl
        refine ⟨?_, fun _ => kept⟩
        rw [kept]
        split at innerMember
        · rename_i before found
          split at innerMember
          · simp only [support_pure, Set.mem_singleton_iff] at innerMember
            subst innerMember
            obtain ⟨⟨peers, owned⟩, covered, marked⟩ := holds
            refine ⟨⟨peers, fun x slot hown => ?_⟩, covered, marked⟩
            obtain ⟨shell, kernel, phaseAt⟩ := owned x slot hown
            have ne : x ≠ owner := fun same => by
              subst same
              change w.owners[x]? = _ at found
              rw [found] at phaseAt
              cases phaseAt
            exact ⟨shell, kernel, by
              change (w.owners.set owner (PqxdhRecordLiftBeacon.Phase.inactive phase))[x]? = _
              rw [List.getElem?_set_ne (Ne.symm ne)]
              exact phaseAt⟩
          · simp only [support_pure, Set.mem_singleton_iff] at innerMember
            subst innerMember
            exact charged
        · simp only [support_pure, Set.mem_singleton_iff] at innerMember
          subst innerMember
          exact charged
    | installServer keyId identity ref =>
        obtain ⟨keeps, known⟩ := installServer_annInv keyId identity ref _ o charged inner innerMember
        refine ⟨keeps, fun visible => known fun slot same => ?_⟩
        subst same
        simp [hiddenEffect] at visible
    | installBeacon owner shell ref =>
        obtain ⟨keeps, known⟩ := installBeacon_annInv owner shell ref _ o charged inner innerMember
        refine ⟨keeps, fun visible => known fun slot same => ?_⟩
        subst same
        simp [hiddenEffect] at visible
    | hash bytes =>
        exact ⟨annInv_view w inner.2 o
          (PqxdhDeploymentEnvironmentJoin.effects_view (.inr (.hash bytes)) (Or.inr ⟨bytes, rfl⟩) w inner innerMember)
          holds, fun _ => rfl⟩

/-- Every annotated run of an environment program keeps the annotation invariant, and relates the annotations before and after by a reflexive transitive relation `Rel` when every hidden install it issues is `allowed` and each allowed hidden install relates its annotations by `Rel`. -/
theorem aRun_rel {α : Type} (allowed : (EnvEffects n).Domain → Bool) (Rel : Origins n → Origins n → Prop)
    (refl : ∀ o, Rel o o) (trans : ∀ a b c, Rel a b → Rel b c → Rel a c)
    (step : ∀ query, allowed query = true → ∀ w o, AnnInv w o →
      ∀ result ∈ support ((aEffects setup codec route query).run (w, o)), Rel o result.2.2)
    (work : OracleComp (EnvEffects n) α)
    (bound : work.IsQueryBoundP (fun query => hiddenEffect query = true ∧ allowed query = false) 0)
    (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (holds : AnnInv w o) :
    ∀ result ∈ support ((simulateQ (aEffects setup codec route) work).run (w, o)),
      AnnInv result.2.1 result.2.2 ∧ Rel o result.2.2 := by
  induction work using OracleComp.inductionOn generalizing w o with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨holds, refl o⟩
  | query_bind query next ih =>
      intro result member
      rw [isQueryBoundP_query_bind_iff] at bound
      have first : ¬ (hiddenEffect query = true ∧ allowed query = false) := by
        rcases bound.1 with notBad | impossible
        · exact notBad
        · exact absurd impossible (Nat.lt_irrefl 0)
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, middleMember, rest⟩ := member
      obtain ⟨middleHolds, visible⟩ := aEffects_keeps setup codec route query w o holds middle middleMember
      have related : Rel o middle.2.2 := by
        by_cases hidden : hiddenEffect query = true
        · have permitted : allowed query = true := by
            cases h : allowed query
            · exact absurd ⟨hidden, h⟩ first
            · rfl
          exact step query permitted w o holds middle middleMember
        · rw [visible (by simpa using hidden)]
          exact refl o
      have nextBound := bound.2 middle.1
      simp only [first, ite_false] at nextBound
      obtain ⟨finalHolds, finalRel⟩ := ih middle.1 nextBound middle.2.1 middle.2.2 middleHolds result rest
      exact ⟨finalHolds, trans _ _ _ related finalRel⟩

/-- An annotated run of an environment program without a hidden install keeps the annotation and the annotation invariant. -/
theorem aRun_free {α : Type} (work : OracleComp (EnvEffects n) α)
    (free : work.IsQueryBoundP (fun query => hiddenEffect query = true) 0)
    (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (holds : AnnInv w o) :
    ∀ result ∈ support ((simulateQ (aEffects setup codec route) work).run (w, o)),
      AnnInv result.2.1 result.2.2 ∧ result.2.2 = o := by
  intro result member
  obtain ⟨keeps, same⟩ := aRun_rel setup codec route (fun _ => false) (fun a b => b = a) (fun _ => rfl)
    (fun _ _ _ left right => right.trans left) (fun _ never => by cases never) work
    (IsQueryBoundP.of_imp (fun _ bad => bad.1) free) w o holds result member
  exact ⟨keeps, same⟩

/-- A hidden Beacon install at an owner. -/
def beaconAt (owner : ℕ) : (EnvEffects n).Domain → Bool
  | .inr (.installBeacon index _ (.hidden _)) => decide (index = owner)
  | _ => false

/-- The annotations of a run whose hidden installs are all Beacon installs at one owner: the peers are unchanged, and so is every other owner. -/
def OwnerRel (owner : ℕ) (o o' : Origins n) : Prop :=
  o'.peers = o.peers ∧ ∀ index, index ≠ owner → o'.owners index = o.owners index

/-- An annotated run of an environment program whose hidden installs are all Beacon installs at one owner changes only that owner's origin. -/
theorem aRun_owner {α : Type} (owner : ℕ) (work : OracleComp (EnvEffects n) α)
    (bound : work.IsQueryBoundP (fun query => hiddenEffect query = true ∧ beaconAt owner query = false) 0)
    (w : PqxdhRecordLiftWorld.State n) (o : Origins n) (holds : AnnInv w o) :
    ∀ result ∈ support ((simulateQ (aEffects setup codec route) work).run (w, o)),
      AnnInv result.2.1 result.2.2 ∧ OwnerRel owner o result.2.2 :=
  aRun_rel setup codec route (beaconAt owner) (OwnerRel owner) (fun _ => ⟨rfl, fun _ _ => rfl⟩)
    (fun _ _ _ left right => ⟨right.1.trans left.1, fun index ne => (right.2 index ne).trans (left.2 index ne)⟩)
    (fun query permitted w o _ result member => by
      rcases query with coin | capability
      · simp [beaconAt] at permitted
      · cases capability with
        | installBeacon index shell ref =>
            cases ref with
            | known kernel => simp [beaconAt] at permitted
            | hidden j =>
                simp only [beaconAt, decide_eq_true_eq] at permitted
                subst permitted
                rw [aEffects_run, support_map] at member
                obtain ⟨inner, _, rfl⟩ := member
                dsimp only
                simp only [annotate]
                split
                · exact ⟨rfl, fun other ne => by simp [Function.update_of_ne ne]⟩
                · exact ⟨rfl, fun _ _ => rfl⟩
        | _ => simp [beaconAt] at permitted)
    work bound w o holds

end Invariant

end BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annotate_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annotate_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.handler_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.handler_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.free_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.free_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_compose

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_reg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_reg

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.lift_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.lift_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.query_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.query_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_fixed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aWorldStep_good

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.worldStep_fixedView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.worldStep_fixedView

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.ledgerStep_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.ledgerStep_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.coinOrSend_fixed' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.coinOrSend_fixed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.fixed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.fixed_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.ledgerStep_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.ledgerStep_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.run_keeps_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.run_keeps_origins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annotatedRun_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annotatedRun_erase

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.world_keeps_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.world_keeps_origins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annInv_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annInv_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annInv_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annInv_same

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annInv_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.annInv_view

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.update_used' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.update_used

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.installServer_annInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.installServer_annInv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.installBeacon_annInv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.installBeacon_annInv

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aEffects_keeps

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aRun_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aRun_rel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aRun_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aRun_free

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aRun_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealOrigins.aRun_owner

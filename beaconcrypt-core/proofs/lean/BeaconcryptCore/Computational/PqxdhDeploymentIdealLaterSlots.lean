-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealHandoff
import BeaconcryptCore.Computational.PqxdhDeploymentIdealAnomalyGuesser
import BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds

/-! LQ-F upstream, unit C3: the post-phase slot invariance U-L4 of the CE-12 design (LQ-F upstream design-v2 section 4.2). CE-11b's hand-off restates C5 on the record lift's view of the all-real chain world of the run phase (`PqxdhDeploymentIdealHandoff.ideal_view_slots`: the view's handle-to-slot map satisfies `IdealSlots`, or the transcript has the Beacon-side `Anomaly`). The later record world adds a post phase after the run. This module shows that the post phase of the ideal environment of a target installs no hidden kernel, so the same restatement holds on the later chain world, and that the anomaly has the same probability in the later world as in the run phase.

- Quiet World requests (`QuietQuery`): coin effects and the shared BLAKE2b capability. The compiled record protocol answers them without changing its control state (`handler_quiet`), so every World client that makes only quiet requests compiles to a service program whose every result carries the control it started from (`schedule_quiet`).
- An environment whose HMAC step issues coin effects only (`HmacCoins`) has a quiet post phase: post coins, post BLAKE2b and the HMAC step's coins (`coins_coinEffect`, `effectLift_quiet`, `post_quiet`). The ideal environment of a target answers HMAC with the real HMAC step, which draws coins only (`envGD_hmacCoins`).
- `post_noinstall` (U-L4): under every private interpreter, the compiled post phase of the ideal environment of a target keeps the record control, so in particular the handle-to-slot map (`PqxdhRecordLiftIdeal.handleSlot`) after the post phase is the one after the run phase; `continueWith_noinstall` adds that the E-only continuation `PqxdhRecordLiftLaterWorlds.continueWith` keeps the Server's public data and the run-phase ledger.
- `later_slots`: on every outcome of the all-real later chain world (`PqxdhRecordLiftLaterWorlds.laterRealChains`) with the ideal environment of a target, the view's handle-to-slot map satisfies `IdealSlots` for the run-phase transcript, or that transcript has the Beacon-side `Anomaly` (from `ideal_view_slots` through `laterChains_split` and `continueWith_noinstall`).
- `later_anomaly_eq`: the anomaly has the same probability on the later chain world's view as on the run-phase record world of the first adversary (`PqxdhRecordLiftLater.run_event`), so the run-phase bounds apply: `later_view_slots_le` (every event on the later view is at most the event with `IdealSlots` plus the run-phase anomaly), `later_view_slots_pk` (the anomaly bounded by the ciphertext guess of the explicit anomaly guesser, `PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk`) and `later_view_slots_ct` (by `ctGuess`, `PqxdhDeploymentIdealAnomalyBound.anomaly_le`).

Premises: `Phase1ReadBack` and `Phase2ReadBack` for `later_slots` and the bounds (through `ideal_view_slots` and the anomaly bounds); the rest are support facts and equalities in law without premises. No assumption or contract is added and no security claim is made. LQ-F claims confidentiality only; the post phase is a classical adversary's coin, HMAC and BLAKE2b requests. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhRecordLiftInterface (Environment WorldSpec EnvEffects effectLift)
open PqxdhRecordLiftProtocol (Control ServiceSpec schedule)
open PqxdhRecordLiftLaterWorlds (Outcome continueWith laterRealChains)
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec)
open PqxdhDeploymentLater (PostSpec)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealSteps (SplitBk)
open PqxdhDeploymentIdealEnv (envGD)
open PqxdhDeploymentIdealTrace (IdealSlots Anomaly)

/-! ### Quiet World requests keep the record control -/

section Quiet
variable {n : ℕ}

/-- World requests that the compiled record protocol answers without changing its control: coin effects and the shared BLAKE2b capability. -/
def QuietQuery : (WorldSpec n).Domain → Prop
  | .inr (.inl (.inl _)) => True
  | .inr (.inl (.inr (.hash _))) => True
  | _ => False

/-- Effect requests that are coins. -/
def CoinEffect : (EnvEffects n).Domain → Prop
  | .inl _ => True
  | .inr _ => False

/-- A quiet World request keeps the record control on every outcome of its compiled step. -/
theorem handler_quiet (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (quiet : QuietQuery query) (control : Control n) :
    ∀ result ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run control), result.2 = control := by
  rcases query with created | (request | record)
  · cases quiet
  · rcases request with coin | capability
    · intro result member
      simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift,
        bind_assoc, pure_bind, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
      obtain ⟨_, _, _, _, rfl⟩ := member
      rfl
    · cases capability
      case hash bytes =>
        intro result member
        simp only [PqxdhRecordLiftProtocol.handler, PqxdhRecordLiftProtocol.effects,
          PqxdhRecordLiftProtocol.capability, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, support_bind,
          support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
        obtain ⟨_, _, _, _, rfl⟩ := member
        rfl
      all_goals cases quiet
  · cases quiet

/-- A World client that makes only quiet requests compiles to a service program whose every result carries the control it started from. -/
theorem schedule_quiet {Result : Type} (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (quiet : client.AllQueriesSatisfy QuietQuery) (control : Control n) :
    ∀ result ∈ support (schedule decode route client control), result.2 = control := by
  induction client using OracleComp.inductionOn generalizing control with
  | pure value =>
      intro result member
      simp only [schedule, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      rw [member]
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at quiet
      intro result member
      simp only [schedule, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨middle, middleMember, final⟩ := member
      rw [ih middle.1 (quiet.2 middle.1) middle.2 result final,
        handler_quiet decode route query quiet.1 control middle middleMember]

/-- A registration computation run with its coins as coin effects requests coins only. -/
theorem coins_coinEffect {α : Type} (work : ProbComp α) :
    (PqxdhDeploymentEnvironment.coins (n := n) work).AllQueriesSatisfy CoinEffect := by
  unfold PqxdhDeploymentEnvironment.coins
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhDeploymentEnvironment.coinFx]
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) ih

/-- Lifting coin effects into World requests issues only quiet requests. -/
theorem effectLift_quiet {α : Type} (work : OracleComp (EnvEffects n) α) (coinsOnly : work.AllQueriesSatisfy CoinEffect) :
    (simulateQ effectLift work).AllQueriesSatisfy QuietQuery := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at coinsOnly
      simp only [simulateQ_bind, simulateQ_spec_query, effectLift]
      refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr ?_) fun reply => ih reply (coinsOnly.2 reply)
      rcases query with coin | capability
      · trivial
      · exact coinsOnly.1.elim

/-- An environment whose HMAC step issues coin effects only. -/
def HmacCoins {E : Type} (env : Environment n E) : Prop :=
  ∀ key message state, ((env.step ⟨.hmac key message, trivial⟩).run state).AllQueriesSatisfy CoinEffect

/-- The post phase of an environment whose HMAC step issues coin effects only makes only quiet requests: post coins, post BLAKE2b and the HMAC step's coins. -/
theorem post_quiet {E Out : Type} (env : Environment n E) (hmacCoins : HmacCoins env)
    (adversary : OracleComp PostSpec Out) (state : E) :
    ((PqxdhRecordLiftLater.post env adversary).run state).AllQueriesSatisfy QuietQuery := by
  unfold PqxdhRecordLiftLater.post
  induction adversary using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine allQueriesSatisfy_bind ?_ (fun result => ih result.1 result.2)
      rcases query with coin | (⟨key, message⟩ | bytes)
      · simp only [PqxdhDeploymentLater.postEmbed, simulateQ_spec_query, PqxdhRecordLiftInterface.native,
          PqxdhRecordLiftInterface.coinLift, StateT.run_lift]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => by simp)
      · simp only [PqxdhDeploymentLater.postEmbed, simulateQ_spec_query, PqxdhRecordLiftInterface.native]
        exact effectLift_quiet _ (hmacCoins key message state)
      · simp only [PqxdhDeploymentLater.postEmbed, simulateQ_spec_query, PqxdhRecordLiftInterface.native, effectLift,
          StateT.run_lift]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => by simp)

end Quiet

/-! ### The post phase of the ideal environment installs no hidden kernel -/

section NoInstall
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : ℕ}

/-- The ideal environment of a target answers HMAC with the real HMAC step, which draws coins only. -/
theorem envGD_hmacCoins (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) :
    HmacCoins (envGD setup codec checks t ensureInit identityIndex runtime) := by
  intro key message state
  exact (PqxdhRecordLiftLaterWorlds.allQueries_map _ _ _).mpr
    ((PqxdhRecordLiftLaterWorlds.allQueries_map _ _ _).mpr (coins_coinEffect _))

/-- U-L4, `post_noinstall`: under every private interpreter, the compiled post phase of the ideal environment of a target, from every environment state, control and private state, keeps the record control on every outcome; in particular the handle-to-slot map after the post phase is the one after the run phase. -/
theorem post_noinstall {σ Out : Type} (impl : QueryImpl (ServiceSpec 2) (StateT σ ProbComp)) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (decode : RawCtxReceive.FrameDecoder)
    (route : RawCtxServerRouting.SenderDecoder) (adversary : OracleComp PostSpec Out)
    (state : EnvState KemSK (Params KemSK count × SplitBk)) (control : Control 2) (secret : σ) :
    ∀ result ∈ support ((simulateQ impl (schedule decode route ((PqxdhRecordLiftLater.post
        (envGD setup codec checks t ensureInit identityIndex runtime) adversary).run state) control)).run secret),
      result.1.2 = control := by
  intro result member
  have projected : result.1 ∈ support ((simulateQ impl (schedule decode route ((PqxdhRecordLiftLater.post
      (envGD setup codec checks t ensureInit identityIndex runtime) adversary).run state) control)).run' secret) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, member, rfl⟩
  exact schedule_quiet decode route _ (post_quiet _ (envGD_hmacCoins setup codec checks t ensureInit identityIndex
    runtime) adversary state) control result.1 (OracleComp.support_simulateQ_run'_subset impl _ secret projected)

/-- The E-only continuation of the later chain worlds with the ideal environment of a target keeps the record control, the Server's public data and the run-phase ledger on every outcome; a failed startup stays failed. -/
theorem continueWith_noinstall {σ X Out R : Type} (impl : QueryImpl (ServiceSpec 2) (StateT σ ProbComp))
    (route : RawCtxServerRouting.SenderDecoder) (t : Target count) (ensureInit : StateT A ProbComp Bool)
    (identityIndex : ℕ) (runtime : A) (reveal : EnvState KemSK (Params KemSK count × SplitBk) → R)
    (second : X → R → OracleComp PostSpec Out)
    (result : (Outcome (EnvState KemSK (Params KemSK count × SplitBk)) X × Control 2) × σ) :
    ∀ later ∈ support (continueWith impl codec route (envGD setup codec checks t ensureInit identityIndex runtime)
        reveal second result),
      later.1.2 = result.1.2 ∧
        later.1.1.map (fun value => (value.1, value.2.1.2)) = result.1.1.map (fun value => (value.1, value.2.1.2)) := by
  rcases result with ⟨⟨_ | ⟨created, ⟨output, ledger⟩, environment⟩, control⟩, secret⟩
  · intro later member
    simp only [continueWith, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · intro later member
    simp only [continueWith, support_map, Set.mem_image] at member
    obtain ⟨posted, postedMember, rfl⟩ := member
    exact ⟨post_noinstall setup codec checks impl t ensureInit identityIndex runtime codec.frameRead route _ environment
      control secret posted postedMember, rfl⟩

end NoInstall

/-! ### C5 restated on the later chain world -/

section Slots
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X Out R : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- C5 restated on the later chain world (U-L4, `later_slots`): under `Phase1ReadBack` and `Phase2ReadBack`, on every outcome of the all-real later chain world with the ideal environment of a target, for every reveal and post-run adversary, the view's handle-to-slot map satisfies `IdealSlots` for the run-phase transcript, or that transcript has the Beacon-side `Anomaly`. The later world is the run-phase world followed by the E-only continuation (`PqxdhRecordLiftLaterWorlds.laterChains_split`), which keeps the control and the ledger (`continueWith_noinstall`), so `PqxdhDeploymentIdealHandoff.ideal_view_slots` carries over. -/
theorem later_slots (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (reveal : EnvState KemSK (Params KemSK count × SplitBk) → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) :
    ∀ result ∈ support (laterRealChains setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
        setup.serverKeyId bounds mode reveal first second),
      ∀ value, (PqxdhRecordLiftIdeal.chainView result).result = some value →
        IdealSlots setup.source.crypto codec setup.serverKeyId t (PqxdhRecordLiftIdeal.chainView result).slots
            value.2.1.transcript ∨
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.transcript := by
  intro result member value found
  rw [laterRealChains, PqxdhRecordLiftLaterWorlds.laterChains_split, mem_support_bind_iff] at member
  obtain ⟨run, runMember, later⟩ := member
  obtain ⟨controlSame, kept⟩ := continueWith_noinstall setup codec checks _ route t ensureInit identityIndex runtime
    reveal second run result later
  rcases runOutcome : run.1.1 with _ | runValue
  · rw [runOutcome] at kept
    have none : result.1.1 = none := Option.map_eq_none_iff.mp kept
    simp [PqxdhRecordLiftIdeal.chainView, PqxdhRecordLiftIdeal.viewOf, none] at found
  · rw [runOutcome] at kept
    obtain ⟨laterValue, laterFound, laterSame⟩ := Option.map_eq_some_iff.mp kept
    have runFound : (PqxdhRecordLiftIdeal.chainView run).result =
        some (runValue.2.1.1, runValue.2.1.2, runValue.2.2) := by
      simp [PqxdhRecordLiftIdeal.chainView, PqxdhRecordLiftIdeal.viewOf, runOutcome]
    have slots := PqxdhDeploymentIdealHandoff.ideal_view_slots setup codec route checks phase1 phase2 t ensureInit
      identityIndex runtime bounds mode first run runMember _ runFound
    have valueSame : value = (laterValue.2.1.1, laterValue.2.1.2, laterValue.2.2) := by
      simp only [PqxdhRecordLiftIdeal.chainView, PqxdhRecordLiftIdeal.viewOf, laterFound, Option.map_some,
        Option.some.injEq] at found
      exact found.symm
    have ledgerSame : value.2.1 = runValue.2.1.2 := by
      rw [valueSame]
      exact congrArg (fun pair => pair.2) laterSame
    have slotsSame : (PqxdhRecordLiftIdeal.chainView result).slots = (PqxdhRecordLiftIdeal.chainView run).slots := by
      simp only [PqxdhRecordLiftIdeal.chainView, PqxdhRecordLiftIdeal.viewOf, controlSame]
    rw [ledgerSame, slotsSame]
    exact slots

open Classical in
/-- The Beacon-side anomaly has the same probability on the later chain world's view with the ideal environment of a target as on the run-phase record world of the first adversary: the anomaly reads only the run-phase ledger, which the post phase does not change (`PqxdhRecordLiftLater.run_event`). -/
theorem later_anomaly_eq (t : Target count) (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (reveal : EnvState KemSK (Params KemSK count × SplitBk) → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) :
    𝒟[(fun view => decide (∃ value, view.result = some value ∧
        Anomaly setup.source.crypto codec serverKid t value.2.1.transcript)) <$>
      (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
          second)] =
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec serverKid t value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode first] := by
  have later : (fun view => decide (∃ value, view.result = some value ∧
        Anomaly setup.source.crypto codec serverKid t value.2.1.transcript)) <$>
      (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
          second) =
      ((fun observed => decide (∃ value, observed = some value ∧
          Anomaly setup.source.crypto codec serverKid t value.2.1.transcript)) ∘ PqxdhRecordLiftLater.eventView) <$>
        PqxdhRecordLiftLater.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode reveal first second := by
    rw [← PqxdhRecordLiftLaterWorlds.laterReal_source, Functor.map_map, Functor.map_map]
    congr 1
    funext result
    simp only [Function.comp_apply]
    rw [show PqxdhRecordLiftLater.eventView (Prod.map id PqxdhRecordLiftWorldCompiler.world
        (PqxdhRecordLiftProtocol.rejoin result)) = PqxdhRecordLiftLaterWorlds.runEventView result from
        (PqxdhRecordLiftLaterWorlds.runEventView_eq result).symm, decide_eq_decide]
    constructor
    · rintro ⟨value, found, anomaly⟩
      have mapped : result.1.1.map (fun inner => (inner.2.1.1, inner.2.1.2, inner.2.2)) = some value := found
      obtain ⟨inner, innerFound, rfl⟩ := Option.map_eq_some_iff.mp mapped
      exact ⟨(inner.1, inner.2.1.2, result.2.produced, PqxdhRecordLiftProtocol.rawCounters result.1.2),
        by simp [PqxdhRecordLiftLaterWorlds.runEventView, innerFound], anomaly⟩
    · rintro ⟨value, found, anomaly⟩
      have mapped : result.1.1.map (fun inner => (inner.1, inner.2.1.2, result.2.produced,
          PqxdhRecordLiftProtocol.rawCounters result.1.2)) = some value := found
      obtain ⟨inner, innerFound, rfl⟩ := Option.map_eq_some_iff.mp mapped
      exact ⟨(inner.2.1.1, inner.2.1.2, inner.2.2),
        by simp [PqxdhRecordLiftIdeal.chainView, PqxdhRecordLiftIdeal.viewOf, innerFound], anomaly⟩
  have run : ((fun observed => decide (∃ value, observed = some value ∧
        Anomaly setup.source.crypto codec serverKid t value.2.1.transcript)) ∘ PqxdhRecordLiftLater.eventView) <$>
      PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
        setup.serverKeyId bounds mode first =
      (fun result => decide (∃ value, result.1 = some value ∧
        Anomaly setup.source.crypto codec serverKid t value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode first := by
    congr 1
    funext result
    rw [Function.comp_apply, decide_eq_decide]
    constructor
    · rintro ⟨value, found, anomaly⟩
      have mapped : result.1.map (fun inner => (inner.1, inner.2.1.2, PqxdhRecordLiftLater.recordView result.2)) =
          some value := found
      obtain ⟨inner, innerFound, rfl⟩ := Option.map_eq_some_iff.mp mapped
      exact ⟨inner, innerFound, anomaly⟩
    · rintro ⟨value, found, anomaly⟩
      exact ⟨(value.1, value.2.1.2, PqxdhRecordLiftLater.recordView result.2),
        by simp [PqxdhRecordLiftLater.eventView, found], anomaly⟩
  rw [later, ← run]
  exact PqxdhRecordLiftLater.run_event setup codec route _ setup.serverKeyId bounds mode reveal first second _

open Classical in
/-- `PqxdhDeploymentIdealHandoff.ideal_world_view_slots`'s split on the later chain world: under `Phase1ReadBack` and `Phase2ReadBack`, for every event `D` of the record lift's view, the probability of `D` on the all-real later chain world with the ideal environment of a target is at most the probability of `D` with `IdealSlots` there plus the probability of the Beacon-side `Anomaly` on the run-phase record world of the first adversary (`later_slots`, `later_anomaly_eq`). -/
theorem later_view_slots_le (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (reveal : EnvState KemSK (Params KemSK count × SplitBk) → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out)
    (decision : PqxdhRecordLiftIdeal.View 2 (EnvState KemSK (Params KemSK count × SplitBk)) Out → Bool) :
    𝒟[decision <$> (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
          second)] {true} ≤
      𝒟[(fun view => decide (decision view = true ∧ ∀ value, view.result = some value →
          IdealSlots setup.source.crypto codec setup.serverKeyId t view.slots value.2.1.transcript)) <$>
        (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
          (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
            second)] {true} +
      𝒟[(fun result => decide (∃ value, result.1 = some value ∧
          Anomaly setup.source.crypto codec setup.serverKeyId t value.2.1.2.transcript)) <$>
        PqxdhRecordLiftWorld.run setup codec route (envGD setup codec checks t ensureInit identityIndex runtime)
          setup.serverKeyId bounds mode first] {true} := by
  rw [← later_anomaly_eq setup codec route checks t ensureInit identityIndex runtime setup.serverKeyId bounds mode reveal
    first second]
  refine Eq.trans_le ?_ (PqxdhDeploymentIdealHandoff.evalDist_le_add _ (fun view => decision view = true) _ _
    fun view member held => ?_)
  · simp only [Bool.decide_eq_true]
  rw [support_map] at member
  obtain ⟨result, resultMember, rfl⟩ := member
  by_cases slotted : ∀ value, (PqxdhRecordLiftIdeal.chainView result).result = some value →
      IdealSlots setup.source.crypto codec setup.serverKeyId t (PqxdhRecordLiftIdeal.chainView result).slots
        value.2.1.transcript
  · exact Or.inl ⟨held, slotted⟩
  · obtain ⟨value, unslotted⟩ := Classical.not_forall.mp slotted
    obtain ⟨found, failed⟩ := Classical.not_imp.mp unslotted
    exact Or.inr ⟨value, found, (later_slots setup codec route checks phase1 phase2 t ensureInit identityIndex runtime
      bounds mode reveal first second result resultMember value found).resolve_left failed⟩

open Classical in
/-- `later_view_slots_le` with the anomaly bounded by the ciphertext guess of the explicit anomaly guesser of the first adversary (`PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk`, the form that CE-12a's predict-then-compare IND-CCA reduction consumes). -/
theorem later_view_slots_pk (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (reveal : EnvState KemSK (Params KemSK count × SplitBk) → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out)
    (decision : PqxdhRecordLiftIdeal.View 2 (EnvState KemSK (Params KemSK count × SplitBk)) Out → Bool) :
    𝒟[decision <$> (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
          second)] {true} ≤
      𝒟[(fun view => decide (decision view = true ∧ ∀ value, view.result = some value →
          IdealSlots setup.source.crypto codec setup.serverKeyId t view.slots value.2.1.transcript)) <$>
        (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
          (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
            second)] {true} +
      PqxdhDeploymentIdealAnomalyGuesser.ctGuessByCca setup
        (PqxdhDeploymentIdealAnomalyGuesser.anomalyGuesser setup codec route checks t ensureInit identityIndex runtime
          bounds mode first) :=
  (later_view_slots_le setup codec route checks phase1 phase2 t ensureInit identityIndex runtime bounds mode reveal first
    second decision).trans (add_le_add le_rfl (PqxdhDeploymentIdealAnomalyGuesser.anomaly_le_pk setup codec route checks
      phase1 phase2 t ensureInit identityIndex runtime setup.serverKeyId bounds mode first))

open Classical in
/-- `later_view_slots_le` with the anomaly bounded by `ctGuess` (`PqxdhDeploymentIdealAnomalyBound.anomaly_le`). -/
theorem later_view_slots_ct (phase1 : PqxdhServerAuthNegativeControl.Phase1ReadBack codec)
    (phase2 : PqxdhServerAuthNegativeControl.Phase2ReadBack codec) (t : Target count)
    (ensureInit : StateT A ProbComp Bool) (identityIndex : ℕ) (runtime : A) (bounds : FreshBounds) (mode : Mode)
    (reveal : EnvState KemSK (Params KemSK count × SplitBk) → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out)
    (decision : PqxdhRecordLiftIdeal.View 2 (EnvState KemSK (Params KemSK count × SplitBk)) Out → Bool) :
    𝒟[decision <$> (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
        (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
          second)] {true} ≤
      𝒟[(fun view => decide (decision view = true ∧ ∀ value, view.result = some value →
          IdealSlots setup.source.crypto codec setup.serverKeyId t view.slots value.2.1.transcript)) <$>
        (PqxdhRecordLiftIdeal.chainView <$> laterRealChains setup codec route
          (envGD setup codec checks t ensureInit identityIndex runtime) setup.serverKeyId bounds mode reveal first
            second)] {true} + PqxdhDeploymentIdealTrace.ctGuess setup :=
  (later_view_slots_le setup codec route checks phase1 phase2 t ensureInit identityIndex runtime bounds mode reveal first
    second decision).trans (add_le_add le_rfl (PqxdhDeploymentIdealAnomalyBound.anomaly_le setup codec route checks
      phase1 phase2 t ensureInit identityIndex runtime setup.serverKeyId bounds mode first))

end Slots

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.handler_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.handler_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.schedule_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.schedule_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.coins_coinEffect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.coins_coinEffect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.effectLift_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.effectLift_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.post_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.post_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.envGD_hmacCoins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.envGD_hmacCoins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.post_noinstall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.post_noinstall

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.continueWith_noinstall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.continueWith_noinstall

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_slots

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_anomaly_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_anomaly_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_view_slots_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_view_slots_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_view_slots_pk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_view_slots_pk

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_view_slots_ct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSlots.later_view_slots_ct

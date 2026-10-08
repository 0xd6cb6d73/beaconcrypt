-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLater
import BeaconcryptCore.Computational.PqxdhRecordLiftIdeal

/-!
# Record-lift later worlds: the two-phase program under every policy and CTX mode (items 4 and 5, stage S6, R6)

**Worlds over an arbitrary World client.** `chainsOf ideal` and `ctxRunOf modes replace` are the chain worlds and the CTX worlds of `PqxdhRecordLiftIdeal` for an arbitrary adaptive World client of the frozen result shape (`Outcome`): the private interpreter of the policy or of the CTX modes over the compiled client `PqxdhRecordLiftProtocol.schedule codec.frameRead route client initialControl`. At the frozen run-phase program they are the run-phase worlds by definition (`chains_eq`, `ctxRun_eq`). `RecordBounded budget client` says that the client makes at most `Budget.sends` joint sends and `Budget.receives` joint raw attempts; the frozen program of an adversary within its budget satisfies it (`program_recordBounded`), and so does the two-phase program, because the post phase makes no record request (`later_recordBounded`, from `PqxdhRecordLiftLater.program_record_bound`).

**The later worlds.** `laterChains ideal`, `laterRealChains`, `laterIdealChains`, `laterCtxRun modes replace`, `laterIdealAuth`, `laterIdealRecords` and `laterRandomRecords` are these worlds at the compiled two-phase program `PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second`: the run phase of `first`, the reveal of the run-final environment state and the generic post phase `second output (reveal state)` through the same environment and the same World handler (decision D1 to D4 unchanged; the ideal worlds are the run-phase ideal interpreters, so every policy and every CTX mode is covered). The all-real later world is the complete two-phase World execution (`laterReal_source`: `PqxdhRecordLiftLater.run`) and gives its CE-shaped observation (`laterReal_game`: `PqxdhRecordLiftLater.game`). Every event of `runEventView` (the Server's public data, the ledger, the produced frames and the raw-attempt counters) has the same law in the all-real later world as in the run-phase real world (`laterReal_event`, through `PqxdhRecordLiftLater.run_event`), so a run-phase fact about an event expressed in this projection, for example a CE-level origin or authentication event of that form, holds unchanged in the later game. The record-lift origin and binding events `UnpublishedAccept`, `UnproducedAccept` and `CrossAccept` of `PqxdhRecordLiftIdeal` are not of that form: they also read `View.slots`, the handle-to-slot map of the final control, which the post phase can extend when the environment installs new peers, so carrying them over would need a slot-monotonicity argument that is not proved here. It is not needed: the later mode makes no origin or authentication claim of its own.

**The policy world followed by the E-only continuation.** For every private interpreter, the compiled two-phase program is the compiled run-phase program followed by `continueWith`, which runs the post phase from the run-final environment state through the same interpreter and keeps the Server's public data and the run-phase ledger (`schedule_split`); so every later chain hybrid is the run-phase hybrid of the same policy followed by the continuation (`laterChains_split`), and every later CTX world the run-phase CTX world of the same modes followed by it (`laterCtxRun_split`). The continuation is E-only: the compiled post phase requests only seed allocation, coins, shared hashes and charges (`post_schedule`, from `post_effects`, `effects_post`, `handler_post`, `schedule_post`), never a chain lookup, a hidden opening or sealing, a caller-known record operation or a publication, so it reads no hidden key, nonce or chain. Hence it is the same under every lookup policy (`continueWith_policy`), and in every CTX mode it is the chain-ideal continuation on the base private state with every CTX key state unchanged (`continueWith_ctx`).

**Contracts.** No theorem of this module has an assumption or contract hypothesis, and no proof step uses a contract of the brief's H-7 list: these are definitional and structural facts. Only inside definitions (structurally) do theorems of this module reach the DH-interface fields `dh_comm`, `xpub_length` and `x25519_length` (through the type of `setup`), `hkdf_length` (through the KDF definitions behind the real chain table) and, for the CTX worlds, `aeadSeal_tag_length` (through the AEAD record-building definitions of the CTX interpreter); per-theorem closure probe. New Claude work; nothing adapted from Codex WIP.
-/

open OracleComp OracleSpec ENNReal CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhDeploymentLater (PostSpec PostBudget)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftProtocol (Service ServiceSpec Control schedule)
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response E X Out R : Type}

/-! ### Worlds over an arbitrary World client -/

/-- The result shape of the frozen run-phase program and of the two-phase program. -/
abbrev Outcome (E X : Type) :=
  Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × (X × PqxdhDeploymentSecrecy.Ledger) × E)

/-- The chain world with selector `ideal` for an arbitrary adaptive World client of the frozen result shape. -/
noncomputable def chainsOf (ideal : Label n → Bool) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) (Outcome E X)) :
    ProbComp (PqxdhRecordLiftProtocol.RunResult n E X) :=
  (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
    (schedule codec.frameRead route client PqxdhRecordLiftProtocol.initialControl)).run
      PqxdhRecordLiftProtocol.initialPrivate

/-- The run-phase chain worlds are `chainsOf` at the frozen program. -/
theorem chains_eq (ideal : Label n → Bool) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    chains ideal setup codec route env serverKid bounds mode adversary =
      chainsOf ideal setup codec route
        (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary) := rfl

/-- The CTX world with key modes `modes` and plaintext map `replace` for an arbitrary adaptive World client. -/
noncomputable def ctxRunOf (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) (Outcome E X)) : ProbComp (PqxdhRecordLiftIdeal.Client n E X × CtxPrivate n) :=
  (simulateQ (ctxInterpreter modes replace setup codec)
    (schedule codec.frameRead route client PqxdhRecordLiftProtocol.initialControl)).run CtxPrivate.initial

/-- The run-phase CTX worlds are `ctxRunOf` at the frozen program. -/
theorem ctxRun_eq (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    ctxRun modes replace setup codec route env serverKid bounds mode adversary =
      ctxRunOf modes replace setup codec route
        (PqxdhRecordLiftInterface.program env setup.source.crypto codec serverKid bounds mode adversary) := rfl

/-- A World client within the record part of a budget: at most `Budget.sends` joint sends and `Budget.receives` joint raw attempts. -/
def RecordBounded {α : Type} (budget : Budget) (client : OracleComp (WorldSpec n) α) : Prop :=
  ∀ kind, client.IsQueryBoundP (PqxdhRecordLiftBudget.WorldRecord kind) (PqxdhRecordLiftBudget.recordBudget budget kind)

/-- The frozen run-phase program of an adversary within its budget is within the record part of the budget. -/
theorem program_recordBounded (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget) (adversary : OracleComp (ModeSpec mode) X)
    (respects : budget.Respects adversary) :
    RecordBounded budget (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode adversary) :=
  PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget adversary respects

/-- The two-phase program of a run-phase adversary within its budget is within the same record budget: the post phase issues no send and no raw attempt. -/
theorem later_recordBounded (env : Environment n E) (crypto : Pqxdh.Crypto) (codec : Codec Reader Response)
    (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (budget : Budget) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : budget.Respects first) :
    RecordBounded budget (PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second) :=
  PqxdhRecordLiftLater.program_record_bound env crypto codec serverKid bounds mode budget reveal first second respects

/-! ### The later worlds -/

section Later
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
  (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)

/-- The later chain hybrid with selector `ideal`: the compiled two-phase program `PqxdhRecordLiftLater.program` under the mixed lookup policy. -/
noncomputable def laterChains (ideal : Label n → Bool) : ProbComp (PqxdhRecordLiftProtocol.RunResult n E Out) :=
  chainsOf ideal setup codec route
    (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)

/-- The later real world: every coordinate real. -/
noncomputable def laterRealChains : ProbComp (PqxdhRecordLiftProtocol.RunResult n E Out) :=
  laterChains setup codec route env serverKid bounds mode reveal first second (fun _ => false)

/-- The later chain-ideal world: every coordinate from the persistent lazy table. -/
noncomputable def laterIdealChains : ProbComp (PqxdhRecordLiftProtocol.RunResult n E Out) :=
  laterChains setup codec route env serverKid bounds mode reveal first second (fun _ => true)

/-- The later CTX world with key modes `modes` and plaintext map `replace`. -/
noncomputable def laterCtxRun (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes) :
    ProbComp (PqxdhRecordLiftIdeal.Client n E Out × CtxPrivate n) :=
  ctxRunOf modes replace setup codec route
    (PqxdhRecordLiftLater.program env setup.source.crypto codec serverKid bounds mode reveal first second)

/-- The later integrity-ideal world: every hidden coordinate in replay mode. -/
noncomputable def laterIdealAuth : ProbComp (PqxdhRecordLiftIdeal.Client n E Out × CtxPrivate n) :=
  laterCtxRun setup codec route env serverKid bounds mode reveal first second (fun _ => .replay) id

/-- The later record-ideal world: replay mode in observation mode O, random mode in observation mode P. -/
noncomputable def laterIdealRecords : ProbComp (PqxdhRecordLiftIdeal.Client n E Out × CtxPrivate n) :=
  laterCtxRun setup codec route env serverKid bounds mode reveal first second (fun _ => recordMode mode) id

/-- The later random-ciphertext world: every hidden coordinate in random mode. -/
noncomputable def laterRandomRecords : ProbComp (PqxdhRecordLiftIdeal.Client n E Out × CtxPrivate n) :=
  laterCtxRun setup codec route env serverKid bounds mode reveal first second (fun _ => .random) id

/-- The all-real later world is the complete two-phase World execution `PqxdhRecordLiftLater.run`. -/
theorem laterReal_source :
    (Prod.map id PqxdhRecordLiftWorldCompiler.world ∘ PqxdhRecordLiftProtocol.rejoin) <$>
      laterRealChains setup codec route env serverKid bounds mode reveal first second =
      PqxdhRecordLiftLater.run setup codec route env serverKid bounds mode reveal first second := by
  rw [laterRealChains, laterChains, chainsOf, PqxdhRecordLiftMixedWorld.policy_real]
  exact PqxdhRecordLiftProtocol.initial_schedule_source setup codec route _

/-- The all-real later world gives the CE-shaped observation `PqxdhRecordLiftLater.game`. -/
theorem laterReal_game :
    PqxdhRecordLiftProtocol.observed <$> laterRealChains setup codec route env serverKid bounds mode reveal first second =
      PqxdhRecordLiftLater.game setup codec route env serverKid bounds mode reveal first second := by
  rw [PqxdhRecordLiftLater.game, ← laterReal_source, Functor.map_map]
  rfl

/-- The run-phase record-event view of a compiled run: the Server's public data, the world-owned ledger, the tagged produced frames and the raw-attempt counters. -/
def runEventView (result : PqxdhRecordLiftProtocol.RunResult n E X) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × PqxdhDeploymentSecrecy.Ledger ×
      List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) × PqxdhRecordLiftWorld.RawCounters) :=
  result.1.1.map fun value => (value.1, value.2.1.2, result.2.produced, PqxdhRecordLiftProtocol.rawCounters result.1.2)

/-- The run-phase record-event view of a compiled run is `PqxdhRecordLiftLater.eventView` of its World projection. -/
theorem runEventView_eq (result : PqxdhRecordLiftProtocol.RunResult n E X) :
    runEventView result = PqxdhRecordLiftLater.eventView
      ((Prod.map id PqxdhRecordLiftWorldCompiler.world ∘ PqxdhRecordLiftProtocol.rejoin) result) := by
  rcases result with ⟨⟨_ | value, control⟩, secret⟩
  · rfl
  · simp only [runEventView, PqxdhRecordLiftLater.eventView, PqxdhRecordLiftLater.recordView, Function.comp_apply,
      Prod.map, id, Option.map_some, PqxdhRecordLiftProtocol.rejoin]
    rw [← PqxdhRecordLiftWorldCompiler.rawCounters_erasure]
    rfl

/-- **Run-phase events carry over.** Every event of `runEventView` (the Server's public data, the ledger, the produced frames and the raw-attempt counters) has the same law in the all-real later world as in the run-phase real world of `first`: the post phase changes none of them (`PqxdhRecordLiftLater.run_event`). A run-phase fact about an event expressed in this projection, for example a CE-level origin or authentication event of that form, therefore holds unchanged in the later game. The record-lift events `UnpublishedAccept`, `UnproducedAccept` and `CrossAccept` are not covered: they also read `View.slots`, which the post phase can extend with new installs, and no slot-monotonicity argument is proved. No later origin or authentication claim is made. -/
theorem laterReal_event
    (event : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × PqxdhDeploymentSecrecy.Ledger ×
      List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) × PqxdhRecordLiftWorld.RawCounters) → Bool) :
    𝒟[(event ∘ runEventView) <$> laterRealChains setup codec route env serverKid bounds mode reveal first second] =
      𝒟[(event ∘ runEventView) <$> realChains setup codec route env serverKid bounds mode first] := by
  have later : (event ∘ runEventView) <$> laterRealChains setup codec route env serverKid bounds mode reveal first second =
      (event ∘ PqxdhRecordLiftLater.eventView) <$>
        PqxdhRecordLiftLater.run setup codec route env serverKid bounds mode reveal first second := by
    rw [← laterReal_source, Functor.map_map]
    congr 1
    funext result
    simp only [Function.comp_apply, runEventView_eq]
  have run : (event ∘ runEventView) <$> realChains setup codec route env serverKid bounds mode first =
      (event ∘ PqxdhRecordLiftLater.eventView) <$>
        PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode first := by
    rw [← PqxdhRecordLiftProtocol.run_source, Functor.map_map, realChains, chains, PqxdhRecordLiftMixedWorld.policy_real]
    congr 1
    funext result
    simp only [Function.comp_apply, runEventView_eq]
  rw [later, run]
  exact PqxdhRecordLiftLater.run_event setup codec route env serverKid bounds mode reveal first second event

/-- In observation mode O the later record-ideal world is the later integrity-ideal world. -/
theorem laterIdealRecords_O (first : OracleComp (ModeSpec .O) X) :
    laterIdealRecords setup codec route env serverKid bounds .O reveal first second =
      laterIdealAuth setup codec route env serverKid bounds .O reveal first second := rfl

/-- In observation mode P the later record-ideal world is the later random-ciphertext world. -/
theorem laterIdealRecords_P (first : OracleComp (ModeSpec .P) X) :
    laterIdealRecords setup codec route env serverKid bounds .P reveal first second =
      laterRandomRecords setup codec route env serverKid bounds .P reveal first second := rfl

end Later

/-! ### The policy world followed by the E-only continuation -/

/-- The E-only continuation: after a run-phase result with environment state, run the post phase of `PqxdhRecordLiftLater.post` from that state through the same private interpreter, keeping the Server's public data and the run-phase ledger; a failed startup stays failed. -/
noncomputable def continueWith {σ : Type} (impl : QueryImpl (ServiceSpec n) (StateT σ ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (reveal : E → R) (second : X → R → OracleComp PostSpec Out)
    (result : (Outcome E X × Control n) × σ) : ProbComp ((Outcome E Out × Control n) × σ) :=
  match result with
  | ((none, control), state) => pure ((none, control), state)
  | ((some (created, (output, ledger), environment), control), state) =>
      (fun later => ((some (created, (later.1.1.1, ledger), later.1.1.2), later.1.2), later.2)) <$>
        (simulateQ impl (schedule codec.frameRead route
          ((PqxdhRecordLiftLater.post env (second output (reveal environment))).run environment) control)).run state

/-- **Split, for every private interpreter.** The compiled two-phase program is the compiled run-phase program of `first` followed by the E-only continuation, from every control and private state. -/
theorem schedule_split {σ : Type} (impl : QueryImpl (ServiceSpec n) (StateT σ ProbComp))
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out) (control : Control n)
    (state : σ) :
    (simulateQ impl (schedule codec.frameRead route
      (PqxdhRecordLiftLater.program env crypto codec serverKid bounds mode reveal first second) control)).run state =
    (simulateQ impl (schedule codec.frameRead route
      (PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode first) control)).run state >>=
        continueWith impl codec route env reveal second := by
  simp only [PqxdhRecordLiftLater.program, schedule, simulateQ_bind, StateT.run_bind]
  apply bind_congr
  rintro ⟨⟨_ | ⟨created, ⟨output, ledger⟩, environment⟩, control'⟩, state'⟩
  · simp [continueWith]
  · simp [continueWith, schedule]

/-- Every later chain hybrid is the run-phase chain hybrid of `first` under the same policy followed by the E-only continuation. -/
theorem laterChains_split (ideal : Label n → Bool) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : E → R) (first : OracleComp (ModeSpec mode) X)
    (second : X → R → OracleComp PostSpec Out) :
    laterChains setup codec route env serverKid bounds mode reveal first second ideal =
      chains ideal setup codec route env serverKid bounds mode first >>=
        continueWith (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
          codec route env reveal second :=
  schedule_split _ _ codec route env serverKid bounds mode reveal first second _ _

/-- Every later CTX world is the run-phase CTX world of `first` in the same key modes followed by the E-only continuation. -/
theorem laterCtxRun_split (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out) :
    laterCtxRun setup codec route env serverKid bounds mode reveal first second modes replace =
      ctxRun modes replace setup codec route env serverKid bounds mode first >>=
        continueWith (ctxInterpreter modes replace setup codec) codec route env reveal second :=
  schedule_split _ _ codec route env serverKid bounds mode reveal first second _ _

/-! ### The continuation is E-only -/

/-- The private services that an E-only continuation can request: seed allocation, coins, shared hashes and charges. No lookup, hidden opening or sealing, caller-known record operation or publication. -/
def PostService : Service n → Prop
  | .allocate _ | .coin _ | .hash _ | .charge _ => True
  | _ => False

/-- World requests that are restricted environment effects (coins and capabilities, including the shared hash). -/
def EffectQuery : (WorldSpec n).Domain → Prop
  | .inr (.inl _) => True
  | _ => False

/-- Lifting restricted effects into World requests issues only effect requests. -/
theorem effectLift_effects {α : Type} (work : OracleComp (EnvEffects n) α) :
    (simulateQ effectLift work).AllQueriesSatisfy EffectQuery := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, effectLift]
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) ih

/-- The post phase of `PqxdhRecordLiftLater.post` issues only restricted environment effects: its coins, its hashes and every effect of the environment's HMAC handler. -/
theorem post_effects (env : Environment n E) (adversary : OracleComp PostSpec Out) (state : E) :
    ((PqxdhRecordLiftLater.post env adversary).run state).AllQueriesSatisfy EffectQuery := by
  unfold PqxdhRecordLiftLater.post
  induction adversary using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine allQueriesSatisfy_bind ?_ (fun result => ih result.1 result.2)
      rcases query with coin | (⟨key, message⟩ | bytes)
      · simp only [PqxdhDeploymentLater.postEmbed, simulateQ_spec_query, native, coinLift, StateT.run_lift]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => by simp)
      · simp only [PqxdhDeploymentLater.postEmbed, simulateQ_spec_query, native]
        exact effectLift_effects _
      · simp only [PqxdhDeploymentLater.postEmbed, simulateQ_spec_query, native, effectLift, StateT.run_lift]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => by simp)

/-- Mapping the result does not change the requests. -/
theorem allQueries_map {κ α β : Type} {spec : OracleSpec κ} (f : α → β) (work : OracleComp spec α) (P : κ → Prop) :
    (f <$> work).AllQueriesSatisfy P ↔ work.AllQueriesSatisfy P := by
  rw [allQueriesSatisfy_def, allQueriesSatisfy_def, isQueryBound_map_iff]

/-- Kernel resolution requests at most one seed allocation. -/
theorem resolve_post (role : Role) (ref : KernelRef n) :
    (PqxdhRecordLiftProtocol.resolve role ref).AllQueriesSatisfy PostService := by
  cases ref with
  | known kernel => simp [PqxdhRecordLiftProtocol.resolve]
  | hidden slot =>
      simp only [PqxdhRecordLiftProtocol.resolve]
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => by simp)

/-- A restricted effect requests only allocation, coin, hash and charge services. -/
theorem effects_post (query : (EnvEffects n).Domain) (control : Control n) :
    ((PqxdhRecordLiftProtocol.effects query).run control).AllQueriesSatisfy PostService := by
  rcases query with coin | capability
  · simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ =>
      allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => by simp))
  · simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    refine allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => ?_)
    cases capability with
    | peerPresent keyId => simp [PqxdhRecordLiftProtocol.capability, StateT.run]
    | ownerPresent owner => simp [PqxdhRecordLiftProtocol.capability, StateT.run]
    | appendOwner sender identity phase => simp [PqxdhRecordLiftProtocol.capability, StateT.run]
    | advanceOwner owner phase =>
        simp only [PqxdhRecordLiftProtocol.capability, StateT.run]
        split
        · split_ifs <;> simp
        · simp
    | installServer keyId identity ref =>
        simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installServer, StateT.run]
        split
        · simp
        · split_ifs
          · exact allQueriesSatisfy_bind (resolve_post _ _) (fun _ => by simp)
          · simp
    | installBeacon owner shell ref =>
        simp only [PqxdhRecordLiftProtocol.capability, PqxdhRecordLiftProtocol.installBeacon, StateT.run]
        split_ifs
        · exact allQueriesSatisfy_bind (resolve_post _ _) (fun _ => by simp)
        · simp
    | hash bytes =>
        simp only [PqxdhRecordLiftProtocol.capability, StateT.run_lift]
        exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr trivial) (fun _ => by simp)

/-- A World request that is a restricted effect requests only allocation, coin, hash and charge services. -/
theorem handler_post (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (effect : EffectQuery query) (control : Control n) :
    ((PqxdhRecordLiftProtocol.handler decode route query).run control).AllQueriesSatisfy PostService := by
  rcases query with created | (request | record)
  · cases effect
  · exact effects_post request control
  · cases effect

/-- A World client that issues only restricted effects compiles to a service program that requests only allocation, coin, hash and charge services. -/
theorem schedule_post {Result : Type} (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (effects : client.AllQueriesSatisfy EffectQuery) (control : Control n) :
    (schedule decode route client control).AllQueriesSatisfy PostService := by
  induction client using OracleComp.inductionOn generalizing control with
  | pure result => simp [schedule]
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at effects
      simp only [schedule, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (handler_post decode route query effects.1 control)
        fun result => ih result.1 (effects.2 result.1) result.2

/-- **The post phase is E-only.** The compiled post phase of every post adversary, from every environment state and control, requests only seed allocation, coins, shared hashes and charges: no chain lookup, no hidden opening or sealing (so no hidden key, nonce or chain is read), no caller-known record operation and no publication. -/
theorem post_schedule (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (adversary : OracleComp PostSpec Out) (state : E) (control : Control n) :
    (schedule decode route ((PqxdhRecordLiftLater.post env adversary).run state) control).AllQueriesSatisfy
      PostService :=
  schedule_post decode route _ (post_effects env adversary state) control

/-- Two implementations that agree on every request a program can make simulate it equally. -/
theorem simulateQ_congr_of_all {κ σ α : Type} {spec : OracleSpec κ} (first second : QueryImpl spec (StateT σ ProbComp))
    (P : κ → Prop) (agree : ∀ query, P query → first query = second query) (work : OracleComp spec α)
    (all : work.AllQueriesSatisfy P) : simulateQ first work = simulateQ second work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at all
      simp only [simulateQ_bind, simulateQ_spec_query, agree query all.1]
      congr 1
      funext reply
      exact ih reply (all.2 reply)

/-- The E-only continuation depends on the private interpreter only through its allocation, coin, hash and charge services. -/
theorem continueWith_congr {σ : Type} (first second : QueryImpl (ServiceSpec n) (StateT σ ProbComp))
    (agree : ∀ query, PostService query → first query = second query) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (reveal : E → R)
    (next : X → R → OracleComp PostSpec Out) :
    continueWith first codec route env reveal next = continueWith second codec route env reveal next := by
  funext result
  rcases result with ⟨⟨_ | ⟨created, ⟨output, ledger⟩, environment⟩, control⟩, state⟩
  · rfl
  · simp only [continueWith]
    rw [simulateQ_congr_of_all first second PostService agree _
      (post_schedule codec.frameRead route env _ environment control)]

/-- Allocation, coin, hash and charge services do not depend on the lookup policy. -/
theorem interpreter_post (ideal other : Label n → Bool) (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : Service n) (post : PostService query) :
    PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec query =
      PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source other) setup codec query := by
  cases query <;> first | rfl | cases post

/-- **One continuation for every policy.** The E-only continuation is the same under every chain lookup policy: the post phase never reads the chain table. -/
theorem continueWith_policy (ideal other : Label n → Bool) (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (reveal : E → R) (next : X → R → OracleComp PostSpec Out) :
    continueWith (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source ideal) setup codec)
        codec route env reveal next =
      continueWith (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftMixedWorld.policy setup.source other) setup codec)
        codec route env reveal next :=
  continueWith_congr _ _ (interpreter_post ideal other setup codec) codec route env reveal next

/-- Simulating through base-state services keeps every CTX key state. -/
theorem simulateQ_onBase {α : Type} (impl : QueryImpl (ServiceSpec n) (StateT (PqxdhRecordLiftProtocol.Private n) ProbComp))
    (work : OracleComp (ServiceSpec n) α) (state : CtxPrivate n) :
    (simulateQ (fun query => onBase (impl query)) work).run state =
      (fun result => (result.1, { state with base := result.2 })) <$> (simulateQ impl work).run state.base := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      have unfolded : (onBase (impl query)).run state =
          (fun result => (result.1, { state with base := result.2 })) <$> (impl query).run state.base := rfl
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, unfolded, bind_map_left, map_bind]
      refine bind_congr fun result => ?_
      rw [ih]

/-- **The CTX continuation.** In every CTX mode and for every plaintext map, the E-only continuation is the chain-ideal world's continuation on the base private state, with every CTX key state unchanged: the post phase makes no keyed CTX request. -/
theorem continueWith_ctx (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (reveal : E → R) (next : X → R → OracleComp PostSpec Out)
    (result : (Outcome E X × Control n) × CtxPrivate n) :
    continueWith (ctxInterpreter modes replace setup codec) codec route env reveal next result =
      (fun later => (later.1, { result.2 with base := later.2 })) <$>
        continueWith (PqxdhRecordLiftProtocol.interpreter (idealPolicy setup) setup codec) codec route env reveal next
          (result.1, result.2.base) := by
  have agree : ∀ query, PostService query → ctxInterpreter modes replace setup codec query =
      (fun query => onBase (PqxdhRecordLiftProtocol.interpreter (idealPolicy setup) setup codec query)) query := by
    intro query post
    cases query <;> first | rfl | cases post
  rw [continueWith_congr _ _ agree]
  rcases result with ⟨⟨_ | ⟨created, ⟨output, ledger⟩, environment⟩, control⟩, state⟩
  · rfl
  · simp only [continueWith, simulateQ_onBase, Functor.map_map]

end BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.chains_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.chains_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.ctxRun_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.ctxRun_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.program_recordBounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.program_recordBounded

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.later_recordBounded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.later_recordBounded

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterReal_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterReal_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterReal_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterReal_game

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.runEventView_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.runEventView_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterReal_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterReal_event

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterIdealRecords_O' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterIdealRecords_O

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterIdealRecords_P' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterIdealRecords_P

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.schedule_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.schedule_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterChains_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterChains_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterCtxRun_split' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.laterCtxRun_split

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.effectLift_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.effectLift_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.post_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.post_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.allQueries_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.allQueries_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.resolve_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.resolve_post

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.effects_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.effects_post

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.handler_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.handler_post

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.schedule_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.schedule_post

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.post_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.post_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.simulateQ_congr_of_all' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.simulateQ_congr_of_all

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.continueWith_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.continueWith_congr

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.interpreter_post' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.interpreter_post

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.continueWith_policy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.continueWith_policy

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.simulateQ_onBase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.simulateQ_onBase

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.continueWith_ctx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLaterWorlds.continueWith_ctx

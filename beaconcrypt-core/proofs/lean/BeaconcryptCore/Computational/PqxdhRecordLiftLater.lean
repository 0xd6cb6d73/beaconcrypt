-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget
import BeaconcryptCore.Computational.PqxdhDeploymentLaterCompile

/-! Generic disclosure continuation through the same environment and World, with a narrow record-view frame, run-phase event equality and additive source costs. Later cryptographic security lifts and CE reveal/source joins remain separate obligations. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core.ratchet.concrete (ConcreteRatchetKernel)
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftLater

open PqxdhRecordLiftInterface
open PqxdhRecordLiftBudget
open PqxdhDeploymentInterface (Mode ModeSpec FreshBounds Budget)
open PqxdhDeploymentLater (PostSpec PostBudget postEmbed postClass)
open PqxdhServerAuthExperiment (Setup Codec)

/-- Continue the same environment through the existing post embedding and native dispatch. -/
def post {n : Nat} {E Out : Type} (env : Environment n E)
    (adversary : OracleComp PostSpec Out) : StateT E (OracleComp (WorldSpec n)) Out :=
  simulateQ (native env) (simulateQ postEmbed adversary)

/-- The reveal is computed from run-final environment state. Created metadata and the run ledger are retained. -/
noncomputable def program {n : Nat} {E X Out R Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out) :
    OracleComp (WorldSpec n) (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E)) := do
  let run ← PqxdhRecordLiftInterface.program env crypto codec serverKid bounds mode first
  match run with
  | none => pure none
  | some (created, (output, ledger), state) => do
      let later ← (post env (second output (reveal state))).run state
      pure (some (created, (later.1, ledger), later.2))

/-- Execute both phases through the same complete World handler and shared cache. -/
noncomputable def run {ι KemSK E X Out R Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out) :=
  (simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
    (program env setup.source.crypto codec serverKid bounds mode reveal first second)).run
      PqxdhRecordLiftWorld.initial

/-- The established observable projection excludes hidden seeds, kernels, caches and cost counters. -/
noncomputable def game {ι KemSK E X Out R Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out) :=
  PqxdhRecordLiftWorld.observed <$>
    run setup codec route env serverKid bounds mode reveal first second

/-- The frame needed to carry run-phase record events across the post phase. -/
def recordView {n : Nat} (state : PqxdhRecordLiftWorld.State n) :=
  (state.produced, PqxdhRecordLiftWorld.rawCounters state)

open PqxdhRecordLiftWorld (State)

/-- Server installation can change peer kernels while preserving all record-event coordinates. -/
theorem install_server_view {n : Nat} (keyId : Std.U64) (identity : RawCtxServerRouting.Identity)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.installServer keyId identity ref).run state)) :
    recordView result.2 = recordView state := by
  cases server : state.server
  case some current =>
    simp only [PqxdhRecordLiftWorld.installServer, StateT.run, server] at supported
    split_ifs at supported
    case pos =>
      simp only [bind_pure_comp, support_map] at supported
      obtain ⟨inner, reached, rfl⟩ := supported
      cases ref
      case hidden slot admitted =>
        obtain ⟨seed, _, _, _, _, _, _, ownerRaw, produced, _⟩ :=
          PqxdhRecordLiftWorld.resolve_hidden_facts .server slot state inner reached
        simp [recordView, PqxdhRecordLiftWorld.rawCounters, PqxdhRecordLiftWorld.markUsed,
          ownerRaw, produced, server]
      case known value admitted =>
        change inner ∈ support (pure (value, state)) at reached
        simp_all [recordView, PqxdhRecordLiftWorld.rawCounters, PqxdhRecordLiftWorld.markUsed]
    all_goals simp_all
  all_goals simp_all [PqxdhRecordLiftWorld.installServer, StateT.run]

/-- Resolving a hidden or supplied kernel preserves the produced-frame and raw-counter record view. -/
theorem resolve_view {n : Nat} (role : Role) (ref : KernelRef n) (state : State n)
    (result : ConcreteRatchetKernel × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.resolve role ref).run state)) :
    recordView result.2 = recordView state := by
  cases ref
  case hidden slot =>
    obtain ⟨_, _, _, _, _, server, _, ownerRaw, produced, _⟩ :=
      PqxdhRecordLiftWorld.resolve_hidden_facts role slot state result supported
    simp [recordView, PqxdhRecordLiftWorld.rawCounters, server, ownerRaw, produced]
  all_goals simp_all [PqxdhRecordLiftWorld.resolve, StateT.run_pure]

/-- Beacon installation retains produced frames and the existing raw-attempt functions. -/
theorem install_beacon_view {n : Nat} (owner : Nat) (shell : BeaconShell)
    (ref : KernelRef n) (state : State n) (result : Bool × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.installBeacon owner shell ref).run state)) :
    recordView result.2 = recordView state := by
  simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run] at supported
  split_ifs at supported
  case pos =>
    simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    cases ref <;> exact resolve_view .beacon _ state inner reached
  all_goals simp_all

/-- Every restricted environment capability preserves the run-phase record view. -/
theorem capability_view {n : Nat} (query : (CapabilitySpec n).Domain) (state : State n)
    (result : (CapabilitySpec n).Range query × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.capability query).run state)) :
    recordView result.2 = recordView state := by
  cases query
  case advanceOwner owner phase =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run] at supported
    split at supported <;> (try split_ifs at supported) <;>
      simp_all [recordView, PqxdhRecordLiftWorld.rawCounters]
  case hash bytes =>
    simp only [PqxdhRecordLiftWorld.capability, PqxdhRecordLiftWorld.sampled, StateT.run,
      bind_pure_comp, Functor.map_map, support_map] at supported
    rcases supported with ⟨_, _, rfl⟩
    rfl
  all_goals first
    | exact install_server_view _ _ _ state result supported
    | exact install_beacon_view _ _ _ state result supported
    | simp_all [PqxdhRecordLiftWorld.capability, StateT.run, recordView, PqxdhRecordLiftWorld.rawCounters]

/-- Direct coins, shared hashes and administrative effects preserve the record-event projection. -/
theorem effects_view {n : Nat} (query : (EnvEffects n).Domain) (state : State n)
    (result : (EnvEffects n).Range query × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects query).run state)) :
    recordView result.2 = recordView state := by
  cases query
  case inl coin =>
    simp only [PqxdhRecordLiftWorld.effects, PqxdhRecordLiftWorld.sampled, StateT.run,
      bind_pure_comp, support_map] at supported
    rcases supported with ⟨_, _, rfl⟩
    rfl
  case inr request => exact capability_view request (PqxdhRecordLiftWorld.chargeEffect (.inr request) state) result supported

/-- Every actual World request outside the two record classes preserves their event coordinates. -/
theorem nonrecord_view {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : (WorldSpec n).Domain)
    (notSend : ¬ WorldRecord .send query) (notRaw : ¬ WorldRecord .raw query)
    (state : State n) (result : (WorldSpec n).Range query × State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.handler setup codec route query).run state)) :
    recordView result.2 = recordView state := by
  rcases query with created | (effect | record)
  case inl =>
    cases found : state.server <;> simp_all [PqxdhRecordLiftWorld.handler,
      PqxdhRecordLiftWorld.initializeServer, StateT.run, recordView, PqxdhRecordLiftWorld.rawCounters]
  case inr.inr => cases kind : recordKind record <;> simp_all [WorldRecord]
  case inr.inl => exact effects_view effect state result supported

/-- An adaptive schedule with no record requests cannot change any run-phase record event coordinate. -/
theorem schedule_view {ι KemSK Reader Response X : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) X)
    (sends : client.IsQueryBoundP (WorldRecord .send) 0)
    (raws : client.IsQueryBoundP (WorldRecord .raw) 0)
    (state : State n) (result : X × State n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route) client).run state)) :
    recordView result.2 = recordView state := by
  induction client using OracleComp.inductionOn generalizing state result
  case query_bind query next ih =>
    simp [isQueryBoundP_query_bind_iff] at sends raws
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, head, tail⟩ := supported
    exact (ih middle.1 (sends.2 middle.1) (raws.2 middle.1) middle.2 result tail).trans
      (nonrecord_view setup codec route query sends.1 raws.1 state middle head)
  all_goals simp_all

/-- The exact post embedding and native dispatch issue no record request, for every environment. -/
theorem post_record_bound {n : Nat} {E Out : Type} (env : Environment n E)
    (adversary : OracleComp PostSpec Out) (kind : RecordKind) (state : E) :
    ((post env adversary).run state).IsQueryBoundP (WorldRecord kind) 0 := by
  apply native_record_bound env kind (simulateQ postEmbed adversary) 0 _ state
  apply (isQueryBoundP_false adversary 0).simulateQ_of_step
  all_goals rintro (coin | (⟨key, message⟩ | bytes)) _ <;> cases kind <;>
    simp [postEmbed, isQueryBoundP_query_iff, NativeRecord, PqxdhDeploymentCompileBudget.commandKind]

/-- The full post computation preserves produced frames and raw counters without any Frame or budget premise. -/
theorem post_view {ι KemSK Reader Response E Out : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (adversary : OracleComp PostSpec Out) (environment : E) (state : State n)
    (result : (Out × E) × State n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
      ((post env adversary).run environment)).run state)) :
    recordView result.2 = recordView state := by
  exact schedule_view setup codec route _ (post_record_bound env adversary .send environment)
    (post_record_bound env adversary .raw environment) state result supported

/-- Run-phase record events retain constructor metadata and ledger but discard either phase's adversary output. -/
def eventView {n : Nat} {E X : Type}
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (X × PqxdhDeploymentSecrecy.Ledger) × E) × State n) :=
  result.1.map fun value => (value.1, value.2.1.2, recordView result.2)

/-- Every event on the retained run-phase record projection has exactly the same distribution after disclosure and post execution. -/
theorem run_event {ι KemSK E X Out R Reader Response : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (event : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      PqxdhDeploymentSecrecy.Ledger ×
      List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame) ×
      PqxdhRecordLiftWorld.RawCounters) → Bool) :
    𝒟[(event ∘ eventView) <$> run setup codec route env serverKid bounds mode reveal first second] =
      𝒟[(event ∘ eventView) <$> PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode first] := by
  simp only [run, program, PqxdhRecordLiftWorld.run, simulateQ_bind, StateT.run_bind, map_bind]
  conv_rhs => rw [map_eq_bind_pure_comp]
  apply evalDist_bind_congr
  rintro ⟨_ | ⟨created, ⟨output, ledger⟩, environment⟩, state⟩
  · simp [eventView]
  · simp only [simulateQ_bind, StateT.run_bind, map_bind, simulateQ_pure, StateT.run_pure,
      map_pure, Function.comp_apply, eventView, Option.map_some]
    conv_rhs => rw [← OracleComp.evalDist_bind_const
      ((simulateQ (PqxdhRecordLiftWorld.handler setup codec route)
        ((post env (second output (reveal environment))).run environment)).run state)]
    apply OracleComp.evalDist_bind_congr_of_support
    intro result supported
    rw [post_view setup codec route env _ environment state result supported]

/-- Additional World effects: direct post coins and hashes, plus every class-six environment effect. -/
def postCost (allowance : Fin 14 → EffectKind → Nat) (budget : PostBudget) (kind : EffectKind) : Nat :=
  (match kind with | .coin => budget.coin | .hash => budget.hash | .administrative => 0) +
    allowance 6 kind * budget.hmac

/-- The fixed three-class partition gives the closed post bill, including administrative work. -/
theorem postCost_partition (allowance : Fin 14 → EffectKind → Nat) (budget : PostBudget) (kind : EffectKind) :
    (∑ post, nativeCost allowance kind (PqxdhDeploymentLaterCompile.postCore post) * budget.cap post) =
      postCost allowance budget kind := by
  cases kind <;> simp [Fin.sum_univ_succ, nativeCost, PqxdhDeploymentLaterCompile.postCore,
    PostBudget.cap, postCost, Nat.add_comm]

/-- A separate PostBudget bounds the actual post World effects through the unchanged environment Frame. -/
theorem post_effect_bound {n : Nat} {E Out : Type} (env : Environment n E) (startupCoins : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (adversary : OracleComp PostSpec Out) (budget : PostBudget) (respects : budget.Respects adversary)
    (kind : EffectKind) (state : E) :
    ((post env adversary).run state).IsQueryBoundP (WorldEffect kind) (postCost allowance budget kind) := by
  rw [← postCost_partition]
  unfold post
  rw [← QueryImpl.simulateQ_compose]
  refine FinitePartitionQueryBounds.weighted_bound postClass
    (fun post => nativeCost allowance kind (PqxdhDeploymentLaterCompile.postCore post))
    budget.cap ((native env) ∘ₛ postEmbed) _ adversary respects (fun query state => ?_) state
  rcases query with coin | (⟨key, message⟩ | bytes)
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    exact native_bound env startupCoins allowance framed kind (.inl coin) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    exact native_bound env startupCoins allowance framed kind (.inr (.hmac key message)) state
  · simp only [QueryImpl.apply_compose, postEmbed, simulateQ_spec_query]
    exact native_bound env startupCoins allowance framed kind (.inr (.hash bytes)) state

/-- The post phase adds no sends or raw attempts, regardless of its length or environment effects. -/
theorem program_record_bound {n : Nat} {E X Out R Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : budget.Respects first) (kind : RecordKind) :
    (program env crypto codec serverKid bounds mode reveal first second).IsQueryBoundP
      (WorldRecord kind) (recordBudget budget kind) := by
  unfold program
  apply (isQueryBoundP_bind (m := 0)
    (PqxdhRecordLiftBudget.program_record_bound env crypto codec serverKid bounds mode budget first respects kind)
    ?_).mono (by omega)
  rintro (_ | ⟨created, ⟨output, ledger⟩, state⟩) _
  · exact isQueryBoundP_pure _ _ 0
  · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      post_record_bound env (second output (reveal state)) kind state

/-- The original startup and run bill plus a separate PostBudget bounds the complete two-phase program. -/
theorem program_effect_bound {n : Nat} {E X Out R Reader Response : Type} (env : Environment n E)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (crypto : Pqxdh.Crypto) (codec : Codec Reader Response) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps) (budget : PostBudget) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : caps.outer.Respects first) (laterRespects : ∀ output disclosed, budget.Respects (second output disclosed))
    (kind : EffectKind) :
    (program env crypto codec serverKid bounds mode reveal first second).IsQueryBoundP (WorldEffect kind)
      (startupCost startupCoins kind + (directCost caps.outer bounds kind + caps.envTotal allowance kind) +
        postCost allowance budget kind) := by
  unfold program
  apply isQueryBoundP_bind
    (PqxdhRecordLiftBudget.program_bound env startupCoins allowance framed crypto codec serverKid bounds mode caps
      first respects kind)
  rintro (_ | ⟨created, ⟨output, ledger⟩, state⟩) _
  · exact isQueryBoundP_pure _ _ _
  · simpa only [bind_pure_comp, isQueryBoundP_map_iff] using
      post_effect_bound env startupCoins allowance framed (second output (reveal state)) budget
        (laterRespects output (reveal state)) kind state

/-- Literal native record-call counts retain their run-phase weights, without a Frame or PostBudget premise. -/
theorem run_native {ι KemSK Reader Response E X Out R : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (budget : Budget) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : budget.Respects first) (kind : RawCtxMixedOwner.CallKind)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode reveal first second)) :
    result.2.primitive.1.native kind ≤
      RawCtxMixedOwner.sendCost kind * budget.sends + RawCtxMixedOwner.receiveCost kind * budget.receives := by
  simpa only [PqxdhRecordLiftWorld.initial, PqxdhRecordLiftWorld.Counts.empty, Nat.zero_add] using
    PqxdhRecordLiftWorldBudget.schedule_native setup codec route _ kind budget.sends budget.receives
      (program_record_bound env setup.source.crypto codec serverKid bounds mode budget reveal first second respects .send)
      (program_record_bound env setup.source.crypto codec serverKid bounds mode budget reveal first second respects .raw)
      PqxdhRecordLiftWorld.initial result supported

/-- Post execution leaves the ordinary-record derivation cap at exactly the established S+51R bound. -/
theorem run_kdf {ι KemSK Reader Response E X Out R : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : caps.outer.Respects first)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode reveal first second)) :
    result.2.primitive.1.native .kdf ≤ caps.derivations := by
  simpa only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost, Nat.one_mul, Caps.derivations] using
    run_native setup codec route env serverKid bounds mode caps.outer reveal first second respects .kdf result supported

/-- Actual effect counters obey the additive run and post bill through one complete World execution. -/
theorem run_effects {ι KemSK Reader Response E X Out R : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps) (budget : PostBudget) (reveal : E → R)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : caps.outer.Respects first) (laterRespects : ∀ output disclosed, budget.Respects (second output disclosed))
    (kind : EffectKind)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode reveal first second)) :
    result.2.primitive.1.effects kind ≤
      startupCost startupCoins kind + (directCost caps.outer bounds kind + caps.envTotal allowance kind) +
        postCost allowance budget kind := by
  simpa only [PqxdhRecordLiftWorld.initial, PqxdhRecordLiftWorld.Counts.empty, Nat.zero_add] using
    PqxdhRecordLiftWorldBudget.schedule_effects setup codec route _ kind _
      (program_effect_bound env startupCoins allowance framed setup.source.crypto codec serverKid bounds mode caps
        budget reveal first second respects laterRespects kind) PqxdhRecordLiftWorld.initial result supported

/-- Both routes to the shared hash cache include the explicit post hash and class-six hash allowance. -/
theorem run_hash {ι KemSK Reader Response E X Out R : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps) (budget : PostBudget) (reveal : E → R)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : caps.outer.Respects first) (laterRespects : ∀ output disclosed, budget.Respects (second output disclosed))
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode reveal first second)) :
    result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
      caps.outer.hash + caps.outer.sends + caps.outer.receives + caps.envTotal allowance .hash +
        postCost allowance budget .hash := by
  have nativeBound := run_native setup codec route env serverKid bounds mode caps.outer reveal
    first second respects .hash result supported
  have effectBound := run_effects setup codec route env serverKid bounds mode caps budget reveal
    startupCoins allowance framed first second respects laterRespects .hash result supported
  simp only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost, Nat.one_mul,
    startupCost, directCost, Nat.zero_add] at nativeBound effectBound
  omega

/-- One complete two-phase execution charges direct coins, shared-hash sampling and all actual seed draws. -/
theorem run_uniform_counts {ι KemSK Reader Response E X Out R : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode reveal first second)) :
    result.2.primitive.1.uniform ≤ result.2.primitive.1.effects .coin +
      64 * (result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash) +
      64 * result.2.seeds.2.draws := by
  have bound := PqxdhRecordLiftWorldBudget.schedule_uniform setup codec route _
    PqxdhRecordLiftWorld.initial result supported
  simpa [PqxdhRecordLiftWorldBudget.uniformCredit, PqxdhRecordLiftWorld.initial,
    PqxdhRecordLiftWorld.Counts.empty, PqxdhRecordLiftLazyTable.initial, Nat.mul_add, Nat.add_assoc] using bound

/-- Both phases share one seed table: draws equal occupied slots and are bounded once by n. -/
theorem run_seed_draws {ι KemSK Reader Response E X Out R : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (reveal : E → R)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode reveal first second)) :
    result.2.seeds.2.draws = (PqxdhRecordLiftWorldBudget.cachedSlots result.2.seeds.1).card ∧
      result.2.seeds.2.draws ≤ n := by
  have accounted := PqxdhRecordLiftWorldBudget.schedule_seed_accounting setup codec route _
    PqxdhRecordLiftWorld.initial result supported
  have exactCount : result.2.seeds.2.draws = (PqxdhRecordLiftWorldBudget.cachedSlots result.2.seeds.1).card := by
    simpa [PqxdhRecordLiftWorldBudget.SeedAccounting, PqxdhRecordLiftWorld.initial,
      PqxdhRecordLiftLazyTable.initial, PqxdhRecordLiftWorldBudget.cachedSlots] using accounted
  exact ⟨exactCount, exactCount.le.trans (PqxdhRecordLiftWorldBudget.cachedSlots_bound result.2.seeds.1)⟩

/-- The final uniform bill has additive post work and a single shared 64*n seed contribution. -/
theorem run_uniform {ι KemSK Reader Response E X Out R : Type} {baseSpec : OracleSpec ι} {n : Nat}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (serverKid : Std.U64)
    (bounds : FreshBounds) (mode : Mode) (caps : Caps) (budget : PostBudget) (reveal : E → R)
    (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat) (framed : Frame env startupCoins allowance)
    (first : OracleComp (ModeSpec mode) X) (second : X → R → OracleComp PostSpec Out)
    (respects : caps.outer.Respects first) (laterRespects : ∀ output disclosed, budget.Respects (second output disclosed))
    (result : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit ×
      (Out × PqxdhDeploymentSecrecy.Ledger) × E) × State n)
    (supported : result ∈ support (run setup codec route env serverKid bounds mode reveal first second)) :
    result.2.primitive.1.uniform ≤
      startupCoins + caps.outer.coin + caps.outer.test + bounds.max * caps.outer.fresh +
        caps.envTotal allowance .coin + postCost allowance budget .coin +
      64 * (caps.outer.hash + caps.outer.sends + caps.outer.receives + caps.envTotal allowance .hash +
        postCost allowance budget .hash) + 64 * n := by
  have counts := run_uniform_counts setup codec route env serverKid bounds mode reveal first second result supported
  have coins := run_effects setup codec route env serverKid bounds mode caps budget reveal startupCoins allowance framed
    first second respects laterRespects .coin result supported
  have hashes := run_hash setup codec route env serverKid bounds mode caps budget reveal startupCoins allowance framed
    first second respects laterRespects result supported
  have draws := (run_seed_draws setup codec route env serverKid bounds mode reveal first second result supported).2
  simp only [startupCost, directCost] at coins
  omega

end BeaconcryptCore.Computational.PqxdhRecordLiftLater

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.install_server_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.install_server_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.resolve_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.resolve_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.install_beacon_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.install_beacon_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.capability_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.capability_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.effects_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.effects_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.nonrecord_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.nonrecord_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.schedule_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.schedule_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.post_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.post_record_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.post_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.post_view

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_event

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.postCost_partition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.postCost_partition

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.post_effect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.post_effect_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.program_record_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.program_record_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.program_effect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.program_effect_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_kdf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_kdf

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_hash

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_uniform_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_uniform_counts

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_seed_draws' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_seed_draws

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftLater.run_uniform
